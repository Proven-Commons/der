/-
  A reader and writer for DER (X.690): one element, nested to any depth.
-/

import Der.Spec.Element

namespace Der

/-! ## Numbers -/

/-- The value of digits in base `2 ^ w`, most significant first. It adds
    up the two halves separately, so a long input takes close to linear
    time rather than the quadratic time of adding one digit at a time to
    a growing number. -/
def ofDigits (w : Nat) (ds : List Nat) : Nat := go ds.length ds
where
  /-- `fuel` bounds the depth of the halving; the length is enough. -/
  go : Nat → List Nat → Nat
    | 0, _ => 0
    | fuel + 1, ds =>
      if ds.length ≤ 16 then ds.foldl (fun n d => n * 2 ^ w + d) 0
      else
        let h := ds.length / 2
        (go fuel (ds.take h) <<< (w * (ds.length - h))) + go fuel (ds.drop h)

/-- The digits of `n` in base `2 ^ w`, most significant first, put in
    front of `acc`. `fuel` bounds the steps; `n` is enough. -/
def toDigitsAux (w : Nat) : Nat → Nat → List Nat → List Nat
  | 0, _, acc => acc
  | fuel + 1, n, acc => if n = 0 then acc else toDigitsAux w fuel (n >>> w) (n % 2 ^ w :: acc)

/-- The digits of `n` in base `2 ^ w`, most significant first, with no
    leading zero: `[0]` for zero. -/
def toDigits (w n : Nat) : List Nat := if n = 0 then [0] else toDigitsAux w n n []

/-! ## Writing -/

/-- The identifier octets for a tag (X.690 8.1.2). -/
def identOctets (cls : Nat) (constructed : Bool) (tag : Nat) : List UInt8 :=
  let lead := cls % 4 * 64 + if constructed then 32 else 0
  if tag < 31 then [(lead + tag).toUInt8]
  else
    let ds := toDigits 7 tag
    (lead + 31).toUInt8 :: (ds.dropLast.map fun d => (d + 128).toUInt8) ++ [(ds.getLastD 0).toUInt8]

/-- The length octets for `n` contents octets, in the fewest octets
    (X.690 8.1.3, 10.1). -/
def lengthOctets (n : Nat) : List UInt8 :=
  if n < 128 then [n.toUInt8]
  else
    let ds := toDigits 8 n
    (128 + ds.length).toUInt8 :: ds.map Nat.toUInt8

mutual
/-- The encoding of an element, as `Der.Spec.der` writes it. -/
def encode : Element → List UInt8
  | .prim cls tag c => identOctets cls false tag ++ lengthOctets c.length ++ c
  | .cons cls tag cs =>
    let body := encodeList cs
    identOctets cls true tag ++ lengthOctets body.length ++ body

/-- The encodings of elements, one after another. -/
def encodeList : List Element → List UInt8
  | [] => []
  | e :: es => encode e ++ encodeList es
end

/-! ## Reading -/

/-- Splits off the subsequent octets of a tag number of 31 or more: the
    octets with bit 8 one, then the first with it zero. Gives their bits
    7 to 1, most significant first, after `acc` reversed, and the octets
    after them. -/
def splitTag : List UInt8 → List Nat → Option (List Nat × List UInt8)
  | [], _ => none
  | b :: bs, acc =>
    if b.toNat < 128 then some ((b.toNat :: acc).reverse, bs)
    else splitTag bs ((b.toNat - 128) :: acc)

/-- The identifier octets at the start of the input: the class, whether
    the element is constructed, the tag number, how many octets they
    take, and the octets after them. Refuses a first subsequent octet
    with bits 7 to 1 zero (8.1.2.4.2 c) and a number below 31 written in
    more than one octet (8.1.2.2). -/
def readIdentifier : List UInt8 → Option (Nat × Bool × Nat × Nat × List UInt8)
  | [] => none
  | b :: bs =>
    let cls := b.toNat / 64
    let constructed := b.toNat / 32 % 2 == 1
    if b.toNat % 32 < 31 then some (cls, constructed, b.toNat % 32, 1, bs)
    else
      match splitTag bs [] with
      | some (d :: ds, rest) =>
        if d = 0 then none
        else
          let tag := ofDigits 7 (d :: ds)
          if tag < 31 then none else some (cls, constructed, tag, ds.length + 2, rest)
      | _ => none

/-- The length given by `k` subsequent length octets of the long form
    at the start of the input, how many length octets there are, and the
    octets after them. Refuses a leading zero octet and a length below
    128, which are not the fewest octets (10.1). -/
def readLong (k : Nat) (bs : List UInt8) : Option (Nat × Nat × List UInt8) :=
  let ds := bs.take k
  if ds.length < k ∨ ds.head? = some 0 then none
  else
    let n := ofDigits 8 (ds.map UInt8.toNat)
    if n < 128 then none else some (n, k + 1, bs.drop k)

/-- The length octets at the start of the input: the length, how many
    octets they take, and the octets after them. Refuses the indefinite
    form (10.1), the initial octet all ones (8.1.3.5 c), and any length
    not in the fewest octets (10.1). -/
def readLength : List UInt8 → Option (Nat × Nat × List UInt8)
  | [] => none
  | b :: bs =>
    if b.toNat < 128 then some (b.toNat, 1, bs)
    else if b.toNat - 128 = 0 ∨ b.toNat - 128 = 127 then none
    else readLong (b.toNat - 128) bs

/-- The universal tags of types encoded as constructed: 8, 11, 16, 17
    and 29. -/
def constructedUniversal (tag : Nat) : Bool :=
  tag == 8 || tag == 11 || tag == 16 || tag == 17 || tag == 29

/-- The universal tags assigned to no type: 15, and 37 on. -/
def reservedUniversal (tag : Nat) : Bool := tag == 15 || 37 ≤ tag

/-- Contents octets of an integer in the fewest octets (8.3.1, 8.3.2). -/
def intOk : List UInt8 → Bool
  | [] => false
  | [_] => true
  | a :: b :: _ => !(a.toNat == 255 && 128 ≤ b.toNat) && !(a.toNat == 0 && b.toNat < 128)

/-- Whether the contents of a primitive universal element are allowed:
    a boolean is 0 or all ones (8.2, 11.1), an integer or an enumerated
    value is in the fewest octets (8.3, 8.4), and a null is empty
    (8.8.2). Other types are not checked in this slice. -/
def contentsOk (tag : Nat) (c : List UInt8) : Bool :=
  match tag with
  | 1 => c == [0] || c == [255]
  | 2 => intOk c
  | 5 => c.isEmpty
  | 10 => intOk c
  | _ => true

/-- Whether a primitive element's tag and contents are allowed: in the
    universal class, not tag 0 or a constructed type, and contents as
    `contentsOk` says. -/
def primOk (cls tag : Nat) (c : List UInt8) : Bool :=
  cls != 0 || (tag != 0 && !constructedUniversal tag && contentsOk tag c)

/-- Whether a constructed element's tag is allowed. -/
def consOk (cls tag : Nat) : Bool :=
  cls != 0 || constructedUniversal tag || reservedUniversal tag

mutual
/-- The element at the start of `b`, if it takes at most `lim` octets:
    the element, the octets it takes, and the octets after it. `fuel`
    bounds the recursion; the length of the input is enough. -/
def readElement : Nat → Nat → List UInt8 → Option (Element × Nat × List UInt8)
  | 0, _, _ => none
  | fuel + 1, lim, b =>
    match readIdentifier b with
    | none => none
    | some (cls, constructed, tag, n1, b1) =>
      match readLength b1 with
      | none => none
      | some (len, n2, b2) =>
        if lim < n1 + n2 + len then none
        else if constructed then
          if consOk cls tag then
            match readElements fuel len b2 with
            | some (cs, b3) => some (.cons cls tag cs, n1 + n2 + len, b3)
            | none => none
          else none
        else
          -- `take` stops at the end of the input, so this costs at most
          -- the length of the contents.
          let c := b2.take len
          if c.length = len ∧ primOk cls tag c = true then
            some (.prim cls tag c, n1 + n2 + len, b2.drop len)
          else none

/-- Elements one after another at the start of `b`, taking exactly `lim`
    octets, and the octets after them. -/
def readElements : Nat → Nat → List UInt8 → Option (List Element × List UInt8)
  | _, 0, b => some ([], b)
  | 0, _ + 1, _ => none
  | fuel + 1, lim, b =>
    match readElement fuel lim b with
    | some (e, n, b') =>
      match readElements fuel (lim - n) b' with
      | some (es, b'') => some (e :: es, b'')
      | none => none
    | none => none
end

/-- The DER element at the start of the input, and the octets after it,
    or `none` when the input does not start with one. -/
def decode (b : List UInt8) : Option (Element × List UInt8) :=
  match readElement b.length b.length b with
  | some (e, _, rest) => some (e, rest)
  | none => none

/-- The DER element that is the whole input, or `none`. -/
def decodeAll (b : List UInt8) : Option Element :=
  match decode b with
  | some (e, []) => some e
  | _ => none

mutual
/-- Whether this slice accepts an element: whether `decode` would read
    back what `encode` writes for it. -/
def valid : Element → Bool
  | .prim cls tag c => cls < 4 && primOk cls tag c && c.length < 256 ^ 126
  | .cons cls tag cs =>
    cls < 4 && consOk cls tag && validList cs && (encodeList cs).length < 256 ^ 126

/-- Whether this slice accepts each element of a list. -/
def validList : List Element → Bool
  | [] => true
  | e :: es => valid e && validList es
end

/-! ## Integers -/

/-- The integer that contents octets encode, or `none` when they are not
    in the fewest octets (X.690 8.3). -/
def readInt (c : List UInt8) : Option Int :=
  if intOk c then
    let u := ofDigits 8 (c.map UInt8.toNat)
    match c with
    | a :: _ => some (if a.toNat < 128 then (u : Int) else (u : Int) - 2 ^ (8 * c.length))
    | [] => none
  else none

/-- The contents octets of an integer, in the fewest octets: for `z ≥ 0`
    the octets of `z`, with a zero octet in front when bit 8 of the first
    is one; for `z < 0` the same for `-z - 1`, with every bit flipped. -/
def writeInt (z : Int) : List UInt8 :=
  let m := if 0 ≤ z then z.toNat else (-z - 1).toNat
  let ds := (toDigits 8 m).map Nat.toUInt8
  let ds := match ds with
    | d :: _ => if 128 ≤ d.toNat then 0 :: ds else ds
    | [] => [0]
  if 0 ≤ z then ds else ds.map (255 - ·)

end Der
