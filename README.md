# der: reading and writing DER (X.690), proved

DER, the Distinguished Encoding Rules of ASN.1, is how X.509 certificates, ECDSA signatures, PKCS and CMS are written. Every TLS client and every signature checker reads it from bytes someone else chose. DER allows exactly one encoding of each value, and much of its security rests on that. When a reader accepts a second encoding of the same value, a signature can be forged against a lenient checker, or two parsers disagree about what a certificate says. Malformed lengths have also given out-of-bounds reads more than once. This first slice gives that guarantee for the framing of every element and for the contents of four types; "What is not proved" lists the types whose contents it does not yet check.

This library reads and writes one DER element, nested to any depth, in Lean:

- identifier octets, with tag numbers of any size (X.690 8.1.2);
- length octets, definite and in the fewest octets (8.1.3, 10.1);
- the contents of a primitive element, or the elements of a constructed one;
- the form, primitive or constructed, that DER gives each universal type, and the contents of BOOLEAN, INTEGER, ENUMERATED and NULL.

Machine-checked proofs show:

- **The reader accepts exactly the encodings of the elements this slice accepts.** It accepts an input exactly when the input starts with the encoding X.690 gives an element this slice accepts, and then gives back the element and the octets after it. So it never reads past the end of its input, and every element it gives lies inside its parent's contents. That is exactly DER for the identifier, length and structure of every element and for the contents of BOOLEAN, INTEGER, ENUMERATED and NULL. For the contents of other types it accepts more than DER does.
- **One encoding per element, one element per input.** Each element has one encoding the reader accepts, and an input starts with the encoding of at most one element. Writing back what the reader read gives the same octets. For the four checked types this is one encoding per value; for the others, two contents octet strings for the same value are two elements.
- **The writer writes the encoding.** It writes `Der.Spec.der` for every tree, and `Der.valid` says whether this slice accepts the tree. For a tree this slice accepts, `Der.Spec.der` is the encoding X.690 gives it, apart from the contents of the types listed under "What is not proved".
- **Integers have one encoding.** `readInt` accepts exactly the contents octets X.690 allows for an INTEGER and gives their value. `writeInt` writes them, and each integer has exactly one.

It is tested against a model of X.690 and other implementations; `tests/TEST-RESULTS.md` holds the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean, on `List UInt8`, with the tree `Der.Element` of `Der/Spec/Element.lean`:

- `Der.decode : List UInt8 → Option (Element × List UInt8)`: the element at the start of the input, and the octets after it.
- `Der.decodeAll : List UInt8 → Option Element`: the element that is the whole input.
- `Der.encode : Element → List UInt8`.
- `Der.valid : Element → Bool`: whether this slice accepts an element.
- `Der.readInt : List UInt8 → Option Int` and `Der.writeInt : Int → List UInt8`: the contents octets of an INTEGER.

An element is `.prim cls tag contents` or `.cons cls tag children`. The class can be any number in the type; `Der.valid` accepts only 0 (universal), 1 (application), 2 (context-specific) and 3 (private). `SPEC.md` says what each function does.

## What is proved

The statements are in `Der/Spec.lean`. The definitions they use are in `Der/Spec/Defs.lean`, written from X.690 (02/2021) and Table 1 of X.680, and the proofs are in `Der/Proofs/`.

| Claim | Theorem |
|-------|---------|
| The writer writes `Der.Spec.der` for every tree. For a tree this slice accepts, that is the encoding X.690 gives it, apart from the contents of the types listed under "What is not proved". | `Der.Spec.encode_eq` |
| `Der.valid` says whether this slice accepts an element. | `Der.Spec.valid_iff` |
| The reader accepts exactly a DER encoding of such an element, followed by anything, and gives back the element and what follows. | `Der.Spec.decode_iff` |
| An input starts with the encoding of at most one element this slice accepts: two whose encodings start the same input are the same, and so is what follows. | `Der.Spec.encoding_unique` |
| Reading what the writer wrote gives back the element. | `Der.Spec.decode_encode` |
| The whole input is one element exactly when it is such an encoding. | `Der.Spec.decodeAll_iff` |
| `readInt` accepts exactly the contents of an INTEGER that X.690 allows, and gives the integer. | `Der.Spec.readInt_iff` |
| `writeInt` writes such contents for the integer, and they are the only ones. | `Der.Spec.writeInt_spec`, `Der.Spec.writeInt_unique` |
| X.690's examples: lengths 38 and 201, BOOLEAN TRUE, and the primitive "Jones" of 8.23.5, with a tag number of 201 in the high form worked by hand. Nineteen inputs that each break a rule are refused, among them the two constructed forms of "Jones". | `Der.Spec.x690_examples`, `Der.Spec.x690_rejects` |

The elements this slice accepts, `Der.Spec.Valid`, are those whose class is one of the four, whose length octets have at most 126 octets after the first, and whose universal tags follow the rules of `SPEC.md`:

- tag 0 is not used;
- 8, 11, 16, 17 and 29 are constructed;
- 15 and 37 and up may be either;
- every other universal tag is primitive;
- a BOOLEAN is 00 or FF, an INTEGER or ENUMERATED is in the fewest octets, and a NULL is empty.

## What is not proved

- **The contents of other types.** These are read as octets and not checked, so the reader accepts encodings DER forbids, and more than one encoding of the same value:
  - REAL (8.5, 11.3);
  - BIT STRING: the initial octet and unused bits (8.6.2, 11.2.1);
  - OBJECT IDENTIFIER and RELATIVE-OID subidentifiers (8.19.2, 8.20.2), and the IRI types (8.21.2, 8.22.2);
  - the string types: UTF-8 in the fewest octets (8.23.10), BMPString and UniversalString lengths (8.23.7, 8.23.8), GeneralString escapes (11.4);
  - UTCTime and GeneralizedTime (11.7, 11.8), and TIME and its subtypes (8.26, 11.9);
  - the components of EXTERNAL, EMBEDDED PDV and CHARACTER STRING (8.16 to 8.18, 8.24), so even an empty one is accepted.

  ECDSA-Sig-Value is the second slice.
- **Rules that depend on the ASN.1 type.** DER orders the components of a SET by tag (10.3) and of a SET OF by encoding (11.6), leaves out components equal to their default (11.5), and drops trailing zero bits from a named bit list (11.2.2). Without a schema, only a weak condition on a SET can be checked: its components are either in tag order or in encoding order. This slice does not check even that.
- **Time and memory.** No proof bounds them. The reader is written to take time linear in its input: it never measures more of the input than an element's length, and it adds up long tag numbers and lengths by halves. Its recursion depth is the nesting depth. The writer is not linear: each level of nesting copies the encoding of what it holds, so its time grows with the square of the nesting depth. Writing a tree 10,000 levels deep takes about 1.6 s, and 100,000 levels about 190 s. `Der.valid` is slower: at each level it writes and measures the encoding of what that level holds, so its time grows about with the cube of the nesting depth. It takes about 3.4 s for a tree 1,000 levels deep, and 38 s for 2,000. The tests time only nested requests: each one goes to a process of its own, which must answer within 60 seconds. They read trees 10,000 and 100,000 levels deep, write ones 10,000 deep, and ask `Der.valid` of ones 1,000 deep.
- **Reading requests and printing answers in `Main.lean`.** The differential tests cover them.

## What you must trust

- The Lean kernel and the five external kernels shipped with Lean, which all check the proofs.
- `lake comparator`, which builds the statements and the proofs in a sandbox, exports them, and checks that each proof proves exactly its statement.
- bubblewrap and the Linux kernel's namespaces, which keep the untrusted build from tampering with that check.
- The Lean compiler, with the C compiler and linker shipped with it, and the runtime, which turn the proved definitions into the program that runs.
- Lean's core library, including the compiled code it puts in place of some definitions the proofs reason about, such as natural number and integer arithmetic, `UInt8`, and the conversion between strings and their characters.
- The operating system and hardware it runs on.
- For the tests only: the model in `tests/run_tests.py`, and the implementations it compares against. The record names their versions.

This project has no dependencies beyond Lean itself.

## Re-check it

Needs Linux, [elan](https://github.com/leanprover/elan), bubblewrap (`apt install bubblewrap`) and Python 3. The oracles also need Go, Rust (cargo) and OpenSSL's headers; the test script leaves out any it cannot build, and the record names them.

```
lake build
lake comparator --paranoid
python3 tests/run_tests.py
python3 tests/plant_bugs.py
```

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Der/Proofs/` proves exactly the statement in `Der/Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

## Layout

- `Der/Basic.lean`: the code under proof.
- `Der/Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Der/Spec/Defs.lean`: the definitions the statements use, written from X.690.
- `Der/Spec/Element.lean`: the tree an element reads into.
- `Der/Proofs.lean` and `Der/Proofs/`: the proofs.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/`: the differential tests, the oracles, and the planted bugs.
