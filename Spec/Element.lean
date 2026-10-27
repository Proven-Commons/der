/-
  The tree a DER element reads into. Part of the specification: a
  reviewer approves it with `Spec.lean` and `Spec/Defs.lean`. The code in
  `Der/` and the definitions in `Spec/Defs.lean` both use it, and it
  holds no logic.
-/

namespace Der

/-- One element of an encoding (X.690 8.1.1): its tag, given by a class
    and a number (8.1.2), and its contents (8.1.4).

    The class is 0 for universal, 1 for application, 2 for
    context-specific and 3 for private, as in Table 1 of X.690.

    A primitive element holds its contents octets. A constructed element
    holds the elements its contents octets encode, in order. -/
inductive Element where
  | prim (cls tag : Nat) (contents : List UInt8)
  | cons (cls tag : Nat) (children : List Element)
  deriving Repr, Inhabited

end Der
