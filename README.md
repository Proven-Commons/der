# der: reading and writing DER (X.690), proved

DER, the Distinguished Encoding Rules of ASN.1, is how X.509 certificates, ECDSA signatures, PKCS and CMS are written. Every TLS client and every signature checker reads it from bytes someone else chose. DER allows exactly one encoding of each value, and much of its security rests on that. When a reader accepts a second encoding of the same value, a signature can be forged against a lenient checker, or two parsers disagree about what a certificate says. Malformed lengths have also given out-of-bounds reads more than once.

This library reads and writes one DER element, nested to any depth, in Lean:

- identifier octets, with tag numbers of any size (X.690 8.1.2);
- length octets, definite and in the fewest octets (8.1.3, 10.1);
- the contents of a primitive element, or the elements of a constructed one;
- the form, primitive or constructed, that DER gives each universal type, and the contents of BOOLEAN, INTEGER and NULL.

Machine-checked proofs show:

- **The reader accepts exactly DER.** It accepts an input exactly when the input starts with the DER encoding of an element this slice accepts. It then gives back the element and the octets after it. So it never reads past the end of its input, and every element it gives lies inside its parent's contents.
- **Each element has one encoding.** Two elements whose encodings start the same input are equal. Writing back what the reader read gives the same octets.
- **The writer writes DER.** It writes, for every such element, the encoding X.690 gives it.
- **Integers have one encoding.** `readInt` accepts exactly the contents octets X.690 allows for an INTEGER and gives their value. `writeInt` writes them, and each integer has exactly one.

It is tested against a model of X.690 and other implementations; `tests/TEST-RESULTS.md` holds the record. It is a project of [Proven Commons](https://github.com/Proven-Commons/mission), built to the verified bar published there.

Status: in progress. The specification has not yet been approved by a reviewer apart from its author, so this is not verified.

## Use it

From Lean, on `List UInt8`, with the tree `Der.Element` of `Spec/Element.lean`:

- `Der.decode : List UInt8 → Option (Element × List UInt8)`: the element at the start of the input, and the octets after it.
- `Der.decodeAll : List UInt8 → Option Element`: the element that is the whole input.
- `Der.encode : Element → List UInt8`.
- `Der.readInt : List UInt8 → Option Int` and `Der.writeInt : Int → List UInt8`: the contents octets of an INTEGER.

An element is `.prim cls tag contents` or `.cons cls tag children`, with the class 0 (universal), 1 (application), 2 (context-specific) or 3 (private). `SPEC.md` says what each function does.

## What is proved

The statements are in `Spec.lean`. The definitions they use are in `Spec/Defs.lean`, written from X.690 (02/2021) and Table 1 of X.680, and the proofs are in `Proofs/`.

| Claim | Theorem |
|-------|---------|
| The writer writes the DER encoding of every element this slice accepts. | `Spec.encode_eq` |
| The reader accepts exactly a DER encoding of such an element, followed by anything, and gives back the element and what follows. | `Spec.decode_iff` |
| Two such elements whose encodings start the same input are the same, and so is what follows. | `Spec.encoding_unique` |
| Reading what the writer wrote gives back the element. | `Spec.decode_encode` |
| The whole input is one element exactly when it is such an encoding. | `Spec.decodeAll_iff` |
| `readInt` accepts exactly the contents of an INTEGER that X.690 allows, and gives the integer. | `Spec.readInt_iff` |
| `writeInt` writes such contents for the integer, and they are the only ones. | `Spec.writeInt_spec`, `Spec.writeInt_unique` |
| X.690's examples: lengths 38 and 201, BOOLEAN TRUE, and the primitive "Jones" of 8.23.5. Seventeen inputs that each break one rule are refused, among them the two constructed forms of "Jones". | `Spec.x690_examples`, `Spec.x690_rejects` |

The elements this slice accepts, `Spec.Valid`, are those whose class is one of the four, whose lengths fit in at most 126 length octets, and whose universal tags follow the rules of `SPEC.md`:

- tag 0 is not used;
- 8, 11, 16, 17 and 29 are constructed;
- 15 and 37 and up may be either;
- every other universal tag is primitive;
- a BOOLEAN is 00 or FF, an INTEGER is in the fewest octets, and a NULL is empty.

## What is not proved

- **The contents of other types.** BIT STRING unused bits, OBJECT IDENTIFIER subidentifiers, the string types, the times and REAL are read as octets and not checked. ECDSA-Sig-Value is the second slice.
- **Rules that depend on the ASN.1 type.** DER orders the components of a SET by tag (10.3) and of a SET OF by encoding (11.6), and leaves out components equal to their default (11.5). A reader with no schema cannot check these, so this one does not.
- **Time and memory.** No proof bounds them. The reader is written to take time linear in its input: it never measures more of the input than an element's length, and it adds up long tag numbers and lengths by halves. Its recursion depth is the nesting depth. The tests time deep and long inputs.
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

`lake comparator --paranoid` builds the statements and the proofs in a sandbox. It checks that each theorem in `Proofs/` proves exactly the statement in `Spec.lean`, using only the axioms `propext`, `Classical.choice`, and `Quot.sound`, and replays it through every kernel shipped with Lean.

## Layout

- `Der/Basic.lean`: the code under proof.
- `Spec.lean`: the statements, with `sorry` for proofs. A reviewer approves this file.
- `Spec/Defs.lean`: the definitions the statements use, written from X.690.
- `Spec/Element.lean`: the tree an element reads into.
- `Proofs.lean` and `Proofs/`: the proofs.
- `Main.lean`: the command-line tool the tests drive.
- `lakefile.toml`: the build. It names the package and its version, its libraries and executable, and the default targets, and sets nothing else.
- `comparator.json`: which theorems `lake comparator` checks, and which axioms it allows.
- `bar.toml`: the record for the bar check: status, authors, approvals, and where things are.
- `SPEC.md`: the specification in plain words.
- `tests/`: the differential tests, the oracles, and the planted bugs.
