# Specification: der

DER, the Distinguished Encoding Rules of ASN.1 (Rec. ITU-T X.690, https://www.itu.int/rec/T-REC-X.690), writes each value in exactly one way. X.509 certificates, ECDSA signatures, PKCS and CMS all use it. This library reads and writes one DER element, nested to any depth:

- its identifier octets: the class and number of its tag, and whether it is primitive or constructed (8.1.2);
- its length octets, in the definite form and the fewest octets (8.1.3, 10.1);
- its contents: octets for a primitive element, and the elements they encode for a constructed one (8.1.4).

It checks the contents of four universal types, BOOLEAN, INTEGER, ENUMERATED and NULL, and the form (primitive or constructed) of every universal type. The contents of other types (REAL, BIT STRING, OBJECT IDENTIFIER, RELATIVE-OID, the IRI types, the strings, the times, and the components of EXTERNAL, EMBEDDED PDV and CHARACTER STRING) are a later slice, and `Der/Spec/Defs.lean` lists the clauses it leaves unchecked. So is the order of SET components, which depends on the ASN.1 type.

A reviewer who did not write this specification approves it. The approval also covers `Der/Spec.lean`, `Der/Spec/Defs.lean`, `Der/Spec/Element.lean`, and the other files that `bar.toml` lists.

## Elements

`Der/Spec/Element.lean` gives the tree: an element is primitive, with a class, a tag number and contents octets, or constructed, with a class, a tag number and a list of elements. The class can be any number in the type. Table 1 of X.690 has four classes, 0 (universal), 1 (application), 2 (context-specific) and 3 (private), and `Der.Spec.Valid` accepts only these.

`Der/Spec/Defs.lean` writes the DER encoding of a tree, `Der.Spec.der`, from X.690:

- **Identifier octets** (8.1.2). A tag number up to 30 is one octet: the class in bits 8 and 7, bit 6 one for constructed, the number in bits 5 to 1. A larger number is a leading octet with bits 5 to 1 all ones, then the number in base 128, most significant first, bit 8 set on every octet but the last, and no leading zero digit.
- **Length octets** (8.1.3, 10.1). DER uses the definite form "encoded in the minimum number of octets": a single octet up to 127, and above that an octet giving the number of octets that follow, then the length in base 256 with no leading zero.
- **Contents octets** (8.1.4). A constructed element's contents are the encodings of its elements, one after another.

`Der.Spec.Valid` says which trees this slice accepts:

- the class is one of the four;
- the length fits the long form, whose first octet may not be all ones (8.1.3.5 c), so at most 126 octets follow it;
- in the universal class, tag 0 is not used (X.680 Table 1 reserves it for the encoding rules, and DER has no end-of-contents octets);
- tags 8, 11, 16, 17 and 29 (external, embedded-pdv, sequence, set, character string) are constructed, tags 15 and 37 and up (reserved in X.680) may be either, and every other universal tag is primitive, as clauses 8 and 10.2 require;
- a BOOLEAN's contents are 00 or FF (8.2, 11.1), an INTEGER's are one or more octets in the fewest (8.3.1, 8.3.2), and so are an ENUMERATED's, since it is encoded as its integer (8.4), and a NULL's are empty (8.8.2).

`Der.Spec.der v` is a DER encoding of `v` exactly when `Der.Spec.Valid v` holds and the contents of the types this slice does not check are as DER asks. For a tree outside `Der.Spec.Valid`, `Der.Spec.der` still gives octets, but the reader does not read them back as that tree.

**The writer** writes `Der.Spec.der` for every tree. `Der.valid` says whether a tree is in `Der.Spec.Valid`.

**The reader** accepts exactly the octet strings that start with `Der.Spec.der` of a tree this slice accepts, and gives back the tree and the octets after it. Since `Der.Spec.der` puts each element's encoding inside its parent's contents, every element the reader gives lies inside its parent, and the reader never reads past the end of its input. Since `Der.Spec.der` is a function, each tree has one encoding the reader accepts; since the reader is a function, each input starts with the encoding of at most one tree (`encoding_unique`). For BOOLEAN, INTEGER, ENUMERATED and NULL that is one encoding per value. For the contents of other types it is not: two contents octet strings that encode the same value, one of which DER forbids, are two trees here. Reading the whole input as one element is the same with nothing after it.

## Integers

`Der.Spec.IntegerContents` is 8.3.1 and 8.3.2: one or more octets, and when there are two or more, the bits of the first octet and bit 8 of the second are not all ones and not all zero. `Der.Spec.integerValue` is 8.3.3: the octets as a two's complement number.

**`readInt`** accepts exactly the allowed contents and gives the integer they encode. **`writeInt`** writes allowed contents that encode the integer. Each integer has one encoding: allowed contents are what `writeInt` writes for their value.

## What must always hold

Each property is a theorem in `Der/Spec.lean`, under the name given.

| Property | Theorem |
|----------|---------|
| The writer writes `Der.Spec.der` for every tree. | `Der.Spec.encode_eq` |
| `Der.valid` says whether a tree is in `Der.Spec.Valid`. | `Der.Spec.valid_iff` |
| The reader accepts exactly an encoding of such a tree followed by anything, and gives back the tree and what follows. | `Der.Spec.decode_iff` |
| Two trees with encodings at the start of the same input are the same, and so is what follows. | `Der.Spec.encoding_unique` |
| Reading what the writer wrote gives back the tree. | `Der.Spec.decode_encode` |
| The whole input is one element exactly when it is such an encoding. | `Der.Spec.decodeAll_iff` |
| `readInt` accepts exactly the allowed contents of an integer and gives its value. | `Der.Spec.readInt_iff` |
| `writeInt` writes allowed contents for the integer. | `Der.Spec.writeInt_spec` |
| Allowed contents are what `writeInt` writes for their value. | `Der.Spec.writeInt_unique` |
| The examples of X.690: lengths 38 and 201, BOOLEAN TRUE, and the primitive "Jones" of 8.23.5; and a tag number of 201 in the high form, worked by hand. | `Der.Spec.x690_examples` |
| Nineteen inputs that each break a rule, among them the two constructed forms of "Jones", which DER forbids. | `Der.Spec.x690_rejects` |

## The command-line tool

`Main.lean` has these modes:

- `der decode HEX` prints the element at the start of some octets, as a tree, and the octets after it in hex, or exits with 1.
- `der serve` answers requests from the differential tests, one per line. The header comment of `Main.lean` gives the protocol and the syntax of a tree.

HEX is lower-case hex digits in pairs, or `-` for no octets. Malformed HEX, or wrong arguments, exit with 2. Every answer comes from the functions above.
