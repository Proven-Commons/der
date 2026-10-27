# der

A Lean reader for ASN.1 DER elements. This is a Proven Commons project: it rebuilds a widely used format in Lean and proves the new code follows its written specification.

Status: not verified. No code has landed yet. Plan issue 1 holds the first slice, and it is unclaimed. The specification has not been approved by a reviewer, so do not call this verified.

## First slice

DER is the strict subset of BER defined in X.690. The first slice reads one DER element, nested to any depth.

- Definite lengths only, in the shortest length form.
- The shortest tag form.
- INTEGER without a redundant leading byte.
- BOOLEAN as 00 or FF.

A second slice reads ECDSA-Sig-Value, a SEQUENCE of two INTEGERs.

## Main claim

The reader is non-malleable. For every input it accepts, writing the result back gives the same bytes, and each value has one encoding. The reader returns an error instead of reading past the end, and each child stays inside its parent.

## Test oracles

- Wycheproof ECDSA vectors, which flag signatures in BER form and with broken encodings.
- Go encoding/asn1 and cryptobyte.
- rust-asn1, a DER only Rust library.
- OpenSSL asn1parse.

Prior proofs exist in F*, Agda, and Verus, so this build is worth doing only if later Lean work imports it. Reading names out of a certificate is one such use: the hostname project needs it.

## Score

16 out of 18, from two scorers, in the round 3 sheet in the mission repo. The sheet is mission pull request 17.

## What is not in this slice

- Full X.509 certificate parsing.
- BER forms outside DER.
- Any claim about a full ASN.1 implementation.

## Layout, when the first slice lands

The layout follows the Proven Commons template in the mission repo, under bar/template. Spec.lean holds the statements a reviewer approves. Proofs.lean holds the proofs under the same names. Main.lean holds the command line tool used by the tests. The bar check runs in CI on every change.
