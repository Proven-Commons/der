# Wycheproof test vectors

`ecdsa_secp256r1_sha256_test.json` is a copy of
`testvectors_v1/ecdsa_secp256r1_sha256_test.json` from Project Wycheproof
(https://github.com/C2SP/wycheproof), taken from its `main` branch. Its
SHA-256 is 182db4f3e230f6f9fa9f800d2a614dede30284b8e8438bbfe1171905402e9332;
`tests/run_tests.py` checks it before reading the file.

Project Wycheproof is licensed under the Apache License, Version 2.0
(https://www.apache.org/licenses/LICENSE-2.0). The file is unchanged.

The tests read each signature with `all` and count how many of those
flagged `BerEncodedSignature`, `InvalidEncoding` and `MissingZero` the
tool refuses.
