# Test results

Written by `tests/run_tests.py`. Rerun it to check these numbers.

- Lean: Lean (version 4.35.0, x86_64-unknown-linux-gnu, commit eb6cafb7290e8bd5f2937522d8d804f58f02bafc, Release)
- Oracle: the model of X.690 (02/2021) in `tests/run_tests.py`; Go cryptobyte, golang.org/x/crypto/cryptobyte v0.25.0 (h1:ypSNr+bnYL2YhwoMt2zPxHFmbAN1KZs/njMG3hxUp30=), built with go version go1.24.7 linux/amd64; Go encoding/asn1, encoding/asn1 of the standard library of go version go1.24.7 linux/amd64; rust-asn1, the asn1 crate 0.24.1 (checksum c9795210620c0cb3f9a7ce4f882808c38e1ef7b347c90591dceae0886e031fb1), built with rustc 1.97.0 (2d8144b78 2026-07-07); OpenSSL, libcrypto of OpenSSL 3.0.13 30 Jan 2024 (Debian package libssl3t64 3.0.13-0ubuntu3.16), through `tests/oracles/openssl/wrapper.c` compiled with cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
- Go cryptobyte: golang.org/x/crypto/cryptobyte v0.25.0 (h1:ypSNr+bnYL2YhwoMt2zPxHFmbAN1KZs/njMG3hxUp30=), built with go version go1.24.7 linux/amd64
- Go encoding/asn1: encoding/asn1 of the standard library of go version go1.24.7 linux/amd64
- rust-asn1: the asn1 crate 0.24.1 (checksum c9795210620c0cb3f9a7ce4f882808c38e1ef7b347c90591dceae0886e031fb1), built with rustc 1.97.0 (2d8144b78 2026-07-07)
- OpenSSL: libcrypto of OpenSSL 3.0.13 30 Jan 2024 (Debian package libssl3t64 3.0.13-0ubuntu3.16), through `tests/oracles/openssl/wrapper.c` compiled with cc (Ubuntu 13.3.0-6ubuntu2~24.04.1) 13.3.0
- Oracles left out: none
- Seed: 20261027
- Inputs: 1612540
- By kind: 0 to 2 octets all 65793, 0 to 2 octets decode 65793, BOOLEAN contents decode 262, ENUMERATED contents decode 66153, INTEGER contents decode 66153, INTEGER contents readint 66153, NULL contents decode 5, Wycheproof ECDSA signatures all 484, X.690 examples all 4, X.690 examples decode 5, X.690 examples encode 5, constructed BOOLEAN, INTEGER and NULL decode 4, high tag numbers all 240, high tag numbers decode 240, high tag numbers encode 240, high tag numbers, cut short decode 232, high tag numbers, first subsequent octet 0x80 all 232, identifier first octets decode 2432, initial length octets decode 2548, integers around 0 and 2^k writeint 10611, lengths 0 to 100,000 all 30, lengths 0 to 100,000 decode 15, lengths 0 to 100,000 encode 30, lengths 0 to 100,000, cut short all 14, lengths 0 to 100,000, length one less decode 14, lengths 0 to 100,000, length one more decode 15, lengths 0 to 100,000, not in the fewest octets all 20, nested 10,000 deep all 5, nested 10,000 deep decode 1, nested 10,000 deep encode 2, nested 100,000 deep all 5, nested 100,000 deep decode 1, random integer contents readint 25000, random integers writeint 25000, random octets decode 50000, random tree all 100000, random tree encode 100000, random tree valid 100000, random tree, BOOLEAN, INTEGER, ENUMERATED or NULL contents changed all 6297, random tree, BOOLEAN, INTEGER, ENUMERATED or NULL contents changed decode 6294, random tree, a bit flipped decode 100000, random tree, an element running past the one it is in all 8434, random tree, an element running past the one it is in decode 8503, random tree, constructed bit flipped all 24803, random tree, constructed bit flipped decode 25257, random tree, cut short decode 100000, random tree, first subsequent tag octet 0x80 all 25179, random tree, first subsequent tag octet 0x80 decode 25024, random tree, high form for a tag below 31 all 19518, random tree, high form for a tag below 31 decode 19483, random tree, indefinite length all 25044, random tree, indefinite length decode 25036, random tree, length not in the fewest octets all 24991, random tree, length not in the fewest octets decode 25157, random tree, length one less all 22163, random tree, length one less decode 22232, random tree, length one more all 25378, random tree, length one more decode 24714, random tree, octets after all 33283, random tree, octets after decode 66717, random tree, one element not accepted encode 100000, random tree, one element not accepted valid 100000, universal tags 0 to 40 decode 410, universal tags 0 to 40 encode 410, universal tags 0 to 40 valid 410, universal tags 0 to 40, high form all 62
- Answers that differ from the model: 0
- X.690's examples, answered by the model as the standard gives them: 14 of 14
- Elements read (`decode` and `all`): 1084679, of which 418556 are accepted; why the model refuses the others: the contents run past the end of the input 191249, the input ends in the length octets 89253, an element runs past the end of the one it is in 74289, the indefinite length (10.1) 53076, a first subsequent tag octet with bits 7 to 1 zero (8.1.2.4.2 c) 51692, octets after the element 47542, a tag number below 31 in the high form (8.1.2.2) 41230, a long-form length with a leading zero octet (10.1) 32709, a primitive universal type in the constructed form 22644, the input ends in the identifier octets 22579, a long-form length below 128 (10.1) 20210, a BOOLEAN contents octet other than 00 and FF (11.1) 4579, universal 8, 11, 16, 17 or 29 in the primitive form 3865, a BOOLEAN without exactly one contents octet (8.2.1) 2884, the initial length octet 0xFF (8.1.3.5 c) 2639, universal tag 0 (X.680 Table 1, 8.1.5) 1589, an INTEGER with a redundant leading octet (8.3.2) 1522, a NULL with contents octets (8.8.2) 1151, an INTEGER with no contents octets (8.3.1) 634, an ENUMERATED with a redundant leading octet (8.4, 8.3.2) 633, an ENUMERATED with no contents octets (8.4, 8.3.1) 154
- Integer contents read (`readint`): 91153, of which 85899 give a value; why the model refuses the others: an INTEGER with a redundant leading octet (8.3.2) 3560, an INTEGER with no contents octets (8.3.1) 1694
- Encodings asked for: trees 200687, of which the model reads the tool's encoding back as the tree for 101141 of the 101141 the slice accepts; integers 35611
- `valid` asked of 200410 trees, of which the slice accepts 100867; the model's answer holds exactly when it reads the tree's encoding back as the tree, for 200410 of 200410
- Wycheproof: `tests/wycheproof/ecdsa_secp256r1_sha256_test.json`, SHA-256 182db4f3e230f6f9fa9f800d2a614dede30284b8e8438bbfe1171905402e9332: 484 signatures read with `all`, of which the tool refuses 113, every answer as the model's but 0. Flagged as an encoding that is not DER or is broken: BerEncodedSignature 7, of which the tool refuses 7, InvalidEncoding 92, of which the tool refuses 90, MissingZero 1, of which the tool refuses 0. Each flagged one it accepts is an element this slice accepts, with what is wrong in something it does not check: a negative INTEGER where a positive one belongs, a BIT STRING where an INTEGER belongs, or a SEQUENCE given the reserved universal tag 15
- Requests nested 10,000 and 100,000 deep, each sent to a `der serve` of its own: 14, answered within 60 seconds: 14
- Agreement with each oracle over the requests it answers: Go cryptobyte 1064404 of 1211443, Go encoding/asn1 1185392 of 1211443, rust-asn1 1150947 of 1173582, OpenSSL 1047170 of 1211443
- Elements each oracle reads (`decode` and `all`) whose answer the model gives with the rules that oracle reads by, whether or not it agrees with the tool: Go cryptobyte 1084679 of 1084679, Go encoding/asn1 1084679 of 1084679, rust-asn1 1084679 of 1084679, OpenSSL 1084679 of 1084679
- Requests each oracle answers, by operation: Go cryptobyte: all 381979, decode 702700, readint 91153, writeint 35611; Go encoding/asn1: all 381979, decode 702700, readint 91153, writeint 35611; rust-asn1: all 381979, decode 702700, readint 78101, writeint 10802; OpenSSL: all 381979, decode 702700, readint 91153, writeint 35611
- Malformed requests answered `error`: 91 of 91; odd but well-formed requests answered as the model says: 33 of 33
- Requests ending in CR LF: every seventh, 230362
- Last lines sent alone, with no LF, with CR LF, or with a lone CR, answered right: 4 of 4
- Command-line mode `der decode` and wrong arguments, printing and exiting as the model says: 29 of 29
- Failures: 0

## Where the oracles differ

Each disagreement is counted under the reason the model confirms: the model, with the rules the oracle reads by, gives the oracle's answer. The reason names each rule on which those part from DER for the input, with the first input that showed it.

### Go cryptobyte

- ReadAnyASN1Element refuses every tag number of 31 or more (the high form): 139048; for example `decode 1f1f00`
- ReadAnyASN1Element reads universal 8, 11, 16, 17 or 29 in the primitive form: 2912; for example `decode 0800`
- ReadAnyASN1Element reads a universal type other than BOOLEAN and INTEGER in the constructed form: 2901; for example `decode 3a0904034a6f6e04026573`
- ReadAnyASN1Element reads universal tag 0: 846; for example `decode 0000`
- cryptobyte has no reader for NULL, so a NULL with contents is read: 839; for example `decode 050100`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet: 383; for example `decode 0a020000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with no contents octets: 80; for example `decode 0a00`
- ReadAnyASN1Element reads a universal type other than BOOLEAN and INTEGER in the constructed form; ReadAnyASN1Element reads universal tag 0: 29; for example `decode 23020000`
- ReadAnyASN1Element reads a universal type other than BOOLEAN and INTEGER in the constructed form; ReadAnyASN1Element reads universal 8, 11, 16, 17 or 29 in the primitive form; ReadAnyASN1Element reads universal tag 0: 1; for example `decode ba062a0410000000`

### Go encoding/asn1

- parseBase128Int refuses a tag number above 2^31 - 1: 18944; for example `all 1f8880808000020102`
- Unmarshal into a RawValue reads universal 8, 11, 16, 17 or 29 in the primitive form: 3516; for example `decode 0800`
- Unmarshal into a RawValue reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form: 2170; for example `decode 3a0904034a6f6e04026573`
- Unmarshal into a RawValue reads universal tag 0: 919; for example `decode 0000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet: 386; for example `decode 0a020000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with no contents octets: 81; for example `decode 0a00`
- Unmarshal into a RawValue reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form; Unmarshal into a RawValue reads universal tag 0: 33; for example `decode 23020000`
- Unmarshal into a RawValue reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form; Unmarshal into a RawValue reads universal 8, 11, 16, 17 or 29 in the primitive form; Unmarshal into a RawValue reads universal tag 0: 1; for example `decode ba062a0410000000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet; Unmarshal into a RawValue reads universal tag 0: 1; for example `decode 2b82030e0a0700400000000000000900fe8202fe668202fa1f90be5a81d6f3d28148330dd2f01c31542ed157d1361d0efb2723567bfc6cbb70ed5968e1035cae2e98f648c800990ca1e357bbb3323e853994984feb7dc978a0caae794234f7a620297112604d6043b37a78dd2d6ee6e6cfa4b91e2... (1581 characters)`

### rust-asn1

- Tag::from_bytes refuses a tag number above 2^32 - 1: 15480; for example `all 1f9080808000020102`
- strip_tlv reads universal 8, 11, 16, 17 or 29 in the primitive form: 3548; for example `decode 0800`
- strip_tlv reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form: 2186; for example `decode 3a0904034a6f6e04026573`
- strip_tlv reads universal tag 0: 919; for example `decode 0000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet: 386; for example `decode 0a020000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with no contents octets: 81; for example `decode 0a00`
- strip_tlv reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form; strip_tlv reads universal tag 0: 33; for example `decode 23020000`
- strip_tlv reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form; strip_tlv reads universal 8, 11, 16, 17 or 29 in the primitive form; strip_tlv reads universal tag 0: 1; for example `decode ba062a0410000000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet; strip_tlv reads universal tag 0: 1; for example `decode 2b82030e0a0700400000000000000900fe8202fe668202fa1f90be5a81d6f3d28148330dd2f01c31542ed157d1361d0efb2723567bfc6cbb70ed5968e1035cae2e98f648c800990ca1e357bbb3323e853994984feb7dc978a0caae794234f7a620297112604d6043b37a78dd2d6ee6e6cfa4b91e2... (1581 characters)`

### OpenSSL

- ASN1_get_object reads a first subsequent tag octet 0x80 (BER): 47408; for example `decode 1f801f00`
- ASN1_get_object reads a tag number below 31 in the high form (BER): 36095; for example `decode 1f1e00`
- asn1_get_length reads a long-form length with leading zero octets (BER): 25437; for example `decode 04810001`
- ASN1_get_object refuses a tag number above 2^31 - 1: 18944; for example `all 1f8880808000020102`
- asn1_get_length reads the long form for a length below 128 (BER): 17934; for example `decode 04810105`
- ASN1_get_object reads the indefinite length of a constructed element (BER), to end-of-contents octets 00 00: 7232; for example `decode 30800000`
- d2i_ASN1_TYPE reads any single contents octet as a BOOLEAN (BER, 8.2.2): 3984; for example `decode 010101`
- ASN1_get_object reads universal 8, 11, 16, 17 or 29 in the primitive form: 3516; for example `decode 0800`
- ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6): 2170; for example `decode 3a0904034a6f6e04026573`
- ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 919; for example `decode 0000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet: 386; for example `decode 0a020000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with no contents octets: 81; for example `decode 0a00`
- ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 33; for example `decode 23020000`
- ASN1_get_object reads a first subsequent tag octet 0x80 (BER); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 32; for example `decode 7f801f020000`
- ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6); ASN1_get_object reads a tag number below 31 in the high form (BER): 31; for example `decode 3f1e00`
- ASN1_get_object reads a tag number below 31 in the high form (BER); ASN1_get_object reads universal 8, 11, 16, 17 or 29 in the primitive form: 24; for example `all 1f0800`
- asn1_get_length reads the long form for a length below 128 (BER); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 11; for example `decode eb820170758201641a82011ddf500599e69be6a6af311518f2256f323a862ba82ffb64073d982b1375950b8f922b61d4aee7e507b1fe55345889d25f6d2244e53c20072a43ce07deefd66e42d9c2e00acbdf66e4874751496d34c7e3644133833f66e14ecc0bc5e8a0b0d8cb1d74004a67d74bed6... (755 characters)`
- ASN1_get_object reads a first subsequent tag octet 0x80 (BER); ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6): 6; for example `decode 3f801f00`
- d2i_ASN1_TYPE reads any single contents octet as a BOOLEAN (BER, 8.2.2); ASN1_get_object reads a tag number below 31 in the high form (BER): 5; for example `decode 1f010175`
- asn1_get_length reads the initial length octet 0xFF, skipping leading zero octets (BER): 4; for example `decode 04ff0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000... (267 characters)`
- asn1_get_length reads a long-form length with leading zero octets (BER); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 4; for example `decode 208100f33f209ca08201a06b05`
- ASN1_get_object reads a tag number below 31 in the high form (BER); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 3; for example `decode 7f1e020000`
- asn1_get_length reads the long form for a length below 128 (BER); ASN1_get_object reads a tag number below 31 in the high form (BER): 2; for example `decode 1f17810164349104dd26e413ff1f813f00b10082b800ce`
- asn1_get_length reads a long-form length with leading zero octets (BER); ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6): 2; for example `decode 33810030`
- ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6); ASN1_get_object reads the indefinite length of a constructed element (BER), to end-of-contents octets 00 00: 1; for example `decode 3a8004034a6f6e040265730000`
- ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6); ASN1_get_object reads a tag number below 31 in the high form (BER); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 1; for example `decode 3f1e020000`
- ASN1_get_object reads a first subsequent tag octet 0x80 (BER); ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 1; for example `decode 3f801f020000`
- ASN1_get_object reads a tag number below 31 in the high form (BER); the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with no contents octets: 1; for example `all 1f0a00`
- ASN1_get_object reads a universal type other than BOOLEAN, INTEGER and NULL in the constructed form (BER, 8.23.6); ASN1_get_object reads universal 8, 11, 16, 17 or 29 in the primitive form; ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 1; for example `decode ba062a0410000000`
- the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with a redundant leading octet; ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 1; for example `decode 2b82030e0a0700400000000000000900fe8202fe668202fa1f90be5a81d6f3d28148330dd2f01c31542ed157d1361d0efb2723567bfc6cbb70ed5968e1035cae2e98f648c800990ca1e357bbb3323e853994984feb7dc978a0caae794234f7a620297112604d6043b37a78dd2d6ee6e6cfa4b91e2... (1581 characters)`
- asn1_get_length reads a long-form length with leading zero octets (BER); ASN1_get_object reads a tag number below 31 in the high form (BER): 1; for example `decode 5f1d810002a802a97bd15305f601c180318120a73a1f04`
- ASN1_get_object reads a first subsequent tag octet 0x80 (BER); asn1_get_length reads the long form for a length below 128 (BER); ASN1_get_object reads universal tag 0 where no end-of-contents octets are due: 1; for example `decode 1f0081011f`
- ASN1_get_object reads a first subsequent tag octet 0x80 (BER); the oracle program checks no ENUMERATED contents, so it reads an ENUMERATED with no contents octets: 1; for example `decode 1f800a000048059d3f60ff05028080`
- d2i_ASN1_TYPE reads any single contents octet as a BOOLEAN (BER, 8.2.2); asn1_get_length reads the long form for a length below 128 (BER): 1; for example `decode 01810131`
