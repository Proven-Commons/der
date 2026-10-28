# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `Der/Basic.lean` (26 bugs) or to `Main.lean` (5), tested with `tests/run_tests.py --count 5000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| the long form is read for a length below 128 | 991 |
| the long form is refused for a length below 256 | 2663 |
| a leading zero length octet is read | 267 |
| the indefinite length octet 0x80 is read as length 0 | 1391 |
| a tag number below 31 is read in the high form | 1939 |
| a first subsequent tag octet 0x80 is read | 1104 |
| the continuation bit of a tag octet is tested as 0x40 | 4714 |
| the constructed bit is read from bit 7 | 12878 |
| a BOOLEAN 01 is read | 493 |
| an INTEGER with a redundant leading zero octet is read | 412 |
| a NULL with one contents octet is read | 48 |
| universal tag 0 is read | 154 |
| a primitive SEQUENCE is read | 81 |
| a constructed INTEGER is read | 15 |
| universal 29 is taken for a primitive type | 662 |
| the reserved universal numbers start at 38, not 37 | 711 |
| an element may run one octet past the one it is in | 432 |
| the elements of a constructed element must take one octet more than it holds | 5444 |
| the reader's fuel is half the length of the input | 444 |
| decodeAll allows octets after the element | 2404 |
| long numbers: the first half is shifted by the length of the first half, not the second | 529 |
| readInt takes a first octet 0x80 for a positive integer | 511 |
| writeInt writes 128 with no zero octet in front | 628 |
| the writer gives no subsequent tag octet but the last its bit 8 | 3239 |
| the writer writes length 128 in the short form | 46 |
| the writer writes tag number 31 in one octet | 406 |
| Main.lean: `all` allows octets after the element | 2404 |
| Main.lean: `der decode` exits with 0 when the input is not an element | 6 |
| Main.lean: the CR of a CR LF line ending is kept | 48069 |
| Main.lean: a primitive element is printed with its number before its class | 82169 |
| Main.lean: upper-case hex digits are read | 4 |

Bugs caught: 31 of 31
