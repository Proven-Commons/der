# Planted bugs

Written by `tests/plant_bugs.py`. Each bug is a change of one line, to `Der/Basic.lean` (31 bugs) or to `Main.lean` (6), tested with `tests/run_tests.py --count 5000 --no-oracles`, which builds only the executable and compares it with the model alone. Every bug must give failures, and the unchanged code none. A bug that does not build, or a run that gives up or dies, counts as missed.

| Planted bug | Failures |
|---|---|
| none | 0 |
| the long form is read for a length below 128 | 1000 |
| the long form is refused for a length below 256 | 2823 |
| a leading zero length octet is read | 1269 |
| a leading zero length octet is read when 5 or more length octets follow it | 1127 |
| a long-form length is kept modulo 2^32 | 488 |
| the indefinite length octet 0x80 is read as length 0 | 1364 |
| a tag number below 31 is read in the high form | 2002 |
| a first subsequent tag octet 0x80 is read | 1098 |
| the continuation bit of a tag octet is tested as 0x40 | 4760 |
| the constructed bit is read from bit 7 | 12792 |
| a BOOLEAN 01 is read | 571 |
| an INTEGER with a redundant leading zero octet is read | 781 |
| a NULL with one contents octet is read | 148 |
| universal tag 0 is read | 1001 |
| a primitive SEQUENCE is read | 277 |
| a constructed INTEGER is read | 59 |
| universal 29 is taken for a primitive type | 1118 |
| the reserved universal numbers start at 38, not 37 | 845 |
| an element may run one octet past the one it is in | 408 |
| the elements of a constructed element must take one octet more than it holds | 5388 |
| the reader's fuel is half the length of the input | 479 |
| decodeAll allows octets after the element | 2392 |
| long numbers: the first half is shifted by the length of the first half, not the second | 526 |
| readInt takes a first octet 0x80 for a positive integer | 517 |
| writeInt writes 128 with no zero octet in front | 632 |
| the writer gives no subsequent tag octet but the last its bit 8 | 4200 |
| the writer writes length 128 in the short form | 64 |
| the writer writes tag number 31 in one octet | 623 |
| Main.lean: `all` allows octets after the element | 2392 |
| Main.lean: `der decode` exits with 0 when the input is not an element | 6 |
| Main.lean: the CR of a CR LF line ending is kept | 59924 |
| Main.lean: a primitive element is printed with its number before its class | 147997 |
| Main.lean: upper-case hex digits are read | 4 |
| an ENUMERATED is not checked | 649 |
| valid takes a primitive element of class 4 | 214 |
| valid does not look inside a constructed element | 1337 |
| Main.lean: `valid` answers OK for every tree | 5154 |

Bugs caught: 37 of 37
