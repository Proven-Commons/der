// The Go oracles for tests/run_tests.py, one program with two modes:
//
//	der-oracle cryptobyte   golang.org/x/crypto/cryptobyte, at the version
//	                        go.mod pins (go.sum holds its hash)
//	der-oracle asn1         the standard library's encoding/asn1, of the
//	                        installed Go (not pinned; the test record
//	                        gives its version)
//
// Each line of standard input is one request in the form `der serve`
// reads (octets in lower-case hex, `-` for none; integers in decimal),
// and each answer is in the form it writes: `OK ...` or `FAIL`. A
// request the package cannot answer is answered `n/a`, and a line this
// program cannot read `error`. A line may end in LF or CR LF.
//
//	decode HEX     the element at the start of the octets, and the rest
//	all HEX        the element that is the whole input
//	readint HEX    the integer that contents octets encode
//	writeint INT   the contents octets of an integer
//	encode TREE    n/a
//	valid TREE     n/a
//
// An element is read by the package and printed as a tree in the syntax
// of `der serve`. With cryptobyte, String.ReadAnyASN1Element reads each
// element and String.ReadAnyASN1 its contents; a constructed element's
// contents are read the same way, element by element, to their end. An
// element of the universal class with number 1 or 2 must also be read by
// String.ReadASN1Boolean, or String.ReadASN1Integer into a *big.Int.
// With encoding/asn1, Unmarshal into a RawValue reads each element and
// gives its contents, read the same way when it is constructed; an
// element of the universal class with number 1 or 2 must also unmarshal
// into a bool or a *big.Int, and one with number 5 must equal
// NullRawValue in class, number, form and contents.
//
// readint frames the contents octets as an INTEGER element (cryptobyte
// with a Builder, encoding/asn1 with the length octets written here) and
// reads it with ReadASN1Integer or Unmarshal into a *big.Int. writeint
// writes the integer with Builder.AddASN1BigInt or Marshal, and prints
// the contents octets of what they write.
package main

import (
	"bufio"
	"bytes"
	"encoding/asn1"
	"encoding/hex"
	"fmt"
	"io"
	"math/big"
	"os"
	"strings"

	"golang.org/x/crypto/cryptobyte"
	cbasn1 "golang.org/x/crypto/cryptobyte/asn1"
)

func field(f string) ([]byte, bool) {
	if f == "-" {
		return []byte{}, true
	}
	if f == "" || strings.ToLower(f) != f {
		return nil, false
	}
	b, err := hex.DecodeString(f)
	return b, err == nil
}

func toField(b []byte) string {
	if len(b) == 0 {
		return "-"
	}
	return hex.EncodeToString(b)
}

// integer reads a decimal integer, with `-` in front when negative.
func integer(f string) (*big.Int, bool) {
	digits := strings.TrimPrefix(f, "-")
	if digits == "" || strings.Trim(digits, "0123456789") != "" {
		return nil, false
	}
	n, ok := new(big.Int).SetString(digits, 10)
	if !ok {
		return nil, false
	}
	if digits != f {
		n.Neg(n)
	}
	return n, true
}

// cbElement reads one element from s with cryptobyte and writes its tree
// to out.
func cbElement(s *cryptobyte.String, out *bytes.Buffer) bool {
	var elem cryptobyte.String
	var tag cbasn1.Tag
	if !s.ReadAnyASN1Element(&elem, &tag) {
		return false
	}
	cls, num, constructed := int(tag)>>6, int(tag)&0x1f, tag&0x20 != 0
	if cls == 0 && num == 1 {
		e := elem
		var v bool
		if !e.ReadASN1Boolean(&v) || !e.Empty() {
			return false
		}
	}
	if cls == 0 && num == 2 {
		e := elem
		v := new(big.Int)
		if !e.ReadASN1Integer(v) || !e.Empty() {
			return false
		}
	}
	var body cryptobyte.String
	if !elem.ReadAnyASN1(&body, &tag) {
		return false
	}
	if !constructed {
		fmt.Fprintf(out, "p%d.%d.%s", cls, num, toField(body))
		return true
	}
	fmt.Fprintf(out, "c%d.%d(", cls, num)
	for first := true; !body.Empty(); first = false {
		if !first {
			out.WriteByte(',')
		}
		if !cbElement(&body, out) {
			return false
		}
	}
	out.WriteByte(')')
	return true
}

// gaElement reads one element from b with encoding/asn1, writes its tree
// to out, and gives the octets after it.
func gaElement(b []byte, out *bytes.Buffer) ([]byte, bool) {
	var raw asn1.RawValue
	rest, err := asn1.Unmarshal(b, &raw)
	if err != nil {
		return nil, false
	}
	if raw.Class == asn1.ClassUniversal {
		switch raw.Tag {
		case asn1.TagBoolean:
			var v bool
			if r, err := asn1.Unmarshal(raw.FullBytes, &v); err != nil || len(r) != 0 {
				return nil, false
			}
		case asn1.TagInteger:
			var v *big.Int
			if r, err := asn1.Unmarshal(raw.FullBytes, &v); err != nil || len(r) != 0 {
				return nil, false
			}
		case asn1.TagNull:
			n := asn1.NullRawValue
			if raw.Class != n.Class || raw.Tag != n.Tag || raw.IsCompound != n.IsCompound ||
				!bytes.Equal(raw.Bytes, n.Bytes) {
				return nil, false
			}
		}
	}
	if !raw.IsCompound {
		fmt.Fprintf(out, "p%d.%d.%s", raw.Class, raw.Tag, toField(raw.Bytes))
		return rest, true
	}
	fmt.Fprintf(out, "c%d.%d(", raw.Class, raw.Tag)
	body := raw.Bytes
	for first := true; len(body) > 0; first = false {
		if !first {
			out.WriteByte(',')
		}
		var ok bool
		if body, ok = gaElement(body, out); !ok {
			return nil, false
		}
	}
	out.WriteByte(')')
	return rest, true
}

// element reads the element at the start of b: its tree and the rest.
func element(mode string, b []byte) (string, []byte, bool) {
	var out bytes.Buffer
	if mode == "cryptobyte" {
		s := cryptobyte.String(b)
		if !cbElement(&s, &out) {
			return "", nil, false
		}
		return out.String(), s, true
	}
	rest, ok := gaElement(b, &out)
	if !ok {
		return "", nil, false
	}
	return out.String(), rest, true
}

// derLength writes length octets in the fewest octets, to frame contents
// octets as an element.
func derLength(n int) []byte {
	if n < 128 {
		return []byte{byte(n)}
	}
	var digits []byte
	for ; n > 0; n >>= 8 {
		digits = append([]byte{byte(n)}, digits...)
	}
	return append([]byte{0x80 | byte(len(digits))}, digits...)
}

func readint(mode string, c []byte) string {
	v := new(big.Int)
	if mode == "cryptobyte" {
		var b cryptobyte.Builder
		b.AddASN1(cbasn1.INTEGER, func(c2 *cryptobyte.Builder) { c2.AddBytes(c) })
		framed, err := b.Bytes()
		if err != nil {
			return "n/a"
		}
		s := cryptobyte.String(framed)
		if !s.ReadASN1Integer(v) || !s.Empty() {
			return "FAIL"
		}
		return "OK " + v.String()
	}
	framed := append(append([]byte{0x02}, derLength(len(c))...), c...)
	if rest, err := asn1.Unmarshal(framed, &v); err != nil || len(rest) != 0 {
		return "FAIL"
	}
	return "OK " + v.String()
}

func writeint(mode string, n *big.Int) string {
	if mode == "cryptobyte" {
		var b cryptobyte.Builder
		b.AddASN1BigInt(n)
		framed, err := b.Bytes()
		if err != nil {
			return "FAIL"
		}
		s := cryptobyte.String(framed)
		var body cryptobyte.String
		if !s.ReadASN1(&body, cbasn1.INTEGER) || !s.Empty() {
			return "unreadable"
		}
		return "OK " + toField(body)
	}
	framed, err := asn1.Marshal(n)
	if err != nil {
		return "FAIL"
	}
	var raw asn1.RawValue
	if rest, err := asn1.Unmarshal(framed, &raw); err != nil || len(rest) != 0 {
		return "unreadable"
	}
	return "OK " + toField(raw.Bytes)
}

func answer(mode, line string) string {
	parts := strings.Split(line, " ")
	if len(parts) != 2 {
		return "error"
	}
	op, f := parts[0], parts[1]
	switch op {
	case "decode", "all", "readint":
		b, ok := field(f)
		if !ok {
			return "error"
		}
		if op == "readint" {
			return readint(mode, b)
		}
		tree, rest, ok := element(mode, b)
		if !ok || (op == "all" && len(rest) != 0) {
			return "FAIL"
		}
		if op == "all" {
			return "OK " + tree
		}
		return "OK " + tree + " " + toField(rest)
	case "writeint":
		n, ok := integer(f)
		if !ok {
			return "error"
		}
		return writeint(mode, n)
	case "encode", "valid":
		return "n/a"
	}
	return "error"
}

func main() {
	if len(os.Args) != 2 || (os.Args[1] != "cryptobyte" && os.Args[1] != "asn1") {
		fmt.Fprintln(os.Stderr, "usage: der-oracle cryptobyte|asn1")
		os.Exit(2)
	}
	mode := os.Args[1]
	in := bufio.NewReaderSize(os.Stdin, 1<<20)
	out := bufio.NewWriterSize(os.Stdout, 1<<20)
	defer out.Flush()
	for {
		line, err := in.ReadString('\n')
		if line == "" && err != nil {
			if err != io.EOF {
				fmt.Fprintln(os.Stderr, err)
				os.Exit(1)
			}
			return
		}
		line = strings.TrimSuffix(line, "\n")
		line = strings.TrimSuffix(line, "\r")
		fmt.Fprintln(out, answer(mode, line))
	}
}
