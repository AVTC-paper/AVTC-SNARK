package avtc

import (
	"fmt"
	"math/big"
	"testing"
)

func TestDecompose(t *testing.T) {
	n := RandomGroupElement()
	base := big.NewInt(0).Exp(big.NewInt(2), big.NewInt(WordSize), nil)
	dec := Decompose(n, base)
	m := Compose(dec, base)
	if n.Cmp(m) != 0 {
		panic("n != m")
	}
}

func TestXtimesY(t *testing.T) {
	base := big.NewInt(0).Exp(big.NewInt(2), big.NewInt(WordSize), nil)

	x := RandomGroupElement()
	y := RandomGroupElement()

	z := big.NewInt(0).Mul(x, y)

	X := Decompose(x, base)
	Y := Decompose(y, base)

	Z, _, _ := XmulY(X, Y, base)
	z2 := Compose(Z, base)

	if z.Cmp(z2) != 0 {
		panic("z != z2")
	}
}

func TestXplusY(t *testing.T) {
	base := big.NewInt(0).Exp(big.NewInt(2), big.NewInt(WordSize), nil)

	x := RandomGroupElement()
	y := RandomGroupElement()

	z := big.NewInt(0).Add(x, y)

	X := Decompose(x, base)
	Y := Decompose(y, base)


	Z := XPlusY(X, Y, base)
	z2 := Compose(Z, base)

	if z.Cmp(z2) != 0 {
		fmt.Println(z, z2)
		panic("z != z2")
	}
}