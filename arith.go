package avtc

import (
	"crypto/rand"
	"fmt"
	"github.com/consensys/gnark/frontend"
	"math/big"
)

func RandomGroupElement() *big.Int {
	buff := make([]byte, 2048)
	rand.Read(buff)
	r := big.NewInt(0).SetBytes(buff)
	return big.NewInt(0).Mod(r, N)
}

type BaseDec []*big.Int

func (bd BaseDec) ToVariable(words int) []frontend.Variable {
	var res []frontend.Variable
	for _, d := range bd {
		res = append(res, frontend.Variable(d))
	}
	for len(res) < words {
		res = append(res, frontend.Variable(big.NewInt(0)))
	}
	return res
}

func Decompose(n *big.Int, base *big.Int) BaseDec {
	var digitCount int

	m := big.NewInt(0).Set(n)
	for m.Sign() != 0 {
		digitCount++
		m.Div(m, base)
	}

	res := make(BaseDec, digitCount)
	remainder := big.NewInt(0).Set(n)

	for i := len(res) - 1; i >= 0; i-- {
		x := big.NewInt(0).Exp(base, big.NewInt(int64(i)), nil)
		if x.Cmp(n) >= 0 {
			res[i] = big.NewInt(0)
			continue
		}
		times := big.NewInt(0).Div(remainder, x)
		xTimes := big.NewInt(0).Mul(times, x)
		remainder = big.NewInt(0).Sub(remainder, xTimes)
		res[i] = times
	}

	if remainder.Sign() != 0 {
		panic(fmt.Sprintf("remainder is %s but should be 0", remainder.String()))
	}

	return res
}

func Compose(in BaseDec, base *big.Int) *big.Int {
	n := big.NewInt(0)
	for i := len(in) - 1; i >= 0; i-- {
		x := big.NewInt(0).Exp(base, big.NewInt(int64(i)), nil)
		n.Add(n, big.NewInt(0).Mul(x, in[i]))
	}
	return n
}


func XPlusY(X BaseDec, Y BaseDec, base *big.Int) BaseDec {
	var res BaseDec

	longer := len(X)
	if len(Y) > len(X) {
		longer = len(Y)
	}

	for i := len(X); i < longer - 1; i++ {
		X = append(X, big.NewInt(0))
	}

	for i := len(Y); i < longer - 1; i++ {
		Y = append(Y, big.NewInt(0))
	}

	if len(X) != len(Y) {
		panic("X and Y should be equal")
	}

	carries := make([]*big.Int, longer)
	for i := 0; i < len(carries); i++ {
		carries[i] = big.NewInt(0)
	}

	for i := 0; i < longer; i++ {
		XplusY := big.NewInt(0).Add(X[i], Y[i])

		carry := big.NewInt(0)
		if i > 0 {
			carry = carries[i-1]
		}

		XplusY.Add(XplusY, carry)

		digit := big.NewInt(0).Mod(XplusY, base)
		res = append(res, digit)

		if XplusY.Cmp(base) > -1 {
			carries[i].Add(carries[i], big.NewInt(1))
		}
	}

	if carries[len(carries) - 1].Sign() > 0 {
		res = append(res, big.NewInt(1))
	}

	return res
}

func XmulY(X BaseDec, Y BaseDec, base *big.Int) (BaseDec, []*big.Int, []*big.Int) {
	rows := make([][]*big.Int, len(Y))

	for j := 0; j < len(Y); j++ { // Y
		var row []*big.Int
		for i := 0; i < len(X); i++ { // X
			xy := big.NewInt(0).Mul(X[i], Y[j])
			row = append(row, xy)
		}
		rows[j] = row
	}

	summands := make([]*big.Int, len(X)+len(Y))

	for i := 0; i < len(summands); i++ {
		summands[i] = big.NewInt(0)
	}

	for i := 0; i < len(rows); i++ {
		for j := 0; j < len(rows[i]); j++ {
			summands[i+j].Add(summands[i+j], rows[i][j])
		}
	}

	res := make([]*big.Int, len(X) + len(Y))
	var hints []*big.Int
	var carries []*big.Int
	for i := 0; i < len(res); i++ {
		carry := big.NewInt(0)
		if i > 0 {
			carry = big.NewInt(0).Div(summands[i-1], base)
		}
		summands[i].Add(summands[i], carry)
		res[i] = big.NewInt(0).Mod(summands[i], base)

		carries = append(carries, carry)
		hints = append(hints, big.NewInt(0).Div(summands[i], base))
	}

	return res, hints, carries
}
