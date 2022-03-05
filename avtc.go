// Package avtc provides a ZKP-circuit function to compute Attribute Verifiable Timed Commitment.
// The code's purpose is education, don't use it in production.
// The code has not been audited and might contain security vulnerabilities.
// Use at your own risk.

// The code's main purpose is to compare the performance of AVTC implemented
// with the paper's "MPC-in-the-head" approach vs AVTC implemente as a ZK-SNARK.

package avtc

import (
	"crypto/sha256"
	"encoding/binary"
	"fmt"
	"math/big"
	"time"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
)

const (
	Layers      = 98
	WordSize    = 120
	ModulusSize = 2048
	Words       = (ModulusSize+ModulusSize)/WordSize + 2
)

var (
	N    *big.Int
	Base *big.Int
)

func init() {
	N, _ = big.NewInt(0).SetString("27518144449192091323785136890288081002111163008131579389868979123058526612961814169576479652690566315688165545261084691759244102073192775762602945314299857048479498599462787617752344346867312145528536437275377969294777816873672780487846002110944989481483427204154700053455661402700812086819281516246557605984163654710569034300736631406420995589670835608735412121315932554722222442747005055168229165207085101172903012266786259853145875210694315201682190470477846286400598367501391121175336904167177167826762738669787017253904152441033114569221450919087114704937595412378227707650670216958267520527775834443735443469927", 10)
	Base = big.NewInt(0).Exp(big.NewInt(2), big.NewInt(WordSize), nil)
}

type Circuit struct {
	N        []frontend.Variable `gnark:",public"`
	U        []frontend.Variable `gnark:",public"`
	In       []frontend.Variable
	As       [Layers][]frontend.Variable
	Bs       [Layers][]frontend.Variable
	LSBHints [Layers - 2]frontend.Variable
	Ts       [Layers][]frontend.Variable
	TNs      [Layers][]frontend.Variable
	Hints    [Layers][]frontend.Variable
	Carries  [Layers][]frontend.Variable
	Hints2   [Layers][]frontend.Variable
	Carries2 [Layers][]frontend.Variable
	LSBs     [Layers - 2]frontend.Variable

	// SHA256
	Hash      [8][32]frontend.Variable  `gnark:",public"`
	Constants [8][32]frontend.Variable  `gnark:",public"`
	K         [64][32]frontend.Variable `gnark:",public"`
	Data      [16][32]frontend.Variable
	State     [8][32]frontend.Variable
}

func (c *Circuit) Define(api frontend.API) error {
	var output []frontend.Variable

	// Below is the computation that is depicted in 'Algorithm 1' in the paper.
	// We slightly deviate from the paper by feeding the LSBs of successive modular squaring
	// into the hash function, while in the paper we feed into the hash function the XOR of
	// these LSBs with publicly known bits.
	// The reason is that in this implementation we use a hash pre-image that is chosen
	// uniformly at random, while in the paper we describe a commitment to an arbitrary string
	// which can potentially be sampled from a low entropy distribution.
	for layer := 0; layer < Layers; layer++ {
		A := c.As[layer]
		B := c.Bs[layer]
		T := c.Ts[layer]
		TN := c.TNs[layer]
		Hints := c.Hints[layer]
		Carries := c.Carries[layer]

		// Ensure TN = T*N
		assertMulY(api, T, c.N, TN, Hints, Carries)
		// Ensure A = B+T*N   (modulo reduction)
		assertAdd(api, B, TN, A)
		if layer == 0 {
			// A = in^2
			assertMulY(api, c.In, c.In, A, c.Hints2[layer], c.Carries2[layer])
		} else {
			// Previous B squared is our A
			assertMulY(api, c.Bs[layer-1], c.Bs[layer-1], c.As[layer], c.Hints2[layer], c.Carries2[layer])
			// We start the LSBs from layer 1 hence we need to shift the index backwards by 1
			// But we also avoid the last layer which computes U, hence we don't need its LSB.
			if layer < Layers-1 {
				api.AssertIsBoolean(c.LSBs[layer-1])
				twoTimesHintWithoutLSB := api.Mul(big.NewInt(2), c.LSBHints[layer-1])
				api.AssertIsEqual(B[0], api.Add(twoTimesHintWithoutLSB, c.LSBs[layer-1]))
			}
		}

		if layer == Layers-1 {
			output = B
		}
	}

	for i := 0; i < Words; i++ {
		api.AssertIsEqual(c.U[i], output[i])
	}

	// Check the LSBs of the successive modular squaring
	// correspond to the input of the SHA256 function.
	// The rest of the input is known to be zero bits,
	// since the length of the pre-image is known in the scheme.
	for i := 0; i < len(c.LSBs)/8; i++ {
		wordIndex := i / 4
		indexInWord := (i * 8) % 32
		d0 := c.Data[wordIndex][31-indexInWord]
		d1 := c.Data[wordIndex][31-indexInWord-1]
		d2 := c.Data[wordIndex][31-indexInWord-2]
		d3 := c.Data[wordIndex][31-indexInWord-3]
		d4 := c.Data[wordIndex][31-indexInWord-4]
		d5 := c.Data[wordIndex][31-indexInWord-5]
		d6 := c.Data[wordIndex][31-indexInWord-6]
		d7 := c.Data[wordIndex][31-indexInWord-7]

		l0 := c.LSBs[wordIndex*32+indexInWord+7]
		l1 := c.LSBs[wordIndex*32+indexInWord+6]
		l2 := c.LSBs[wordIndex*32+indexInWord+5]
		l3 := c.LSBs[wordIndex*32+indexInWord+4]
		l4 := c.LSBs[wordIndex*32+indexInWord+3]
		l5 := c.LSBs[wordIndex*32+indexInWord+2]
		l6 := c.LSBs[wordIndex*32+indexInWord+1]
		l7 := c.LSBs[wordIndex*32+indexInWord]

		api.AssertIsEqual(d0, l0)
		api.AssertIsEqual(d1, l1)
		api.AssertIsEqual(d2, l2)
		api.AssertIsEqual(d3, l3)
		api.AssertIsEqual(d4, l4)
		api.AssertIsEqual(d5, l5)
		api.AssertIsEqual(d6, l6)
		api.AssertIsEqual(d7, l7)

	}

	AssertSHA256(api, c)

	return nil
}

func assertMulY(api frontend.API, X []frontend.Variable, Y []frontend.Variable, Z []frontend.Variable, Hints []frontend.Variable, carries []frontend.Variable) {
	rows := make([][]frontend.Variable, len(Y)/2)

	api.AssertIsEqual(carries[0], frontend.Variable(0))

	// Ensure the second half of the input digits are zero, so we won't overflow N^2
	for i := len(X) / 2; i < len(X); i++ {
		api.AssertIsEqual(X[i], frontend.Variable(0))
	}

	for i := len(Y) / 2; i < len(Y); i++ {
		api.AssertIsEqual(Y[i], frontend.Variable(0))
	}

	less := big.NewInt(0).Sub(Base, big.NewInt(1))

	// Ensure digits are within range
	for i := 0; i < len(X)/2; i++ {
		api.AssertIsLessOrEqual(X[i], less)
	}
	for i := 0; i < len(Y)/2; i++ {
		api.AssertIsLessOrEqual(Y[i], less)
	}
	for i := 0; i < len(Z); i++ {
		api.AssertIsLessOrEqual(Z[i], less)
	}

	for j := 0; j < len(Y)/2; j++ { // Y
		var row []frontend.Variable
		for i := 0; i < len(X)/2; i++ { // X
			xy := api.Mul(X[i], Y[j])
			row = append(row, xy)
		}
		rows[j] = row
	}

	summands := make([]frontend.Variable, len(Z))

	for i := 0; i < len(summands); i++ {
		summands[i] = frontend.Variable(big.NewInt(0))
	}

	for i := 0; i < len(rows); i++ {
		for j := 0; j < len(rows[i]); j++ {
			summands[i+j] = api.Add(summands[i+j], rows[i][j])
		}
	}

	for i := 0; i < len(Z); i++ {
		carry := frontend.Variable(0)
		if i > 0 {
			carry = carries[i]
		}

		summands[i] = api.Add(summands[i], carry)

		withoutDigit := api.Mul(Hints[i], frontend.Variable(Base))
		withDigit := api.Add(Z[i], withoutDigit)

		api.AssertIsEqual(summands[i], withDigit)
	}
}

func assertAdd(api frontend.API, X []frontend.Variable, Y []frontend.Variable, Z []frontend.Variable) {
	carries := make([]frontend.Variable, Words)
	for i := 0; i < len(carries); i++ {
		carries[i] = big.NewInt(0)
	}

	for i := 0; i < len(Z); i++ {

		XplusY := api.Add(X[i], Y[i])

		carry := frontend.Variable(big.NewInt(0))
		if i > 0 {
			carry = carries[i-1]
		}

		XplusY = api.Add(XplusY, carry)

		// If it's -1 then we want 0, otherwise we want 1
		maybeCarry := api.Cmp(XplusY, frontend.Variable(Base))

		isZero := api.Add(frontend.Variable(1), maybeCarry) // It's either 2 or 1 when we have a carry, otherwise it's 0
		carries[i] = api.Sub(frontend.Variable(1), api.IsZero(isZero))

		api.AssertIsEqual(XplusY, api.Add(api.Mul(carries[i], Base), Z[i]))

	}
}

type LayerPrecomputedValues struct {
	T        BaseDec
	B        BaseDec
	A        BaseDec
	TN       BaseDec
	Hints    BaseDec
	Carries  BaseDec
	Hints2   BaseDec
	Carries2 BaseDec
	LSB      *big.Int
}

type InputOutput struct {
	N        BaseDec
	U        BaseDec
	In       BaseDec
	PreImage []byte
	Hash     []byte
}

func SquareModExtractLSBPlaintext(maxDepth int, in *big.Int, base *big.Int) ([]LayerPrecomputedValues, InputOutput) {
	z := in

	_, inHints, inCarries := XmulY(Decompose(in, base), Decompose(in, base), base)

	n := Decompose(N, base)

	var res []LayerPrecomputedValues

	for i := 0; i < maxDepth; i++ {
		a := big.NewInt(0).Mul(z, z)
		b := big.NewInt(0).Mod(a, N)
		t := big.NewInt(0).Div(big.NewInt(0).Sub(a, b), N)
		tN := big.NewInt(0).Mul(t, N)
		lsb := big.NewInt(int64(b.Bit(0)))
		z = b

		prec := LayerPrecomputedValues{
			A:   Decompose(a, base),
			B:   Decompose(b, base),
			T:   Decompose(t, base),
			TN:  Decompose(tN, base),
			LSB: lsb,
		}

		_, hints, carries := XmulY(prec.T, n, base)

		prec.Hints = hints
		prec.Carries = carries
		if i > 0 {
			_, hints2, carries2 := XmulY(res[i-1].B, res[i-1].B, base)

			prec.Hints2 = hints2
			prec.Carries2 = carries2
		} else {
			prec.Hints2 = inHints
			prec.Carries2 = inCarries
		}

		res = append(res, prec)
	}

	// Start with a pre-image full of zeroes
	preImage := make([]byte, 48)
	// Fill the pre-image with bits according to LSBs
	for i := 1; i < len(res)-1; i++ {
		lsb := byte(res[i].LSB.Uint64() & 1)
		byteIndex := (i - 1) / 8
		bitIndex := (i - 1) % 8
		// Turn on the appropriate bit in the pre-image
		preImage[byteIndex] = preImage[byteIndex] | (lsb << bitIndex)
	}

	h := sha256.New()
	h.Write(preImage)
	hash := h.Sum(nil)

	u := Compose(res[len(res)-1].B, base)

	return res, InputOutput{
		In:       Decompose(in, base),
		N:        n,
		U:        Decompose(u, base),
		Hash:     hash,
		PreImage: preImage,
	}
}

func AssertSHA256(api frontend.API, c *Circuit) error {
	for i := 0; i < 8; i++ {
		for j := 0; j < 32; j++ {
			api.AssertIsBoolean(c.State[i][j])
		}
	}

	for i := 0; i < 16; i++ {
		for j := 0; j < 32; j++ {
			api.AssertIsBoolean(c.Data[i][j])
		}
	}

	constants := constants()
	for i := 0; i < 8; i++ {
		for j := 0; j < 32; j++ {
			api.AssertIsEqual(c.Constants[i][j], constants[i][j])
		}
	}

	k := k()
	for i := 0; i < 64; i++ {
		for j := 0; j < 32; j++ {
			api.AssertIsEqual(c.K[i][j], k[i][j])
		}
	}

	c.compute(api)

	return nil
}

type SHA256Witness struct {
	Hash      [8][32]frontend.Variable  `gnark:",public"`
	Constants [8][32]frontend.Variable  `gnark:",public"`
	K         [64][32]frontend.Variable `gnark:",public"`
	Data      [16][32]frontend.Variable
	State     [8][32]frontend.Variable
}

func PrepareSHA256Witness(preImage []byte, hash []byte) SHA256Witness {
	witness := SHA256Witness{
		Constants: constants(),
		K:         k(),
	}
	for i := 0; i < 8; i++ {
		witness.State[i] = witness.Constants[i]
	}
	for i := 0; i < len(witness.Data); i++ {
		for j := 0; j < 32; j++ {
			witness.Data[i][j] = uint32(0)
		}
	}

	// 5.1.1

	// Put one after the input
	witness.Data[len(preImage)/4][31] = uint32(1)

	// Put the bit length at the end
	for j := 0; j < 32; j++ {
		witness.Data[15][j] = uint32((len(preImage) * 8 >> j) & 1)
	}

	fillData(preImage, &witness.Data)
	fillHash(hash, &witness.Hash)

	return witness
}

func fillData(in []byte, data *[16][32]frontend.Variable) {
	for i := 0; i < len(in)/4; i++ {
		v1 := binary.BigEndian.Uint32([]byte{in[4*i], in[4*i+1], in[4*i+2], in[4*i+3]})
		for j := 0; j < 32; j++ {
			(*data)[i][j] = (v1 >> j) & 1
		}
	}
}

func fillHash(in []byte, data *[8][32]frontend.Variable) {
	for i := 0; i < len(in)/4; i++ {
		v1 := binary.BigEndian.Uint32([]byte{in[4*i], in[4*i+1], in[4*i+2], in[4*i+3]})
		for j := 0; j < 32; j++ {
			(*data)[i][j] = (v1 >> j) & 1
		}
	}
}

func constants() [8][32]frontend.Variable {
	x := [8]uint32{
		0x6a09e667,
		0xbb67ae85,
		0x3c6ef372,
		0xa54ff53a,
		0x510e527f,
		0x9b05688c,
		0x1f83d9ab,
		0x5be0cd19,
	}

	var constants [8][32]frontend.Variable
	for i := 0; i < 8; i++ {
		for j := 0; j < 32; j++ {
			constants[i][j] = (x[i] >> j) & 1
		}
	}

	return constants
}

func k() [64][32]frontend.Variable {
	x := [64]uint32{
		0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
		0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
		0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
		0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
		0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
		0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
		0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
		0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
	}

	var k [64][32]frontend.Variable

	for i := 0; i < 64; i++ {
		for j := 0; j < 32; j++ {
			k[i][j] = (x[i] >> j) & 1
		}
	}

	return k
}

func (c *Circuit) print(api frontend.API, W [64][32]frontend.Variable) {
	for i := 0; i < len(W); i++ {
		var vars []frontend.Variable
		for j := 0; j < 32; j++ {
			vars = append(vars, W[i][j])
		}
		api.Println(vars...)
	}
}

func (c *Circuit) compute(api frontend.API) {
	var W [64][32]frontend.Variable

	for t := 0; t < 16; t++ {
		for i := 0; i < 32; i++ {
			W[t][i] = c.Data[t][i]
		}
	}

	for t := 16; t < 64; t++ {
		sig1word := c.sig1Word(api, W[t-2])
		W[t] = c.add(api, c.add(api, c.add(api, sig1word, W[t-7]), c.sig0Word(api, W[t-15])), W[t-16])
	}

	a := c.State[0]
	b := c.State[1]
	C := c.State[2]
	d := c.State[3]
	e := c.State[4]
	f := c.State[5]
	g := c.State[6]
	h := c.State[7]

	for t := 0; t < 64; t++ {
		kt := c.K[t]
		T1 := c.add(api, c.add(api, c.add(api, c.add(api, h, c.ssig1Word(api, e)), c.chWord(api, e, f, g)), kt), W[t])
		T2 := c.add(api, c.ssig0Word(api, a), c.majWord(api, a, b, C))
		h = g
		g = f
		f = e
		e = c.add(api, d, T1)
		d = C
		C = b
		b = a
		a = c.add(api, T1, T2)
	}

	c.State[0] = c.add(api, a, c.State[0])
	c.State[1] = c.add(api, b, c.State[1])
	c.State[2] = c.add(api, C, c.State[2])
	c.State[3] = c.add(api, d, c.State[3])
	c.State[4] = c.add(api, e, c.State[4])
	c.State[5] = c.add(api, f, c.State[5])
	c.State[6] = c.add(api, g, c.State[6])
	c.State[7] = c.add(api, h, c.State[7])

	for i := 0; i < 8; i++ {
		for j := 0; j < 32; j++ {
			api.AssertIsBoolean(c.Hash[i][j])
			api.AssertIsBoolean(c.State[i][j])
			api.AssertIsEqual(c.Hash[i][j], c.State[i][j])
		}
	}
}

func (c *Circuit) add(api frontend.API, x [32]frontend.Variable, y [32]frontend.Variable) [32]frontend.Variable {
	return c.addBinary(api, x, y)
}

func (c *Circuit) addBinary(api frontend.API, X [32]frontend.Variable, Y [32]frontend.Variable) [32]frontend.Variable {
	carry := frontend.Variable(0)
	var z [32]frontend.Variable
	for i := 0; i < 32; i++ {
		x := X[i]
		y := Y[i]
		xXorY := api.Xor(x, y)
		xAndY := api.And(x, y)
		z[i] = api.Xor(xXorY, carry)
		carryAndXxorY := api.And(carry, xXorY)
		carry = api.Or(xAndY, carryAndXxorY)
	}

	return z
}

func (c *Circuit) xor(api frontend.API, xb [32]frontend.Variable, yb [32]frontend.Variable) [32]frontend.Variable {
	var zb [32]frontend.Variable
	for i := 0; i < 32; i++ {
		zb[i] = api.Xor(xb[i], yb[i])
	}
	return zb
}

func (c *Circuit) and(api frontend.API, xb [32]frontend.Variable, yb [32]frontend.Variable) [32]frontend.Variable {
	var zb [32]frontend.Variable
	for i := 0; i < 32; i++ {
		zb[i] = api.And(xb[i], yb[i])
	}
	return zb
}

func (c *Circuit) not(api frontend.API, xb [32]frontend.Variable) [32]frontend.Variable {
	var nxb [32]frontend.Variable
	for i := 0; i < 32; i++ {
		nxb[i] = api.Xor(xb[i], 1)
	}
	return nxb
}

func (c *Circuit) rotateRight(api frontend.API, x [32]frontend.Variable, i int) [32]frontend.Variable {
	xr := c.shiftRight(api, x, i)
	xl := c.shiftLeft(api, x, 32-i)

	var b [32]frontend.Variable
	for j := 0; j < 32; j++ {
		b[j] = api.Or(xr[j], xl[j])
	}
	return b
}

func (c *Circuit) shiftRight(api frontend.API, xb [32]frontend.Variable, i int) [32]frontend.Variable {
	var b [32]frontend.Variable
	for j := 0; j < 32; j++ {
		b[j] = 0
	}
	for j := 0; j < 32-i; j++ {
		b[j] = xb[j+i]
	}
	return b
}

func (c *Circuit) shiftLeft(api frontend.API, xb [32]frontend.Variable, i int) [32]frontend.Variable {
	var b [32]frontend.Variable
	for j := 0; j < 32; j++ {
		b[j] = 0
	}
	for j := 0; j < 32-i; j++ {
		b[j+i] = xb[j]
	}
	return b
}

func (c *Circuit) ssig0Word(api frontend.API, xb [32]frontend.Variable) [32]frontend.Variable {
	return c.xor(api, c.xor(api, c.rotateRight(api, xb, 2), c.rotateRight(api, xb, 13)), c.rotateRight(api, xb, 22))
}

func (c *Circuit) ssig1Word(api frontend.API, xb [32]frontend.Variable) [32]frontend.Variable {
	return c.xor(api, c.xor(api, c.rotateRight(api, xb, 6), c.rotateRight(api, xb, 11)), c.rotateRight(api, xb, 25))
}

func (c *Circuit) sig0Word(api frontend.API, xb [32]frontend.Variable) [32]frontend.Variable {
	return c.xor(api, c.xor(api, c.rotateRight(api, xb, 7), c.rotateRight(api, xb, 18)), c.shiftRight(api, xb, 3))
}

func (c *Circuit) sig1Word(api frontend.API, xb [32]frontend.Variable) [32]frontend.Variable {
	return c.xor(api, c.xor(api, c.rotateRight(api, xb, 17), c.rotateRight(api, xb, 19)), c.shiftRight(api, xb, 10))
}

func (c *Circuit) chWord(api frontend.API, xb [32]frontend.Variable, yb [32]frontend.Variable, zb [32]frontend.Variable) [32]frontend.Variable {
	return c.xor(api, c.and(api, xb, yb), c.and(api, c.not(api, xb), zb))
}

func (c *Circuit) majWord(api frontend.API, xb [32]frontend.Variable, yb [32]frontend.Variable, zb [32]frontend.Variable) [32]frontend.Variable {
	return c.xor(api, c.xor(api, c.and(api, xb, yb), c.and(api, xb, zb)), c.and(api, yb, zb))
}

func RunBenchmark() {
	fmt.Println("Running with", Layers, "layers")
	in := RandomGroupElement()

	precomputed, inOut := SquareModExtractLSBPlaintext(Layers, in, Base)

	sha256Witness := PrepareSHA256Witness(inOut.PreImage, inOut.Hash)

	var c Circuit
	c.N = make([]frontend.Variable, Words)
	c.U = make([]frontend.Variable, Words)

	c.In = make([]frontend.Variable, Words)

	for layer := 0; layer < Layers; layer++ {
		c.As[layer] = make([]frontend.Variable, Words)
		c.Bs[layer] = make([]frontend.Variable, Words)
		c.Hints[layer] = make([]frontend.Variable, Words)
		c.Hints2[layer] = make([]frontend.Variable, Words)
		c.Carries[layer] = make([]frontend.Variable, Words)
		c.Carries2[layer] = make([]frontend.Variable, Words)
		c.Ts[layer] = make([]frontend.Variable, Words)
		c.TNs[layer] = make([]frontend.Variable, Words)
	}

	assignment := Circuit{
		In: inOut.In.ToVariable(Words),
		U:  inOut.U.ToVariable(Words),
		N:  inOut.N.ToVariable(Words),
	}

	for layer := 0; layer < Layers; layer++ {
		assignment.As[layer] = precomputed[layer].A.ToVariable(Words)
		assignment.Bs[layer] = precomputed[layer].B.ToVariable(Words)
		assignment.Ts[layer] = precomputed[layer].T.ToVariable(Words)
		assignment.TNs[layer] = precomputed[layer].TN.ToVariable(Words)
		assignment.Carries[layer] = precomputed[layer].Carries.ToVariable(Words)
		assignment.Hints[layer] = precomputed[layer].Hints.ToVariable(Words)
		assignment.Carries2[layer] = precomputed[layer].Carries2.ToVariable(Words)
		assignment.Hints2[layer] = precomputed[layer].Hints2.ToVariable(Words)

		// The first layer performs the preliminary modular squaring to ensure
		// the input is a Quadratic residue, so we ignore it.

		// The last layer is also ignored from the same reason.
		// We use the last layer to compute 'u' and therefore
		// we do not want to take its LSB.

		// In the paper it is shown differently, but here we just use the outputs
		// of the first and last layers to avoid code duplication,
		// since they perform modular squaring which is what we need.

		if layer > 0 && layer < Layers-1 {
			assignment.LSBs[layer-1] = precomputed[layer].LSB

			lsb := precomputed[layer].B[0].Bit(0)
			withoutLSB := big.NewInt(0).Sub(precomputed[layer].B[0], big.NewInt(int64(lsb)))
			halfWithoutLSB := big.NewInt(0).Div(withoutLSB, big.NewInt(2))
			assignment.LSBHints[layer-1] = frontend.Variable(halfWithoutLSB)
		}
	}

	assignment.Hash = sha256Witness.Hash
	assignment.Data = sha256Witness.Data
	assignment.K = sha256Witness.K
	assignment.Constants = sha256Witness.Constants
	assignment.State = sha256Witness.State

	ccs, err := frontend.Compile(ecc.BN254, backend.GROTH16, &c)
	if err != nil {
		panic(err)
	}

	t1 := time.Now()
	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		panic(err)
	}
	fmt.Println("Setup elapsed", time.Since(t1))

	fmt.Println("Total", ccs.GetNbConstraints(), "constraints")

	witness, err := frontend.NewWitness(&assignment, ecc.BN254)
	if err != nil {
		panic(err)
	}

	publicWitness, err := witness.Public()
	if err != nil {
		panic(err)
	}

	t1 = time.Now()
	proof, err := groth16.Prove(ccs, pk, witness)
	if err != nil {
		panic(err)
	}

	fmt.Println("Proof time:", time.Since(t1))

	t1 = time.Now()
	err = groth16.Verify(proof, vk, publicWitness)
	if err != nil {
		panic(err)
	}
	fmt.Println("Verification time:", time.Since(t1))
}
