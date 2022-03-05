package avtc

import (
	"fmt"
	"math/big"
	"testing"

	"github.com/consensys/gnark-crypto/ecc"
	"github.com/consensys/gnark/backend"
	"github.com/consensys/gnark/backend/groth16"
	"github.com/consensys/gnark/frontend"
)

func TestAVTC(t *testing.T) {
	RunBenchmark()
}

type MulCircuit struct {
	A       []frontend.Variable
	B       []frontend.Variable `gnark:",public"`
	C       []frontend.Variable
	Hints   []frontend.Variable
	Carries []frontend.Variable
}

func (c *MulCircuit) Define(api frontend.API) error {
	assertMulY(api, c.A, c.B, c.C, c.Hints, c.Carries)
	return nil
}

type AddCircuit struct {
	A []frontend.Variable
	B []frontend.Variable
	C []frontend.Variable
}

func (c *AddCircuit) Define(api frontend.API) error {
	assertAdd(api, c.A, c.B, c.C)
	return nil
}

func TestMul(t *testing.T) {
	var c MulCircuit
	c.A = make([]frontend.Variable, Words)
	c.B = make([]frontend.Variable, Words)
	c.C = make([]frontend.Variable, Words)
	c.Hints = make([]frontend.Variable, Words)
	c.Carries = make([]frontend.Variable, Words)

	ccs, err := frontend.Compile(ecc.BN254, backend.GROTH16, &c)
	if err != nil {
		panic(err)
	}

	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		panic(err)
	}

	fmt.Println("Total", ccs.GetNbConstraints(), "constraints")

	a := RandomGroupElement()
	b := RandomGroupElement()

	A := Decompose(a, Base)
	B := Decompose(b, Base)
	C, hints, carries := XmulY(A, B, Base)

	x := A.ToVariable(Words)
	y := B.ToVariable(Words)
	z := C.ToVariable(Words)

	assignment := MulCircuit{A: x, B: y, C: z, Hints: make([]frontend.Variable, Words), Carries: make([]frontend.Variable, Words)}

	for i := 0; i < Words; i++ {
		if i < len(hints) {
			assignment.Hints[i] = frontend.Variable(hints[i])
		} else {
			assignment.Hints[i] = frontend.Variable(big.NewInt(0))
		}
	}

	for i := 0; i < Words; i++ {
		if i < len(carries) {
			assignment.Carries[i] = frontend.Variable(carries[i])
		} else {
			assignment.Carries[i] = frontend.Variable(big.NewInt(0))
		}
	}

	witness, err := frontend.NewWitness(&assignment, ecc.BN254)
	if err != nil {
		panic(err)
	}

	publicWitness, _ := witness.Public()

	proof, err := groth16.Prove(ccs, pk, witness)
	if err != nil {
		panic(err)
	}

	err = groth16.Verify(proof, vk, publicWitness)
	if err != nil {
		panic(err)
	}
}

func TestAdd(t *testing.T) {
	var c AddCircuit
	c.A = make([]frontend.Variable, Words)
	c.B = make([]frontend.Variable, Words)
	c.C = make([]frontend.Variable, Words)

	ccs, err := frontend.Compile(ecc.BN254, backend.GROTH16, &c)
	if err != nil {
		panic(err)
	}

	pk, vk, err := groth16.Setup(ccs)
	if err != nil {
		panic(err)
	}

	fmt.Println("Total", ccs.GetNbConstraints(), "constraints")

	a := RandomGroupElement()
	b := RandomGroupElement()

	A := Decompose(a, Base)
	B := Decompose(b, Base)
	C := XPlusY(A, B, Base)

	x := A.ToVariable(Words)
	y := B.ToVariable(Words)
	z := C.ToVariable(Words)

	assignment := AddCircuit{A: x, B: y, C: z}
	witness, err := frontend.NewWitness(&assignment, ecc.BN254)
	if err != nil {
		panic(err)
	}

	publicWitness, _ := witness.Public()

	proof, err := groth16.Prove(ccs, pk, witness)
	if err != nil {
		panic(err)
	}

	err = groth16.Verify(proof, vk, publicWitness)
	if err != nil {
		panic(err)
	}
}
