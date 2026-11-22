/- P6 native source fields: small, isolated. -/
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
abbrev p6P (X : N8NativeInput l) : Nat := (completionRationalPrime (nativeFPlaceOverBad X)).val
abbrev p6Place (X : N8NativeInput l) : FinitePlaceAtPrime X.S.arithmetic.F (p6P X) :=
  ⟨nativeFPlaceOverBad X, rfl⟩
abbrev p6Places (X : N8NativeInput l) : Unit -> Unit -> FinitePlaceAtPrime X.S.arithmetic.F (p6P X) :=
  fun _ _ => p6Place X
abbrev p6Tuple (X : N8NativeInput l) : Unit -> Unit := fun _ => Unit.unit
abbrev P6Block (X : N8NativeInput l) : Type :=
  ArithmeticTensorTupleBlock (K := X.S.arithmetic.F) (p := p6P X) (p6Places X) (p6Tuple X)
local instance p6BlockMeasurableSpace (X : N8NativeInput l) : MeasurableSpace (P6Block X) := borel _
local instance p6BlockBorelSpace (X : N8NativeInput l) : BorelSpace (P6Block X) := ⟨rfl⟩
noncomputable def p6Witness (X : N8NativeInput l) :
    TensorCoreWitness (p := p6P X) (p6Places X) (p6Tuple X) :=
  tensorCoreWitness (p := p6P X) (p6Places X) (p6Tuple X)
#check p6Witness
end LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
