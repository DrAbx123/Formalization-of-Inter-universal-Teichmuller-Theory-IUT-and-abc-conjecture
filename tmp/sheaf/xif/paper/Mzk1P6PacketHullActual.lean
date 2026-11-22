/- P6 actual PacketHullData inhabitant from the actual F-place and native q. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.n8.closure.NativeC3
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import Mathlib.Tactic
set_option synthInstance.maxHeartbeats 4000000
set_option maxHeartbeats 4000000
noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullActual
variable {l : PrimeGeFive} (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l)
abbrev p6P (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) : Nat :=
  (NumberFieldFinitePlace.completionRationalPrime (LeanFormal.IUT.N8Closure.NativeC3.nativeFPlaceOverBad X)).val
abbrev p6Place (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) : FinitePlaceAtPrime X.S.arithmetic.F (p6P X) :=
  ⟨LeanFormal.IUT.N8Closure.NativeC3.nativeFPlaceOverBad X, rfl⟩
abbrev p6Places (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) : PUnit -> PUnit -> FinitePlaceAtPrime X.S.arithmetic.F (p6P X) :=
  fun _ _ => p6Place X
abbrev p6Tuple (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) : PUnit -> PUnit := fun _ => PUnit.unit
abbrev P6Block (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) : Type :=
  ArithmeticTensorTupleBlock (K := X.S.arithmetic.F) (p := p6P X) (p6Places X) (p6Tuple X)
local instance p6BlockMeasurableSpace (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) :
    MeasurableSpace (P6Block X) := borel _
local instance p6BlockBorelSpace (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) :
    BorelSpace (P6Block X) := ⟨rfl⟩

def p6AlgEquivPUnit (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) : P6Block X ≃ₐ[ℚ_[p6P X]] (PUnit -> P6Block X) where
  toFun x := fun _ => x
  invFun f := f PUnit.unit
  left_inv _ := rfl
  right_inv f := by funext i; cases i; rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl
noncomputable def p6PacketHullData (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) :
    PacketHullData (K := X.S.arithmetic.F) (p := p6P X) (p6Places X) (p6Tuple X)
      (J := PUnit) (E := fun _ => P6Block X) where
  mu := MeasureTheory.Measure.addHaar
  inst := inferInstance
  e := p6AlgEquivPUnit X
  istar := PUnit.unit
  varpi := (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q
  hvarpi := (LeanFormal.IUT.N8Closure.NativeC3.nativeQActual X).q_ne_zero
  Phi := {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X) ->
    phi u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X)}
  hPhi_ne := ⟨LinearEquiv.refl ℚ_[p6P X] (P6Block X), by
    intro u hu
    simpa using hu⟩
  hPhi := by intro phi hphi u hu; exact hphi u hu
  exceptional := Finset.univ
  small_outside := by intro i hi; exact absurd (Finset.mem_univ i) hi
theorem p6PacketHullData_nonempty (X : LeanFormal.IUT.N8Closure.NativeInput.N8NativeInput l) :
    Nonempty (PacketHullData (K := X.S.arithmetic.F) (p := p6P X)
      (p6Places X) (p6Tuple X) (J := PUnit) (E := fun _ => P6Block X)) :=
  ⟨p6PacketHullData X⟩
#print axioms p6PacketHullData
#print axioms p6PacketHullData_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullActual
