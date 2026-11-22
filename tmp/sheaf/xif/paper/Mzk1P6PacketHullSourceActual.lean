/- P6 PacketHullData source fields from the actual tensor-core witness. -/
import tmp.sheaf.xif.paper.Mzk1P6SourceFieldsActual
import tmp.sheaf.n8.closure.NativeC3
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Tactic
noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
open LeanFormal.IUT.XiFPaper.Mzk1P6SourceFieldsActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullSourceActual
variable {l : PrimeGeFive} (X : N8NativeInput l)
noncomputable def p6PacketHullData (X : N8NativeInput l) :
    PacketHullData (p := p6P X) (p6Places X) (p6Tuple X)
      (J := (p6Witness X).J) (E := (p6Witness X).E) := by
  let W := p6Witness X
  letI : Fintype W.J := W.fintype
  letI (j : W.J) : NontriviallyNormedField (W.E j) := W.field j
  letI (j : W.J) : NormedAlgebra ℚ_[p6P X] (W.E j) := W.alg j
  letI (j : W.J) : FiniteDimensional ℚ_[p6P X] (W.E j) := W.finite j
  letI (j : W.J) : ProperSpace (W.E j) := FiniteDimensional.proper ℚ_[p6P X] (W.E j)
  exact {
    mu := MeasureTheory.Measure.addHaar
    inst := inferInstance
    e := W.equiv
    istar := Unit.unit
    varpi := 1
    hvarpi := one_ne_zero
    Phi := {phi | ∀ u, u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X) ->
      phi u ∈ arithmeticTupleUnitLogLattice (p6Places X) (p6Tuple X)}
    hPhi_ne := ⟨LinearEquiv.refl ℚ_[p6P X] (P6Block X), by
      intro u hu; simpa using hu⟩
    hPhi := by intro phi hphi u hu; exact hphi u hu
    exceptional := Finset.univ
    small_outside := by intro i hi; exact absurd (Finset.mem_univ i) hi }
theorem p6PacketHullData_nonempty (X : N8NativeInput l) :
    Nonempty (PacketHullData (p := p6P X) (p6Places X) (p6Tuple X)
      (J := (p6Witness X).J) (E := (p6Witness X).E)) :=
  ⟨p6PacketHullData X⟩
#print axioms p6PacketHullData
#print axioms p6PacketHullData_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullSourceActual
