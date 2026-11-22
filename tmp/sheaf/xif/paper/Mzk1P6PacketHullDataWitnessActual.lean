/- P6 PacketHullData from the actual tensor-core field-product witness. -/
import tmp.sheaf.xif.paper.Mzk1TensorCoreWitnessActual
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 2000000
noncomputable section
open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1TensorCoreWitnessActual
open LeanFormal.IUT.XiFPaper.Mzk1BoxReadoutLocalActual
namespace LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullDataWitnessActual
universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] [Nonempty ι]
variable {V : ι -> Type w} [∀ i, Fintype (V i)] [∀ i, DecidableEq (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
/-- Actual PacketHullData from an actual tensor-core field-product witness. -/
noncomputable def packetHullDataOfWitness
    (W : TensorCoreWitness places tuple)
    [Finite W.J]
    [∀ j, NontriviallyNormedField (W.E j)]
    [∀ j, NormedAlgebra ℚ_[p] (W.E j)]
    [∀ j, FiniteDimensional ℚ_[p] (W.E j)]
    [∀ j, ProperSpace (W.E j)] :
    PacketHullData places tuple (J := W.J) (E := W.E) := by
  let istar : ι := Classical.choice (inferInstance : Nonempty ι)
  let varpi : CommonPrimeCompletion (places istar (tuple istar)) :=
    (p : CommonPrimeCompletion (places istar (tuple istar)))
  refine
    { mu := MeasureTheory.Measure.addHaar
      inst := inferInstance
      e := W.equiv
      istar := istar
      varpi := varpi
      hvarpi := ?_
      Phi := {LinearEquiv.refl ℚ_[p] (ArithmeticTensorTupleBlock places tuple)}
      hPhi_ne := ⟨LinearEquiv.refl _ _, by simp⟩
      hPhi := ?_
      exceptional := Finset.univ
      small_outside := ?_ }
  · change (p : CommonPrimeCompletion (places istar (tuple istar))) ≠ 0
    exact_mod_cast (Fact.out : Nat.Prime p).ne_zero
  · intro phi hphi u hu
    simp only [Set.mem_singleton_iff] at hphi
    subst hphi
    simpa using hu
  · intro i hi
    exact absurd (Finset.mem_univ i) hi
theorem packetHullDataOfWitness_nonempty
    (W : TensorCoreWitness places tuple) :
    Nonempty (PacketHullData places tuple (J := W.J) (E := W.E)) :=
  letI : Fintype W.J := W.fintype
  letI : Finite W.J := Finite.of_fintype W.J
  letI (j : W.J) : NontriviallyNormedField (W.E j) := W.field j
  letI (j : W.J) : NormedAlgebra ℚ_[p] (W.E j) := W.alg j
  letI (j : W.J) : FiniteDimensional ℚ_[p] (W.E j) := W.finite j
  letI (j : W.J) : ProperSpace (W.E j) := FiniteDimensional.proper ℚ_[p] (W.E j)
  ⟨packetHullDataOfWitness places tuple W⟩
#print axioms packetHullDataOfWitness
end LeanFormal.IUT.XiFPaper.Mzk1P6PacketHullDataWitnessActual
end