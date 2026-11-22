import tmp.sheaf.xif.paper.S2321OUnitsChainFinalActual
import tmp.sheaf.xif.paper.S2232Layer1PrimeAlignmentActual
import Mathlib.Data.Nat.Prime.Infinite

/-! # S2324: whether S2135 is satisfiable for arbitrary T

S2135 is exactly `qVFamTensorP T b ∈ primeStrip 2 7`, equivalently
`qVFamTensorP T b ≤ 7`.  This file records the exact universal and
counterexample alternatives, proves their classical dichotomy, and records the
source obstruction (there are odd primes above 7) without fabricating a concrete
T or a universal source proof. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2324S2135DecideActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S2232Layer1PrimeAlignmentActual
open LeanFormal.IUT.XiFPaper.S2135Layer1SplitActual
open LeanFormal.IUT.XiFPaper.S2321OUnitsChainFinalActual

universe u

variable {l : PrimeGeFive}

theorem s2324_not_strip_iff_gt_seven
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    ¬ S2135PrimeAlignmentRequired T b ↔
      7 < qVFamTensorP T b := by
  rw [S2135PrimeAlignmentRequired, s2232_mem_primeStrip_iff_le_seven]
  exact Nat.not_le

/-- The universal alternative: every T,b has qVFamTensorP ≤ 7. -/
def S2324Universal : Prop :=
  ∀ (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)), qVFamTensorP T b ≤ 7

/-- The counterexample alternative: some actual T,b has qVFamTensorP > 7. -/
structure S2324CounterexampleRequired
    (l : PrimeGeFive) where
  T : SourceNativeInitialThetaData.{0} l
  b : Bad (nativePlaceSelection T)
  gt_seven : 7 < qVFamTensorP T b

theorem s2324_counterexample_not_strip
    (C : S2324CounterexampleRequired l) :
    ¬ S2135PrimeAlignmentRequired C.T C.b :=
  (s2324_not_strip_iff_gt_seven C.T C.b).mpr C.gt_seven

theorem s2324_dichotomy
    (l : PrimeGeFive) :
    S2324Universal (l := l) ∨
      Nonempty (S2324CounterexampleRequired l) := by
  classical
  by_cases h : ∀ (T : SourceNativeInitialThetaData.{0} l)
      (b : Bad (nativePlaceSelection T)), qVFamTensorP T b ≤ 7
  · exact Or.inl h
  · right
    push_neg at h
    obtain ⟨T, b, hb⟩ := h
    exact ⟨{ T := T, b := b, gt_seven := hb }⟩

/-- Actual arithmetic obstacle: primes above 7 exist; source arithmetic fields
(oddness/coprimality) do not bound them. -/
theorem s2324_prime_above_seven :
    ∃ p : Nat, Nat.Prime p ∧ 7 < p :=
  let ⟨p, hp, hpp⟩ := Nat.exists_infinite_primes 8
  ⟨p, hpp, by omega⟩

/-- If S2135 were universal, the whole chain would be unconditional. -/
theorem s2324_chain_universal_of_universal
    (h : S2324Universal (l := l)) :
    ∀ (T : SourceNativeInitialThetaData.{0} l)
      (b : Bad (nativePlaceSelection T)),
      Nonempty (S2321OUnitsChain T b) :=
  fun T b =>
    (s2321Chain_iff_primeAlignment T b).mpr (by
      by_contra hnot
      exact (Nat.not_lt.mpr (h T b))
        ((s2324_not_strip_iff_gt_seven T b).mp hnot))

/-- Exact missing decision data. -/
def S2324DecisionRequired : Prop :=
  Nonempty (S2324CounterexampleRequired l) ∨
    ∀ (T : SourceNativeInitialThetaData.{0} l)
      (b : Bad (nativePlaceSelection T)),
      Nonempty (S2321OUnitsChain T b)

#check s2324_not_strip_iff_gt_seven
#check S2324Universal
#check S2324CounterexampleRequired
#check s2324_counterexample_not_strip
#check s2324_dichotomy
#check s2324_prime_above_seven
#check s2324_chain_universal_of_universal
#check S2324DecisionRequired

end LeanFormal.IUT.XiFPaper.S2324S2135DecideActual
end
