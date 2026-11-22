import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncLimitZeroActual
import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncLimitConsumerActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperQZeroLimitConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual
open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitConsumerActual

universe u

/-- Paper-level data for the q^0 coefficient of the symmetric theta limit. -/
structure PaperQZeroLimitData (K : Type u) [Field K] where
  coeff : HahnSeries Int K
  coeff_eq : coeff = etaleThetaSymmetricCoeffLimit K (0 : HalfInt)
  value_eq : coeff =
    HahnSeries.single (thetaUExponent 0) (1 : K) +
      HahnSeries.single (thetaUExponent (-1)) (-1 : K)
  support_eq : coeff.support = ({1, -1} : Set Int)
  support_encard : coeff.support.encard = 2
  support_finite : coeff.support.Finite
  support_nonempty : coeff.support.Nonempty
  thetaCoeffAt_eq : coeff = thetaCoeffAt K 0

noncomputable def paperQZeroLimitData (K : Type u) [Field K] :
    PaperQZeroLimitData K where
  coeff := etaleThetaSymmetricCoeffLimit K (0 : HalfInt)
  coeff_eq := rfl
  value_eq := etaleThetaSymmetricCoeffLimit_zero K
  support_eq := etaleThetaSymmetricCoeffLimit_zero_support_eq K
  support_encard := etaleThetaSymmetricCoeffLimit_zero_support_encard K
  support_finite := etaleThetaSymmetricCoeffLimit_zero_support_finite K
  support_nonempty := etaleThetaSymmetricCoeffLimit_zero_support_nonempty K
  thetaCoeffAt_eq := etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt K

@[simp] theorem paperQZeroLimitData_coeff (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff =
      etaleThetaSymmetricCoeffLimit K (0 : HalfInt) := rfl

@[simp] theorem paperQZeroLimitData_value (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) :=
  (paperQZeroLimitData K).value_eq

@[simp] theorem paperQZeroLimitData_support_eq (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support = ({1, -1} : Set Int) :=
  (paperQZeroLimitData K).support_eq

@[simp] theorem paperQZeroLimitData_support_encard (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.encard = 2 :=
  (paperQZeroLimitData K).support_encard

@[simp] theorem paperQZeroLimitData_thetaCoeffAt (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff = thetaCoeffAt K 0 :=
  (paperQZeroLimitData K).thetaCoeffAt_eq

@[simp] theorem paperQZeroLimitData_coeff_thetaUExponent_zero
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.coeff (thetaUExponent 0) = 1 := by
  rw [paperQZeroLimitData_coeff]
  rw [show thetaUExponent 0 = (1 : Int) by unfold thetaUExponent; norm_num]
  exact etaleThetaSymmetricCoeffLimit_zero_coeff_one K

@[simp] theorem paperQZeroLimitData_coeff_thetaUExponent_neg_one
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.coeff (thetaUExponent (-1)) = -1 := by
  rw [paperQZeroLimitData_coeff]
  rw [show thetaUExponent (-1) = (-1 : Int) by unfold thetaUExponent; norm_num]
  exact etaleThetaSymmetricCoeffLimit_zero_coeff_neg_one K

theorem paperQZeroLimitData_support_mem_iff (K : Type u) [Field K] (x : Int) :
    x ∈ (paperQZeroLimitData K).coeff.support ↔
      x = thetaUExponent 0 ∨ x = thetaUExponent (-1) := by
  rw [paperQZeroLimitData_support_eq]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff, thetaUExponent]

theorem paperQZeroLimitData_support_eq_thetaCoeffAt
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support = (thetaCoeffAt K 0).support := by
  rw [paperQZeroLimitData_thetaCoeffAt]

theorem paperQZeroLimitData_coeff_ne_zero (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff ≠ 0 := by
  rw [paperQZeroLimitData_coeff]
  exact etaleThetaSymmetricCoeffLimit_zero_ne_zero K

theorem paperQZeroLimitData_support_encard_eq_thetaCoeffAt
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.encard =
      (thetaCoeffAt K 0).support.encard := by
  rw [paperQZeroLimitData_support_eq_thetaCoeffAt]

theorem paperQZeroLimitData_support_finite_eq_thetaCoeffAt
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.Finite ↔
      (thetaCoeffAt K 0).support.Finite := by
  rw [paperQZeroLimitData_support_eq_thetaCoeffAt]

theorem paperQZeroLimitData_coeff_eq_trunc (K : Type u) [Field K]
    (N : Nat)
    (hN : Classical.choose
      (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)) <= N) :
    (paperQZeroLimitData K).coeff =
      (etaleThetaSymmetricTrunc K N).coeff (0 : HalfInt) := by
  rw [paperQZeroLimitData_coeff]
  exact etaleThetaSymmetricCoeffLimit_eq_trunc K 0 N hN

theorem paperQZeroLimitData_coeff_eq_trunc_choose (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff =
      (etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt) := by
  rw [paperQZeroLimitData_coeff]
  exact etaleThetaSymmetricCoeffLimit_eq_trunc_choose K 0

theorem paperQZeroLimitData_support_eq_trunc_choose
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support =
      ((etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
          (0 : HalfInt)).support := by
  rw [paperQZeroLimitData_coeff_eq_trunc_choose]

theorem paperQZeroLimitData_support_encard_eq_trunc_choose
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.encard =
      ((etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
          (0 : HalfInt)).support.encard := by
  rw [paperQZeroLimitData_support_eq_trunc_choose]

theorem paperQZeroLimitData_support_finite_eq_trunc_choose
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.Finite ↔
      ((etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
          (0 : HalfInt)).support.Finite := by
  rw [paperQZeroLimitData_support_eq_trunc_choose]

theorem paperQZeroLimitData_support_nonempty_iff_trunc_choose
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.Nonempty ↔
      ((etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
          (0 : HalfInt)).support.Nonempty := by
  rw [paperQZeroLimitData_support_eq_trunc_choose]

theorem paperQZeroLimitData_support_eq_pair_support
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support =
      ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support := by
  rw [paperQZeroLimitData_support_eq_thetaCoeffAt]
  rfl

theorem paperQZeroLimitData_coeff_eq_pair (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff =
      (thetaPairTerm K 0).coeff (thetaQExponent 0) := by
  rw [paperQZeroLimitData_thetaCoeffAt]
  rfl

theorem trunc_choose_zero_support_encard_via_paper (K : Type u) [Field K] :
    ((etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt)).support.encard = 2 := by
  rw [← paperQZeroLimitData_support_eq_trunc_choose]
  exact paperQZeroLimitData_support_encard K

theorem trunc_choose_zero_support_finite_via_paper (K : Type u) [Field K] :
    ((etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt)).support.Finite :=
  (paperQZeroLimitData_support_finite_eq_trunc_choose K).mp
    (paperQZeroLimitData K).support_finite

theorem trunc_choose_zero_support_nonempty_via_paper (K : Type u) [Field K] :
    ((etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt)).support.Nonempty :=
  (paperQZeroLimitData_support_nonempty_iff_trunc_choose K).mp
    (paperQZeroLimitData K).support_nonempty

theorem trunc_choose_zero_eq_paper_coeff (K : Type u) [Field K] :
    (etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt) = (paperQZeroLimitData K).coeff :=
  (paperQZeroLimitData_coeff_eq_trunc_choose K).symm

theorem paperQZeroLimitData_support_encard_eq_pair_support
    (K : Type u) [Field K] :
    (paperQZeroLimitData K).coeff.support.encard =
      ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support.encard := by
  rw [paperQZeroLimitData_support_eq_pair_support]

#check paperQZeroLimitData
#check paperQZeroLimitData_value
#check paperQZeroLimitData_thetaCoeffAt

end LeanFormal.IUT.XiFPaper.PaperQZeroLimitConsumerActual

end