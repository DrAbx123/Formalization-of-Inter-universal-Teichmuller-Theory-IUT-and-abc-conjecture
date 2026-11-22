import tmp.sheaf.xif.paper.EtaleThetaSymmetricTruncLimitZeroActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitConsumerActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing
open LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitActual

universe u

theorem etaleThetaSymmetricTrunc_coeff_const_of_ge (K : Type u) [Field K]
    (e : HalfInt) (N : Nat)
    (hN : Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e) <= N) :
    forall M : Nat, N <= M ->
      (etaleThetaSymmetricTrunc K M).coeff e =
        (etaleThetaSymmetricTrunc K N).coeff e := by
  intro M hNM
  induction M, hNM using Nat.le_induction with
  | base => rfl
  | succ m hNm ih =>
      rw [etaleThetaSymmetricCoeffLimit_spec K e m (le_trans hN hNm), ih]

theorem etaleThetaSymmetricCoeffLimit_eq_trunc (K : Type u) [Field K]
    (e : HalfInt) (N : Nat)
    (hN : Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e) <= N) :
    etaleThetaSymmetricCoeffLimit K e =
      (etaleThetaSymmetricTrunc K N).coeff e := by
  unfold etaleThetaSymmetricCoeffLimit
  rw [etaleThetaSymmetricTrunc_coeff_const_of_ge K e
    (Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e)) le_rfl N hN]

theorem etaleThetaSymmetricCoeffLimit_eq_trunc_choose (K : Type u) [Field K]
    (e : HalfInt) :
    etaleThetaSymmetricCoeffLimit K e =
      (etaleThetaSymmetricTrunc K
        (Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e))).coeff e := by
  unfold etaleThetaSymmetricCoeffLimit
  rfl

theorem etaleThetaSymmetricCoeffLimit_trunc_eq (K : Type u) [Field K]
    (e : HalfInt) (N : Nat)
    (hN : Classical.choose (etaleThetaSymmetricTrunc_coeff_eventually_stable K e) <= N) :
    (etaleThetaSymmetricTrunc K N).coeff e =
      etaleThetaSymmetricCoeffLimit K e :=
  (etaleThetaSymmetricCoeffLimit_eq_trunc K e N hN).symm

theorem etaleThetaSymmetricCoeffLimit_zero_eq_trunc (K : Type u) [Field K]
    (N : Nat)
    (hN : Classical.choose
      (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)) <= N) :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      (etaleThetaSymmetricTrunc K N).coeff (0 : HalfInt) :=
  etaleThetaSymmetricCoeffLimit_eq_trunc K 0 N hN

theorem etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      (etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt) :=
  etaleThetaSymmetricCoeffLimit_eq_trunc_choose K 0

theorem etaleThetaSymmetricTrunc_choose_zero_eq_thetaCoeffAt_consumer
    (K : Type u) [Field K] :
    (etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt) = thetaCoeffAt K 0 := by
  rw [← etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose]
  exact etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt K

theorem etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer
    (K : Type u) [Field K] :
    ((etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt)).support = (thetaCoeffAt K 0).support := by
  rw [etaleThetaSymmetricTrunc_choose_zero_eq_thetaCoeffAt_consumer]

theorem etaleThetaSymmetricTrunc_choose_zero_ne_zero_consumer
    (K : Type u) [Field K] :
    (etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt) ≠ 0 := by
  rw [etaleThetaSymmetricTrunc_choose_zero_eq_thetaCoeffAt_consumer]
  exact thetaCoeffAt_zero_ne_zero_minimal K

theorem etaleThetaSymmetricTrunc_choose_zero_support_encard_consumer
    (K : Type u) [Field K] :
    ((etaleThetaSymmetricTrunc K
      (Classical.choose
        (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
        (0 : HalfInt)).support.encard = 2 := by
  rw [etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer]
  exact thetaCoeffAt_zero_support_encard K

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_trunc_choose_consumer
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support =
      ((etaleThetaSymmetricTrunc K
        (Classical.choose
          (etaleThetaSymmetricTrunc_coeff_eventually_stable K (0 : HalfInt)))).coeff
          (0 : HalfInt)).support := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose]

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_thetaCoeffAt_consumer
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support =
      (thetaCoeffAt K 0).support := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_trunc_choose_consumer,
    etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer]

theorem etaleThetaSymmetricCoeffLimit_zero_support_finite_consumer
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Finite := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_trunc_choose_consumer,
    etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer]
  exact thetaCoeffAt_zero_support_finite K

theorem etaleThetaSymmetricCoeffLimit_zero_support_encard_consumer
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.encard = 2 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_trunc_choose_consumer,
    etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer]
  exact thetaCoeffAt_zero_support_encard K

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_one_via_trunc_choose
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff (1 : Int) = 1 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose,
    etaleThetaSymmetricTrunc_coeff_zero_all]
  have hne : (1 : Int) ≠ -1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_neg_one_via_trunc_choose
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff (-1 : Int) = -1 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose,
    etaleThetaSymmetricTrunc_coeff_zero_all]
  have hne : (-1 : Int) ≠ 1 := by norm_num
  simp [thetaUExponent, HahnSeries.coeff_add, HahnSeries.coeff_single, hne]

theorem etaleThetaSymmetricCoeffLimit_zero_value_via_trunc_choose
    (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      HahnSeries.single (thetaUExponent 0) (1 : K) +
        HahnSeries.single (thetaUExponent (-1)) (-1 : K) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose,
    etaleThetaSymmetricTrunc_coeff_zero_all]

theorem etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt_via_trunc_choose
    (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) = thetaCoeffAt K 0 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_trunc_choose,
    etaleThetaSymmetricTrunc_choose_zero_eq_thetaCoeffAt_consumer]

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_thetaUExponent
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support =
      ({thetaUExponent 0, thetaUExponent (-1)} : Set Int) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_trunc_choose_consumer,
    etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer,
    thetaCoeffAt_zero_support_eq]
  norm_num [thetaUExponent]

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_thetaUExponent_zero
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff
      (thetaUExponent 0) = 1 := by
  rw [show thetaUExponent 0 = (1 : Int) by unfold thetaUExponent; norm_num,
    etaleThetaSymmetricCoeffLimit_zero_coeff_one]

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_thetaUExponent_neg_one
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff
      (thetaUExponent (-1)) = -1 := by
  rw [show thetaUExponent (-1) = (-1 : Int) by unfold thetaUExponent; norm_num,
    etaleThetaSymmetricCoeffLimit_zero_coeff_neg_one]

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_eq_zero_of_ne_thetaUExponent
    (K : Type u) [Field K] (x : Int)
    (h1 : x ≠ thetaUExponent 0) (h2 : x ≠ thetaUExponent (-1)) :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff x = 0 := by
  apply etaleThetaSymmetricCoeffLimit_zero_coeff_eq_zero_of_ne K x
  · rwa [show thetaUExponent 0 = (1 : Int) by unfold thetaUExponent; norm_num] at h1
  · rwa [show thetaUExponent (-1) = (-1 : Int) by unfold thetaUExponent; norm_num] at h2

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_one_neg_one_via_trunc_choose
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support = ({1, -1} : Set Int) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_trunc_choose_consumer,
    etaleThetaSymmetricTrunc_choose_zero_support_eq_consumer,
    thetaCoeffAt_zero_support_eq]

theorem etaleThetaSymmetricCoeffLimit_zero_support_encard_via_trunc_choose
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.encard = 2 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_one_neg_one_via_trunc_choose]
  apply Set.encard_pair
  norm_num

theorem etaleThetaSymmetricCoeffLimit_zero_support_finite_via_trunc_choose
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Finite := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_one_neg_one_via_trunc_choose]
  exact (Set.finite_singleton (-1 : Int)).insert 1

theorem etaleThetaSymmetricCoeffLimit_zero_support_nonempty_via_trunc_choose
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support.Nonempty := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_one_neg_one_via_trunc_choose]
  exact ⟨(1 : Int), by simp⟩

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_thetaUExponent_zero_ne_zero
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff
      (thetaUExponent 0) ≠ 0 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_coeff_thetaUExponent_zero]
  norm_num

theorem etaleThetaSymmetricCoeffLimit_zero_coeff_thetaUExponent_neg_one_ne_zero
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).coeff
      (thetaUExponent (-1)) ≠ 0 := by
  rw [etaleThetaSymmetricCoeffLimit_zero_coeff_thetaUExponent_neg_one]
  norm_num

theorem etaleThetaSymmetricCoeffLimit_zero_support_mem_iff
    (K : Type u) [Field K] (x : Int) :
    x ∈ (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support ↔
      x = thetaUExponent 0 ∨ x = thetaUExponent (-1) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_thetaUExponent]
  simp [Set.mem_insert_iff, Set.mem_singleton_iff]

theorem etaleThetaSymmetricCoeffLimit_zero_support_eq_pair_support
    (K : Type u) [Field K] :
    (etaleThetaSymmetricCoeffLimit K (0 : HalfInt)).support =
      ((thetaPairTerm K 0).coeff (thetaQExponent 0)).support := by
  rw [etaleThetaSymmetricCoeffLimit_zero_support_eq_thetaCoeffAt_consumer]
  rfl

theorem etaleThetaSymmetricCoeffLimit_zero_eq_pair_via_trunc_choose
    (K : Type u) [Field K] :
    etaleThetaSymmetricCoeffLimit K (0 : HalfInt) =
      (thetaPairTerm K 0).coeff (thetaQExponent 0) := by
  rw [etaleThetaSymmetricCoeffLimit_zero_eq_thetaCoeffAt_via_trunc_choose]
  rfl

#check etaleThetaSymmetricCoeffLimit_eq_trunc
#check etaleThetaSymmetricCoeffLimit_trunc_eq

end LeanFormal.IUT.XiFPaper.EtaleThetaSymmetricTruncLimitConsumerActual

end