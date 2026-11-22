import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.GroupTheory.Sylow
import Mathlib.GroupTheory.IndexNormal
import Mathlib.GroupTheory.GroupAction.ConjAct
import Mathlib.Data.Nat.Prime.Basic
import tmp.sheaf.xif.paper.S2020DicksonActionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

/-! ## Preparation: the twelve-point action and the order count -/

instance : MulAction GL2 PairRep where
  smul := pairAct
  one_smul := pairAct_one
  mul_smul := pairAct_mul

lemma orbit_card_eq_twelve (H : Subgroup GL2) (htrans : PairTransitive H) (x : PairRep) :
    Nat.card (MulAction.orbit H x) = 12 := by
  have horbit : MulAction.orbit H x = Set.univ := by
    ext y
    exact ⟨fun _ => Set.mem_univ y, fun _ => by
      rw [MulAction.mem_orbit_iff]
      obtain ⟨h, hh, hhx⟩ := htrans x y
      exact ⟨⟨h, hh⟩, hhx⟩⟩
  let e : MulAction.orbit H x ≃ PairRep :=
    { toFun := fun y => y.1
      invFun := fun y => ⟨y, by rw [horbit]; exact Set.mem_univ y⟩
      left_inv := fun y => by apply Subtype.ext; rfl
      right_inv := fun y => rfl }
  rw [Nat.card_congr e, natCard_pairRep]

lemma card_stabilizer_eq_div (H : Subgroup GL2) (htrans : PairTransitive H) (x : PairRep)
    (h12 : 12 ∣ Nat.card H) :
    Nat.card (MulAction.stabilizer H x) = Nat.card H / 12 := by
  letI : Fintype H := Fintype.ofFinite H
  letI : Fintype (MulAction.orbit H x) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer H x) := Fintype.ofFinite _
  have horbit := orbit_card_eq_twelve H htrans x
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := H) (b := x)
  have hOS' : Nat.card (MulAction.orbit H x) * Nat.card (MulAction.stabilizer H x) = Nat.card H := by
    simpa only [← Nat.card_eq_fintype_card] using hOS
  rw [horbit] at hOS'
  rcases h12 with ⟨k, hk⟩
  have hmul : 12 * Nat.card (MulAction.stabilizer H x) = 12 * k := by
    rw [hOS', hk]
  have hs : Nat.card (MulAction.stabilizer H x) = k :=
    Nat.mul_left_cancel (by norm_num) hmul
  rw [hs, hk, Nat.mul_div_cancel_left k (by norm_num)]

lemma twelve_dvd_card (H : Subgroup GL2) (htrans : PairTransitive H) :
    12 ∣ Nat.card H := by
  letI : Fintype H := Fintype.ofFinite H
  let x : PairRep := ⟨![1, 0], by decide⟩
  letI : Fintype (MulAction.orbit H x) := Fintype.ofFinite _
  letI : Fintype (MulAction.stabilizer H x) := Fintype.ofFinite _
  have horbit := orbit_card_eq_twelve H htrans x
  have hOS := MulAction.card_orbit_mul_card_stabilizer_eq_card_group (G := H) (b := x)
  have hOS' : Nat.card (MulAction.orbit H x) * Nat.card (MulAction.stabilizer H x) = Nat.card H := by
    simpa only [← Nat.card_eq_fintype_card] using hOS
  rw [horbit] at hOS'
  exact ⟨Nat.card (MulAction.stabilizer H x), hOS'.symm⟩

lemma mat_sub_one_mul_add_one (M : Mat) (hM : M * M = 1) : (M - 1) * (M + 1) = 0 := by
  calc (M - 1) * (M + 1) = (M - 1) * M + (M - 1) * 1 := by rw [mul_add]
    _ = (M * M - 1 * M) + (M - 1) := by rw [sub_mul, mul_one]
    _ = (1 - M) + (M - 1) := by rw [hM, one_mul]
    _ = 0 := by abel

lemma involution_fixes_pair (A : GL2) (hA : A ^ 2 = 1) :
    ∃ x : PairRep, pairAct A x = x := by
  by_cases hA1 : A = 1
  · refine ⟨⟨![1, 0], by decide⟩, ?_⟩
    rw [hA1]
    exact pairAct_one _
  · have hM : (A : Mat) * (A : Mat) = 1 := by
      have h := congrArg (fun y : GL2 => (y : Mat)) hA
      simpa [pow_two] using h
    have hprod : ((A : Mat) - 1) * ((A : Mat) + 1) = 0 := mat_sub_one_mul_add_one (A : Mat) hM
    have hdet : ((A : Mat) - 1).det * ((A : Mat) + 1).det = 0 := by
      rw [← Matrix.det_mul, hprod, Matrix.det_zero]
    rcases mul_eq_zero.mp hdet with hd | hd
    · obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := (A : Mat) - 1)).mpr hd
      have hfix : (A : Mat) *ᵥ v = v := by
        have hsub : (A : Mat) *ᵥ v - v = 0 := by
          simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hAv
        exact sub_eq_zero.mp hsub
      refine ⟨⟨normalize v, normalize_isRep v hv⟩, ?_⟩
      apply Subtype.ext
      show normalize (A • normalize v) = normalize v
      rcases normalize_eq_or_neg v with hv' | hv'
      · rw [hv']
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hfix]
        exact hv'
      · rw [hv']
        have hneg : (A : Mat) *ᵥ (-v) = -v := by
          rw [mulVec_neg, hfix]
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hneg, normalize_neg]
        exact hv'
    · obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := (A : Mat) + 1)).mpr hd
      have hfix : (A : Mat) *ᵥ v = -v := by
        have hsum : (A : Mat) *ᵥ v + v = 0 := by
          simpa [Matrix.add_mulVec, Matrix.one_mulVec] using hAv
        exact eq_neg_of_add_eq_zero_left hsum
      refine ⟨⟨normalize v, normalize_isRep v hv⟩, ?_⟩
      apply Subtype.ext
      show normalize (A • normalize v) = normalize v
      rcases normalize_eq_or_neg v with hv' | hv'
      · rw [hv']
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hfix, normalize_neg, hv']
      · rw [hv']
        have hneg : (A : Mat) *ᵥ (-v) = v := by
          rw [mulVec_neg, hfix, neg_neg]
        rw [Units.smul_def, Matrix.smul_eq_mulVec, hneg, hv']

lemma not_card_12_or_60 (H : Subgroup GL2) (htrans : PairTransitive H)
    (hcard : Nat.card H = 12 ∨ Nat.card H = 60) : False := by
  letI : Fintype H := Fintype.ofFinite H
  have h12 : 12 ∣ Nat.card H := by rcases hcard with h | h <;> rw [h] <;> norm_num
  have hstabval : ∀ x : PairRep, Nat.card (MulAction.stabilizer H x) = 1 ∨
      Nat.card (MulAction.stabilizer H x) = 5 := by
    intro x
    have hx := card_stabilizer_eq_div H htrans x h12
    rcases hcard with h | h
    · left; rw [hx, h]
    · right; rw [hx, h]
  have h2 : 2 ∣ Nat.card H := by rcases hcard with h | h <;> rw [h] <;> norm_num
  have h2f : 2 ∣ Fintype.card H := by simpa [Nat.card_eq_fintype_card] using h2
  obtain ⟨h, hh⟩ := exists_prime_orderOf_dvd_card 2 h2f
  have hh2 : (h : GL2) ^ 2 = 1 := by
    have hpow := pow_orderOf_eq_one h
    rw [hh] at hpow
    exact congrArg (fun y : H => (y : GL2)) hpow
  obtain ⟨x, hx⟩ := involution_fixes_pair (h : GL2) hh2
  have hle : Subgroup.zpowers h ≤ MulAction.stabilizer H x := by
    rw [Subgroup.zpowers_le]
    rw [MulAction.mem_stabilizer_iff]
    exact hx
  have hdvd : 2 ∣ Nat.card (MulAction.stabilizer H x) := by
    have h2' : Nat.card (Subgroup.zpowers h) ∣ Nat.card (MulAction.stabilizer H x) :=
      Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hh] at h2'
  rcases hstabval x with hs | hs
  · rw [hs] at hdvd; norm_num at hdvd
  · rw [hs] at hdvd; norm_num at hdvd

lemma order_cases (n : ℕ) (h12 : 12 ∣ n) (hdvd : n ∣ 480)
    (hne12 : n ≠ 12) (hne60 : n ≠ 60) :
    n = 24 ∨ n = 48 ∨ n = 96 ∨ n = 120 ∨ n = 240 ∨ n = 480 := by
  rcases h12 with ⟨m, hm⟩
  have hm_dvd : m ∣ 40 := by
    have h : 12 * m ∣ 12 * 40 := by
      simpa [show 12 * 40 = 480 by norm_num] using (hm ▸ hdvd)
    exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 12)).mp h
  have hm_cases : m = 1 ∨ m = 2 ∨ m = 4 ∨ m = 5 ∨ m = 8 ∨ m = 10 ∨ m = 20 ∨ m = 40 := by
    have hm_le : m ≤ 40 := Nat.le_of_dvd (by norm_num) hm_dvd
    interval_cases m <;> norm_num at hm_dvd <;> omega
  rcases hm_cases with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exfalso; exact hne12 (by rw [hm])
  · left; rw [hm]
  · right; left; rw [hm]
  · exfalso; exact hne60 (by rw [hm])
  · right; right; left; rw [hm]
  · right; right; right; left; rw [hm]
  · right; right; right; right; left; rw [hm]
  · right; right; right; right; right; rw [hm]

lemma card_dvd_480 (H : Subgroup GL2) : Nat.card H ∣ 480 := by
  have h := Subgroup.card_subgroup_dvd_card H
  rw [natCard_GL2] at h
  exact h

/-! ## The order-24 case: a normal subgroup of order three -/

lemma le_normalizer_map_of_normal {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Normal] : H ≤ Subgroup.normalizer (K.map H.subtype : Set G) := by
  intro h hh
  rw [Subgroup.mem_set_normalizer_iff]
  intro y
  constructor
  · intro hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    have hk' : (⟨h, hh⟩ : H) * k * (⟨h, hh⟩ : H)⁻¹ ∈ K :=
      Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk ⟨h, hh⟩
    exact Subgroup.mem_map.mpr ⟨_, hk', by simp [mul_assoc]⟩
  · intro hy
    obtain ⟨k, hk, hk_eq⟩ := Subgroup.mem_map.mp hy
    have hk' : (⟨h, hh⟩ : H)⁻¹ * k * (⟨h, hh⟩ : H) ∈ K := by
      simpa using Subgroup.Normal.conj_mem (inferInstance : K.Normal) k hk (⟨h, hh⟩ : H)⁻¹
    refine Subgroup.mem_map.mpr ⟨_, hk', ?_⟩
    change H.subtype ((⟨h, hh⟩ : H)⁻¹ * k * (⟨h, hh⟩ : H)) = y
    rw [show H.subtype ((⟨h, hh⟩ : H)⁻¹ * k * (⟨h, hh⟩ : H))
        = h⁻¹ * ((k : H) : G) * h by simp [mul_assoc]]
    rw [show ((k : H) : G) = H.subtype k from rfl]
    rw [hk_eq]
    group

lemma factorization_six_three : Nat.factorization 6 3 = 1 := by
  have hmem : 3 ∈ (3 : ℕ).primeFactorsList := by
    rw [Nat.mem_primeFactorsList (by norm_num)]
    exact ⟨by norm_num, dvd_rfl⟩
  rw [show 6 = 2 * 3 by norm_num]
  rw [Nat.factorization_eq_of_coprime_right (by norm_num : Nat.Coprime 2 3) hmem]
  exact Nat.Prime.factorization_self (by norm_num)

lemma exists_normal_three_of_card24 (H : Subgroup GL2) (hcard : Nat.card H = 24)
    (hdet : DetSurjectiveOn H) :
    ∃ P : Subgroup GL2, Nat.card P = 3 ∧
      H ≤ Subgroup.normalizer (P : Set GL2) := by
  letI : Fintype H := Fintype.ofFinite H
  let f : H →* K5ˣ := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).comp H.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨h, hh, hhd⟩ := hdet a
    exact ⟨⟨h, hh⟩, hhd⟩
  let K : Subgroup H := f.ker
  have hidx : K.index = 4 := by
    dsimp [K]
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have hKcard : Nat.card K = 6 := by
    have hmul := Subgroup.index_mul_card (H := K)
    rw [hidx, hcard] at hmul
    omega
  letI : Fintype K := Fintype.ofFinite K
  let P : Sylow 3 K := default
  have hPcard : Nat.card P = 3 := by
    rw [Sylow.card_eq_multiplicity, hKcard, factorization_six_three]
    norm_num
  haveI : Finite (Sylow 3 K) := Sylow.finite_of_finiteIndex P
  have hPchar : P.Characteristic := by
    have hnorm : P.Normal := by
      have hidx2 : P.index = 2 := by
        have hmul := Subgroup.index_mul_card (H := (P : Subgroup K))
        rw [hPcard, hKcard] at hmul
        omega
      exact Subgroup.normal_of_index_eq_two hidx2
    exact Sylow.characteristic_of_normal P hnorm
  let PH : Subgroup H := P.map K.subtype
  have hPHnormal : PH.Normal := inferInstance
  have hPHcard : Nat.card PH = 3 := by
    dsimp [PH]
    rw [Subgroup.card_map_of_injective K.subtype_injective, hPcard]
  refine ⟨PH.map H.subtype, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective H.subtype_injective, hPHcard]
  · exact le_normalizer_map_of_normal H PH

lemma normalizer_card_of_subgroup_three (P : Subgroup GL2) (hP : Nat.card P = 3) :
    Nat.card (Subgroup.normalizer (P : Set GL2)) = 48 := by
  letI : Fintype P := Fintype.ofFinite P
  have hdvd : 3 ∣ Nat.card P := by rw [hP]
  have hdvd' : 3 ∣ Fintype.card P := by simpa [Nat.card_eq_fintype_card] using hdvd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card 3 hdvd'
  have hzle : Subgroup.zpowers ((g : P) : GL2) ≤ P := by
    rw [Subgroup.zpowers_le]
    exact g.2
  have hzcard : Nat.card (Subgroup.zpowers ((g : P) : GL2)) = 3 := by
    rw [Nat.card_zpowers]
    simpa using hg
  have hzmem : (Subgroup.zpowers ((g : P) : GL2) : Subgroup GL2) = P := by
    apply Subgroup.eq_of_le_of_card_ge hzle
    rw [hP, hzcard]
  rw [← hzmem]
  exact normalizerCard_proof (g : GL2) (by simpa using hg)

/-! ## The 120/240 exclusion via transvections -/

lemma five_dvd_contradiction (H : Subgroup GL2) (hdet : DetSurjectiveOn H)
    (htrans : PairTransitive H) (h5 : 5 ∣ Nat.card H)
    (hcard : Nat.card H = 120 ∨ Nat.card H = 240) : False := by
  letI : Fintype H := Fintype.ofFinite H
  let f : H →* K5ˣ := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).comp H.subtype
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨h, hh, hhd⟩ := hdet a
    exact ⟨⟨h, hh⟩, hhd⟩
  have hidx : f.ker.index = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hf, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have hmul := Subgroup.index_mul_card (G := H) (H := f.ker)
  rw [hidx] at hmul
  have hSL := sl_le_of_five_dvd H htrans h5
  have htrv1H : trv1 ∈ H := hSL (Subgroup.subset_closure (by simp))
  have htrv2H : trv2 ∈ H := hSL (Subgroup.subset_closure (by simp))
  have hSLker : Subgroup.closure ({trv1, trv2} : Set GL2) ≤ f.ker.map H.subtype := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | rfl
    · refine Subgroup.mem_map.mpr ⟨⟨trv1, htrv1H⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      exact trv1_det
    · refine Subgroup.mem_map.mpr ⟨⟨trv2, htrv2H⟩, ?_, rfl⟩
      rw [MonoidHom.mem_ker]
      exact trv2_det
  have h120 : 120 ∣ Nat.card f.ker := by
    have h := Subgroup.card_dvd_of_le hSLker
    rw [card_closure_trv, Subgroup.card_map_of_injective H.subtype_injective] at h
    exact h
  obtain ⟨k, hk⟩ := h120
  have h480 : 480 ∣ Nat.card H := by
    refine ⟨k, ?_⟩
    rw [← hmul, hk]
    ring
  rcases hcard with h | h <;> rw [h] at h480 <;> norm_num at h480

/-! ## Closing the classification -/

theorem dicksonTransitiveClassification_proof : S2009DicksonTransitiveClassification := by
  intro H hdet htrans hne
  have h12 : 12 ∣ Nat.card H := twelve_dvd_card H htrans
  have hdvd : Nat.card H ∣ 480 := card_dvd_480 H
  have hne12 : Nat.card H ≠ 12 := fun h =>
    not_card_12_or_60 H htrans (Or.inl h)
  have hne60 : Nat.card H ≠ 60 := fun h =>
    not_card_12_or_60 H htrans (Or.inr h)
  rcases order_cases (Nat.card H) h12 hdvd hne12 hne60 with h24 | h48 | h96 | h120 | h240 | h480
  · rcases exists_normal_three_of_card24 H h24 hdet with ⟨P, hP3, hHN⟩
    right
    exact ⟨Subgroup.normalizer (P : Set GL2), hHN,
      normalizer_card_of_subgroup_three P hP3⟩
  · right
    exact ⟨H, le_refl H, h48⟩
  · left
    exact ⟨H, le_refl H, h96⟩
  · exfalso
    exact five_dvd_contradiction H hdet htrans (by rw [h120]; norm_num) (Or.inl h120)
  · exfalso
    exact five_dvd_contradiction H hdet htrans (by rw [h240]; norm_num) (Or.inr h240)
  · exfalso
    apply hne
    apply Subgroup.eq_top_of_card_eq
    rw [h480, natCard_GL2]

end LeanFormal.IUT.XiFPaper.S2009DicksonActual
