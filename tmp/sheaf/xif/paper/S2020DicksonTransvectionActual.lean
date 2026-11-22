import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.Index
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.GroupTheory.OrderOfElement
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Algebra.CharP.Lemmas
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual

noncomputable section
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

local instance charP_mat : CharP Mat 5 where
  cast_eq_zero_iff x := by
    constructor
    · intro h
      have h00 : (x : K5) = 0 := by
        simpa [Matrix.natCast_apply] using congrFun (congrFun h 0) 0
      exact (CharP.cast_eq_zero_iff K5 5 x).mp h00
    · intro h
      have hK : (x : K5) = 0 := (CharP.cast_eq_zero_iff K5 5 x).mpr h
      ext i j
      simp [Matrix.natCast_apply, hK]

lemma ordersix_three : Nat.factorization 6 3 = 1 := by
  have hmem : 3 ∈ (3 : ℕ).primeFactorsList := by
    rw [Nat.mem_primeFactorsList (by norm_num)]
    exact ⟨by norm_num, dvd_rfl⟩
  rw [show 6 = 2 * 3 by norm_num]
  rw [Nat.factorization_eq_of_coprime_right (by norm_num : Nat.Coprime 2 3) hmem]
  exact Nat.Prime.factorization_self (by norm_num)

lemma units_five_eq_one (u : K5ˣ) (h : u ^ 5 = 1) : u = 1 := by
  have hdvd5 : orderOf u ∣ 5 := by rw [orderOf_dvd_iff_pow_eq_one]; exact h
  have hdvd4 : orderOf u ∣ 4 := by
    have h4 : Nat.card K5ˣ = 4 := by rw [Nat.card_eq_fintype_card]; decide
    rw [← h4]
    exact orderOf_dvd_natCard u
  have hdvd1 : orderOf u ∣ 1 := by
    simpa using Nat.dvd_gcd hdvd5 hdvd4
  exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)

lemma det_eq_one_of_order_five (a : GL2) (ha : orderOf a = 5) :
    (a : Mat).det = 1 := by
  have ha5 : a ^ 5 = 1 := by simpa [ha] using pow_orderOf_eq_one a
  have hdet5 : Matrix.GeneralLinearGroup.det a ^ 5 = 1 := by
    rw [← map_pow, ha5, map_one]
  have hdet1 : Matrix.GeneralLinearGroup.det a = 1 := units_five_eq_one _ hdet5
  exact congrArg Units.val hdet1

theorem orderFiveUnipotent_proof : S2014OrderFiveUnipotent := by
  intro a ha
  let A : Mat := (a : Mat)
  have ha5 : a ^ 5 = 1 := by
    have h := pow_orderOf_eq_one a
    rwa [ha] at h
  have hA5 : A ^ 5 = 1 := by
    have h := congrArg (fun x : GL2 => (x : Mat)) ha5
    simpa [A] using h
  by_cases hA1 : A = 1
  · refine ⟨![1, 0], by decide, ?_⟩
    simp [Units.smul_def, hA1, A]
  · have hchar : (A - 1) ^ 5 = A ^ 5 - 1 := by
      simpa using (sub_pow_expChar_of_commute (R := Mat) (p := 5) (x := A) (y := (1 : Mat)) (Commute.one_right A))
    have hnil : (A - 1) ^ 5 = 0 := by
      rw [hchar, hA5, sub_self]
    have hdet : (A - 1).det = 0 := by
      by_contra hdet
      have hunit : IsUnit (A - 1) := (Matrix.isUnit_iff_isUnit_det (A - 1)).mpr (isUnit_iff_ne_zero.mpr hdet)
      have hpowunit : IsUnit ((A - 1) ^ 5) := hunit.pow 5
      rw [hnil] at hpowunit
      exact not_isUnit_zero hpowunit
    obtain ⟨v, hv, hAv⟩ := (Matrix.exists_mulVec_eq_zero_iff (M := A - 1)).mpr hdet
    refine ⟨v, hv, ?_⟩
    have hsub : A *ᵥ v - v = 0 := by
      simpa [Matrix.sub_mulVec, Matrix.one_mulVec] using hAv
    have hsmul : A *ᵥ v = v := sub_eq_zero.mp hsub
    rw [Units.smul_def]
    simpa [A] using hsmul

lemma fix_e1_form (A : GL2) (hfix : A • (![1, 0] : V2) = ![1, 0])
    (hdet : (A : Mat).det = 1) :
    (A : Mat) = !![1, (A : Mat) 0 1; 0, 1] := by
  have h0 := congrFun hfix 0
  have h1 := congrFun hfix 1
  have h00 : (A : Mat) 0 0 = 1 := by
    simpa [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h0
  have h10 : (A : Mat) 1 0 = 0 := by
    simpa [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h1
  have h11 : (A : Mat) 1 1 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    rw [h00, h10] at hdet
    linear_combination hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h10, h11]

lemma pow_form_fix_e1 (A : GL2) (hfix : A • (![1, 0] : V2) = ![1, 0])
    (hdet : (A : Mat).det = 1) (n : ℕ) :
    ((A ^ n : GL2) : Mat) = !![1, (n : K5) * ((A : Mat) 0 1); 0, 1] := by
  induction n with
  | zero =>
      rw [pow_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, Units.val_mul, ih, fix_e1_form A hfix hdet]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ] <;> ring

lemma trv1_mem_of_fixes_e1 (H : Subgroup GL2) (A : GL2) (hA : A ∈ H)
    (hfix : A • (![1, 0] : V2) = ![1, 0]) (hdet : (A : Mat).det = 1) (hne : A ≠ 1) :
    trv1 ∈ H := by
  let t : K5 := (A : Mat) 0 1
  have ht : t ≠ 0 := by
    intro ht0
    apply hne
    apply Units.ext
    rw [fix_e1_form A hfix hdet]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [t, ht0]
  let n : ℕ := (t⁻¹).val
  have hnt : (n : K5) * t = 1 := by
    dsimp [n]
    rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ ht]
  have hpow := pow_form_fix_e1 A hfix hdet n
  have hAeq : A ^ n = trv1 := by
    apply Units.ext
    rw [hpow, hnt]
    rfl
  have hmem : A ^ n ∈ H := pow_mem hA n
  rwa [hAeq] at hmem

lemma fix_e2_form (A : GL2) (hfix : A • (![0, 1] : V2) = ![0, 1])
    (hdet : (A : Mat).det = 1) :
    (A : Mat) = !![1, 0; (A : Mat) 1 0, 1] := by
  have h0 := congrFun hfix 0
  have h1 := congrFun hfix 1
  have h01 : (A : Mat) 0 1 = 0 := by
    simpa [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h0
  have h11 : (A : Mat) 1 1 = 1 := by
    simpa [Units.smul_def, Matrix.smul_eq_mulVec, Matrix.mulVec, dotProduct, Fin.sum_univ_two,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] using h1
  have h00 : (A : Mat) 0 0 = 1 := by
    rw [Matrix.det_fin_two] at hdet
    rw [h01, h11] at hdet
    linear_combination hdet
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h00, h01, h11]

lemma pow_form_fix_e2 (A : GL2) (hfix : A • (![0, 1] : V2) = ![0, 1])
    (hdet : (A : Mat).det = 1) (n : ℕ) :
    ((A ^ n : GL2) : Mat) = !![1, 0; (n : K5) * ((A : Mat) 1 0), 1] := by
  induction n with
  | zero =>
      rw [pow_zero]
      ext i j
      fin_cases i <;> fin_cases j <;> simp
  | succ n ih =>
      rw [pow_succ, Units.val_mul, ih, fix_e2_form A hfix hdet]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [Matrix.mul_apply, Fin.sum_univ_two, Nat.cast_succ] <;> ring

lemma trv2_mem_of_fixes_e2 (H : Subgroup GL2) (A : GL2) (hA : A ∈ H)
    (hfix : A • (![0, 1] : V2) = ![0, 1]) (hdet : (A : Mat).det = 1) (hne : A ≠ 1) :
    trv2 ∈ H := by
  let t : K5 := (A : Mat) 1 0
  have ht : t ≠ 0 := by
    intro ht0
    apply hne
    apply Units.ext
    rw [fix_e2_form A hfix hdet]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [t, ht0]
  let n : ℕ := (t⁻¹).val
  have hnt : (n : K5) * t = 1 := by
    dsimp [n]
    rw [ZMod.natCast_zmod_val, inv_mul_cancel₀ ht]
  have hpow := pow_form_fix_e2 A hfix hdet n
  have hAeq : A ^ n = trv2 := by
    apply Units.ext
    rw [hpow, hnt]
    rfl
  have hmem : A ^ n ∈ H := pow_mem hA n
  rwa [hAeq] at hmem

lemma line_image_eq_e1 (h : GL2) (v : V2) (hv : v ≠ 0)
    (hp : pairAct h ⟨normalize v, normalize_isRep v hv⟩ = ⟨![1, 0], by decide⟩) :
    h • v = ![1, 0] ∨ h • v = -![1, 0] := by
  have hp' : normalize (h • normalize v) = ![1, 0] := by
    have h := congrArg Subtype.val hp
    simpa [pairAct] using h
  have h1 : h • normalize v = ![1, 0] ∨ h • normalize v = -![1, 0] := by
    rcases normalize_eq_or_neg (h • normalize v) with hw | hw
    · left; rw [hw] at hp'; exact hp'
    · right
      have hneg : -(h • normalize v) = ![1, 0] := by rw [← hw]; exact hp'
      simpa using congrArg Neg.neg hneg
  rcases h1 with hw | hw <;> rcases normalize_eq_or_neg v with hv' | hv'
  · left; rw [hv'] at hw; exact hw
  · right
    rw [hv'] at hw
    have hneg : -(h • v) = ![1, 0] := by simpa using hw
    simpa using congrArg Neg.neg hneg
  · right; rw [hv'] at hw; exact hw
  · left
    rw [hv'] at hw
    have hneg : -(h • v) = -![1, 0] := by simpa using hw
    simpa using congrArg Neg.neg hneg

lemma line_image_eq_e2 (h : GL2) (v : V2) (hv : v ≠ 0)
    (hp : pairAct h ⟨normalize v, normalize_isRep v hv⟩ = ⟨![0, 1], by decide⟩) :
    h • v = ![0, 1] ∨ h • v = -![0, 1] := by
  have hp' : normalize (h • normalize v) = ![0, 1] := by
    have h := congrArg Subtype.val hp
    simpa [pairAct] using h
  have h1 : h • normalize v = ![0, 1] ∨ h • normalize v = -![0, 1] := by
    rcases normalize_eq_or_neg (h • normalize v) with hw | hw
    · left; rw [hw] at hp'; exact hp'
    · right
      have hneg : -(h • normalize v) = ![0, 1] := by rw [← hw]; exact hp'
      simpa using congrArg Neg.neg hneg
  rcases h1 with hw | hw <;> rcases normalize_eq_or_neg v with hv' | hv'
  · left; rw [hv'] at hw; exact hw
  · right
    rw [hv'] at hw
    have hneg : -(h • v) = ![0, 1] := by simpa using hw
    simpa using congrArg Neg.neg hneg
  · right; rw [hv'] at hw; exact hw
  · left
    rw [hv'] at hw
    have hneg : -(h • v) = -![0, 1] := by simpa using hw
    simpa using congrArg Neg.neg hneg



abbrev SL2 := Matrix.SpecialLinearGroup (Fin 2) K5
def sl1 : SL2 := Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (1 : K5)
def sl2 : SL2 := Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (1 : K5)

lemma toGL_sl1 : ((sl1 : SL2) : GL2) = trv1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl1, trv1, Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single]

lemma toGL_sl2 : ((sl2 : SL2) : GL2) = trv2 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sl2, trv2, Matrix.SpecialLinearGroup.transvection, Matrix.transvection, Matrix.single]

lemma transvection_zero_one_nat (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (n : K5) = sl1 ^ n := by
  induction n with
  | zero => simp [sl1]
  | succ n ih =>
      rw [Nat.cast_succ, Matrix.SpecialLinearGroup.transvection_add, ih, pow_succ]
      rfl

lemma transvection_one_zero_nat (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (n : K5) = sl2 ^ n := by
  induction n with
  | zero => simp [sl2]
  | succ n ih =>
      rw [Nat.cast_succ, Matrix.SpecialLinearGroup.transvection_add, ih, pow_succ]
      rfl

lemma transvection_mem_closure_zero_one (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (0 : Fin 2) ≠ 1) (n : K5) ∈
      Subgroup.closure ({sl1, sl2} : Set SL2) := by
  rw [transvection_zero_one_nat]
  exact pow_mem (Subgroup.subset_closure (by simp [sl1])) n

lemma transvection_mem_closure_one_zero (n : ℕ) :
    Matrix.SpecialLinearGroup.transvection (by decide : (1 : Fin 2) ≠ 0) (n : K5) ∈
      Subgroup.closure ({sl1, sl2} : Set SL2) := by
  rw [transvection_one_zero_nat]
  exact pow_mem (Subgroup.subset_closure (by simp [sl2])) n

lemma transvection_mem_closure (i j : Fin 2) (hij : i ≠ j) (c : K5) :
    Matrix.SpecialLinearGroup.transvection hij c ∈ Subgroup.closure ({sl1, sl2} : Set SL2) := by
  fin_cases i
  · fin_cases j
    · exact (hij rfl).elim
    · have hh : hij = (by decide : (0 : Fin 2) ≠ 1) := Subsingleton.elim _ _
      rw [hh, ← ZMod.natCast_zmod_val c]
      exact transvection_mem_closure_zero_one c.val
  · fin_cases j
    · have hh : hij = (by decide : (1 : Fin 2) ≠ 0) := Subsingleton.elim _ _
      rw [hh, ← ZMod.natCast_zmod_val c]
      exact transvection_mem_closure_one_zero c.val
    · exact (hij rfl).elim

lemma closure_sl_eq_top : Subgroup.closure ({sl1, sl2} : Set SL2) = ⊤ := by
  rw [eq_top_iff]
  intro A hA
  exact Matrix.SL2.transvection_induction
    (P := fun A => A ∈ Subgroup.closure ({sl1, sl2} : Set SL2))
    (fun i j hij c => transvection_mem_closure i j hij c)
    (fun A B hA hB => mul_mem hA hB) A

def slEquivKer : SL2 ≃ (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by
    rw [MonoidHom.mem_ker]
    exact Matrix.SpecialLinearGroup.coeToGL_det A⟩
  invFun u := ⟨(u.1 : Mat), by
    have h := congrArg Units.val u.2
    simpa using h⟩
  left_inv A := by
    apply Matrix.SpecialLinearGroup.ext
    intro i j
    rfl
  right_inv u := by
    apply Subtype.ext
    apply Units.ext
    rfl

lemma card_sl2 : Nat.card SL2 = 120 := by
  have hcard : Nat.card SL2 = Nat.card (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker :=
    Nat.card_congr slEquivKer
  rw [hcard]
  have hsurj : Function.Surjective (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)) :=
    Matrix.GeneralLinearGroup.det_surjective
  have hidx : (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker.index = 4 := by
    rw [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
      Nat.card_eq_fintype_card]
    decide
  have hmul := Subgroup.index_mul_card (H := (Matrix.GeneralLinearGroup.det (n := Fin 2) (R := K5)).ker)
  rw [hidx, natCard_GL2] at hmul
  omega

def slEquivMap : SL2 ≃ (⊤ : Subgroup SL2).map Matrix.SpecialLinearGroup.toGL where
  toFun A := ⟨Matrix.SpecialLinearGroup.toGL A, by
    exact Subgroup.mem_map.mpr ⟨A, Subgroup.mem_top A, rfl⟩⟩
  invFun x := Classical.choose x.2
  left_inv A := by
    apply Matrix.SpecialLinearGroup.toGL_injective
    exact (Classical.choose_spec (Subgroup.mem_map.mpr ⟨A, Subgroup.mem_top A, rfl⟩)).2
  right_inv x := by
    apply Subtype.ext
    exact (Classical.choose_spec x.2).2

lemma card_map_top : Nat.card ((⊤ : Subgroup SL2).map Matrix.SpecialLinearGroup.toGL) = 120 := by
  rw [← Nat.card_congr slEquivMap, card_sl2]

lemma closure_trv_eq_map : Subgroup.closure ({trv1, trv2} : Set GL2) =
    (Subgroup.closure ({sl1, sl2} : Set SL2)).map Matrix.SpecialLinearGroup.toGL := by
  have hset : ({trv1, trv2} : Set GL2) =
      Matrix.SpecialLinearGroup.toGL '' ({sl1, sl2} : Set SL2) := by
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_image]
    constructor
    · rintro (rfl | rfl)
      · exact ⟨sl1, Or.inl rfl, toGL_sl1⟩
      · exact ⟨sl2, Or.inr rfl, toGL_sl2⟩
    · rintro ⟨y, (rfl | rfl), hy⟩
      · left
        rw [← hy, toGL_sl1]
      · right
        rw [← hy, toGL_sl2]
  rw [hset, ← MonoidHom.map_closure]

lemma card_closure_trv : Nat.card (Subgroup.closure ({trv1, trv2} : Set GL2)) = 120 := by
  rw [closure_trv_eq_map, closure_sl_eq_top, card_map_top]


end LeanFormal.IUT.XiFPaper.S2009DicksonActual
