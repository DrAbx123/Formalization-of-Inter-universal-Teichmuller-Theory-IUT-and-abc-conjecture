import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
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


lemma orderOf_conj_eq (g : GL2) (x : GL2) : orderOf (x * g * x⁻¹) = orderOf g := by
  have hsem : SemiconjBy x g (x * g * x⁻¹) := by
    show x * g = (x * g * x⁻¹) * x
    group
  exact (SemiconjBy.orderOf_eq x hsem).symm

lemma sl_le_of_five_dvd (H : Subgroup GL2) (htrans : PairTransitive H)
    (h5 : 5 ∣ Nat.card H) :
    Subgroup.closure ({trv1, trv2} : Set GL2) ≤ H := by
  letI : Fintype H := Fintype.ofFinite H
  have h5' : 5 ∣ Fintype.card H := by simpa [Nat.card_eq_fintype_card] using h5
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card 5 h5'
  have haGL : orderOf (a : GL2) = 5 := by simpa using ha
  have hdet_a : ((a : GL2) : Mat).det = 1 := det_eq_one_of_order_five (a : GL2) haGL
  obtain ⟨v, hv, hav⟩ := orderFiveUnipotent_proof (a : GL2) haGL
  let vp : PairRep := ⟨normalize v, normalize_isRep v hv⟩
  let e1p : PairRep := ⟨![1, 0], by decide⟩
  obtain ⟨h1, hh1, hp1⟩ := htrans vp e1p
  have hline1 : h1 • v = ![1, 0] ∨ h1 • v = -![1, 0] := line_image_eq_e1 h1 v hv hp1
  let b1 : GL2 := h1 * (a : GL2) * h1⁻¹
  have hb1H : b1 ∈ H := by
    dsimp [b1]
    exact H.mul_mem (H.mul_mem hh1 a.2) (H.inv_mem hh1)
  have hb1fixv : b1 • (h1 • v) = h1 • v := by
    dsimp [b1]
    rw [mul_smul, mul_smul, inv_smul_smul, hav]
  have hb1fix : b1 • (![1, 0] : V2) = ![1, 0] := by
    rcases hline1 with hl | hl
    · rw [← hl]; exact hb1fixv
    · have hneg : b1 • (-( ![1, 0] : V2)) = -( ![1, 0] : V2) := by rw [← hl]; exact hb1fixv
      have hlin : b1 • (-( ![1, 0] : V2)) = -(b1 • (![1, 0] : V2)) := by rw [smul_neg]
      rw [hlin] at hneg
      exact neg_injective hneg
  have hb1det : (b1 : Mat).det = 1 := by
    have hda : Matrix.GeneralLinearGroup.det (a : GL2) = 1 := Units.ext hdet_a
    have hd : Matrix.GeneralLinearGroup.det b1 = 1 := by
      dsimp [b1]
      rw [map_mul, map_mul, map_inv, hda]
      simp
    exact congrArg Units.val hd
  have hb1ord : orderOf b1 = 5 := by
    dsimp [b1]
    rw [orderOf_conj_eq (a : GL2) h1]
    exact haGL
  have hb1ne : b1 ≠ 1 := by
    intro hb
    have h1ord : orderOf b1 = 1 := by rw [hb, orderOf_one]
    rw [hb1ord] at h1ord
    norm_num at h1ord
  have htrv1 : trv1 ∈ H :=
    trv1_mem_of_fixes_e1 H b1 hb1H hb1fix hb1det hb1ne
  let e2p : PairRep := ⟨![0, 1], by decide⟩
  obtain ⟨h2, hh2, hp2⟩ := htrans vp e2p
  have hline2 : h2 • v = ![0, 1] ∨ h2 • v = -![0, 1] := line_image_eq_e2 h2 v hv hp2
  let b2 : GL2 := h2 * (a : GL2) * h2⁻¹
  have hb2H : b2 ∈ H := by
    dsimp [b2]
    exact H.mul_mem (H.mul_mem hh2 a.2) (H.inv_mem hh2)
  have hb2fixv : b2 • (h2 • v) = h2 • v := by
    dsimp [b2]
    rw [mul_smul, mul_smul, inv_smul_smul, hav]
  have hb2fix : b2 • (![0, 1] : V2) = ![0, 1] := by
    rcases hline2 with hl | hl
    · rw [← hl]; exact hb2fixv
    · have hneg : b2 • (-( ![0, 1] : V2)) = -( ![0, 1] : V2) := by rw [← hl]; exact hb2fixv
      have hlin : b2 • (-( ![0, 1] : V2)) = -(b2 • (![0, 1] : V2)) := by rw [smul_neg]
      rw [hlin] at hneg
      exact neg_injective hneg
  have hb2det : (b2 : Mat).det = 1 := by
    have hda : Matrix.GeneralLinearGroup.det (a : GL2) = 1 := Units.ext hdet_a
    have hd : Matrix.GeneralLinearGroup.det b2 = 1 := by
      dsimp [b2]
      rw [map_mul, map_mul, map_inv, hda]
      simp
    exact congrArg Units.val hd
  have hb2ord : orderOf b2 = 5 := by
    dsimp [b2]
    rw [orderOf_conj_eq (a : GL2) h2]
    exact haGL
  have hb2ne : b2 ≠ 1 := by
    intro hb
    have h2ord : orderOf b2 = 1 := by rw [hb, orderOf_one]
    rw [hb2ord] at h2ord
    norm_num at h2ord
  have htrv2 : trv2 ∈ H :=
    trv2_mem_of_fixes_e2 H b2 hb2H hb2fix hb2det hb2ne
  rw [Subgroup.closure_le]
  intro y hy
  rcases hy with rfl | rfl
  · exact htrv1
  · exact htrv2

end LeanFormal.IUT.XiFPaper.S2009DicksonActual