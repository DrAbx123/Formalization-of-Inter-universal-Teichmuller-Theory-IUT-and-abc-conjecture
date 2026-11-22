import Mathlib.Tactic
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Basic
import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Card
import Mathlib.LinearAlgebra.Matrix.Nondegenerate
import Mathlib.GroupTheory.OrderOfElement
import tmp.sheaf.xif.paper.S2014DicksonClassificationActual

noncomputable section
set_option maxHeartbeats 4000000
open Matrix
namespace LeanFormal.IUT.XiFPaper.S2009DicksonActual

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

end LeanFormal.IUT.XiFPaper.S2009DicksonActual