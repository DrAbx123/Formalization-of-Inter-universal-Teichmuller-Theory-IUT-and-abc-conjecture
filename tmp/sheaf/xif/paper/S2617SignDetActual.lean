import tmp.sheaf.xif.paper.S2009DicksonActual
import Mathlib.LinearAlgebra.Matrix.Transvection

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 200000

namespace LeanFormal.IUT.XiFPaper.S2617SignDetActual

open LeanFormal.IUT.XiFPaper.S2009DicksonActual

abbrev K := K5
abbrev N := Fin 2
local instance : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Quadratic character of F5. -/
def chi (a : K) : ℤ := if a = 0 then 0 else if a = 1 ∨ a = 4 then 1 else -1

lemma chi_mul (a b : K) : chi (a * b) = chi a * chi b := by
  fin_cases a <;> fin_cases b <;> decide

/-- The GL2 element attached to a matrix, with a fixed choice on singular matrices. -/
noncomputable def glOf (A : Matrix N N K) : GL2 :=
  if h : A.det ≠ 0 then Matrix.GeneralLinearGroup.mkOfDetNeZero A h else 1

lemma glOf_of_det_ne_zero {A : Matrix N N K} (h : A.det ≠ 0) :
    glOf A = Matrix.GeneralLinearGroup.mkOfDetNeZero A h := by
  unfold glOf
  rw [dif_pos h]

/-- The sign/quadratic-character defect. -/
def S2617f (A : Matrix N N K) : ℤ :=
  ((Equiv.Perm.sign (pairPermHom (glOf A)) : ℤˣ) : ℤ) * chi A.det

lemma S2617f_mul {A B : Matrix N N K} (hA : A.det ≠ 0) (hB : B.det ≠ 0)
    (hAB : (A * B).det ≠ 0) :
    S2617f (A * B) = S2617f A * S2617f B := by
  have hmk : Matrix.GeneralLinearGroup.mkOfDetNeZero (A * B) hAB =
      Matrix.GeneralLinearGroup.mkOfDetNeZero A hA *
        Matrix.GeneralLinearGroup.mkOfDetNeZero B hB := by
    ext i j
    simp [Matrix.mul_apply]
  have hgl : glOf (A * B) = glOf A * glOf B := by
    rw [glOf_of_det_ne_zero hAB, glOf_of_det_ne_zero hA, glOf_of_det_ne_zero hB, hmk]
  have hsign : Equiv.Perm.sign (pairPermHom (glOf (A * B))) =
      Equiv.Perm.sign (pairPermHom (glOf A)) * Equiv.Perm.sign (pairPermHom (glOf B)) := by
    rw [hgl, map_mul, map_mul]
  have hchi : chi (A * B).det = chi A.det * chi B.det := by
    rw [Matrix.det_mul]
    exact chi_mul A.det B.det
  unfold S2617f
  rw [hsign, hchi]
  push_cast
  ring

theorem S2617f_eq_one (A : Matrix N N K) (h : A.det ≠ 0) : S2617f A = 1 := by
  refine (Matrix.diagonal_transvection_induction_of_det_ne_zero
    (P := fun M => M.det ≠ 0 → S2617f M = 1) A h ?_ ?_ ?_) h
  · intro D hD
    revert D hD
    decide
  · intro t h
    rcases t with ⟨i, j, hij, c⟩
    fin_cases i <;> fin_cases j <;> fin_cases c
    all_goals (revert hij h; decide)
  · intro A B hA hB PA PB hAB
    rw [S2617f_mul hA hB hAB, PA hA, PB hB, one_mul]


lemma S2617_glOf_coe (h : GL2) :
    glOf (h : Matrix N N K) = h := by
  have hdet : (h : Matrix N N K).det ≠ 0 := by
    simpa using Units.ne_zero h.det
  rw [glOf_of_det_ne_zero hdet]
  ext i j
  simp

lemma chi_eq_neg_one {a : K} (ha : a ≠ 0) (h : chi a = -1) :
    a = 2 ∨ a = 3 := by
  fin_cases a <;> simp [chi] at h ⊢ <;> tauto

theorem S2617_det_cycle12 (h : GL2)
    (hc : (pairPermHom h).cycleType = ({12} : Multiset ℕ)) :
    (Matrix.GeneralLinearGroup.det h : K) = 2 ∨
      (Matrix.GeneralLinearGroup.det h : K) = 3 := by
  have hs : ((Equiv.Perm.sign (pairPermHom h) : ℤˣ) : ℤ) = -1 := by
    rw [Equiv.Perm.sign_of_cycleType, hc]
    simp
  have hf : S2617f (h : Matrix N N K) = 1 := by
    apply S2617f_eq_one
    simpa using Units.ne_zero h.det
  have hchi : chi ((h : Matrix N N K).det) = -1 := by
    have hsign : ((Equiv.Perm.sign (pairPermHom (glOf (h : Matrix N N K))) : ℤˣ) : ℤ) = -1 := by
      rw [S2617_glOf_coe]
      exact hs
    unfold S2617f at hf
    rw [hsign] at hf
    linarith
  have hchi' : chi ((Matrix.GeneralLinearGroup.det h : K)) = -1 := by
    simpa using hchi
  have ha : ((Matrix.GeneralLinearGroup.det h : K)) ≠ 0 := by
    simpa using Units.ne_zero h.det
  exact chi_eq_neg_one ha hchi'


theorem S2617DetSurjective_of_twelveCycle (H : Subgroup GL2) (h : GL2)
    (hh : h ∈ H)
    (hc : (pairPermHom h).cycleType = ({12} : Multiset ℕ)) :
    DetSurjectiveOn H := by
  intro a
  have hd := S2617_det_cycle12 h hc
  fin_cases a
  · exact ⟨1, H.one_mem, by decide⟩
  · rcases hd with hd | hd
    · have hdu : Matrix.GeneralLinearGroup.det h = (ZMod.unitOfCoprime 2 (by decide)) := by
        ext
        simpa using hd
      refine ⟨h, hh, ?_⟩
      rw [hdu]
      decide
    · have hdu : Matrix.GeneralLinearGroup.det h = (ZMod.unitOfCoprime 3 (by decide)) := by
        ext
        simpa using hd
      refine ⟨h ^ 3, H.pow_mem hh 3, ?_⟩
      rw [map_pow, hdu]
      decide
  · rcases hd with hd | hd
    · have hdu : Matrix.GeneralLinearGroup.det h = (ZMod.unitOfCoprime 2 (by decide)) := by
        ext
        simpa using hd
      refine ⟨h ^ 3, H.pow_mem hh 3, ?_⟩
      rw [map_pow, hdu]
      decide
    · have hdu : Matrix.GeneralLinearGroup.det h = (ZMod.unitOfCoprime 3 (by decide)) := by
        ext
        simpa using hd
      refine ⟨h, hh, ?_⟩
      rw [hdu]
      decide
  · rcases hd with hd | hd
    · have hdu : Matrix.GeneralLinearGroup.det h = (ZMod.unitOfCoprime 2 (by decide)) := by
        ext
        simpa using hd
      refine ⟨h ^ 2, H.pow_mem hh 2, ?_⟩
      rw [map_pow, hdu]
      decide
    · have hdu : Matrix.GeneralLinearGroup.det h = (ZMod.unitOfCoprime 3 (by decide)) := by
        ext
        simpa using hd
      refine ⟨h ^ 2, H.pow_mem hh 2, ?_⟩
      rw [map_pow, hdu]
      decide

end LeanFormal.IUT.XiFPaper.S2617SignDetActual
end