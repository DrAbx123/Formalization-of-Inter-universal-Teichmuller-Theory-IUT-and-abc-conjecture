import tmp.sheaf.xif.paper.S3128SignRankTwoActual
noncomputable section
open CategoryTheory AlgebraicGeometry
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionAttempt
open LeanFormal.IUT.XiFPaper.S3119NegInvolutionOverActual
open LeanFormal.IUT.XiFPaper.S3128SignRankTwoActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S3128SignActionActual
abbrev S3128SignGroup := Multiplicative (ZMod 2)
abbrev S3128SignGen : S3128SignGroup := Multiplicative.ofAdd (1 : ZMod 2)
@[simp] lemma S3128ofAdd_zero : (Multiplicative.ofAdd (0 : ZMod 2) : S3128SignGroup) = 1 := rfl
@[simp] lemma S3128ofAdd_one : (Multiplicative.ofAdd (1 : ZMod 2) : S3128SignGroup) = S3128SignGen := rfl
@[simp] lemma S3128ofAdd_mul00 : (Multiplicative.ofAdd (0 : ZMod 2) * Multiplicative.ofAdd (0 : ZMod 2) : S3128SignGroup) = 1 := by decide
@[simp] lemma S3128ofAdd_mul01 : (Multiplicative.ofAdd (0 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) : S3128SignGroup) = S3128SignGen := by decide
@[simp] lemma S3128ofAdd_mul10 : (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (0 : ZMod 2) : S3128SignGroup) = S3128SignGen := by decide
@[simp] lemma S3128ofAdd_mul11 : (Multiplicative.ofAdd (1 : ZMod 2) * Multiplicative.ofAdd (1 : ZMod 2) : S3128SignGroup) = 1 := by decide
@[simp] lemma S3128SignGen_ne_one : S3128SignGen ≠ (1 : S3128SignGroup) := by decide
@[simp] lemma S3128SignGen_mul_self : S3128SignGen * S3128SignGen = (1 : S3128SignGroup) := by decide
@[simp] lemma S3128SignGen_mul_one : S3128SignGen * (1 : S3128SignGroup) = S3128SignGen := by simp
@[simp] lemma S3128SignOne_mul_gen : (1 : S3128SignGroup) * S3128SignGen = S3128SignGen := by simp
noncomputable def S3128SignSmul (m : S3128SignGroup) (a : S1348CoordinateRing l) : S1348CoordinateRing l :=
  if m = 1 then a else S3119NegQuotientHom (l := l) a
noncomputable instance S3128SignSMul : SMul S3128SignGroup (S1348CoordinateRing l) :=
  ⟨S3128SignSmul⟩
@[simp] lemma S3128Sign_smul_def (m : S3128SignGroup) (a : S1348CoordinateRing l) :
    m • a = S3128SignSmul m a := rfl
@[simp] lemma S3128NegQuotientHom_hom (a : S1348CoordinateRing l) :
    S3119NegQuotientHom (l := l) (S3119NegQuotientHom (l := l) a) = a :=
  AlgHom.congr_fun (S3119NegQuotientHom_sq (l := l)) a
noncomputable instance S3128SignAction : MulSemiringAction S3128SignGroup (S1348CoordinateRing l) where
  smul := S3128SignSmul
  one_smul a := by simp [S3128SignSmul]
  mul_smul m n a := by
    fin_cases m <;> fin_cases n <;>
      simp only [S3128Sign_smul_def, S3128SignSmul] <;>
      split_ifs <;> (first | rfl | contradiction | simp_all [S3128NegQuotientHom_hom])
  smul_zero m := by
    fin_cases m <;> simp [S3128SignSmul]
  smul_add m a b := by
    fin_cases m <;>
      simp only [S3128Sign_smul_def, S3128SignSmul] <;>
      split_ifs <;> (first | rfl | contradiction | simp_all)
  smul_one m := by
    fin_cases m <;> simp [S3128SignSmul]
  smul_mul m a b := by
    fin_cases m <;>
      simp only [S3128Sign_smul_def, S3128SignSmul] <;>
      split_ifs <;> (first | rfl | contradiction | simp_all [map_mul])
theorem S3128SignGen_smul_t : S3128SignGen • (S3128t (l := l)) = -(S3128t (l := l)) := by
  rw [S3128Sign_smul_def, S3128SignSmul]
  rw [if_neg S3128SignGen_ne_one, S3128t_anti]
theorem S3128SignGen_smul_x :
    S3128SignGen • (S3128x (l := l)) = S3128x (l := l) := by
  rw [S3128Sign_smul_def, S3128SignSmul, if_neg S3128SignGen_ne_one]
  simp [S3128x, S3119NegQuotientHom_mk, S3119NegPolyHom_X0]

theorem S3128SignGen_smul_y :
    S3128SignGen • (S3128y (l := l)) = -S3128y (l := l) - S3128x (l := l) := by
  rw [S3128Sign_smul_def, S3128SignSmul, if_neg S3128SignGen_ne_one]
  simp [S3128y, S3128x, S3119NegQuotientHom_mk, S3119NegPolyHom_X1]

#check S3128SignGen_smul_y
#check S3128SignGen_smul_x
#check S3128SignAction
#check S3128SignGen_smul_t
end LeanFormal.IUT.XiFPaper.S3128SignActionActual
end
