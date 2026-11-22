/- hbad 的 Ftpd 层最终形式（Lead 定稿: d_mod = [Fmod:Q], S_ar = log d_Ftpd + log f_Ftpd, 系数 2·d_mod）。
  s^Q^ADiv 的 e_v：F*=Q 时 e_v=1（Q 无分歧），故 log(s^Q)=Σ_{wQ∈V(Q)^dst} log p_wQ
  ⇒ primorial 形式就是 paper L1572 的 LHS（不需要额外桥不等式）。
  本件: 两个 per-segment 界 ⇒ Σ_{qNo∪dNo} log p ≤ 2 d_mod·SAr_Ftpd。
  donor: Mzk1ULHSqlLambdaNumericTruncActual.{qSupportNoSpecial,dSupportNoSpecial,sum_union_log_le_add};
  Mzk1ULSArFtpdIdentityActual.{SAr_tripodal_Ftpd,FtpdLam};
  Mzk1ULTripodalConductorActual.logConductorDegOf（DONE 23:55:17）。 -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericTruncActual
import tmp.sheaf.xif.paper.Mzk1ULSArFtpdIdentityActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadFtpdActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericTruncActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSArFtpdIdentityActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- **hbad_ftpd (最终形态)**: qNo/dNo 两个 per-segment 界 ⇒ 截断 union ≤ 2·[Fmod:Q]·SAr_Ftpd。 -/
theorem hbad_ftpd_trunc (lam : ℂ) (hlam : IsAlgebraic ℚ lam)
    (hE : (legendreWeierstrassCurve lam).IsElliptic)
    (VBad : Set (FinitePlace ↥(Iut.fieldOfModuli ℂ (legendreWeierstrassCurve lam))))
    (hq : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) ≤
      (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        logConductorDegOf ℂ (legendreWeierstrassCurve lam) VBad)
    (hd : (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        (letI := numberField_FtpdLam lam hlam
         logDifferentF ↥(FtpdLam lam)))
    (hdmod : 0 ≤ (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ))
    (hSAr0 : 0 ≤ SAr_tripodal_Ftpd lam hlam hE VBad) :
    (∑ p ∈ qSupportNoSpecial T ∪ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      2 * (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        SAr_tripodal_Ftpd lam hlam hE VBad := by
  have h1 := sum_union_log_le_add (s := qSupportNoSpecial T) (t := dSupportNoSpecial T)
  have h2 : (∑ p ∈ qSupportNoSpecial T, Real.log (p : ℝ)) +
      (∑ p ∈ dSupportNoSpecial T, Real.log (p : ℝ)) ≤
      (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        (logConductorDegOf ℂ (legendreWeierstrassCurve lam) VBad +
          (letI := numberField_FtpdLam lam hlam
           logDifferentF ↥(FtpdLam lam))) := by
    linarith
  have h3 : logConductorDegOf ℂ (legendreWeierstrassCurve lam) VBad +
      (letI := numberField_FtpdLam lam hlam
       logDifferentF ↥(FtpdLam lam)) =
      SAr_tripodal_Ftpd lam hlam hE VBad := by
    unfold SAr_tripodal_Ftpd
    ring
  rw [h3] at h2
  have h4 : (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
      SAr_tripodal_Ftpd lam hlam hE VBad ≤
      2 * (Module.finrank ℚ (T.arithmetic.Fmod) : ℝ) *
        SAr_tripodal_Ftpd lam hlam hE VBad := by linarith [hSAr0]
  linarith [h1, h2, h4]

#print axioms hbad_ftpd_trunc

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadFtpdActual
