/- S_ar 域身份核对（Lead 要求，1 轻件）:
  per-λ: Fmod = Q(j(lam))，Ftpd = Fmod(E[2]) = Q(j(lam),lam) = Q(lam)（j 是 lam 的有理函数）。
  定义 SAr_tripodal_Ftpd := logDifferentF ↥(FtpdLam lam) + logConductorDegOf ℂ E VBad（f_Ftpd 逐位加权）。
  donor: Mzk1ULTripodalFieldActual.FtpdLam/jOfLam（DONE）;
  Mzk1ULFtpdNumberFieldActual.numberField_FtpdLam（DONE）;
  Mzk1ULPaperLettersActual.logDifferentF（DONE）;
  Mzk1ULTripodalConductorActual.logConductorDegOf（DONE 23:55:17）。 -/
import LeanFormal.IUT.ABCBridge.Geometry.LegendreWeierstrassCurve
import tmp.sheaf.xif.paper.Mzk1ULFtpdNumberFieldActual
import tmp.sheaf.xif.paper.Mzk1ULTripodalConductorActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULSArFtpdIdentityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalFieldActual
open LeanFormal.IUT.XiFPaper.ULTripodalNumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULPaperLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1ULTripodalConductorActual

/-- jOfLam lam ∈ adjoin ℚ {lam}（公开版）。 -/
theorem jOfLam_mem_adjoin (lam : ℂ) : jOfLam lam ∈ IntermediateField.adjoin ℚ ({lam} : Set ℂ) := by
  set A := IntermediateField.adjoin ℚ ({lam} : Set ℂ)
  have hlam : lam ∈ A := IntermediateField.mem_adjoin_of_mem ℚ (Set.mem_singleton lam)
  have h256 : (256 : ℂ) ∈ A := by simpa using A.natCast_mem 256
  have hsq : lam ^ 2 ∈ A := by rw [pow_two]; exact A.mul_mem hlam hlam
  have h1 : (1 : ℂ) ∈ A := A.one_mem
  have hbase : (1 - lam + lam ^ 2) ∈ A := A.add_mem (A.sub_mem h1 hlam) hsq
  have hcube : (1 - lam + lam ^ 2) ^ 3 ∈ A := by
    rw [pow_succ, pow_two]
    exact A.mul_mem (A.mul_mem hbase hbase) hbase
  have hnum : (256 : ℂ) * (1 - lam + lam ^ 2) ^ 3 ∈ A := A.mul_mem h256 hcube
  have hden : lam ^ 2 * (1 - lam) ^ 2 ∈ A := by
    have h2 : (1 - lam) ^ 2 ∈ A := by
      rw [pow_two]
      exact A.mul_mem (A.sub_mem h1 hlam) (A.sub_mem h1 hlam)
    exact A.mul_mem hsq h2
  unfold jOfLam
  exact A.div_mem hnum hden

/-- **Ftpd = Q(λ)**（per-λ）: FtpdLam lam = adjoin ℚ {lam}。 -/
theorem FtpdLam_eq_adjoin_lam (lam : ℂ) :
    FtpdLam lam = IntermediateField.adjoin ℚ ({lam} : Set ℂ) := by
  apply le_antisymm
  · show IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    · exact jOfLam_mem_adjoin lam
    · exact IntermediateField.subset_adjoin ℚ _ (by simp)
  · show IntermediateField.adjoin ℚ ({lam} : Set ℂ) ≤
      IntermediateField.adjoin ℚ ({jOfLam lam, lam} : Set ℂ)
    rw [IntermediateField.adjoin_le_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rcases hx with rfl
    exact IntermediateField.subset_adjoin ℚ _ (by simp)

/-- **S_ar 的 Ftpd 层定义**: log d_Ftpd + log f_Ftpd（逐位加权的 conductor）。 -/
noncomputable def SAr_tripodal_Ftpd (lam : ℂ) (hlam : IsAlgebraic ℚ lam) (logF : ℝ) : ℝ :=
  (letI := numberField_FtpdLam lam hlam
   logDifferentF ↥(FtpdLam lam)) + logF

/-- SAr_Ftpd 的 log d 部分就是 Ftpd 的 rootDiscr log（rfl 口径）。 -/
theorem SAr_tripodal_Ftpd_defs (lam : ℂ) (hlam : IsAlgebraic ℚ lam) (logF : ℝ) :
    SAr_tripodal_Ftpd lam hlam logF =
      (letI := numberField_FtpdLam lam hlam
       Real.log (NumberField.rootDiscr ↥(FtpdLam lam))) + logF := rfl

#print axioms FtpdLam_eq_adjoin_lam
#print axioms jOfLam_mem_adjoin
#print axioms SAr_tripodal_Ftpd_defs

end LeanFormal.IUT.XiFPaper.Mzk1ULSArFtpdIdentityActual