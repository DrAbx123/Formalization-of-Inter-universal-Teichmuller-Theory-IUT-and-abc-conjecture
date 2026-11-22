/- hsumF 无条件闭合（emmy DONE 22:46:26 Mzk1ULLocalizationObligationsActual.localConductor_eq_global_self）:
   Sum_{P in bad} localLogF K P = [K:Q] * logConductorDeg K bad。
   localLogF K P = f_P * log(natAbs) 与 donor 的 f_P * log|underIntGen| 差 natAbs/cast_abs 的桥。 -/
import tmp.sheaf.xif.paper.Mzk1ULLocalizationObligationsActual
import tmp.sheaf.xif.paper.Mzk1ULLocalConductorDegActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFClosedActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalizationObligationsActual
open LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

variable (K : Type*) [Field K] [NumberField K]

theorem natAbs_cast_abs (z : Int) : ((z.natAbs : Real)) = |(z : Real)| := by
  rw [← Int.cast_abs, Int.abs_eq_natAbs]
  norm_num

theorem hsumF_closed (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    (∑ P ∈ bad, localLogF K P) =
      (Module.finrank ℚ K : Real) * logConductorDeg K bad := by
  rw [← localConductor_eq_global_self (K := K) bad]
  apply Finset.sum_congr rfl
  intro P _
  unfold localLogF
  rw [natAbs_cast_abs]

#print axioms natAbs_cast_abs
#print axioms hsumF_closed

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFClosedActual