/- hbad_fmod 组装件（Lead 裁 (a)）：把 hbad 归约到 q 段/d 段两个 per-segment 界。
  输入: hq  q 段 ≤ d_mod·logConductorFActual；hd d 段 ≤ d_mod·logDifferentF Fmod；
  hspecial 走 Mzk1ULSpecialPrimesNumericActual.specialPrimes_log_sum_le。
  donor: Mzk1ULHSQLambdaNumericActual.sum_union_log_le_add（DONE 13:32:30）;
  Mzk1ULSArFmodActual.SAr_tripodal_Fmod（本批）;
  Mzk1ULSQPaperActual.{qSupportPrimes,dSupportPrimes,specialPrimes}。 -/
import tmp.sheaf.xif.paper.Mzk1ULHSQLambdaNumericActual
import tmp.sheaf.xif.paper.Mzk1ULSArFmodActual
import tmp.sheaf.xif.paper.Mzk1ULSpecialPrimesNumericActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.Mzk1ULSQPaperActual
open LeanFormal.IUT.XiFPaper.Mzk1ULHSQLambdaNumericActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSArFmodActual
open LeanFormal.IUT.XiFPaper.Mzk1ULSpecialPrimesNumericActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- hbad 归约: q 段/d 段两个界 ⇒ Σ_{q∪d} log p ≤ 2 d_mod·SAr_Fmod + 5 + log l。 -/
theorem hbad_fmod_of_segments (dmod Sar : ℝ)
    (hSar : Sar = SAr_tripodal_Fmod (T := T))
    (hq : (∑ p ∈ qSupportPrimes T, Real.log (p : ℝ)) ≤
      dmod * logConductorFActual (T := T))
    (hd : (∑ p ∈ dSupportPrimes T, Real.log (p : ℝ)) ≤
      dmod * logDifferentF T.arithmetic.Fmod)
    (hdmod : 0 ≤ dmod) (hSar0 : 0 ≤ Sar)
    (hlogl : 0 ≤ Real.log (l.value : ℝ)) :
    (∑ p ∈ qSupportPrimes T ∪ dSupportPrimes T, Real.log (p : ℝ)) ≤
      2 * dmod * Sar + 5 + Real.log (l.value : ℝ) := by
  have h1 := sum_union_log_le_add (s := qSupportPrimes T) (t := dSupportPrimes T)
  have h2 : (∑ p ∈ qSupportPrimes T, Real.log (p : ℝ)) +
      (∑ p ∈ dSupportPrimes T, Real.log (p : ℝ)) ≤
      dmod * (logConductorFActual (T := T) + logDifferentF T.arithmetic.Fmod) := by
    linarith
  have h3 : logConductorFActual (T := T) + logDifferentF T.arithmetic.Fmod = Sar := by
    rw [hSar]
    unfold SAr_tripodal_Fmod
    ring
  rw [h3] at h2
  have h4 : dmod * Sar ≤ 2 * dmod * Sar := by linarith [hSar0]
  linarith [h1, h2, h4, hlogl]

#print axioms hbad_fmod_of_segments

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadAssemblyActual
