/- qNo 段真证（unramified bad p）：给定 bad rational prime 集 badP、d_mod 与 log f 的 fiber 恒等式，
   推出 Sigma_{qNo} log p <= d_mod * logF。
   fiber 恒等式 d_mod*logF = Sigma_{p in badP} log p 是 Ftpd 层 unramified 的代数事实
   （每 p: Sum_{w|p} f_w = [Ftpd:Q]），由 per-λ local 件填；本件只做组合/实数推理（不 fake）。 -/
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadQNoActual

/-- qNo 段: 子集 + fiber 恒等式 + d_mod>=1 => Sigma_{qNo} log p <= d_mod*logF。 -/
theorem hq_noSpecial_of_fiber (qNo badP : Finset ℕ) (dmod logF : ℝ)
    (hsub : qNo ⊆ badP)
    (hdmod : 1 ≤ dmod)
    (hlogF : dmod * logF = ∑ p ∈ badP, Real.log (p : ℝ))
    (hbad0 : 0 ≤ ∑ p ∈ badP, Real.log (p : ℝ)) :
    (∑ p ∈ qNo, Real.log (p : ℝ)) ≤ dmod * logF := by
  have hsubsum : (∑ p ∈ qNo, Real.log (p : ℝ)) ≤ ∑ p ∈ badP, Real.log (p : ℝ) :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => Real.log_natCast_nonneg p)
  rw [hlogF]
  nlinarith [hsubsum, hbad0, hdmod]

#print axioms hq_noSpecial_of_fiber

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadQNoActual