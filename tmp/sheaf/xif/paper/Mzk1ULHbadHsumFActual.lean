/- hsumF（L3 的 f 侧）: per-place conductor log 的求和恒等，直接用 DONE donor:
   Mzk1ULLocalConductorDegActual.sum_localLogF_eq_finrank_mul（DONE 14:13:26）:
     Sum_{P in S} localLogF K P = [K:Q] * logConductorDeg K S.
   本件 instantiate K = F 层（T.arithmetic.F），S = 任意 HeightOneSpectrum Finset。
   到 rational-prime 层的 fiber 聚合（Sum_p Sum_{P|p} = Sum_P）需要 Ideal -> HeightOneSpectrum
   的桥（IsPrime/ne_bot 由 differentPlaces/badFPrimeSet 的 normalizedFactors 成员给出）；
   该聚合留给 hsumF_aggregate（或用 emmy 的 sum_fiber_aggregate）。
   注: d_mod=[Fmod:Q] vs [F:Q] 差由裁 (c) 的 SAr_F 口径处理（logConductorDeg F = logConductorFActual 的桥另证）。 -/
import tmp.sheaf.xif.paper.Mzk1ULLocalConductorDegActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual

variable (K : Type*) [Field K] [NumberField K]

/-- hsumF（谱层）: Sum localLogF = [K:Q]*logConductorDeg（donor 的 re-export，真证）。 -/
theorem hsumF_spectrum (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    (∑ P ∈ S, localLogF K P) =
      (Module.finrank ℚ K : ℝ) * logConductorDeg K S :=
  sum_localLogF_eq_finrank_mul K S

/-- hsumF（非负）: 每项 nonneg ⇒ 和 nonneg（给定 residue prime ≥1）。 -/
theorem hsumF_nonneg (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (h : ∀ P ∈ S, (1 : ℝ) ≤ ((underIntGen (K := K) (P : Ideal (𝓞 K))).natAbs : ℝ)) :
    0 ≤ ∑ P ∈ S, localLogF K P := by
  apply Finset.sum_nonneg
  intro P hP
  exact localLogF_nonneg K P (h P hP)

#print axioms hsumF_spectrum
#print axioms hsumF_nonneg

end LeanFormal.IUT.XiFPaper.Mzk1ULHbadHsumFActual