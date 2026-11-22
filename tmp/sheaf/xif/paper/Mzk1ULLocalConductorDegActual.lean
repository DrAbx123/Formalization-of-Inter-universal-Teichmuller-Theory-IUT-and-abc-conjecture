/- U-C: local per-place conductor logarithms and their sum identity (hcond numeric).

Companion of `Mzk1ULConductorDegActual.logConductorDeg` (= (Sum localLogF)/[K:Q]);
this file provides the per-place object `localLogF` with
  Sum_{P in S} localLogF P = [K:Q] * logConductorDeg K S,
i.e. david's `f_vQ` side when K = Fmod (then [K:Q] = d_mod).  Reuse:
`Mzk1HT82PaperWeightDiffActual.underIntGen` and `Ideal.inertiaDeg` (same shape as
david's `logConductorFActual`), and `Mzk1ULConductorDegActual.logConductorDeg`.
-/
import tmp.sheaf.xif.paper.Mzk1ULConductorDegActual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual

variable (K : Type*) [Field K] [NumberField K]

/-- local (per-place) conductor logarithm: log |N P| = f_P log p_P. -/
noncomputable def localLogF (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℝ :=
  ((P.asIdeal).inertiaDeg ℤ : ℝ) *
    Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ)

/-- PROVED (definitional): localLogF = f_P * log p_P. -/
theorem localLogF_eq (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    localLogF K P = ((P.asIdeal).inertiaDeg ℤ : ℝ) *
      Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ) := rfl

/-- PROVED: the local conductor log is nonnegative when the residue prime is >= 1. -/
theorem localLogF_nonneg (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (h : (1 : ℝ) ≤ ((underIntGen (K := K) P.asIdeal).natAbs : ℝ)) :
    0 ≤ localLogF K P := by
  unfold localLogF
  exact mul_nonneg (by positivity) (Real.log_nonneg h)

/-- PROVED: the sum of the local conductor logs is [K:Q] times the conductor. -/
theorem sum_localLogF_eq_finrank_mul (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    (∑ P ∈ S, localLogF K P) =
      (Module.finrank ℚ K : ℝ) * logConductorDeg K S := by
  have h : (Module.finrank ℚ K : ℝ) ≠ 0 := by
    exact_mod_cast Module.finrank_pos.ne'
  unfold localLogF logConductorDeg
  field_simp [h]

/-- PROVED: for a single bad place, localLogF = log |N P| in the inertia form. -/
theorem localLogF_eq_inertia_mul_log (P : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) :
    localLogF K P = ((P.asIdeal).inertiaDeg ℤ : ℝ) *
      Real.log ((underIntGen (K := K) P.asIdeal).natAbs : ℝ) := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ULLocalConductorDegActual
end