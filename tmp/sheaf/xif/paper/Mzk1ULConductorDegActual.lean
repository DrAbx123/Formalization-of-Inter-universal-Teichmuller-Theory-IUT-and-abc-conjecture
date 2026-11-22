/- U-C: generic place-weighted conductor log f_K = (1/[K:Q]) * Sum_{p in bad} f_p log p.

Paper (IUT IV L1305-1353 + Def 1.9): log f_K = (Sum_{p in Supp} f_p log p)/[K:Q] with
f_p the inertia degree over Q.  Uses david's `underIntGen` (the rational prime under a
maximal ideal) and `Ideal.inertiaDeg`, i.e. exactly the same shape as
`Mzk1ULBadFPrimeSetActual.logConductorFActual` but for an arbitrary number field and
an explicit bad-place set.  This is the paper-faithful replacement for the legacy
prime-counted `logConductorF` (SUPERSEDED / NOT PAPER).
-/
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.RingTheory.RamificationInertia.Inertia
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual

open NumberField
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

variable (K : Type*) [Field K] [NumberField K]

/-- generic normalized place-weighted conductor on a finite set of height-one primes. -/
noncomputable def logConductorDeg
    (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) : ℝ :=
  (∑ p ∈ bad,
      ((p.asIdeal).inertiaDeg ℤ : ℝ) *
        Real.log ((underIntGen (K := K) p.asIdeal).natAbs : ℝ)) /
    (Module.finrank ℚ K : ℝ)

/-- PROVED (definitional): the conductor is the normalized inertia-weighted sum. -/
theorem logConductorDeg_eq (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    logConductorDeg K bad
      = (∑ p ∈ bad,
          ((p.asIdeal).inertiaDeg ℤ : ℝ) *
            Real.log ((underIntGen (K := K) p.asIdeal).natAbs : ℝ)) /
        (Module.finrank ℚ K : ℝ) := rfl

/-- PROVED: the conductor of the empty bad set is zero. -/
theorem logConductorDeg_empty :
    logConductorDeg K (∅ : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) = 0 := by
  simp [logConductorDeg]

/-- PROVED: the conductor is nonnegative when each bad prime has absNorm at least 1. -/
theorem logConductorDeg_nonneg (bad : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K)))
    (h : ∀ p ∈ bad,
      (1 : ℝ) ≤ ((underIntGen (K := K) p.asIdeal).natAbs : ℝ)) :
    0 ≤ logConductorDeg K bad := by
  apply div_nonneg _ (by positivity)
  apply Finset.sum_nonneg
  intro p hp
  have hf : (0 : ℝ) ≤ ((p.asIdeal).inertiaDeg ℤ : ℝ) := by positivity
  exact mul_nonneg hf (Real.log_nonneg (h p hp))

end LeanFormal.IUT.XiFPaper.Mzk1ULConductorDegActual
end