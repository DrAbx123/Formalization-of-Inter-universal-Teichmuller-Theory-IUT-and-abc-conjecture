import tmp.sheaf.xif.paper.ExpEst02ElementaryEstimatesActual
import LeanFormal.IUT.IUTIV.Estimates.Section2
import Mathlib.NumberTheory.Chebyshev
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ExpEst02RealizedActual — realized [ExpEst] paper inputs

Genuine realization of the three ExpEst02 paper-input predicates from
already-proved Mathlib/IUT IV assets:
* B1 explicit PNT upper on the nth prime, from
  iutIVProp16_index_le_four_thirds_nthPrime (Section2);
* B2 prime-reciprocal-sum shape, from
  iutIVProp16_primeCounting_le_four_thirds_eventually (Section2);
* B3 Chebyshev theta linear bound, from Mathlib's theta_le_log4_mul_x.
The predicates are no longer bare paper-input registrations.  No closure
claim for the remaining ExpEst inputs; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ExpEst02RealizedActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.XiFPaper.ExpEst02ElementaryEstimatesActual

/-- B1: the explicit PNT upper bound on the nth prime is realized. -/
theorem expEstPNTUpper_realized :
    ExpEstPNTUpperPaperInput (fun n : Nat => Nat.nth Nat.Prime n) := by
  obtain ⟨n0, h⟩ := iutIVProp16_index_le_four_thirds_nthPrime
  refine ⟨n0, fun n hn => ?_⟩
  have h' := h n hn
  have hnle : (n : Real) ≤ ((n + 1 : Nat) : Real) := by
    exact_mod_cast Nat.le_succ n
  linarith

/-- B2: the prime-reciprocal-sum shape is realized by the prime-counting bound. -/
theorem expEstPrimeReciprocalSum_realized :
    ExpEstPrimeReciprocalSumPaperInput
      (fun eta : Real => (Nat.primeCounting ⌊eta⌋₊ : Real)) := by
  obtain ⟨eta0, hpos, h⟩ := iutIVProp16_primeCounting_le_four_thirds_eventually
  exact ⟨eta0, hpos, h⟩

/-- B3: the Chebyshev theta linear bound is realized (C = log 4). -/
theorem expEstChebyshevTheta_realized :
    ExpEstChebyshevThetaPaperInput Chebyshev.theta := by
  refine ⟨1, Real.log 4, by norm_num, Real.log_pos (by norm_num), fun eta heta => ?_⟩
  exact Chebyshev.theta_le_log4_mul_x (by linarith)


/-- LANA-reference shape of the explicit Chebyshev certificate: threshold ≥ 5,
lower factor 2/3 and upper factor 2. -/
theorem chebyshevBoundExplicit_realized :
    ∃ ξ : Real, 5 ≤ ξ ∧
      (∀ x : Real, ξ ≤ x → 2 / 3 * x ≤ Chebyshev.theta x) ∧
      (∀ x : Real, ξ ≤ x → Chebyshev.theta x ≤ 2 * x) := by
  obtain ⟨ξ, hξ, hb⟩ := iutIVProp21ii_theta_two_sided_eventually
  refine ⟨ξ, hξ, fun x hx => (hb x hx).1, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have h := (hb x hx).2
  nlinarith

/-- LANA-reference shape of the explicit prime-counting certificate:
threshold > 1 and π(x) ≤ 3x/(2 log x) eventually. -/
theorem primeCountingBoundExplicit_realized :
    ∃ η : Real, 1 < η ∧
      ∀ x : Real, η ≤ x →
        (Nat.primeCounting ⌊x⌋₊ : Real) ≤ 3 * x / (2 * Real.log x) := by
  obtain ⟨η0, _hpos, h⟩ := iutIVProp16_primeCounting_le_four_thirds_eventually
  refine ⟨max η0 2, lt_of_lt_of_le (by norm_num) (le_max_right _ _), fun x hx => ?_⟩
  have hx1 : 1 < x := by
    have h2 : (2 : Real) ≤ x := le_trans (le_max_right _ _) hx
    linarith
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hxη : η0 ≤ x := le_trans (le_max_left _ _) hx
  have hle := h x hxη
  have h43 : 4 * x / (3 * Real.log x) ≤ 3 * x / (2 * Real.log x) := by
    calc 4 * x / (3 * Real.log x) = (4 / 3) * (x / Real.log x) := by
          field_simp [ne_of_gt hlog]
      _ ≤ (3 / 2) * (x / Real.log x) :=
          mul_le_mul_of_nonneg_right (by norm_num) (div_nonneg hx0.le hlog.le)
      _ = 3 * x / (2 * Real.log x) := by
          field_simp [ne_of_gt hlog]
  exact le_trans hle h43

/-- All three ExpEst02 Class B inputs are realized together. -/
theorem expEstClassB_realized :
    ExpEstPNTUpperPaperInput (fun n : Nat => Nat.nth Nat.Prime n) ∧
      ExpEstPrimeReciprocalSumPaperInput
        (fun eta : Real => (Nat.primeCounting ⌊eta⌋₊ : Real)) ∧
      ExpEstChebyshevThetaPaperInput Chebyshev.theta :=
  ⟨expEstPNTUpper_realized, expEstPrimeReciprocalSum_realized,
    expEstChebyshevTheta_realized⟩

end LeanFormal.IUT.XiFPaper.Mzk1ExpEst02RealizedActual

end
