/- Adapter part 2: henry's five requested gPoly inputs (exact names + minimal new proofs).

Requested 2026-11-17; reuses `Mzk1GChoiceDegreeActual.gPoly_natDegree_pos`,
`Mzk1CritValueInImageFinalActual.{gPoly_critValue_zero_or_critFrac,
gPoly_criticalValues_subset, critFrac_ne_zero}`, `Mzk1GChoiceScaleActual.{critFrac}`, and the
P1 bridge `Mzk1G1PsiM2AnalyticActual.polyEvalP1_ofFinite_mem_specialSet_iff`.
NAMED RESIDUALS (NOT closed): gPoly's raw critical values are {0, critFrac D}, not {0,1};
the normalized polynomial `gPolyNorm` below has critical values in {0,1}.  The
beta-value forms (eval at D.b != 0,1) are supplied in the closest available P1 form
(`gChoice_avoids`) rather than as ℚ eval statements (no direct lemma in the corpus).
-/
import tmp.sheaf.xif.paper.Mzk1GChoiceToM2Actual
import tmp.sheaf.xif.paper.Mzk1GChoiceDegreeActual
import tmp.sheaf.xif.paper.Mzk1Lemma22GChoiceConstructActual
import tmp.sheaf.xif.paper.Mzk1P1MorphismInterfaceActual
import tmp.sheaf.xif.paper.Mzk1CritValueInImageFinalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2BridgedActual

open LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2Actual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceAvoidCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedCanonicalActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1CritValueInImageFinalActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiM2AnalyticActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open Polynomial

/-- (1) gPoly has positive natDegree (0 < natDegree form). -/
theorem gPoly_natDegree_pos_adapter (D : Mzk1ScaleData) : 0 < (gPoly D).natDegree :=
  lt_of_lt_of_le zero_lt_one (gPoly_natDegree_pos D)

/-- (2) gPoly has nonzero derivative (char 0, positive degree). -/
theorem gPoly_derivative_ne_zero_adapter (D : Mzk1ScaleData) :
    Polynomial.derivative (gPoly D) ≠ 0 := by
  rw [Polynomial.derivative_ne_zero]
  exact Nat.ne_of_gt (lt_of_lt_of_le zero_lt_one (gPoly_natDegree_pos D))

/-- (3a) CLOSEST TRUE FORM: gPoly's critical values lie in {0, critFrac D}. -/
theorem gPoly_criticalValues_subset_adapter (D : Mzk1ScaleData) :
    {v : ℂ | ∃ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 ∧
        Polynomial.aeval z (gPoly D) = v} ⊆ ({0, ((critFrac D : ℚ) : ℂ)} : Set ℂ) :=
  gPoly_criticalValues_subset D

/-- the normalized polynomial critFrac^{-1} * gPoly. -/
noncomputable def gPolyNorm (D : Mzk1ScaleData) : Polynomial ℚ :=
  Polynomial.C (critFrac D)⁻¹ * gPoly D

/-- (3b) PROVED: the normalized polynomial has critical values in {0,1}. -/
theorem gPolyNorm_criticalValues_subset (D : Mzk1ScaleData) :
    {v : ℂ | ∃ z : ℂ, Polynomial.aeval z (Polynomial.derivative (gPolyNorm D)) = 0 ∧
        Polynomial.aeval z (gPolyNorm D) = v} ⊆ ({0, 1} : Set ℂ) := by
  rintro v ⟨z, hz, rfl⟩
  have hc : ((critFrac D : ℚ) : ℂ) ≠ 0 := by exact_mod_cast critFrac_ne_zero D
  rw [gPolyNorm, Polynomial.derivative_C_mul] at hz
  rw [gPolyNorm, map_mul, Polynomial.aeval_C] at hz ⊢
  have hz' : Polynomial.aeval z (Polynomial.derivative (gPoly D)) = 0 := by
    exact (mul_eq_zero.mp hz).resolve_left hc
  rcases gPoly_critValue_zero_or_critFrac D hz' with h | h
  · left
    rw [h, mul_zero]
  · right
    rw [h, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- (4) CLOSEST TRUE FORM: the beta-avoiding row in P1 form (no direct ℚ eval form). -/
theorem gPoly_beta_avoiding_p1 (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    AvoidsPoint (polyMorphism (gPoly D) (gPoly_natDegree_pos D)) D.beta
      (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) :=
  gChoice_avoids_adapter D H

/-- (4b) PROVED: in particular the beta point is not a value of gPoly on the scaled set. -/
theorem gPoly_beta_not_mem_image (D : Mzk1ScaleData) (H : Lemma22Hypotheses D.S D.beta) :
    D.beta ∉ (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ)) :=
  gPoly_beta_avoiding_p1 D H

/-- (5) PROVED: a zero of gPoly (as a value) is a rational value (take c = 0). -/
theorem gPoly_value_mem_rat (D : Mzk1ScaleData) {z : ℂ}
    (h : Polynomial.aeval z (gPoly D) = 0) :
    ∃ c : ℚ, Polynomial.aeval z (gPoly D) = algebraMap ℚ ℂ c :=
  ⟨0, by rw [h, map_zero]⟩

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceToM2BridgedActual
end