import tmp.sheaf.xif.paper.Mzk1GChoiceIntegrationActual
import tmp.sheaf.xif.paper.Mzk1BelyiCanonicalActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

/-!
# Mzk1GChoiceUnramifiedCanonicalActual — unramified interface for the g-choice step

STEP 0 prior-art (reuse, no re-proof): corpus [Mzk1] Lemma 2.1 (b) (derivative
computation f'(x) = x^{m-1}(x-1)^{n-1}((m+n)x-m), so critical points are 0,1,r) and
Lemma 2.2 unramified-away-from-image condition (lines 106-135); stage4
Mzk1Lemma22GChoiceConstructActual (Mzk1ScaleData, fq, f0q, gPoly), Mzk1PolyChainRuleActual
(polyUnramifiedAt_comp_finite/infty PROVED), Mzk1PolyMapActual (polyMapPoints/polyMorphism/
polyUnramifiedAt); stepxi Mzk1BelyiCanonicalActual (canonical TauCeti B_{m,n}: derivative
root set ⊆ {0,1,m/(m+n)}, critical values ⊆{0,1}, eval 0/1 =0).

THIS FILE (parallel to stage4's Mzk1GChoiceUnramifiedActual; no edit to his files) gives:
* gPoly_ne_zero / gPoly_unramified_infty: at infinity gPoly is unramified (PROVED);
* the named shape GChoiceDataUnramifiedShape matching Mzk1GChoiceData.hunram exactly;
* canonicalBelyi_criticalPoints_row / canonicalBelyi_criticalValues_row: the canonical
  Belyi control rows (rootSet of B' ⊆ {0,1,r}; critical values ⊆ {0,1});
* gChoice_unramified_of_criticalInTarget: REDUCTION — if every critical point of gPoly
  maps into the target set (the Lemma 2.1 (b) conclusion), then the unramified shape
  holds; this isolates the remaining finite-critical-point/derivative-API obligation;
* criticalInTarget_of_canonicalBelyi: the intended discharge route, as a named Prop
  hypothesis (finite critical points of the scaled polynomial lie in the image/target).
HONEST SCOPE: infinity case + reduction + shapes PROVED; the finite critical-point
inclusion for gPoly (derivative/root API for the shifted scaled polynomial) remains the
named hypothesis - it is stage4's remaining unramified step. No closure claim.
Registry frozen 14041; no registry edits.  No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedCanonicalActual

open Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PolyMapActual
open LeanFormal.IUT.XiFPaper.Mzk1Lemma22GChoiceConstructActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceIntegrationActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceScaleActual
open LeanFormal.IUT.XiFPaper.Mzk1GChoiceDegreeActual
open TauCeti

/-- gPoly is nonzero (natDegree >= 1). -/
theorem gPoly_ne_zero (D : Mzk1ScaleData) : gPoly D ≠ 0 := by
  intro h
  have hpos := gPoly_natDegree_pos D
  rw [h, Polynomial.natDegree_zero] at hpos
  omega

/-- **Infinity is unramified (PROVED):** the polynomial map is unramified at infinity
(nonvanishing). -/
theorem gPoly_unramified_infty (D : Mzk1ScaleData) :
    polyUnramifiedAt (gPoly D) P1Point.infty := by
  simpa [polyUnramifiedAt, P1Point.infty] using gPoly_ne_zero D

/-- The named unramified shape, exactly the Mzk1GChoiceData.hunram field for gPoly. -/
def GChoiceDataUnramifiedShape (D : Mzk1ScaleData) : Prop :=
  UnramifiedOver (polyMorphism (gPoly D) (gPoly_natDegree_pos D))
    {p | p ∉ (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))}
    (polyUnramifiedAt (gPoly D))

/-- Canonical Belyi derivative-root row: critical points of B_{m,n} lie in
{0, 1, m/(m+n)} (canonical TauCeti Belyi). -/
theorem canonicalBelyi_criticalPoints_row (m n : ℕ) (L : Type*) [Field L] [Algebra ℚ L] :
    (derivative (belyiPolynomial ℚ m n)).rootSet L ⊆
      ({(0 : L), (1 : L), ((m : L) / ((m : L) + (n : L)))} : Set L) :=
  rootSet_derivative_belyiPolynomial_subset L m n

/-- Canonical Belyi critical-values row: critical values of B_{m,n} lie in {0,1}. -/
theorem canonicalBelyi_criticalValues_row (m n : ℕ) :
    (belyiPolynomial ℚ m n).criticalValues ℚ ⊆ ({0, 1} : Set ℚ) :=
  LeanFormal.IUT.XiFPaper.Mzk1BelyiCanonicalActual.belyi_criticalValues_subset m n

/-- The finite-critical-point inclusion target for gPoly (paper Lemma 2.1 (b)):
every point at which gPoly fails the derivative test maps into the target set. -/
def GChoiceCriticalInTarget (D : Mzk1ScaleData) : Prop :=
  ∀ p : P1Point ℚ,
    ¬ polyUnramifiedAt (gPoly D) p →
      (polyMorphism (gPoly D) (gPoly_natDegree_pos D)).mapPoints p ∈
        (↑(D.S.image (polyMapPoints (gPoly D))) : Set (P1Point ℚ))

/-- **Unramified reduction (PROVED):** if every critical point of gPoly maps into the
target (the Lemma 2.1 (b) conclusion), then gPoly is unramified over the complement of
the target — i.e. the unramified shape holds. -/
theorem gChoice_unramified_of_criticalInTarget (D : Mzk1ScaleData)
    (hcrit : GChoiceCriticalInTarget D) : GChoiceDataUnramifiedShape D := by
  intro p hp
  by_contra hnu
  exact hp (hcrit p hnu)

/-- The intended discharge route for the finite critical points: the canonical Belyi
polynomial B_{m,n} has derivative roots {0,1,m/(m+n)} and critical values {0,1}; for
gPoly = shift/scale of the same Belyi function the critical points of gPoly are the
pre-images of the same set.  This is recorded as a named Prop (stage4 finite-derivative
step); combined with gChoice_unramified_of_criticalInTarget it yields the shape. -/
def GChoiceCriticalInTargetCanonicalBelyi (D : Mzk1ScaleData) : Prop :=
  GChoiceCriticalInTarget D

/-- Row ledger: (unramified component, Lean evidence, status). -/
def mzk1GChoiceUnramifiedRows : List (String × String × String) :=
  [ ("gPoly nonzero / infinity unramified", "gPoly_ne_zero, gPoly_unramified_infty", "PROVED"),
    ("canonical Belyi derivative roots {0,1,r}", "canonicalBelyi_criticalPoints_row (TauCeti rootSet_derivative_belyiPolynomial_subset)", "PROVED (reuse)"),
    ("canonical Belyi critical values {0,1}", "canonicalBelyi_criticalValues_row (Mzk1BelyiCanonicalActual.belyi_criticalValues_subset)", "PROVED (reuse)"),
    ("unramified shape matching Mzk1GChoiceData.hunram", "GChoiceDataUnramifiedShape (def)", "DEFINED"),
    ("reduction: critical points in target => unramified shape", "gChoice_unramified_of_criticalInTarget", "PROVED"),
    ("finite critical points of gPoly in target", "GChoiceCriticalInTarget (named Prop; derivative/root API for shifted scaled polynomial)", "NAMED GATE (stage4)"),
    ("paper-level unramified/Thm 2.5", "no closure claim", "OPEN") ]

theorem mzk1GChoiceUnramifiedRows_length : mzk1GChoiceUnramifiedRows.length = 7 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1GChoiceUnramifiedCanonicalActual

end
