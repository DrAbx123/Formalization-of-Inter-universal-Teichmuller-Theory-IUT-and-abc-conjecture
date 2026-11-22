import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1BelyiCVCompositionActual
import tmp.sheaf.xif.paper.Mzk1G1TwoSectionPsiLocalActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalPsiActual
open AlgebraicGeometry Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1BelyiCVCompositionActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual
open LeanFormal.IUT.XiFPaper.RestatedLemma24InterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1P1MorphismInterfaceActual

/-- B2, zero divisor: on the first affine Fermat chart, every prime containing one of the
protected linear factors x - t (t in T) contains the actual chart coordinate
u = prod (x - t) of psi; i.e. the T-fibers are exactly the 0-fiber of psi. -/
theorem psi_protected_fiber_maps_to_zero {n : Nat} (T : Finset ℚ) (P : Ideal (R n))
    [P.IsPrime] {t : ℚ} (ht : t ∈ T)
    (hPt : chartX n - algebraMap ℚ (R n) t ∈ P) : psiChart0Coord n T ∈ P :=
  (psiChart0Coord_mem_iff n T P).mpr ⟨t, ht, hPt⟩

/-- B2, unramified over 0 (value level): zero is NOT a critical value of the first stage
psi; every point of the 0-fiber of the protected-to-zero polynomial is a simple zero. -/
theorem psi_unramified_over_zero {T : Finset ℚ} {x : ℚ}
    (hx : Polynomial.eval x (protectedToZeroPolynomial T) = 0) :
    Polynomial.eval x (Polynomial.derivative (protectedToZeroPolynomial T)) ≠ 0 :=
  zero_not_critical_value hx

/-- B2, divisor level: the local vanishing order of the first stage at every protected
point is exactly 1. -/
theorem psi_simple_zero {T : Finset ℚ} {t : ℚ} (ht : t ∈ T) :
    Polynomial.rootMultiplicity t (protectedToZeroPolynomial T) = 1 :=
  LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual.rootMultiplicity_protectedToZero_of_mem ht

/-- B1, "must avoid" side, for the composite phi = q.comp psi: if q(0) is neither 0 nor 1
then the whole protected set T maps outside the Belyi set {0,1,infinity} in P^1(Q). -/
theorem phi_protected_avoids_belyi {T : Finset ℚ} {q : Polynomial ℚ}
    (h0 : Polynomial.eval 0 q ≠ 0) (h1 : Polynomial.eval 0 q ≠ 1) {t : ℚ} (ht : t ∈ T) :
    polyEvalP1 (q.comp (protectedToZeroPolynomial T)) (P1Point.ofFinite t) ∉ specialSet ℚ :=
  comp_T_avoids_specialSet h0 h1 ht

/-- B1, branch side: the critical values of the composite phi = q.comp psi lie in {0,1}
as soon as q carries the first stage's critical values into {0,1} and q is unramified
away from {0,1}. -/
theorem phi_branch_values {T : Finset ℚ} {q : Polynomial ℚ}
    (hpsi : ∀ c ∈ criticalValuesOverC (protectedToZeroPolynomial T),
      Polynomial.aeval c q ∈ ({0, 1} : Set ℂ))
    (hq : criticalValuesOverC q ⊆ ({0, 1} : Set ℂ)) :
    criticalValuesOverC (q.comp (protectedToZeroPolynomial T)) ⊆ ({0, 1} : Set ℂ) :=
  comp_criticalValues_subset hpsi hq

/-- The assembly of the actual first-stage data delivered so far: the two actual affine
scheme morphisms of psi = [s0:s1] (on the two Fermat charts), the B2 divisor data and the
B1 value data of the composite.  NOTE: this is the two-chart affine assembly; the global
morphism Y_n -> P^1 is obtained after the two charts are glued (G-A) and P^1 is available. -/
theorem noncriticalPsi_twoChartActual (n : Nat) (T : Finset ℚ) :
    (Nonempty (FermatChart n ⟶ Spec (CommRingCat.of (Polynomial ℚ)))) ∧
    (Nonempty (Spec (CommRingCat.of (psiChartInfDomain n T)) ⟶
      Spec (CommRingCat.of (Polynomial ℚ)))) ∧
    (∀ t ∈ T, Polynomial.eval t (protectedToZeroPolynomial T) = 0) ∧
    (∀ t ∈ T, Polynomial.rootMultiplicity t (protectedToZeroPolynomial T) = 1) := by
  refine ⟨⟨psiChart0Map n T⟩, ⟨psiChartInfMap n T⟩, ?_, ?_⟩
  · intro t ht
    exact eval_protectedToZero_of_mem ht
  · intro t ht
    exact psi_simple_zero ht

#print axioms psi_protected_fiber_maps_to_zero
#print axioms psi_unramified_over_zero
#print axioms psi_simple_zero
#print axioms phi_protected_avoids_belyi
#print axioms phi_branch_values
#print axioms noncriticalPsi_twoChartActual
end LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalPsiActual
