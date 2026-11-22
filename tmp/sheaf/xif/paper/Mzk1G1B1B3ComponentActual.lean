import tmp.sheaf.xif.paper.Mzk1G1PsiChartMapsActual
import tmp.sheaf.xif.paper.Mzk1G1NoncriticalPsiComponentActual
import tmp.sheaf.xif.paper.Mzk1G1TwoSectionDataActual
import tmp.sheaf.xif.paper.Mzk1G1BelyiCVCompositionActual
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1B1B3ComponentActual
open AlgebraicGeometry Polynomial
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiChartMapsActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProtectedToZeroMapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1TwoSectionDataActual
open LeanFormal.IUT.XiFPaper.Mzk1Consumer24AdapterUnconditionalActual

/-- Actual B1/B2/B3 component data for the two-section map psi = [s0:s1] on the two
affine Fermat charts:

* the two ACTUAL affine scheme morphisms of psi (first chart -> A^1_u with u = prod (x-t),
  second chart D(q) -> A^1_v with v = q^{-1} r^{|T|}),
* the protected-to-zero divisor data: T is carried to 0 and every zero is simple
  (root multiplicity exactly 1), i.e. the 0-fiber is unramified over 0 (B2),
* the two global sections with unit ideal (no common zero),
* the accepted finite-beta polynomial stage (the h in phi = h o psi).

B3 (phi^* O(1) = L^d and omega_Y(E_phi) = phi^* omega_{P^1}(0+1+infty)) is NOT part of
this structure: it needs the global curve Y_n (G-A) and the canonical sheaf (G-B) and is
not claimed here. -/
structure NoncriticalB1B3Component (n : Nat) (T : Finset ℚ) where
  chart0 : FermatChart n ⟶ Spec (CommRingCat.of (Polynomial ℚ))
  chart0_eq : chart0 = psiChart0Map n T
  chart1 : Spec (CommRingCat.of (psiChartInfDomain n T)) ⟶
    Spec (CommRingCat.of (Polynomial ℚ))
  chart1_eq : chart1 = psiChartInfMap n T
  protected_zero : ∀ t ∈ T, Polynomial.eval t (protectedToZeroPolynomial T) = 0
  protected_unramified : ∀ t ∈ T,
    Polynomial.eval t (Polynomial.derivative (protectedToZeroPolynomial T)) ≠ 0
  simple_zero : ∀ t ∈ T,
    Polynomial.rootMultiplicity t (protectedToZeroPolynomial T) = 1
  twoSection : TwoSectionData ℚ[X]
  finiteBeta : FiniteBetaCorrectedBase

/-- Inhabitant of the actual B1/B2 component: all fields are proved. -/
noncomputable def noncriticalB1B3Component (n : Nat) (T : Finset ℚ) :
    NoncriticalB1B3Component n T where
  chart0 := psiChart0Map n T
  chart0_eq := rfl
  chart1 := psiChartInfMap n T
  chart1_eq := rfl
  protected_zero := fun t ht => eval_protectedToZero_of_mem ht
  protected_unramified := fun t ht => eval_derivative_protectedToZero_ne_zero ht
  simple_zero := fun t ht => rootMultiplicity_protectedToZero_of_mem ht
  twoSection := protectedToZeroTwoSection T
  finiteBeta := LeanFormal.IUT.XiFPaper.Mzk1G1NoncriticalPsiComponentActual.finiteBeta_component

/-- The protected set is carried to a SINGLE value by the composite phi = q o psi. -/
theorem phi_collapses_protected {T : Finset ℚ} {q : Polynomial ℚ} {t : ℚ} (ht : t ∈ T) :
    Polynomial.eval t (q.comp (protectedToZeroPolynomial T)) = Polynomial.eval 0 q :=
  LeanFormal.IUT.XiFPaper.Mzk1G1BelyiCVCompositionActual.comp_eval_on_T ht

#print axioms noncriticalB1B3Component
#print axioms phi_collapses_protected
end LeanFormal.IUT.XiFPaper.Mzk1G1B1B3ComponentActual
