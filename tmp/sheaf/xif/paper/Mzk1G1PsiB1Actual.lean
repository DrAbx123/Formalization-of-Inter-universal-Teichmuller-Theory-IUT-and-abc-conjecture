import tmp.sheaf.xif.paper.Mzk1G1PsiGlueCompatActual
import tmp.sheaf.xif.paper.Mzk1G1ProjectiveLineBoundaryActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiniteFiberActual
import tmp.sheaf.xif.paper.Mzk1G1PsiFiberFiniteActual
import tmp.sheaf.xif.paper.Mzk1G1PsiHPolyFinalActual
import Mathlib.Tactic

/-!
# HANDOFF (emmy -> team): B1 / b1FiniteProducer status

## Inventory (all DONE, three axioms, no placeholders)
* psi (unconditional): Mzk1G1PsiGlueCompatActual.psi, psi_ι_false, psi_ι_true
* hPoly (unconditional up to h != 0): Mzk1G1PsiHPolyFinalActual.hPoly (h) (hh), hPoly_ι_c0/c1/c2,
  hPoly_compat, hPolyCover, hPolyCover_iSup_opensRange
* phi (this file): phi n T h hh := psi n T ; hPoly h hh  (composition order: psi first)
* boundary bookkeeping (this file): B1FiniteProducer, AvoidsBoundary, boundarySetGlued_eq,
  boundaryPreimage_finite_of_each
* fibre finiteness chart-0: Mzk1G1PsiFiberFiniteActual.finite_primes_of_finite_quotient,
  finite_primes_of_psiChart0
* fibre finiteness chartInf / D(q): Mzk1G1PsiFiberFiniteInfActual.quot_finiteDim_psiInf,
  finite_primes_of_psiChartInf, finite_primes_of_psiChartInf_localized
  (scoped: 0 < n, T.Nonempty, 0 notin T; if 0 in T use T.erase 0, q drops that factor)
* quotient finiteness: Mzk1G1PsiQuotientFiniteActual.quot_finiteDim, chartRing_finite_g
* M2 algebraic skeleton: Mzk1G1PsiM2ProducerActual (AlgPoint, muMeasure, muMeasure_wf, M1 bridge);
  Mzk1G1PsiM2CoreActual (isRatPoint, muList, lex descent, ratToP1)

## Remaining gaps (assigned)
A (grace): bridge finite prime spectrum -> scheme-point fibres; for q in {0,1,infinity},
  (phi n T h hh).base preimage of {q} is finite.  Consume: finite_primes_of_psiChart0 /
  finite_primes_of_psiChartInf + psi_ι_false/true + hPoly_ι_c0/c1/c2 + the
  PrimeSpectrum <-> Spec.map point dictionary.
B (henry, Mzk1G1PsiM2AnalyticActual): analytic h.  For the finite algebraic set
  S1 = psi(S) union Branch(psi) (Branch(psi) has non-rational points: images of n-th roots of
  unity) produce h : Q[t], h != 0 with h(S1) subset {0,1,infinity},
  h(0) notin {0,1,infinity}, criticalValuesOverC h subset {0,1} and no critical point at
  values outside {0,1}.  Route 4.3 L304-317: Galois closure, measure (max reduced degree,
  total degree), rational Mobius with Cauchy bound R(d0) and B(d0), strict measure decrease,
  composition law.  Donors: Mzk1G1BelyiCVCompositionActual.comp_criticalValues_subset,
  cvCompositionLaw_proved, comp_T_avoids_specialSet, comp_preserves_values.  Rational base
  case available: Mzk1G1PsiM2ProducerActual.mzk1Lemma24Target_of_finite (three axioms).
C (andrew): scheme-level psi(T) = {0} (B2): choose the rational protected set T' so that
  psi n T' maps the points to avoid to 0; then phi(T) = {h(0)} and T-avoidance follows from
  h(0) notin {0,1,infinity} (B).  Chart-level donors: Mzk1G1NoncriticalPsiActual and
  psi_ι_false/true.

## Chart-direction ruling (Lead, 22:2x): psi -> psiFixed
The current psi (henry) sends the protected divisor D_T to the point lambda = infinity, because
psiChart0 = chartMorphismInf (psiChart0Coord) with psiChart0Coord = prod (x - t_i), so that
psiChart0Coord = 0 lands at t = 0, i.e. lambda = infinity.  Route B2 requires
psi^{-1}(0) = D_T, so andrew is writing Mzk1G1PsiFixedActual.psiFixed (same cover, chart
assignments swapped, psiFixed = inv o psi with inv the P1 involution).  Once psiFixed lands,
phi becomes psiFixed ≫ hPoly h hh here, and the Branch bookkeeping is
Branch(psiFixed) = inv(Branch(psi)) (for henry's analytic h).

## Interface lemma (deferred until A/C statements land)
Once A, B, C are available, b1FiniteProducer is a three-line assembly:
  boundaryPreimage_finite_of_each (A for the three points) + h(0) notin specialSet (B) + C.
Stating a reduction interface now would risk vacuous or mis-shaped hypotheses, so it is
deliberately deferred; the exact assembly is recorded above.
-/


/-!
# B1 final target (route §4): the finite-boundary producer

Target (verbatim interface agreed with andrew's G-K lane):

  B1FiniteProducer n :=
    forall T : Finset (fermatCurveScheme n),
      exists phi : fermatCurveScheme n ⟶ projectiveLineGlued,
        (phi.base ⁻¹' boundarySetGlued).Finite /\ (forall x in T, phi.base x notin boundarySetGlued)

The actual phi is hPoly composed with the unconditional psi of Mzk1G1PsiGlueCompatActual:
  phi := hPoly n T \circ psi n T,
where hPoly comes from henry's Mzk1G1PsiHPolyFinalActual (route §4.4, DONE: pieces/chart maps/
overlap compatibility), and the finite-beta polynomial h of route §4.3 is supplied by the M2
algebraic-point recursion (Mzk1G1PsiM2ProducerActual + M1 base case for the rational end).

This file contains the unconditional bookkeeping that does not depend on hPoly yet.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineBoundaryActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiFiniteFiberActual

variable (n : Nat)

/-- The B1 target: for every finite set T of points to avoid, there is a morphism Y_n -> P^1
with finite boundary preimage and avoiding the boundary on T. -/
def B1FiniteProducer : Prop :=
  ∀ T : Finset (fermatCurveScheme n),
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (φ.base ⁻¹' boundarySetGlued).Finite ∧
        (∀ x ∈ T, φ.base x ∉ boundarySetGlued)

open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGlueCompatActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiHPolyFinalActual

/-- The actual composite morphism: phi = psi (unconditional, henry 19:54) followed by
hPoly (henry 22:09, unconditional up to h != 0). -/
noncomputable def phi (n : Nat) (T : Finset ℚ) (h : Polynomial ℚ) (hh : h ≠ 0) :
    fermatCurveScheme n ⟶ projectiveLineGlued :=
  psi n T ≫ hPoly h hh

/-- The T-avoidance predicate. -/
def AvoidsBoundary (φ : fermatCurveScheme n ⟶ projectiveLineGlued)
    (T : Finset (fermatCurveScheme n)) : Prop :=
  ∀ x ∈ T, φ.base x ∉ boundarySetGlued

/-- The boundary set is the union of the three points. -/
theorem boundarySetGlued_eq :
    boundarySetGlued = p1Zero ∪ p1One ∪ p1Infinity := rfl

/-- Finiteness of the boundary preimage reduces to the three point fibres. -/
theorem boundaryPreimage_finite_of_each (φ : fermatCurveScheme n ⟶ projectiveLineGlued)
    (h0 : (φ.base ⁻¹' p1Zero).Finite) (h1 : (φ.base ⁻¹' p1One).Finite)
    (h2 : (φ.base ⁻¹' p1Infinity).Finite) :
    (φ.base ⁻¹' boundarySetGlued).Finite := by
  rw [boundarySetGlued_eq]
  exact ((h0.union h1).union h2)

#print axioms boundarySetGlued_eq
#print axioms boundaryPreimage_finite_of_each
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual