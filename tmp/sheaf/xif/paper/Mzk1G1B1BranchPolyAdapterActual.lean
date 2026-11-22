import tmp.sheaf.xif.paper.Mzk1G1B1FinalHAvoidActual
import tmp.sheaf.xif.paper.Mzk1G1B1DTFixedMonoActual
import tmp.sheaf.xif.paper.Mzk1G1B2Fixed4Actual
import Mathlib.Tactic

/-!
# B1 with a PsiPoly-protected set: interface adapter (no new mathematics)

b1FiniteProducer_of_branch (Mzk1G1B1FinalHAvoidActual) consumes, for every T, a rational
protected set Tr with (T : Set _) subset DTFixed n Tr.  For the general (Galois stable) T the
protected set will instead be the zero divisor D_T of the explicit psi produced by
Mzk1G1B2PsiPolyActual (grace, in progress).

This file records the purely formal adapter: a family of protected sets DTPoly together with
the covering hypothesis that on the given finite T the PsiPoly-protected set is contained in
some DTFixed n Tr produces B1FiniteProducer.  No new hypothesis on T, no change of target.

Expected instantiation (once grace's file lands):
  DTPoly T := zero divisor of psiPoly n T  (as a set of points of the curve),
  hbranchPoly: the psiPoly side gives T inside DTPoly T and h with h(0) outside {0,1},
  hcover: the PsiPoly zero divisor is contained in DTFixed n Tr for a suitable rational Tr.
-/

noncomputable section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Polynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1BranchPolyAdapterActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiB1Actual
open LeanFormal.IUT.XiFPaper.B1FinalHAvoidActual
open LeanFormal.IUT.XiFPaper.Mzk1G1B2FixedActual

/-- B1 from a PsiPoly-style protected set family. -/
theorem b1FiniteProducer_of_branchPoly (n : Nat) (hn : 0 < n)
    (DTPoly : Finset (fermatCurveScheme n) → Set (fermatCurveScheme n))
    (hbranchPoly : ∀ T : Finset (fermatCurveScheme n),
      ∃ (h : Polynomial ℚ) (hh : h ≠ 0),
        0 < h.natDegree ∧ (T : Set (fermatCurveScheme n)) ⊆ DTPoly T ∧
          h.eval 0 ∉ ({0, 1} : Set ℚ))
    (hcover : ∀ T : Finset (fermatCurveScheme n),
      ∃ Tr : Finset ℚ, Tr.Nonempty ∧
        ((T : Set (fermatCurveScheme n)) ∩ DTPoly T) ⊆ DTFixed n Tr) :
    B1FiniteProducer n := by
  refine LeanFormal.IUT.XiFPaper.B1FinalHAvoidActual.b1FiniteProducer_of_branch n hn ?_
  intro T
  obtain ⟨h, hh, hdeg, hsub, h0⟩ := hbranchPoly T
  obtain ⟨Tr, hTr, hTTr⟩ := hcover T
  refine ⟨Tr, h, hh, hTr, hdeg, ?_, h0⟩
  exact fun x hx => hTTr ⟨hx, hsub hx⟩

#print axioms b1FiniteProducer_of_branchPoly
end LeanFormal.IUT.XiFPaper.Mzk1G1BranchPolyAdapterActual