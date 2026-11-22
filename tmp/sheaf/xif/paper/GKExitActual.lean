/- G-K exit alignment (route §7): adapters from the G-C B1 producer to the
route §7.1 family, and the §7.3 GKData assembly with the route quantifier order. -/
import tmp.sheaf.xif.paper.Mzk1G1DisjointFamilyActual
import tmp.sheaf.xif.paper.Mzk1G1FiniteDisjointBelyiActual
import tmp.sheaf.xif.paper.Mzk1G1KvCompactActual
import Mathlib.Tactic
noncomputable section
open AlgebraicGeometry CategoryTheory
namespace LeanFormal.IUT.XiFPaper.GKExitActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
open LeanFormal.IUT.XiFPaper.G1FiniteDisjointBelyiActual
open LeanFormal.IUT.XiFPaper.G1KvCompactActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatCurveActual
open LeanFormal.IUT.XiFPaper.Mzk1G1ProjectiveLineGluedActual
/-- The G-C producer shape (canonical boundary, `boundaryPreimageGlued`). -/
def GCB1FiniteProducer (n : ℕ) : Prop :=
  ∀ T : Finset (fermatCurveScheme n),
    ∃ φ : fermatCurveScheme n ⟶ projectiveLineGlued,
      (Mzk1G1ProjectiveLineBoundaryActual.boundaryPreimageGlued φ).Finite ∧
        (∀ x ∈ T, x ∉ Mzk1G1ProjectiveLineBoundaryActual.boundaryPreimageGlued φ)
/-- The G-C producer gives the section 7.1 finite producer. -/
theorem b1FiniteProducer_of_GC (n : ℕ) (h : GCB1FiniteProducer n) : B1FiniteProducer n := by
  intro T
  obtain ⟨φ, hfin, havoid⟩ := h T
  refine ⟨φ, ?_, ?_⟩
  · rwa [← gluedBoundaryPreimage_eq n φ] at hfin
  · intro x hx hmem
    exact havoid x hx (by rwa [gluedBoundaryPreimage_eq n φ] at hmem)
/-- Route §7.1 exit: from the G-C producer one gets the finite disjoint family
`GluedBelyiFamily` with `r = d * |V|` (E1 proven, not assumed). -/
theorem hasGluedBelyiFamily_of_GC (n d : ℕ) (V : Finset ℕ) (h : GCB1FiniteProducer n) :
    HasGluedBelyiFamily n d V :=
  hasGluedBelyiFamily_of_b1 n d V (b1StepProducer_of_finite (b1FiniteProducer_of_GC n h))
#print axioms b1FiniteProducer_of_GC
#print axioms hasGluedBelyiFamily_of_GC
end LeanFormal.IUT.XiFPaper.GKExitActual