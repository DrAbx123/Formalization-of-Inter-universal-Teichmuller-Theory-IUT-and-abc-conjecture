/- G-K 7.3 local topology, batch 4: the product tuple space `X` and its nonemptiness. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGKLocalTopologyBatch3Actual
import Mathlib.Tactic

noncomputable section
open Polynomial MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyBatch4Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyBatch3Actual

/-- The underlying point of a chart-0 point space, as a pair. -/
theorem chart0PointSpace_val (n : Nat) (L : Type) [Field L] [Algebra ℚ L]
    [TopologicalSpace L] (p : chart0PointSpace n L) :
    (p.1 : L × L) ∈ chart0Points n L := p.2

/-- Nonemptiness of a product tuple space from nonemptiness of each chart space. -/
theorem gkProductSpace_nonempty (n d : Nat) (ι : Type) [Fintype ι]
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra ℚ (L i)] [∀ i, TopologicalSpace (L i)]
    (h : ∀ i, Nonempty (chart0PointSpace n (L i))) :
    Nonempty (gkProductSpace n d ι L) :=
  ⟨fun i _ => (h i).some⟩

#print axioms chart0PointSpace_val
#print axioms gkProductSpace_nonempty
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyBatch4Actual
