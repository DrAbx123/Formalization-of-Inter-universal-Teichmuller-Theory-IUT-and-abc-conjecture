/- G-K 7.3 local topology, batch 3: chart-0 point space vs ring homs, and the
product tuple space of route 7.3. -/
import tmp.sheaf.xif.paper.Mzk1G1PsiGKLocalTopologyBatch2Actual
import tmp.sheaf.xif.paper.Mzk1G1FermatOverlapActual
import tmp.sheaf.xif.paper.Mzk1G1UniversalHgenInterfaceActual
import Mathlib.Tactic

noncomputable section
open Polynomial MvPolynomial
namespace LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyBatch3Actual
open LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatAffineChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatSecondChartActual
open LeanFormal.IUT.XiFPaper.Mzk1G1FermatOverlapActual
open LeanFormal.IUT.XiFPaper.Mzk1G1UniversalHgenInterfaceActual

/-- The map from chart-0 ring homs to the chart-0 point set. -/
noncomputable def chart0HomToPoint (n : Nat) (L : Type) [Field L] [Algebra ℚ L]
    (φ : R n →+* L) : {p : L × L // p ∈ chart0Points n L} :=
  ⟨chart0PointOfHom n φ, chart0PointOfHom_mem n φ⟩

/-- The map from infinity-chart ring homs to the infinity-chart point set. -/
noncomputable def chartInfHomToPoint (n : Nat) (L : Type) [Field L] [Algebra ℚ L]
    (φ : R2 n →+* L) : {p : L × L // p ∈ chartInfPoints n L} :=
  ⟨chartInfPointOfHom n φ, chartInfPointOfHom_mem n φ⟩

/-- The point map of the chart-0 coordinates, unfolded. -/
theorem chart0HomToPoint_val (n : Nat) (L : Type) [Field L] [Algebra ℚ L]
    (φ : R n →+* L) :
    (chart0HomToPoint n L φ).1 = (φ (x0 n), φ (x1 n)) := rfl

/-- The product tuple space `X = prod_v Y_n(L_v)^d` of route 7.3: for each place `i`,
`d`-tuples of chart-0 points of the curve over the local field `L i`. -/
def gkProductSpace (n d : Nat) (ι : Type) [Fintype ι]
    (L : ι → Type) [∀ i, Field (L i)] [∀ i, Algebra ℚ (L i)] [∀ i, TopologicalSpace (L i)] :=
  (i : ι) → Fin d → chart0PointSpace n (L i)

#print axioms chart0HomToPoint_val
end LeanFormal.IUT.XiFPaper.Mzk1G1PsiGKLocalTopologyBatch3Actual
