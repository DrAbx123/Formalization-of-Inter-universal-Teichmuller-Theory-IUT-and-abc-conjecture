/- GK §7.3 assembly: package the analytic input `GKCompactInput` from the product tuple
space `X = prod_i (ProjY (L i))^d` plus the boundary-distance functions `delta_i`.
Only `delta` (continuity + pointwise coverage) remains to be built from the morphisms
`phi_i`; this file closes the X/top/comp/non part of the interface. -/
import tmp.sheaf.xif.paper.Mzk1G1GKProductActual
import tmp.sheaf.xif.paper.Mzk1G1DisjointFamilyActual
import Mathlib.Tactic

noncomputable section
open scoped Valued WithZeroTopology
open ValuativeRel
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKCompactInputShapeActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProductActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjectiveCompactActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjQuotientActual

variable {ι : Type} [Fintype ι]
variable (L : ι → Type) [∀ i, NormedField (L i)] [∀ i, ValuativeRel (L i)]
  [∀ i, TopologicalSpace (L i)] [∀ i, IsNonarchimedeanLocalField (L i)]
  [∀ i, T2Space (L i)]

/-- **Assembly of the G-K compact input.** The product tuple space (compact, nonempty)
is already fixed; the boundary-distance functions `delta_i` and their two properties are
the remaining analytic content (built from the morphisms `phi_i` in the next batch). -/
noncomputable def gkCompactInputOfProduct (n r d : Nat) (hn : 0 < n)
    (delta : Fin (r + 1) → gkProductSpace (L := L) n d → ℝ)
    (hcont : ∀ i, Continuous (delta i))
    (hcover : ∀ x, ∃ i, 0 < delta i x) : GKCompactInput n r where
  X := gkProductSpace (L := L) n d
  top := inferInstance
  comp := gkProductSpace_compactSpace (L := L) n d
  non := gkProductSpace_nonempty (L := L) n d hn
  delta := delta
  delta_cont := hcont
  delta_cover := hcover

/-- Route §7.3: compactness yields a fixed positive minimum of the maximal boundary
distance, for the assembled product input. -/
theorem exists_delta0_of_product (n r d : Nat) (hn : 0 < n)
    (delta : Fin (r + 1) → gkProductSpace (L := L) n d → ℝ)
    (hcont : ∀ i, Continuous (delta i))
    (hcover : ∀ x, ∃ i, 0 < delta i x) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ x, ∃ i, δ₀ ≤ delta i x :=
  (gkCompactInputOfProduct (L := L) n r d hn delta hcont hcover).exists_delta0

#print axioms gkCompactInputOfProduct
#print axioms exists_delta0_of_product
end LeanFormal.IUT.XiFPaper.Mzk1G1GKCompactInputShapeActual