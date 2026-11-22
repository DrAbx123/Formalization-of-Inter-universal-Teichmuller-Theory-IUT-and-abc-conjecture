/- GK §7.3, batch δ2: assembly of boundary-distance functions on the product tuple space
from local lambda-coordinate functions and per-place distances.
REUSE: `Mzk1G1GKDeltaActual` (distances), `Mzk1G1GKProductActual` (`gkProductSpace`),
`Mzk1G1GKCompactInputShapeActual.gkCompactInputOfProduct`,
`Mzk1G1DisjointFamilyActual.GKCompactInput.exists_delta0`. DEDUP: no existing assembly. -/
import tmp.sheaf.xif.paper.Mzk1G1GKDeltaActual
import tmp.sheaf.xif.paper.Mzk1G1GKCompactInputShapeActual
import Mathlib.Topology.Order.Lattice
import Mathlib.Tactic

noncomputable section
open scoped Valued WithZeroTopology
open ValuativeRel
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaAssemblyActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProductActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjQuotientActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKCompactInputShapeActual

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable (L : ι → Type) [∀ i, NormedField (L i)] [∀ i, ValuativeRel (L i)]
  [∀ i, TopologicalSpace (L i)] [∀ i, IsNonarchimedeanLocalField (L i)]
  [∀ i, T2Space (L i)]

/-- The boundary-distance functions `delta_j`: `min over places i and points k of
dist_i(lambda_{j,i}(x i k))`. -/
def deltaOfDist (n d r : Nat) [NeZero d] (dist : ∀ i, L i → ℝ)
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i)
    (j : Fin (r + 1)) (x : gkProductSpace (L := L) n d) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (fun i =>
    Finset.univ.inf' Finset.univ_nonempty (fun k => dist i (lam j i (x i k))))

/-- `delta_j(x)` is bounded above by every local distance at the tuple points. -/
theorem deltaOfDist_le (n d r : Nat) [NeZero d] {dist : ∀ i, L i → ℝ}
    {lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i}
    {j : Fin (r + 1)} {x : gkProductSpace (L := L) n d} (i : ι) (k : Fin d) :
    deltaOfDist (L := L) n d r dist lam j x ≤ dist i (lam j i (x i k)) := by
  unfold deltaOfDist
  exact le_trans (Finset.inf'_le _ (Finset.mem_univ i))
    (Finset.inf'_le _ (Finset.mem_univ k))

/-- `delta_j` as a function on the tuple space. -/
noncomputable def deltaFun (n d r : Nat) [NeZero d] (dist : ∀ i, L i → ℝ)
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i)
    (j : Fin (r + 1)) : gkProductSpace (L := L) n d → ℝ :=
  fun x => deltaOfDist (L := L) n d r dist lam j x

/-- Assembly of the G-K compact input from per-place lambda functions and distances; the
continuity of the delta functions and their pointwise coverage are supplied as the chart-layer
obligations (next batch). -/
noncomputable def gkCompactInputOfLambda (n r d : Nat) [NeZero d]
    (dist : ∀ i, L i → ℝ) (hdist : ∀ i, Continuous (dist i))
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i)
    (hcont : ∀ j, Continuous (deltaFun (L := L) n d r dist lam j))
    (hcover : ∀ x : gkProductSpace (L := L) n d,
      ∃ j, 0 < deltaOfDist (L := L) n d r dist lam j x)
    (hn : 0 < n) : GKCompactInput n r :=
  gkCompactInputOfProduct (L := L) n r d hn (deltaOfDist (L := L) n d r dist lam)
    (fun j => hcont j) hcover

/-- `delta_j(x)` is positive as soon as every local distance at the tuple points is. -/
theorem deltaOfDist_pos_of (n d r : Nat) [NeZero d] {dist : ∀ i, L i → ℝ}
    {lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i}
    {j : Fin (r + 1)} {x : gkProductSpace (L := L) n d}
    (h : ∀ i k, 0 < dist i (lam j i (x i k))) :
    0 < deltaOfDist (L := L) n d r dist lam j x := by
  unfold deltaOfDist
  refine (Finset.lt_inf'_iff (Finset.univ_nonempty : (Finset.univ : Finset ι).Nonempty)).mpr ?_
  intro i _
  refine (Finset.lt_inf'_iff (Finset.univ_nonempty : (Finset.univ : Finset (Fin d)).Nonempty)).mpr ?_
  intro k _
  exact h i k

/-- **Cover reduction**: if at every tuple some family member has all local distances
positive, then the delta functions cover the tuple space pointwise. -/
theorem delta_cover_of_local_pos (n d r : Nat) [NeZero d] (dist : ∀ i, L i → ℝ)
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i)
    (h : ∀ x : gkProductSpace (L := L) n d, ∃ j, ∀ i k, 0 < dist i (lam j i (x i k))) :
    ∀ x : gkProductSpace (L := L) n d,
      ∃ j, 0 < deltaOfDist (L := L) n d r dist lam j x := by
  intro x
  obtain ⟨j, hj⟩ := h x
  exact ⟨j, deltaOfDist_pos_of (L := L) n d r (j := j) (x := x) hj⟩
#print axioms deltaOfDist_le
#print axioms gkCompactInputOfLambda
#print axioms deltaOfDist_pos_of
#print axioms delta_cover_of_local_pos
end LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaAssemblyActual