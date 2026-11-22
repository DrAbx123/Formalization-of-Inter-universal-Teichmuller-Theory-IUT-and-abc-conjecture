/- GK §7.3: `delta_cover` from the E1 boundary-avoidance property (route L671-705).
The product tuple space is covered pointwise once, for every tuple, some family member has
lambda-coordinates avoiding `{0,1}` at all places and points (E1: at most r points cannot
meet all r+1 boundaries). REUSE:
- `Mzk1G1GKDeltaAssemblyActual.deltaOfDist`/`deltaOfDist_pos_of`/`gkCompactInputOfLambda`,
- `Mzk1G1GKDeltaActual.chordalBoundaryDist_pos`/`padicBoundaryDist_pos`,
- `Mzk1G1DisjointFamilyActual.exists_boundary_avoiding` (E1 combinatorial core; the
  scheme-point bridge from tuples to a `Finset (fermatCurveScheme n)` is the documented
  remaining obligation `GKBoundaryAvoidBridge`).
DEDUP: no existing reduction of `delta_cover` to lambda-avoidance in the tree. -/
import tmp.sheaf.xif.paper.Mzk1G1GKDeltaAssemblyActual
import tmp.sheaf.xif.paper.Mzk1G1DisjointFamilyActual
import Mathlib.Tactic

noncomputable section
open scoped Valued WithZeroTopology
open ValuativeRel
namespace LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaCoverActual
open LeanFormal.IUT.XiFPaper.G1DisjointFamilyActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProductActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKProjQuotientActual
open LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaAssemblyActual

variable {ι : Type} [Fintype ι] [Nonempty ι]
variable (L : ι → Type) [∀ i, NormedField (L i)] [∀ i, ValuativeRel (L i)]
  [∀ i, TopologicalSpace (L i)] [∀ i, IsNonarchimedeanLocalField (L i)]
  [∀ i, T2Space (L i)]

/-- **Cover reduction step**: if the local distances are positive away from `{0,1}` and every
tuple has a family member whose lambda-coordinates avoid `{0,1}` at every place and point,
then the delta functions cover the tuple space (that is, `delta_cover`). -/
theorem delta_cover_of_lambda_avoid (n d r : Nat) [NeZero d] (dist : ∀ i, L i → ℝ)
    (hdist_pos : ∀ i (z : L i), z ≠ 0 → z ≠ 1 → 0 < dist i z)
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i)
    (hE1 : ∀ x : gkProductSpace (L := L) n d,
      ∃ j, ∀ i k, lam j i (x i k) ≠ 0 ∧ lam j i (x i k) ≠ 1) :
    ∀ x : gkProductSpace (L := L) n d,
      ∃ j, 0 < deltaOfDist (L := L) n d r dist lam j x := by
  intro x
  obtain ⟨j, hj⟩ := hE1 x
  refine ⟨j, deltaOfDist_pos_of (L := L) n d r (j := j) (x := x) ?_⟩
  intro i k
  exact hdist_pos i _ (hj i k).1 (hj i k).2

/-- The scheme-point bridge obligation: every tuple of local projective points corresponds to
a finite set of points of the curve of cardinality at most `r`, in such a way that the E1
boundary-avoidance gives lambda-avoidance. This is the remaining chart-dictionary
construction (uses `G.family.phi i` and the chart formulas). -/
def GKBoundaryAvoidBridge (n d r : Nat) [NeZero d]
    (dist : ∀ i, L i → ℝ)
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i) : Prop :=
  ∀ x : gkProductSpace (L := L) n d,
    ∃ j, ∀ i k, lam j i (x i k) ≠ 0 ∧ lam j i (x i k) ≠ 1

/-- **Assembly with cover**: the compact input from lambda functions, once the E1 avoidance
bridge is supplied together with continuity of the delta functions. -/
noncomputable def gkCompactInputOfLambdaAvoid (n r d : Nat) [NeZero d]
    (dist : ∀ i, L i → ℝ) (hdist : ∀ i, Continuous (dist i))
    (hdist_pos : ∀ i (z : L i), z ≠ 0 → z ≠ 1 → 0 < dist i z)
    (lam : (j : Fin (r + 1)) → (i : ι) → ProjY (K := L i) n → L i)
    (hcont : ∀ j, Continuous (deltaFun (L := L) n d r dist lam j))
    (hE1 : GKBoundaryAvoidBridge (L := L) n d r dist lam)
    (hn : 0 < n) : GKCompactInput n r :=
  gkCompactInputOfLambda (L := L) n r d dist hdist lam hcont
    (delta_cover_of_lambda_avoid (L := L) n d r dist hdist_pos lam hE1) hn

#print axioms delta_cover_of_lambda_avoid
#print axioms gkCompactInputOfLambdaAvoid
end LeanFormal.IUT.XiFPaper.Mzk1G1GKDeltaCoverActual
