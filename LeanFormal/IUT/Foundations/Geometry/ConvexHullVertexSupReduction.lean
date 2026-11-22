import Mathlib.Analysis.Convex.Jensen
import Mathlib.Data.ENNReal.Real

/-!
# Vertex reduction for sup-type volumes over convex hulls of finite vertex sets

Mechanical piece for the geometric route (iii) of the hunit normalization
obligation (task `hunit-epsilon-transfer-20261016`; consumer chain
`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume` of
`ABCBridge/Bridge/Cor312ComparisonGapSupplyLayer.lean:167` and its reshaped
epsilon form in `HunitEpsilonTransferReduction.lean`).

The value-realized hull volume of a region `S` is the sup-type volume

`sourceSetVolume v S = iSup_{x in S} ENNReal.ofReal (sourceLocalLogDegree v x)`

(`SourceImageHullVolume.lean:188`).  The geometric route models the holomorphic
hull as the convex hull of the finitely many possible theta-pilot images
(vertices).  The lemmas below are the vertex reduction: for a convex integrand,
the hull sup equals the vertex sup, so the hull bound needs to be verified only
on the vertices (the finite possible-image family).  This is the sup-volume
analogue of the maximum principle; the segment case is Mathlib's
`ConvexOn.le_max_of_mem_segment` (`Analysis/Convex/Jensen.lean:392`).

Mathlib status (correction of the outsider-survey note, recorded in the task
report): the real-valued Finset maximum principle already exists in the pinned
snapshot as `ConvexOn.le_sup_of_mem_convexHull`
(`Analysis/Convex/Jensen.lean:341`) and `ConvexOn.exists_ge_of_mem_convexHull`
(`.lean:377`); the lemmas below build on it and add the `ENNReal`-valued sup
reduction in the exact `iSup ofReal` shape of the source set volume, which is
not in Mathlib.

Paper anchors: IUT III, Corollary 3.12 statement (theta-pilot possible images,
their union, and the holomorphic hull of the union; corpus lines 10324-10337);
Remark 3.9.5, (i) (`lambda * O` hull form), (ii) (P1)-(P3) and the intersection
display, (iii) (the hull log-volume sandwich).  The convex-hull vertex model is
the reduction's carrier-side shape, not a paper statement; the lemmas below
assert no carrier, no hull construction and no normalization.

Scope: pure order/convexity lemmas over real vector spaces.
-/

namespace LeanFormal.IUT

universe u

/-- **Vertex reduction for sup-type volumes, containment form.**  If a region
`S` (the hull model) is contained in the convex hull of a finite vertex set `t`,
then the sup-type volume `iSup ENNReal.ofReal (f .)` over `S` is bounded by the
vertex sup whenever the integrand `f` is convex on that convex hull.  Proof: the
finite real maximum principle (`ConvexOn.exists_ge_of_mem_convexHull`) bounds
every point value by a vertex value; `ENNReal.ofReal` is monotone and `ENNReal`
is a complete lattice.  This is the form consumed by the geometric route, where
only `hull ⊆ convexHull (vertices)` is established. -/
theorem iSup_ofReal_le_iSup_vertices_of_subset_convexHull {E : Type u} [AddCommGroup E]
    [Module Real E] {f : E → Real} {t : Finset E} {S : Set E}
    (hS : S ⊆ convexHull Real (t : Set E))
    (hf : ConvexOn Real (convexHull Real (t : Set E)) f) :
    (⨆ x ∈ S, ENNReal.ofReal (f x)) ≤ ⨆ i ∈ t, ENNReal.ofReal (f i) := by
  refine iSup₂_le fun x hx => ?_
  obtain ⟨y, hy, hxy⟩ :=
    hf.exists_ge_of_mem_convexHull (subset_convexHull Real (t : Set E)) (hS hx)
  exact le_trans (ENNReal.ofReal_le_ofReal hxy)
    (le_iSup_of_le y (le_iSup_of_le hy le_rfl))

/-- **Vertex reduction for sup-type volumes, equality form.**  For an integrand
convex on the convex hull of a finite vertex set `t`, the sup-type volume over
the vertices' convex hull equals the vertex sup: the vertices lie in their own
convex hull, and the maximum principle bounds the hull by the vertices. -/
theorem convexHull_iSup_ofReal_eq_iSup_vertices {E : Type u} [AddCommGroup E]
    [Module Real E] (f : E → Real) {t : Finset E}
    (hf : ConvexOn Real (convexHull Real (t : Set E)) f) :
    (⨆ x ∈ convexHull Real (t : Set E), ENNReal.ofReal (f x)) =
      ⨆ i ∈ t, ENNReal.ofReal (f i) := by
  refine le_antisymm ?_ ?_
  · exact iSup_ofReal_le_iSup_vertices_of_subset_convexHull
      (subset_refl (convexHull Real (t : Set E))) hf
  · refine iSup₂_le fun i hi => ?_
    exact le_iSup_of_le i
      (le_iSup_of_le (subset_convexHull Real (t : Set E) hi) le_rfl)

end LeanFormal.IUT
