import LeanFormal.IUT.Foundations.Geometry.ConvexHullVertexSupReduction

/-!
# Mzk1HullVertexBoundConsumerActual — real consumer: hull-volume bound from vertex bounds

Status: PENDING-VERIFY. No sorry, no axiom.
Consumer (not adapted copy): combines the existing vertex-sup reduction
`iSup_ofReal_le_iSup_vertices_of_subset_convexHull` with monotonicity of
`ENNReal.ofReal` to derive: a uniform vertex bound for a convex integrand bounds
the sup-type hull volume. This is the geometric-route consumer shape for the
Cor 3.12 / hunit normalization prerequisite; it proves no paper statement itself. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullVertexBoundConsumerActual

open LeanFormal.IUT

universe u

/-- Real consumer: hull sup-volume bounded by ENNReal.ofReal of a vertex bound. -/
theorem hull_volume_le_of_vertex_bound {E : Type u} [AddCommGroup E] [Module Real E]
    {f : E → Real} {t : Finset E} {S : Set E} {b : Real}
    (hS : S ⊆ convexHull Real (t : Set E))
    (hf : ConvexOn Real (convexHull Real (t : Set E)) f)
    (hb : ∀ i ∈ t, f i ≤ b) :
    (⨆ x ∈ S, ENNReal.ofReal (f x)) ≤ ENNReal.ofReal b := by
  calc
    (⨆ x ∈ S, ENNReal.ofReal (f x))
        ≤ ⨆ i ∈ t, ENNReal.ofReal (f i) :=
      LeanFormal.IUT.iSup_ofReal_le_iSup_vertices_of_subset_convexHull hS hf
    _ ≤ ENNReal.ofReal b :=
      iSup₂_le fun i hi => ENNReal.ofReal_le_ofReal (hb i hi)

/-- Real consumer: equality form plus a vertex bound bounds the hull sup-volume. -/
theorem hull_volume_le_of_eq_vertex_bound {E : Type u} [AddCommGroup E] [Module Real E]
    {f : E → Real} {t : Finset E} {b : Real}
    (hf : ConvexOn Real (convexHull Real (t : Set E)) f)
    (hb : ∀ i ∈ t, f i ≤ b) :
    (⨆ x ∈ convexHull Real (t : Set E), ENNReal.ofReal (f x)) ≤ ENNReal.ofReal b := by
  calc
    (⨆ x ∈ convexHull Real (t : Set E), ENNReal.ofReal (f x))
        = ⨆ i ∈ t, ENNReal.ofReal (f i) :=
      LeanFormal.IUT.convexHull_iSup_ofReal_eq_iSup_vertices f hf
    _ ≤ ENNReal.ofReal b :=
      iSup₂_le fun i hi => ENNReal.ofReal_le_ofReal (hb i hi)

end LeanFormal.IUT.XiFPaper.Mzk1HullVertexBoundConsumerActual
