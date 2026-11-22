import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HunitEpsilonTransferReduction
import LeanFormal.IUT.Foundations.Geometry.ConvexHullVertexSupReduction

/-!
# Card B: vertex finiteness, finite vertex checks for hunit, and the conditional convexity card

Task `hunit-epsilon-transfer-20261016`, Card B continuation (see
`logs/coordination/hunit-epsilon-transfer-20261016.md`, section 6): the vertex
interface of the hunit normalization obligation,
(hull = convex hull of vertices) + (logDegree convexity / degree geometry) +
(vertex finiteness), with the consumer chain
`cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound` (T3 of
`HunitEpsilonTransferReduction.lean`) ->
`cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume`
(`Cor312ComparisonGapSupplyLayer.lean:167`) -> the gap assembly
(`Cor312ComparisonGapReduction.lean:367`).

Contents:

* `possibleThetaPilotImageSet_finite`: the union of the possible theta-pilot
  images is a finite set (its index type `SignedLabel l.value` is a `Fintype`).
* `sourceSetVolume_possibleImageSet_eq_labelSup`: the sup-type log-volume of
  the image union is the supremum over the finitely many signed labels — the
  vertex check in its finite, label-indexed form.  The image set is the range
  of the label-to-point map, so this is a pure reindexing with no degree
  faithfulness hypothesis (contrast the explicit theta-value identity
  `sourceSetVolume_possibleImage_eq`, `SourceImageHullVolume.lean:220`, which
  is conditional on degree faithfulness).
* `cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound` /
  `..._of_labelVolumeBound` / `..._of_labelEpsilonBound`: the hunit input of
  the gap assembly follows from a lower bound checked at the image union / at
  the finite labels (sharp or epsilon shape).  These wirings use only the
  existing monotonicity `sourceHullVolume_ge_imageVolume`
  (`SourceImageHullVolume.lean:209`) — the hull contains the image union, so
  the "verify only at the vertices" direction for hunit needs no convexity.
* `SourceHullConvexVertexData`: the **named conditional card** standing in for
  the missing hull geometry: a real vector space `E`, a map `toE` of global
  value points into `E`, a convex `g : E -> Real` on the convex hull of the
  vertex images, agreement of `g` with `sourceLocalLogDegree` on the hull,
  vertex domination, and the vertices-on-the-hull direction.
* `sourceHullVolume_le_vertices_of_convexVertexData`: the conditional upper
  reduction `hull volume <= vertex volume` — the first consumer of the vertex
  reduction `iSup_ofReal_le_iSup_vertices_of_subset_convexHull` of
  `Foundations/Geometry/ConvexHullVertexSupReduction.lean`.
* `vertices_le_sourceHullVolume_of_convexVertexData` and
  `sourceHullVolume_eq_vertices_of_convexVertexData`: the reverse direction
  (vertices on the hull; no geometry) and the conditional volume-level
  identification `hull volume = vertex volume`.

Honesty labels:
* The convexity card is a **conditional form**: no datum of this shape is
  constructed anywhere in the tree.  The direct route is not merely unproved
  but unsayable at the current layer: `ThetaPilotPoint v` is a multiplicative
  value-monoid point space (`SourceImageHull.lean`), `sourceLocalLogDegree` is
  additive over `*` (`sourceLocalLogDegree_mul`,
  `SourceImageHullVolume.lean:115`) and there is no `Real`-module structure to
  state convexity against.  The card's `(E, toE, g, convexOn_g)` fields are
  exactly that named gap; route (iii) (Card A) remains open and untouched.
* The paper claims no convex-hull identification of the holomorphic hull; that
  identification is the card, not a proved statement.
* No frozen file is modified; the concurrent `IQHullValueCarrierWiring.lean`
  is not imported.

Paper anchors: IUT III, Corollary 3.12 (corpus `Inter-universal Teichmuller
Theory III.txt:10324-10338`: the holomorphic hull of the union of the possible
images of a Theta-pilot object; the signed labels `j` of Remark 3.1.1, (ii));
Remark 3.9.5, (i)-(iii).
-/

namespace LeanFormal.IUT

universe ua uv upi umon ui uE

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Vertex finiteness and the finite vertex checks for hunit -/

/-- **Vertex finiteness.**  The union of the possible theta-pilot images is
finite: it is the range of the label-to-point map over the finite type of
signed labels. -/
theorem possibleThetaPilotImageSet_finite (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (I.possibleThetaPilotImageSet v R n).Finite := by
  have hrange : I.possibleThetaPilotImageSet v R n =
      Set.range (fun j : SignedLabel l.value => I.sourceThetaPilotPoint v R n j) := by
    ext x
    rw [I.mem_possibleThetaPilotImageSet_iff v R n x, Set.mem_range]
    exact exists_congr fun j => eq_comm
  rw [hrange]
  exact Set.finite_range _

/-- **Label-indexed form of the image-union log-volume.**  The sup-type
log-volume of the possible images is the supremum over the finitely many
signed labels of the point log-degrees: the finite vertex check, obtained by
reindexing along the label-to-point map; no degree-faithfulness hypothesis. -/
theorem sourceSetVolume_possibleImageSet_eq_labelSup (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) =
      ⨆ j : SignedLabel l.value,
        ENNReal.ofReal (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j)) := by
  unfold sourceSetVolume sourcePointVolume
  refine le_antisymm ?_ ?_
  · refine iSup₂_le fun x hx => ?_
    obtain ⟨j, rfl⟩ := (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
    exact le_iSup_of_le j le_rfl
  · refine iSup_le fun j => ?_
    exact le_iSup_of_le (I.sourceThetaPilotPoint v R n j)
      (le_iSup_of_le (I.sourceThetaPilotPoint_mem v R n j) le_rfl)

/-- **Hunit from a bound checked at the possible images (vertices).**  If the
degree bound is at most the log-volume of the image union plus `D0`, then the
hunit input of the Corollary 3.12 gap assembly holds: the hull contains the
image union (`sourceHullVolume_ge_imageVolume`), so its log-volume dominates
it.  This is a sufficient vertex check; convexity is not used. -/
theorem cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : Real} (hD₀ : 0 ≤ D₀)
    (hvb : ENNReal.ofReal D.degreeBound ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) + ENNReal.ofReal D₀) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_degreeBound_le_hullVolume v R n D hD₀
    (le_trans hvb
      (add_le_add (I.sourceHullVolume_ge_imageVolume v R n) (le_refl (ENNReal.ofReal D₀))))

/-- **Hunit from the finite label check.**  The same wiring with the check
stated over the finitely many signed labels, via
`sourceSetVolume_possibleImageSet_eq_labelSup` — the literal "verify only at
the vertices" form of the hunit normalization input. -/
theorem cor312GapSupply_sourceInterface_hunit_of_labelVolumeBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : Real} (hD₀ : 0 ≤ D₀)
    (hlb : ENNReal.ofReal D.degreeBound ≤
      (⨆ j : SignedLabel l.value,
        ENNReal.ofReal (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) +
        ENNReal.ofReal D₀) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀ :=
  I.cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound v R n D hD₀ (by
    rwa [sourceSetVolume_possibleImageSet_eq_labelSup])

/-- **Hunit from the epsilon-shaped finite label check (T3 wiring).**  The
epsilon form of the label check feeds the reshaped hunit input
`cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound`
(`HunitEpsilonTransferReduction.lean:118`), i.e. the vertex check is
consumable in the epsilon shape produced by epsilon-absorbed estimates. -/
theorem cor312GapSupply_sourceInterface_hunit_of_labelEpsilonBound (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) {D₀ : Real} (hD₀ : 0 ≤ D₀)
    (hε : ∀ ε : NNReal, 0 < ε →
      ENNReal.ofReal D.degreeBound ≤
        (⨆ j : SignedLabel l.value,
          ENNReal.ofReal (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) +
          ENNReal.ofReal D₀ + (ε : ENNReal)) :
    (I.sourceUnitRegionHaarInterface v R n D).logVolume
        (I.sourceUnitRegionHaarInterface v R n D).unitRegion ≤
      (I.sourceUnitRegionHaarInterface v R n D).logVolume
          (I.sourceUnitRegionHaarInterface v R n D).hull + ENNReal.ofReal D₀ := by
  refine I.cor312GapSupply_sourceInterface_hunit_of_epsilon_hullBound v R n D hD₀ ?_
  intro ε hε0
  have hle : (⨆ j : SignedLabel l.value,
        ENNReal.ofReal (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) ≤
      I.sourceHullVolume v R n := by
    rw [← sourceSetVolume_possibleImageSet_eq_labelSup]
    exact I.sourceHullVolume_ge_imageVolume v R n
  exact le_trans (hε ε hε0)
    (add_le_add (add_le_add hle (le_refl (ENNReal.ofReal D₀))) (le_refl (ε : ENNReal)))

/-! ## 2. The conditional convexity card and the volume-level identification -/

/-- **Card B, named conditional datum.**  The missing geometric identification
of the source holomorphic hull with the convex hull of finitely many vertices,
in a real vector space `E`: a map `toE` of global value points into `E`, a
convex function `g` on the convex hull of the vertex images, agreement of `g`
with the source log-degree on the hull, domination of `g` by the vertex
log-degrees at the vertices, and the vertices-on-the-hull direction.  No datum
of this shape is constructed in the tree; this structure is the conditional
form of the geometric input of route (iii) (Card A, untouched). -/
structure SourceHullConvexVertexData (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (E : Type uE) [AddCommGroup E] [Module Real E] where
  /-- The model map of global value points into the real vector space. -/
  toE : I.ThetaPilotPoint v → E
  /-- The convex model of the log-degree on the convex hull of the vertex images. -/
  g : E → Real
  /-- The finite vertex list. -/
  vertices : Finset (I.ThetaPilotPoint v)
  /-- The vertices lie on the hull. -/
  vertices_subset_hull :
    ∀ i ∈ vertices, i ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))
  /-- Every hull point maps into the convex hull of the vertex images. -/
  hull_image_subset_convexHull :
    ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      toE x ∈ convexHull Real (toE '' (vertices : Set (I.ThetaPilotPoint v)))
  /-- The model function is convex on that convex hull. -/
  convexOn_g :
    ConvexOn Real (convexHull Real (toE '' (vertices : Set (I.ThetaPilotPoint v)))) g
  /-- On the hull, the model function reproduces the source log-degree. -/
  g_eq_logDegree_on_hull :
    ∀ x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
      g (toE x) = I.sourceLocalLogDegree v x
  /-- At the vertices, the model values are dominated by the vertex log-degrees. -/
  g_le_logDegree_on_vertices :
    ∀ i ∈ vertices, g (toE i) ≤ I.sourceLocalLogDegree v i

/-- **Conditional upper reduction: hull volume at most the vertex sup.**  Under
the convexity card every hull point value is bounded by a vertex value (the
maximum principle of `iSup_ofReal_le_iSup_vertices_of_subset_convexHull`), so
the hull log-volume is at most the finite vertex sup. -/
theorem sourceHullVolume_le_vertices_of_convexVertexData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {E : Type uE} [AddCommGroup E] [Module Real E]
    (C : SourceHullConvexVertexData (I := I) v R n E) :
    I.sourceHullVolume v R n ≤
      ⨆ i ∈ C.vertices, ENNReal.ofReal (I.sourceLocalLogDegree v i) := by
  have hVfin : (C.toE '' (C.vertices : Set (I.ThetaPilotPoint v))).Finite :=
    Set.Finite.image C.toE (Finset.finite_toSet C.vertices)
  have hbridge :
      (⨆ x ∈ C.toE '' (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        ENNReal.ofReal (C.g x)) ≤
      ⨆ i ∈ C.toE '' (C.vertices : Set (I.ThetaPilotPoint v)),
        ENNReal.ofReal (C.g i) := by
    have hS : C.toE '' (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ⊆
        convexHull Real (hVfin.toFinset : Set E) := by
      intro x hx
      obtain ⟨y, hy, rfl⟩ := hx
      have hy' := C.hull_image_subset_convexHull y hy
      simpa only [Set.Finite.coe_toFinset] using hy'
    have hf : ConvexOn Real (convexHull Real (hVfin.toFinset : Set E)) C.g := by
      simpa only [Set.Finite.coe_toFinset] using C.convexOn_g
    simpa only [Set.Finite.mem_toFinset] using
      iSup_ofReal_le_iSup_vertices_of_subset_convexHull
        (S := C.toE '' (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)))
        (t := hVfin.toFinset) (f := C.g) hS hf
  have hL : I.sourceHullVolume v R n ≤
      ⨆ x ∈ C.toE '' (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        ENNReal.ofReal (C.g x) := by
    unfold sourceHullVolume sourceSetVolume sourcePointVolume
    refine iSup₂_le fun x hx => ?_
    rw [← C.g_eq_logDegree_on_hull x hx]
    exact le_iSup_of_le (C.toE x) (le_iSup_of_le ⟨x, hx, rfl⟩ le_rfl)
  have hR : (⨆ i ∈ C.toE '' (C.vertices : Set (I.ThetaPilotPoint v)),
        ENNReal.ofReal (C.g i)) ≤
      ⨆ i ∈ C.vertices, ENNReal.ofReal (I.sourceLocalLogDegree v i) := by
    refine iSup₂_le fun i hi => ?_
    obtain ⟨j, hj, rfl⟩ := hi
    exact le_trans (ENNReal.ofReal_le_ofReal (C.g_le_logDegree_on_vertices j hj))
      (le_iSup_of_le j (le_iSup_of_le hj le_rfl))
  exact le_trans hL (le_trans hbridge hR)

/-- **Reverse direction: the vertex sup is at most the hull volume.**  The
vertices lie on the hull, so their point volumes are bounded by the hull
sup-type volume; no geometry is used.  For the possible images this direction
is unconditional (`possibleThetaPilotImage_subset_sourceHolomorphicHull`,
`SourceImageHull.lean:408`); here it is a card field because the vertex list is
part of the card. -/
theorem vertices_le_sourceHullVolume_of_convexVertexData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {E : Type uE} [AddCommGroup E] [Module Real E]
    (C : SourceHullConvexVertexData (I := I) v R n E) :
    (⨆ i ∈ C.vertices, ENNReal.ofReal (I.sourceLocalLogDegree v i)) ≤
      I.sourceHullVolume v R n := by
  unfold sourceHullVolume sourceSetVolume sourcePointVolume
  refine iSup₂_le fun i hi => ?_
  exact le_iSup_of_le i (le_iSup_of_le (C.vertices_subset_hull i hi) le_rfl)

/-- **Conditional identification: hull volume = vertex volume.**  Under the
convexity card the two directions sandwich; this is the conditional form of
"hull = convex hull of the vertices" at the log-volume level. -/
theorem sourceHullVolume_eq_vertices_of_convexVertexData (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {E : Type uE} [AddCommGroup E] [Module Real E]
    (C : SourceHullConvexVertexData (I := I) v R n E) :
    I.sourceHullVolume v R n =
      ⨆ i ∈ C.vertices, ENNReal.ofReal (I.sourceLocalLogDegree v i) :=
  le_antisymm (sourceHullVolume_le_vertices_of_convexVertexData (I := I) v R n C)
    (vertices_le_sourceHullVolume_of_convexVertexData (I := I) v R n C)

end OriginalInput
end Theorem311Source

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the Card B assembly: vertex finiteness, the finite label
checks for hunit, and the conditional convexity card with the volume-level
identification. -/
def hullVertexConvexityAssembly : Obligation :=
  { id := "IUT-III.cor312-hull-vertex-convexity-assembly"
    source :=
      "IUT III, Corollary 3.12 (holomorphic hull of the union of the possible " ++
        "images of a Theta-pilot object; signed labels of Remark 3.1.1, (ii); " ++
        "corpus lines 10324-10338); Remark 3.9.5, (i)-(iii)"
    status := VerificationStatus.interface
    note :=
      "Card B of the vertex interface (hunit-epsilon-transfer-20261016 report). " ++
        "PROVED: (B1) vertex finiteness (possibleThetaPilotImageSet_finite); " ++
        "(B2) the label-indexed vertex check form of the image-union log-volume " ++
        "(sourceSetVolume_possibleImageSet_eq_labelSup, no degree-faithfulness " ++
        "hypothesis); (B3) hunit wirings from the image-union / finite label / " ++
        "epsilon label checks to the hunit input of the gap assembly " ++
        "(cor312GapSupply_sourceInterface_hunit_of_vertexVolumeBound, " ++
        "..._of_labelVolumeBound, ..._of_labelEpsilonBound), all via the existing " ++
        "monotonicity sourceHullVolume_ge_imageVolume; (B4) the conditional upper " ++
        "reduction and the volume-level identification under the named convexity " ++
        "card SourceHullConvexVertexData " ++
        "(sourceHullVolume_le_vertices_of_convexVertexData, " ++
        "sourceHullVolume_eq_vertices_of_convexVertexData) -- the first consumer " ++
        "of Foundations/Geometry/ConvexHullVertexSupReduction.lean. NOT proved: " ++
        "an actual datum of the card (no hull geometry in the tree); the direct " ++
        "convexity of sourceLocalLogDegree is unstatable at this layer " ++
        "(ThetaPilotPoint is a multiplicative value monoid without a Real-module " ++
        "structure). Route (iii) (Card A) remains open."
    dependsOn :=
      [ "IUT-III.cor312-hunit-epsilon-transfer"
      , "IUT-III.corollary-3.12-source-image-hull-volume"
      , "IUT-III.cor312-comparison-gap-reduction" ] }

end LeanFormal.IUT.Audit
