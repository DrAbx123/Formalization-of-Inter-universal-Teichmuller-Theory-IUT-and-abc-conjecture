import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealGeometryReduction

/-!
# Card-HULLREAL R9 attack: edge control and product-edge normalization

Task `hunit-epsilon-transfer-20261016`, R9 attack round (report section 18).
R9 is the remaining inequality of the via-images identity (section 17, items
R9/R10):

`sourceHullVolume v R n <= sourceSetVolume v (possibleThetaPilotImageSet v R n)`,

i.e. every point of the source holomorphic hull -- by the generator
characterization `sourceHolomorphicHull_eq_closure` a finite product of
possible theta-pilot images and scaling units -- has point log-volume at most
the edge volume (the supremum over the possible images).

What is proved here:

* `sourceImageVolume`: the edge volume as a named object; and the image-side
  edge control `sourcePointVolume_le_sourceImageVolume` (definitional: each
  possible image lies in the set whose supremum is the edge volume).
* Scaling-side edge control is free under the contraction condition
  (`sourcePointVolume_scaling_le_sourceImageVolume_of_contraction`): a
  nonpositive log-degree forces point volume zero.  The contraction input is
  the field consumed by `IQCarrierHaarData.sourceSetVolume_scaledRegionImage_le`.
* The edge volume is unconditionally finite (`sourceImageVolume_lt_top`), via
  the finite-label vertex form of section 17 (Card B).
* The naive subadditive attack (route A) is blocked, with exact bounds:
  subadditivity gives `2 * B` for two factors
  (`sourcePointVolume_mul_le_two_mul_sourceImageVolume`) and `length * B` for
  finite products (`sourcePointVolume_listProd_le_length_mul_sourceImageVolume`),
  never `B`.
* The product-edge normalization is not a value-layer theorem
  (`not_sourcePointVolume_mul_le_max_of_thetaValue_gt_one`): under pointwise
  degree faithfulness, a positive-degree possible image squared has point
  volume strictly above the maximum of the factors' volumes, so no pointwise
  max-stability can be derived from the additive `sourceLocalLogDegree_mul`.
  The normalization is a region-level (log-shell) input, cf. III:10851-10863
  (the log-Kummer correspondence in the 1-column and the tensor packets of
  log-shells that constitute `1,circ U`).
* Conditional R9: with the product-edge normalization as a named hypothesis
  (and scaling edge control, or the contraction condition from which it is
  free), R9 is proved (`sourceHullVolume_le_imageVolume_of_productEdgeNormalization`,
  `..._of_contraction_and_productEdgeNormalization`), by closure induction over
  the generator characterization of section 17 (R1).
* Interface level: `IQHullEdgeBoundInterface` names the exact missing field of
  the realized interface (`hull_logVolume_le_imageSet`) -- the sharpened
  normalization that the existing `IQHullLogVolumeInterface` fields
  (containment into a scaled unit region, plus finiteness of the normalized
  unit volume) do not supply; the transfer
  `iqHullEdgeBound_logVolume_hull_le_ofReal` replaces the hull-level
  upper-bound slot of the certificate consumers by image-set-level data.  The
  raw Haar measure of `PadicLogShellModel` is not the [AbsTopIII] normalized
  log-volume (carrier-line report `iq-hull-haar-logshell-landing`); the edge
  bound is exactly the missing sharp constraint.
* Unconditional R9 is refuted in the value layer under pointwise degree
  faithfulness (`not_sourceHullVolume_le_imageVolume_of_degreeFaithful`): the
  hull volume is `top` while the edge volume is finite.  Hence R9 must be
  conditional; the unconditional statement is recorded as the R9 card in
  report section 18, with the region-level normalization (III:10843-10848,
  10851-10863; [AbsTopIII] Proposition 5.7 / Corollary 5.10 normalization) as
  the required input.

Paper route vs. our route: the corpus obtains the finiteness and the negative
sign of `-|log(Theta)|` from the compactness of the `1,circ U_{j,vQ}` together
with the definition of the log-volume (III:10402-10411), and matches
`-|log(q)|` (the log-volume of the q-pilot representation region on
`1,circ U_Q`) against it through the log-Kummer correspondence in the 1-column
(III:10851-10863); the present value layer has no region-level log-shell
object, so this file proves the pointwise decomposition and records the
region-level input as the named hypothesis / interface field above.  No
degree-faithful premise is introduced as an assumption anywhere.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe u ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The edge volume -/

/-- The edge volume `B` of the via-images identity (R9): the log-volume of the
union of possible theta-pilot images, the supremum of the point log-volumes of
the possible images (the "possible images" of the proof of Corollary 3.12,
III:10381-10402). -/
def sourceImageVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : ENNReal :=
  I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)

/-! ## 2. Edge control: definitional on the images, free under contraction -/

/-- **Image-side edge control (definitional).**  Each possible image has point
log-volume at most the edge volume. -/
theorem sourcePointVolume_le_sourceImageVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j) ≤
      I.sourceImageVolume v R n := by
  unfold sourceImageVolume sourceSetVolume
  exact le_iSup_of_le (I.sourceThetaPilotPoint v R n j)
    (le_iSup_of_le (I.sourceThetaPilotPoint_mem v R n j) le_rfl)

/-- A nonpositive `mu_log` log-degree forces zero point log-volume. -/
theorem sourcePointVolume_eq_zero_of_logDegree_nonpos (v : V)
    (x : I.ThetaPilotPoint v) (hx : I.sourceLocalLogDegree v x ≤ 0) :
    I.sourcePointVolume v x = 0 :=
  ENNReal.ofReal_eq_zero.mpr hx

/-- **Scaling-side edge control under contraction.**  A scaling unit with
nonpositive log-degree (a contraction, the field consumed by
`IQCarrierHaarData.sourceSetVolume_scaledRegionImage_le`) has zero point
log-volume, hence volume at most the edge volume. -/
theorem sourcePointVolume_scaling_le_sourceImageVolume_of_contraction (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {s : I.ThetaPilotPoint v} (hs : s ∈ I.sourceScalingUnits v)
    (hdeg : I.sourceLocalLogDegree v s ≤ 0) :
    I.sourcePointVolume v s ≤ I.sourceImageVolume v R n := by
  rw [sourcePointVolume_eq_zero_of_logDegree_nonpos I v s hdeg]
  exact zero_le

/-! ## 3. The naive subadditive attack (route A) and its exact bounds -/

/-- **Two-factor naive bound.**  Subadditivity of the point log-volume
(section 17, R2) gives only `2 * B` for a product of two points of volume at
most `B`: the subadditive estimate cannot close R9 by itself. -/
theorem sourcePointVolume_mul_le_two_mul_sourceImageVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {x y : I.ThetaPilotPoint v}
    (hx : I.sourcePointVolume v x ≤ I.sourceImageVolume v R n)
    (hy : I.sourcePointVolume v y ≤ I.sourceImageVolume v R n) :
    I.sourcePointVolume v (x * y) ≤ 2 * I.sourceImageVolume v R n :=
  calc I.sourcePointVolume v (x * y)
      ≤ I.sourcePointVolume v x + I.sourcePointVolume v y :=
        sourcePointVolume_mul_le I v x y
    _ ≤ I.sourceImageVolume v R n + I.sourceImageVolume v R n := add_le_add hx hy
    _ = 2 * I.sourceImageVolume v R n := (two_mul _).symm

/-- **Finite-product naive bound.**  For a finite list of points each of volume
at most `B`, the product's volume is at most `length * B`: linear in the number
of factors.  This is the precise shape in which the subadditive attack is
blocked; the normalization that collapses `length * B` to `B` is the
region-level log-shell input of III:10851-10863. -/
theorem sourcePointVolume_listProd_le_length_mul_sourceImageVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (L : List (I.ThetaPilotPoint v))
    (hL : ∀ x ∈ L, I.sourcePointVolume v x ≤ I.sourceImageVolume v R n) :
    I.sourcePointVolume v L.prod ≤
      (L.length : ENNReal) * I.sourceImageVolume v R n := by
  revert hL
  induction L with
  | nil =>
      intro hL
      simp [sourcePointVolume, I.sourceLocalLogDegree_one]
  | cons x L ih =>
      intro hL
      have hx : I.sourcePointVolume v x ≤ I.sourceImageVolume v R n :=
        hL x List.mem_cons_self
      have hL' : ∀ y ∈ L, I.sourcePointVolume v y ≤ I.sourceImageVolume v R n :=
        fun y hy => hL y (List.mem_cons_of_mem x hy)
      rw [List.prod_cons, List.length_cons]
      calc I.sourcePointVolume v (x * L.prod)
          ≤ I.sourcePointVolume v x + I.sourcePointVolume v L.prod :=
            sourcePointVolume_mul_le I v x L.prod
        _ ≤ I.sourceImageVolume v R n +
              (L.length : ENNReal) * I.sourceImageVolume v R n :=
            add_le_add hx (ih hL')
        _ = ((L.length : ENNReal) + 1) * I.sourceImageVolume v R n := by
            rw [add_comm, add_mul, one_mul]
        _ = ((L.length + 1 : ℕ) : ENNReal) * I.sourceImageVolume v R n := by
            rw [Nat.cast_add, Nat.cast_one]

/-! ## 4. The product-edge normalization is not a value-layer theorem -/

/-- **Negative calibration.**  Under the pointwise degree-faithful
realization, the product of a positive-degree possible image with itself has
point volume strictly larger than the maximum of its factor volumes: the
product-edge normalization (max-stability) fails already at the two-image
level, so the additive value layer cannot supply the normalization hypothesis
of the conditional R9; the normalization must come from the region-level
log-shell geometry (III:10851-10863). -/
theorem not_sourcePointVolume_mul_le_max_of_thetaValue_gt_one (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (j : SignedLabel l.value) (h1 : 1 < I.thetaValueAt (n.val : Int) 0 j) :
    ¬ I.sourcePointVolume v
        (I.sourceThetaPilotPoint v R n j * I.sourceThetaPilotPoint v R n j) ≤
      max (I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j))
        (I.sourcePointVolume v (I.sourceThetaPilotPoint v R n j)) := by
  intro h
  have hc : (0 : ℝ) < (Fintype.card (SourceVolumeIndex l) : ℝ) := by
    exact_mod_cast sourceVolumeIndex_card_pos l
  have hL : 0 < Real.log (I.thetaValueAt (n.val : Int) 0 j) :=
    Real.log_pos h1
  have hcL : 0 < (Fintype.card (SourceVolumeIndex l) : ℝ) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j) := mul_pos hc hL
  have hprod : I.sourcePointVolume v
        (I.sourceThetaPilotPoint v R n j * I.sourceThetaPilotPoint v R n j) =
      ENNReal.ofReal
        (((Fintype.card (SourceVolumeIndex l) : ℝ) *
            Real.log (I.thetaValueAt (n.val : Int) 0 j)) +
          ((Fintype.card (SourceVolumeIndex l) : ℝ) *
            Real.log (I.thetaValueAt (n.val : Int) 0 j))) := by
    unfold sourcePointVolume
    rw [I.sourceLocalLogDegree_mul,
      I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg]
  have hfac := I.sourcePointVolume_thetaPilotPoint v R n j hdeg
  rw [hprod, hfac, max_self] at h
  have hle := (ENNReal.ofReal_le_ofReal_iff hcL.le).mp h
  linarith

/-! ## 5. Conditional R9 by closure induction -/

/-- **Conditional R9 (named normalization hypotheses).**  If (i) the scaling
units have volume at most the edge volume (free under contraction, section 2)
and (ii) every product of two hull points has point volume at most the maximum
of the factors' volumes (the product-edge normalization, the region-level
log-shell input), then the hull volume is at most the edge volume.  The
image-side edge control is definitional
(`sourcePointVolume_le_sourceImageVolume`); the only non-structural content is
(ii), which section 4 shows is not a value-layer theorem. -/
theorem sourceHullVolume_le_imageVolume_of_productEdgeNormalization (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hprod : ∀ x y : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      I.sourcePointVolume v (x * y) ≤
        max (I.sourcePointVolume v x) (I.sourcePointVolume v y))
    (hscal : ∀ s ∈ I.sourceScalingUnits v,
      I.sourcePointVolume v s ≤ I.sourceImageVolume v R n) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n := by
  unfold sourceImageVolume
  rw [sourceHullVolume_le_imageVolume_iff_forall_pointVolume_le]
  intro z hz
  rw [sourceHolomorphicHull_eq_closure I v R n] at hz
  refine Submonoid.closure_induction (motive := fun z _ =>
    I.sourcePointVolume v z ≤
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) ?_ ?_ ?_ hz
  · intro x hx
    rcases hx with hx | hx
    · obtain ⟨j, rfl⟩ := (I.mem_possibleThetaPilotImageSet_iff v R n x).mp hx
      exact sourcePointVolume_le_sourceImageVolume I v R n j
    · exact hscal x hx
  · simp [sourcePointVolume, I.sourceLocalLogDegree_one]
  · intro x y hx hy ihx ihy
    have hx' : x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
      rw [sourceHolomorphicHull_eq_closure I v R n]
      exact hx
    have hy' : y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) := by
      rw [sourceHolomorphicHull_eq_closure I v R n]
      exact hy
    exact le_trans (hprod x y hx' hy') (max_le ihx ihy)

/-- **Conditional R9, contraction form.**  If the scaling units are
contractions (`mu_log` log-degree at most zero -- the HaarData contraction
field), the scaling edge control is free and the product-edge normalization is
the only remaining input. -/
theorem sourceHullVolume_le_imageVolume_of_contraction_and_productEdgeNormalization
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hprod : ∀ x y : I.ThetaPilotPoint v,
      x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      y ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) →
      I.sourcePointVolume v (x * y) ≤
        max (I.sourcePointVolume v x) (I.sourcePointVolume v y))
    (hscal0 : ∀ s ∈ I.sourceScalingUnits v,
      I.sourceLocalLogDegree v s ≤ 0) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n :=
  sourceHullVolume_le_imageVolume_of_productEdgeNormalization I v R n hprod
    (fun s hs =>
      sourcePointVolume_scaling_le_sourceImageVolume_of_contraction I v R n hs
        (hscal0 s hs))

/-! ## 6. The edge volume is finite; unconditional R9 is refutable -/

/-- **Finiteness of the edge volume (unconditional).**  The union of possible
theta-pilot images has finite log-volume: it is the finite label-indexed
supremum of finite point volumes (no degree-faithfulness hypothesis). -/
theorem sourceImageVolume_lt_top (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceImageVolume v R n < ⊤ := by
  unfold sourceImageVolume
  rw [sourceSetVolume_possibleImageSet_eq_labelSup (I := I) v R n]
  have hsup : Finset.univ.sup (fun j : SignedLabel l.value =>
      ENNReal.ofReal
        (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) < ⊤ := by
    rw [Finset.sup_lt_iff (show (⊥ : ENNReal) < ⊤ from bot_lt_top)]
    intro b _
    exact ENNReal.ofReal_lt_top
  have hle : (⨆ j : SignedLabel l.value,
      ENNReal.ofReal
        (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) ≤
      Finset.univ.sup (fun j : SignedLabel l.value =>
        ENNReal.ofReal
          (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j))) :=
    iSup_le fun j => Finset.le_sup (f := fun k : SignedLabel l.value =>
      ENNReal.ofReal (I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n k)))
      (Finset.mem_univ j)
  exact lt_of_le_of_lt hle hsup

/-- **Unconditional R9 is refuted under degree faithfulness.**  If the
realization is pointwise degree faithful, the hull volume is `top`
(`sourceHullVolume_eq_top_of_degreeFaithful`) while the edge volume is finite
(`sourceImageVolume_lt_top`); hence R9 fails.  Unconditional R9 is therefore
not a theorem of the present value layer: it must be conditional on data
excluding pointwise degree faithfulness (the region-level normalization),
confirming the R9 card of report section 18. -/
theorem not_sourceHullVolume_le_imageVolume_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    ¬ I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n := by
  intro h
  have hB := sourceImageVolume_lt_top I v R n
  have hθ : I.sourceHullVolume v R n ≤
      ENNReal.ofReal (I.sourceImageVolume v R n).toReal := by
    rwa [ENNReal.ofReal_toReal (ne_top_of_lt hB)]
  exact I.sourceThetaBound_unsat_of_degreeFaithful v R n hdeg ⟨_, hθ⟩

end OriginalInput
end Theorem311Source

/-! ## 7. The interface-level edge bound -/

/-- The edge-bound extension of `IQHullLogVolumeInterface`: the sharpened
normalization that R9 needs, i.e. that the hull log-volume is at most the
image-set log-volume (the interface-level form of `hull <= image`).  The
existing fields supply the containment `hull` in the scaled unit region and
the finiteness normalization of the scaled unit region only; the sharp edge
bound is exactly the input left open by the raw-vs-normalized log-volume gap
of the carrier line (the raw Haar measure of `PadicLogShellModel` is not the
[AbsTopIII] Proposition 5.7 / Corollary 5.10 normalized log-volume; see the
`iq-hull-haar-logshell-landing` report). -/
structure IQHullEdgeBoundInterface (X : Type u) extends IQHullLogVolumeInterface X where
  /-- The edge bound: the hull log-volume is at most the image-set log-volume. -/
  hull_logVolume_le_imageSet : logVolume hull ≤ logVolume imageSet

/-- **Consumer transfer at the interface level.**  Under the edge bound, an
upper bound checked at the image set transfers to the hull.  This replaces
the hull-level upper-bound slot of the certificate consumers
(`CertificateHullWiring.iqHullCertificate`, its `hθ` slot) by image-set-level
data; the `q`-side input of those consumers is already at the image set. -/
theorem iqHullEdgeBound_logVolume_hull_le_ofReal {X : Type u}
    (W : IQHullEdgeBoundInterface X) {θ : ℝ}
    (himg : W.logVolume W.imageSet ≤ ENNReal.ofReal θ) :
    W.logVolume W.hull ≤ ENNReal.ofReal θ :=
  le_trans W.hull_logVolume_le_imageSet himg

/-- A consistency witness: the singleton-real interface extended by the
trivial edge bound (its hull and image set coincide), showing that the
extension is satisfiable.  This is a check on the data interface only, not a
model of the paper's carrier. -/
noncomputable def iqHullEdgeBoundSingletonWitness : IQHullEdgeBoundInterface ℝ :=
  { IQHullLogVolumeInterface.singletonRealWitness with
      hull_logVolume_le_imageSet := le_of_eq rfl }

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the R9 edge-normalization attack round on the remaining
inequality `hull <= image` of the via-images identity: the named edge volume,
the free edge control, the exact naive bounds, the negative calibration of
product max-stability, the conditional R9 forms, the interface-level edge
bound, and the refutation of unconditional R9 under degree faithfulness. -/
def cardHullRealEdgeNormalizationReduction : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-edge-normalization-reduction"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f): corpus lines " ++
        "10381-10414 (possible images; compactness of 1,circ U; finiteness of " ++
        "-|log(Theta)|), 10843-10848 (-|log(Theta)| = log-volume of 1,circ U; " ++
        "-|log(q)| = log-volume of the q-representation region), 10851-10863 " ++
        "(log-Kummer correspondence in the 1-column; tensor packets of " ++
        "log-shells constituting 1,circ U); Remark 3.9.5, (i)-(ii)"
    status := VerificationStatus.interface
    note :=
      "R9 attack round. Proved: edge volume named and image-side edge control " ++
        "definitional (sourcePointVolume_le_sourceImageVolume); scaling edge " ++
        "control free under contraction; edge volume finite unconditionally; " ++
        "naive subadditive bounds 2*B and length*B (route A blocked exactly); " ++
        "product max-stability refuted on the value layer under degree " ++
        "faithfulness (not_sourcePointVolume_mul_le_max_of_thetaValue_gt_one); " ++
        "conditional R9 under the named product-edge normalization " ++
        "(+ contraction form), by closure induction over R1; interface-level " ++
        "edge bound IQHullEdgeBoundInterface with consumer transfer replacing " ++
        "the hull-level upper-bound slot by image-set-level data. " ++
        "Unconditional R9 refuted under pointwise degree faithfulness " ++
        "(hull volume top, edge volume finite): R9 must be conditional. " ++
        "NOT proved: unconditional R9 -- requires the region-level log-shell " ++
        "normalization (III:10851-10863; [AbsTopIII] Prop 5.7 / Cor 5.10 " ++
        "normalized log-volume; raw Haar is not normalized). R9 card in " ++
        "report section 18."
    dependsOn :=
      [ "IUT-III.corollary-3.12-card-hullreal-geometry-reduction",
        "IUT-III.corollary-3.12-card-hullreal-omodule-compactness",
        "IUT-III.corollary-3.12-source-image-hull-volume",
        "IUT-III.corollary-3.12-card-hullreal-signed-log-volume" ] }

end LeanFormal.IUT.Audit
