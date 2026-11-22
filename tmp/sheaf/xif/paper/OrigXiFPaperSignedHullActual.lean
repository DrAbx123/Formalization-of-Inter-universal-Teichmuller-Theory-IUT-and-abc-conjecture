import tmp.sheaf.xif.PaperSignedHull
import tmp.sheaf.xif.paper.ThetaHullActual
import tmp.sheaf.xif.paper.SignedHullLogActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# Layer O: actual `PaperSignedHull` from the actual theta hull / determinant /
# log-volume, with its `ThetaLink` ray

Layer: **O** (original-text Theta-link). This file uses only paper-level
Theta-link objects:

* `ActualThetaHull` (`tmp/sheaf/xif/paper/ThetaHullActual.lean`): the actual
  compact `1,circ U_{j,vQ}` image union, its holomorphic hull, the normalized
  Haar/log-shell unit region, and the `lambda * O` containment of Remark 3.9.5;
* `SignedHullLogActual` (`tmp/sheaf/xif/paper/SignedHullLogActual.lean`): the
  actual finite log-shell packets, their determinant/log-volume, the positive
  determinant tensor power `M` of `det^{tensor M}`, and the actual procession
  weights/values;
* `PaperSignedHull` (`tmp/sheaf/xif/PaperSignedHull.lean`): the paper-level
  signed hull carrier consumed by `ThetaLinkActual`;
* `hullLogVolumeRay` (`HullDeterminantLogVolumeReduction.lean`): the ray
  `R_{<= -|log Theta|}` of IUT III, Corollary 3.12, Step (xi-f), whose
  membership is exactly the conclusion type of
  `ThetaLinkActual.link_implies_inclusion`.

It deliberately does **not** use the normalized model (N), the native target
(T), `SourceDefinition31Data` (S), or any D4-D9 assembly (D).

## What is constructed

1. `OrigXiFThetaHullAmbient`: the ambient hull/log-volume interface is read
   off the actual theta hull (image union, hull, Haar log-volume, unit region,
   `lambda`-scaling, finiteness and Haar normalization). No log-volume is
   supplied by hand.
2. `OrigXiFDeterminantFiniteHull`: the finite hull whose volumes are the actual
   determinant-procession log-scales (nonnegative because the hull packet
   scales are at least one).
3. `OrigXiFSignedThetaHullLogVolume`: the signed hull log-volume of the paper,
   defined as the negative of the actual normalized Haar log-volume of the
   actual holomorphic hull (never a free `Real`). It is proved equal to the
   actual signed determinant-procession normalization
   `SignedHullLogActual.signedProcessionNormalizedLogVolume`, and nonpositive.
4. `OrigXiFPaperSignedHull`: the actual `PaperSignedHull` built from 1-3. Its
   `signedHullLogVolume` is proved equal to `OrigXiFSignedThetaHullLogVolume`,
   i.e. to the negative actual theta-hull log-volume.
5. `OrigXiFThetaHullLogVolumeRay` and `OrigXiFThetaLinkRay_iff_le`: the
   `hullLogVolumeRay` required by `ThetaLinkActual` at the actual signed hull
   scalar, with membership computed as
   `qPilotLogVolume <= OrigXiFSignedThetaHullLogVolume D`.
   `OrigXiFThetaLinkRayObligation` is literally the proposition type of the
   consumer field `ThetaLinkActual.link_implies_inclusion`.

## Exact remaining paper obligation

The only bridge datum is the field

  thetaHull.haar.logVolume thetaHull.compactHull.hull
    = ENNReal.ofReal determinant.procession.average

of `OrigXiFPaperSignedHullData`: the paper's identification of the
procession-normalized mono-analytic hull log-volume with the actual
determinant-procession average (IUT III, Step (xi-d)/(xi-e)). It is carried as
explicit data of the actual objects, not as an axiom, and it is a proposition
about actual quantities, not a free real parameter. No inhabitant of the data
structure is asserted; the construction and all theorems are conditional on it.

No `PUnit`, `True`, `sorry`, `axiom`, arbitrary inhabitant, or `Nonempty`
witness is used.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT
namespace XiFPaper
namespace OrigXiF

open scoped BigOperators
open LeanFormal.IUT.XiFPaperThetaHull

universe u

variable {X : Type u} [TopologicalSpace X] {l : PrimeGeFive}

/-! ## 1. Actual paper data: actual theta hull + actual determinant/log-volume -/

/-- The actual layer-O data for the paper signed hull.

`thetaHull` is the actual `1,circ U` theta hull surface (compact image union,
holomorphic hull, normalized Haar log-volume, `lambda * O` containment).
`determinant` is the actual determinant/log-volume packet construction (hull
log-shell packet, unit reference packet, positive determinant tensor power,
actual procession). `hull_logVolume_eq_procession` is the paper's exact
procession-normalization identification between the actual hull log-volume and
the actual determinant-procession average.

No field is a free real parameter and no inhabitant is asserted. -/
structure OrigXiFPaperSignedHullData (X : Type u) [TopologicalSpace X]
    (l : PrimeGeFive) where
  /-- The actual `1,circ U` theta hull surface. -/
  thetaHull : ActualThetaHull X l
  /-- The actual determinant/log-volume packet data for the signed hull. -/
  determinant : SignedHullLogActual (SignedLabel l.value)
  /-- Paper procession normalization (Step (xi-d)/(xi-e)): the actual
  normalized Haar log-volume of the actual hull is the actual
  determinant-procession average. -/
  hull_logVolume_eq_procession :
    thetaHull.haar.logVolume thetaHull.compactHull.hull =
      ENNReal.ofReal determinant.procession.average

/-! ## 2. Ambient interface from the actual theta hull -/

/-- The actual paper-level ambient hull/log-volume interface read off the
actual theta hull. Every field is a projection of `ActualThetaHull`; no
log-volume functional, hull, unit region, or scaling is introduced by hand. -/
noncomputable def OrigXiFThetaHullAmbient (T : ActualThetaHull X l) :
    IQHullLogVolumeInterface X where
  imageSet := T.compactHull.imageSet
  hull := T.compactHull.hull
  imageSet_subset_hull := T.compactHull.imageSet_subset_hull
  logVolume := T.haar.logVolume
  logVolume_mono := T.haar.logVolume_mono
  unitRegion := T.haar.unitRegion
  scaleShift := T.haar.scaleShift
  hull_subset_scaleShift := T.hull_subset_scaleShift
  unitRegion_logVolume_lt_top := by
    rw [T.haar.unitRegion_normalized]
    exact ENNReal.one_lt_top
  scaleShift_unitRegion_logVolume_le := T.haar.scaleShift_unitRegion_le

/-- The ambient interface of the theta hull has the actual hull as its hull. -/
theorem OrigXiFThetaHullAmbient_hull (T : ActualThetaHull X l) :
    (OrigXiFThetaHullAmbient T).hull = T.compactHull.hull := rfl

/-- The ambient interface of the theta hull has the actual normalized Haar
log-volume as its log-volume. -/
theorem OrigXiFThetaHullAmbient_logVolume (T : ActualThetaHull X l) :
    (OrigXiFThetaHullAmbient T).logVolume = T.haar.logVolume := rfl

/-! ## 3. Actual finite hull from the determinant procession -/

/-- The actual finite hull of the determinant procession: label `j` carries
the actual log-scale of the hull packet, and the finite hull volume is the
sum of these actual log-scales. The containment `value j <= hullVolume` is
proved from the actual hull-packet scaling (all scales at least one), not
assumed. -/
noncomputable def OrigXiFDeterminantFiniteHull
    (D : SignedHullLogActual (SignedLabel l.value)) :
    FiniteHull (SignedLabel l.value) where
  volume i := D.procession.value i
  hullVolume := ∑ i : SignedLabel l.value, D.procession.value i
  contains i := by
    have hnonneg : ∀ j : SignedLabel l.value, 0 ≤ D.procession.value j := by
      intro j
      rw [D.procession_values j]
      exact Real.log_nonneg (D.hull_scales_ge_one j)
    exact Finset.single_le_sum (fun j _ => hnonneg j) (Finset.mem_univ i)

/-! ## 4. The actual signed hull log-volume -/

/-- The actual theta hull log-volume: the normalized Haar log-volume of the
actual compact holomorphic hull `1,circ U` (the magnitude `|log Theta|` of the
paper). -/
noncomputable def OrigXiFThetaHullLogVolume
    (D : OrigXiFPaperSignedHullData X l) : ENNReal :=
  D.thetaHull.haar.logVolume D.thetaHull.compactHull.hull

/-- The actual signed hull log-volume `-|log(Theta)|` of the paper: minus the
actual normalized Haar log-volume of the actual holomorphic hull. This is not a
free real parameter; it is computed from the actual theta hull and proved equal
to the actual determinant-procession normalization below. -/
noncomputable def OrigXiFSignedThetaHullLogVolume
    (D : OrigXiFPaperSignedHullData X l) : Real :=
  -(OrigXiFThetaHullLogVolume D).toReal

/-- The actual hull log-volume is the actual determinant-procession average
(the paper procession normalization, in `ENNReal` form). -/
theorem OrigXiFThetaHullLogVolume_eq_ofReal_procession
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFThetaHullLogVolume D =
      ENNReal.ofReal D.determinant.procession.average :=
  D.hull_logVolume_eq_procession

/-- The actual hull log-volume is the actual determinant procession
normalization of `SignedHullLogActual`. -/
theorem OrigXiFThetaHullLogVolume_eq_determinant
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFThetaHullLogVolume D =
      ENNReal.ofReal D.determinant.processionNormalizedLogVolume := by
  rw [OrigXiFThetaHullLogVolume_eq_ofReal_procession]
  rfl

/-- The actual hull log-volume is finite (the paper's finiteness of
`-|log Theta|`). -/
theorem OrigXiFThetaHullLogVolume_lt_top
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFThetaHullLogVolume D < ⊤ := by
  rw [OrigXiFThetaHullLogVolume_eq_ofReal_procession]
  exact ENNReal.ofReal_lt_top

/-- The actual signed hull log-volume is the signed determinant-procession
normalization of the actual determinant/log-volume data. -/
theorem OrigXiFSignedThetaHullLogVolume_eq_determinant
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFSignedThetaHullLogVolume D =
      D.determinant.signedProcessionNormalizedLogVolume := by
  unfold OrigXiFSignedThetaHullLogVolume OrigXiFThetaHullLogVolume
  rw [D.hull_logVolume_eq_procession]
  have hnonneg : 0 ≤ D.determinant.procession.average :=
    D.determinant.processionNormalizedLogVolume_nonneg
  rw [ENNReal.toReal_ofReal hnonneg]
  rfl

/-- The actual signed hull log-volume is minus the actual procession average
of the determinant log-scales. -/
theorem OrigXiFSignedThetaHullLogVolume_eq_neg_average
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFSignedThetaHullLogVolume D = -D.determinant.procession.average := by
  rw [OrigXiFSignedThetaHullLogVolume_eq_determinant]
  rfl

/-- The actual signed hull log-volume is nonpositive: it is `-|log Theta|`. -/
theorem OrigXiFSignedThetaHullLogVolume_nonpos
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFSignedThetaHullLogVolume D ≤ 0 := by
  rw [OrigXiFSignedThetaHullLogVolume_eq_determinant]
  exact SignedHullLogActual.signedProcessionNormalizedLogVolume_nonpos D.determinant

/-- The actual signed hull log-volume is the negative of the actual hull
log-volume: the sign convention `-|log Theta|`, not an `ENNReal` clamp. -/
theorem OrigXiFSignedThetaHullLogVolume_eq_neg_toReal
    (D : OrigXiFPaperSignedHullData X l) :
    OrigXiFSignedThetaHullLogVolume D = -(OrigXiFThetaHullLogVolume D).toReal :=
  rfl

/-- The actual signed hull log-volume is bounded below by `-1` by the actual
compactness/Haar normalization of the theta hull
(`ActualThetaHull.hull_logVolume_le_one`). -/
theorem OrigXiFSignedThetaHullLogVolume_ge_neg_one
    (D : OrigXiFPaperSignedHullData X l) :
    -1 ≤ OrigXiFSignedThetaHullLogVolume D := by
  have hle : OrigXiFThetaHullLogVolume D ≤ 1 :=
    ActualThetaHull.hull_logVolume_le_one D.thetaHull
  have hto : (OrigXiFThetaHullLogVolume D).toReal ≤ (1 : ENNReal).toReal :=
    ENNReal.toReal_mono (ne_of_lt ENNReal.one_lt_top) hle
  rw [ENNReal.toReal_one] at hto
  unfold OrigXiFSignedThetaHullLogVolume
  linarith

/-! ## 5. The actual paper signed hull -/

/-- The actual `PaperSignedHull` built from the actual theta hull, the actual
determinant/log-volume procession, and the paper procession-normalization
identification. Its ambient interface is the actual theta-hull interface, its
procession is the actual determinant procession, and its signed hull scalar is
the actual `-|log Theta|` of section 4. -/
noncomputable def OrigXiFPaperSignedHull
    (D : OrigXiFPaperSignedHullData X l) :
    PaperSignedHull X (SignedLabel l.value) where
  ambient := OrigXiFThetaHullAmbient D.thetaHull
  procession := D.determinant.procession
  hull := OrigXiFDeterminantFiniteHull D.determinant
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := D.determinant.weights_nonnegative
  average_nonneg := D.determinant.processionNormalizedLogVolume_nonneg
  hull_logVolume_eq_average := by
    simpa [OrigXiFThetaHullAmbient] using D.hull_logVolume_eq_procession

/-- The constructed paper signed hull carries the actual determinant
procession. -/
theorem OrigXiFPaperSignedHull_procession
    (D : OrigXiFPaperSignedHullData X l) :
    (OrigXiFPaperSignedHull D).procession = D.determinant.procession := rfl

/-- The constructed paper signed hull has the actual theta hull as its ambient
hull. -/
theorem OrigXiFPaperSignedHull_ambient_hull
    (D : OrigXiFPaperSignedHullData X l) :
    (OrigXiFPaperSignedHull D).ambient.hull = D.thetaHull.compactHull.hull := rfl

/-- The constructed paper signed hull has the actual normalized Haar
log-volume of the theta hull as its ambient log-volume. -/
theorem OrigXiFPaperSignedHull_ambient_logVolume
    (D : OrigXiFPaperSignedHullData X l) :
    (OrigXiFPaperSignedHull D).ambient.logVolume = D.thetaHull.haar.logVolume := rfl

/-- The hull log-volume equality of the constructed paper signed hull is the
actual paper procession normalization. -/
theorem OrigXiFPaperSignedHull_hull_logVolume
    (D : OrigXiFPaperSignedHullData X l) :
    (OrigXiFPaperSignedHull D).ambient.logVolume
        (OrigXiFPaperSignedHull D).ambient.hull =
      ENNReal.ofReal D.determinant.procession.average :=
  D.hull_logVolume_eq_procession

/-- **The signed hull scalar of the actual paper signed hull is the actual
signed theta hull log-volume**, i.e. minus the actual normalized Haar
log-volume of the actual `1,circ U` hull, equivalently the actual signed
determinant-procession normalization. -/
theorem OrigXiFPaperSignedHull_signedHullLogVolume
    (D : OrigXiFPaperSignedHullData X l) :
    (OrigXiFPaperSignedHull D).signedHullLogVolume =
      OrigXiFSignedThetaHullLogVolume D := by
  rw [PaperSignedHull.signedHullLogVolume_eq_neg_average,
    OrigXiFSignedThetaHullLogVolume_eq_determinant]
  change -D.determinant.procession.average =
    D.determinant.signedProcessionNormalizedLogVolume
  rfl

/-- The constructed paper signed hull also realizes the actual signed
determinant-procession normalization through `SignedHullLogActual`. -/
theorem OrigXiFPaperSignedHull_signedHullLogVolume_eq_determinant
    (D : OrigXiFPaperSignedHullData X l) :
    (OrigXiFPaperSignedHull D).signedHullLogVolume =
      D.determinant.signedProcessionNormalizedLogVolume := by
  rw [OrigXiFPaperSignedHull_signedHullLogVolume,
    OrigXiFSignedThetaHullLogVolume_eq_determinant]

/-! ## 6. The `ThetaLink` ray at the actual signed hull scalar -/

/-- The paper ray `R_{<= -|log Theta|}` of Step (xi-f) at the actual signed
theta hull log-volume. -/
noncomputable def OrigXiFThetaHullLogVolumeRay
    (D : OrigXiFPaperSignedHullData X l) : Set Real :=
  hullLogVolumeRay (OrigXiFSignedThetaHullLogVolume D)

/-- Membership in the actual ray is the actual signed-hull log-volume
inequality. -/
theorem OrigXiFmem_thetaHullLogVolumeRay_iff
    (D : OrigXiFPaperSignedHullData X l) {lambdaValue : Real} :
    lambdaValue ∈ OrigXiFThetaHullLogVolumeRay D ↔
      lambdaValue ≤ OrigXiFSignedThetaHullLogVolume D :=
  Iff.rfl

/-- The `hullLogVolumeRay` required by `ThetaLinkActual` at the actual paper
signed hull is the ray of the actual signed theta hull log-volume. -/
theorem OrigXiFPaperSignedHull_hullLogVolumeRay_eq
    (D : OrigXiFPaperSignedHullData X l) :
    hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume =
      OrigXiFThetaHullLogVolumeRay D := by
  rw [OrigXiFThetaHullLogVolumeRay, OrigXiFPaperSignedHull_signedHullLogVolume]

/-- **The `ThetaLink` ray obligation at the actual hull is exactly the actual
signed-hull log-volume inequality.** This is the computation of the consumer
field `ThetaLinkActual.link_implies_inclusion`, whose conclusion type is
`O.qPilotLogVolume ∈ hullLogVolumeRay P.signedHullLogVolume`. -/
theorem OrigXiFThetaLinkRay_iff_le
    (D : OrigXiFPaperSignedHullData X l) (qPilotLogVolume : Real) :
    qPilotLogVolume ∈
        hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume ↔
      qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume D := by
  rw [OrigXiFPaperSignedHull_hullLogVolumeRay_eq,
    OrigXiFmem_thetaHullLogVolumeRay_iff]

/-- The proposition consumed by the paper `ThetaLink`, at the actual signed
hull: the q-pilot scalar lies in `R_{<= -|log Theta|}` for the actual signed
theta hull log-volume. -/
def OrigXiFThetaLinkRayObligation
    (D : OrigXiFPaperSignedHullData X l) (qPilotLogVolume : Real) : Prop :=
  qPilotLogVolume ∈
    hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume

/-- The consumer obligation is the actual signed-hull log-volume inequality. -/
theorem OrigXiFThetaLinkRayObligation_iff
    (D : OrigXiFPaperSignedHullData X l) (qPilotLogVolume : Real) :
    OrigXiFThetaLinkRayObligation D qPilotLogVolume ↔
      qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume D :=
  OrigXiFThetaLinkRay_iff_le D qPilotLogVolume

/-- Producer direction for the `ThetaLink` field: the paper comparison
`-|log q| <= -|log Theta|` at the actual signed hull scalar gives the required
ray membership. -/
theorem OrigXiFthetaLinkRay_of_neg_abs_le
    (D : OrigXiFPaperSignedHullData X l) {qParameter : Real}
    (h : -|Real.log qParameter| ≤ OrigXiFSignedThetaHullLogVolume D) :
    -|Real.log qParameter| ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume :=
  (OrigXiFThetaLinkRay_iff_le D (-|Real.log qParameter|)).mpr h

/-- Consumer direction for `ThetaLinkActual.link_implies_inclusion`: at the
actual paper signed hull, the ray membership yields the actual signed-hull
log-volume inequality. -/
theorem OrigXiFle_of_thetaLinkRay
    (D : OrigXiFPaperSignedHullData X l) {qPilotLogVolume : Real}
    (h : qPilotLogVolume ∈
      hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume) :
    qPilotLogVolume ≤ OrigXiFSignedThetaHullLogVolume D :=
  (OrigXiFThetaLinkRay_iff_le D qPilotLogVolume).mp h

/-- The comparison in the precise form of IUT III, Corollary 3.12, Step
(xi-f), at the actual signed hull scalar. -/
theorem OrigXiFthetaLinkRay_iff_neg_abs_le
    (D : OrigXiFPaperSignedHullData X l) {qParameter : Real} :
    (-|Real.log qParameter| ∈
        hullLogVolumeRay (OrigXiFPaperSignedHull D).signedHullLogVolume) ↔
      -|Real.log qParameter| ≤ OrigXiFSignedThetaHullLogVolume D :=
  OrigXiFThetaLinkRay_iff_le D (-|Real.log qParameter|)

end OrigXiF
end XiFPaper
end LeanFormal.IUT
