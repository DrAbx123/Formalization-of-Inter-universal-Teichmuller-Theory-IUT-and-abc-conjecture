import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullVertexConvexityAssembly
import Mathlib.Tactic

/-!
# Card-HULLREAL: the signed wrapper layer for `-|log(Theta)|` (Step (xi-d)-(xi-f))

Task `hunit-epsilon-transfer-20261016`, signed-surface construction package
(stance recorded in `logs/coordination/hunit-epsilon-transfer-20261016.md`,
sections 15-16).  The Card-STEPXI-XIF-INCLUSION downdrill
(`SourceProcessionStepXIInclusionResidual.lean`) found that the pinned
comparison `q <= hullValue` has zero discriminating power on every realized
carrier: all in-tree real hull carriers are nonnegative
(`sourceRealHullVolume_nonneg`, `CertificateHullWiring.lean:251`) while the
corpus `q` is negative, so the inclusion holds from nonnegativity alone
(`negativeValue_le_sourceRealHullVolume`, same file `:196`).  This file
constructs the signed wrapper layer on which the corpus comparison has genuine
content.

Corpus anchors (IUT III, Corollary 3.12 proof, Step (xi)):

* (xi-d), III:10843-10848: `R^{<= -|log(Theta)|} := {lambda in R | lambda <=
  -|log(Theta)|} subset R; -|log(q)| in R`, where `-|log(Theta)|` is by
  definition the (negative) log-volume of `1,circ U`, and `-|log(q)|` is the
  log-volume of the region that arises from the representation of the q-pilot
  object at (1,0) on `1,circ U_Q`.
* (xi-e), III:10880-10887: the multiradial construction followed by the
  holomorphic hull and the log-volume yields a collection of possible
  log-volumes of output data `R^{<= -|log(Theta)|}`.
* (xi-f), III:10895-10898: the inclusion `-|log(q)| in R^{<= -|log(Theta)|}`,
  hence the inequality `-|log(q)| <= -|log(Theta)| in R`, i.e. `C_Theta >= -1`.
* The definition of `|log(Theta)|`, III:1051-1053 and III:990-993: the
  log-volume of the holomorphic hull of the union of possible images of the
  Theta-pilot object; this is exactly the tree's `sourceHullVolume`
  (`SourceImageHullVolume.lean:191-195`).

Contents:

* `sourceSignedHullLogVolume` / `sourceSignedImageLogVolume`: the signed
  carriers `-|log(Theta)|` and the negative image-union log-volume, with
  nonpositivity and the two sign-conversion laws relating the signed
  comparisons to the `ENNReal` layer of `sourceHullVolume`
  (`sourceSignedHullLogVolume_le_neg_iff`,
  `neg_le_sourceSignedHullLogVolume_iff`).  At `qSigned = -x` the (xi-f)
  inequality is exactly the non-vacuous upper bound
  `sourceHullVolume <= ofReal x` (the corpus "computation of an upper bound"
  shape, III:990-993), not the vacuous `ofReal q <= ...` shape that killed
  discriminating power on the nonnegative layer.
* `SourceXifSignedComparison`: the named condition carrying the corpus
  comparison at the value layer, with the signed certificate wiring
  (`sourceSignedHullCertificate`, `sourceSignedHullLinkEvidence`,
  `cor312OfSourceSignedHullComparison`) into the existing
  `FiniteCertificateBridge` consumer (`q_le_hull` face).
* The reduction `sourceSignedImageComparison_iff_realParts_eq`: with the
  possible-image region as the q-side carrier, the (xi-f) comparison is
  equivalent to the normalization "hull real part = image-union real part"
  (the (xi-d) "computed via the possible images" statement), i.e. to
  Card-HULLREAL hull-geometry content; the equivalent `ENNReal` normalization
  `sourceHullVolume = image-union volume` is recorded both ways.
* `sourceSignedSurface_comparison_not_forced_by_sign`: on the signed surface
  the comparison is not forced by the sign constraints (the discriminating
  power restored by the wrapper).
* Vertex form under the normalization
  (`sourceXifSignedComparison_neg_iff_forall_labelDegree_le_of_hullVolume_eq_imageVolume`):
  the comparison becomes the finite label check `deg_j <= x` for all signed
  labels, via `sourceSetVolume_possibleImageSet_le_ofReal_iff` and Card B's
  `sourceSetVolume_possibleImageSet_eq_labelSup`.
* Honest boundary: under pointwise degree faithfulness the signed hull carrier
  collapses to `0` (`sourceSignedHullLogVolume_eq_zero_of_degreeFaithful`) and
  the comparison becomes trivial
  (`sourceXifSignedComparison_trivial_of_degreeFaithful`); the content lives
  only in worlds where the hull volume is finite.  No degree-faithful premise
  is introduced as evidence anywhere, and the vacuous satisfaction is never a
  witness.

Not proved here: the corpus comparison itself.  It is supplied as the named
hypothesis `SourceXifSignedComparison`; the residual of
`SourceProcessionStepXIInclusionResidual.lean` is reduced to this condition,
not discharged.  No source carrier or arithmetic content is manufactured.

Paper route vs. our route: the corpus derives the inclusion from the
Theta x mu-LGP-link apparatus (tautological identification of the Theta-pilot
and q-pilot objects, III:1042-1058, 10880-10898).  The tree has no such
object, so the value-layer transcription takes the region carrier
`sourceHolomorphicHull` for the Theta side and the possible-image union for
the q side (the same cross-reference the corpus itself makes, III:10846-10847
"cf. the discussion of possible images"), and keeps the comparison as the
named condition; the corpus derivation is recorded only as the target shape.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe ua uv upi umon ui

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Signed carriers and sign facts -/

/-- The signed hull log-volume `-|log(Theta)|`: the negative of the real part
of the value-realized hull log-volume, i.e. of the tree's `sourceHullVolume`,
the log-volume of the source holomorphic hull of the union of possible
theta-pilot images (corpus III:1051-1053; III:10843-10848: `-|log(Theta)|` is
by definition the negative log-volume of `1,circ U`). -/
def sourceSignedHullLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : ℝ :=
  -(I.sourceRealHullVolume v R n)

/-- The signed possible-image log-volume: the negative of the real part of
the image-union log-volume `sourceSetVolume` over the possible theta-pilot
images.  This is the value-layer carrier standing for the corpus "region that
arises from the representation of the q-pilot object at (1,0) on
`1,circ U_Q`" (III:10847-10848), whose log-volume is `-|log(q)|`. -/
def sourceSignedImageLogVolume (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : ℝ :=
  -(I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal

/-- `-|log(Theta)|` is nonpositive: the sign carried by the corpus
(III:10846-10848). -/
theorem sourceSignedHullLogVolume_nonpos (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceSignedHullLogVolume v R n ≤ 0 :=
  neg_nonpos.mpr (I.sourceRealHullVolume_nonneg v R n)

/-- The signed image log-volume is nonpositive. -/
theorem sourceSignedImageLogVolume_nonpos (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceSignedImageLogVolume v R n ≤ 0 :=
  neg_nonpos.mpr ENNReal.toReal_nonneg

/-- (xi-d) identification at the value layer: the signed hull log-volume is
the negative of the real part of the log-volume of the source holomorphic
hull set carrier (the `1,circ U`-analog). -/
theorem sourceSignedHullLogVolume_eq_neg_hullSetVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    I.sourceSignedHullLogVolume v R n =
      -(I.sourceSetVolume v
        (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v))).toReal :=
  rfl

/-! ## 2. Sign-conversion laws: signed comparisons <-> the ENNReal layer -/

/-- **Sign-conversion law (lower side).**  For `0 <= x` and finite hull
volume, `-|log(Theta)| <= -x` is exactly the `ENNReal`-layer lower bound
`ofReal x <= sourceHullVolume`: moving to the signed surface loses no content. -/
theorem sourceSignedHullLogVolume_le_neg_iff (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) {x : ℝ} (hx : 0 ≤ x) :
    I.sourceSignedHullLogVolume v R n ≤ -x ↔
      ENNReal.ofReal x ≤ I.sourceHullVolume v R n := by
  unfold sourceSignedHullLogVolume sourceRealHullVolume
  rw [neg_le_neg_iff]
  constructor
  · intro h
    calc ENNReal.ofReal x ≤ ENNReal.ofReal (I.sourceHullVolume v R n).toReal :=
        ENNReal.ofReal_le_ofReal h
      _ = I.sourceHullVolume v R n := ENNReal.ofReal_toReal (ne_top_of_lt hfin)
  · intro h
    exact ofReal_le_toReal_of_ne_top (ne_top_of_lt hfin) h

/-- **Sign-conversion law (upper side).**  For `0 <= x` and finite hull
volume, `-x <= -|log(Theta)|` is exactly the `ENNReal` upper bound
`sourceHullVolume <= ofReal x`: the hull log-volume is bounded by the q-side
magnitude `x`.  This is the transfer consumed by the (xi-f) comparison at
`x := -qSigned`, and the value-layer reading of the corpus "computation of an
upper bound for |log(q)|" (III:990-993). -/
theorem neg_le_sourceSignedHullLogVolume_iff (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) {x : ℝ} (hx : 0 ≤ x) :
    -x ≤ I.sourceSignedHullLogVolume v R n ↔
      I.sourceHullVolume v R n ≤ ENNReal.ofReal x := by
  unfold sourceSignedHullLogVolume sourceRealHullVolume
  rw [neg_le_neg_iff]
  constructor
  · intro h
    calc I.sourceHullVolume v R n =
          ENNReal.ofReal (I.sourceHullVolume v R n).toReal :=
        (ENNReal.ofReal_toReal (ne_top_of_lt hfin)).symm
      _ ≤ ENNReal.ofReal x := ENNReal.ofReal_le_ofReal h
  · intro h
    exact toReal_le_of_le_ofReal hx h

/-! ## 3. The (xi-f) comparison as a named condition and its reductions -/

/-- The corpus (xi-f) comparison `-|log(q)| <= -|log(Theta)|`
(III:10895-10898) at the value layer: the signed q-value is at most the
signed hull log-volume.  This is the named condition under which the signed
certificate below closes; it is not derived here. -/
def SourceXifSignedComparison (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (qSigned : ℝ) : Prop :=
  qSigned ≤ I.sourceSignedHullLogVolume v R n

/-- The (xi-f) comparison at `qSigned = -x` is exactly the `ENNReal` upper
bound `sourceHullVolume <= ofReal x` (sign-conversion law, upper side). -/
theorem sourceXifSignedComparison_neg_iff (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) {x : ℝ} (hx : 0 ≤ x) :
    SourceXifSignedComparison I v R n (-x) ↔
      I.sourceHullVolume v R n ≤ ENNReal.ofReal x :=
  neg_le_sourceSignedHullLogVolume_iff I v R n hfin hx

/-- **Realized-direction law.**  The tree's hull contains the image union, so
in signed terms the hull value is at most the image value:
`-|log(Theta)| <= -(image-union log-volume)`.  This is the direction the
present carriers prove; the corpus direction (next lemma) is its converse. -/
theorem sourceSignedHullLogVolume_le_sourceSignedImageLogVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedHullLogVolume v R n ≤ I.sourceSignedImageLogVolume v R n := by
  unfold sourceSignedHullLogVolume sourceSignedImageLogVolume sourceRealHullVolume
  rw [neg_le_neg_iff]
  exact ENNReal.toReal_mono (ne_top_of_lt hfin)
    (I.sourceHullVolume_ge_imageVolume v R n)

/-- **Reduction law ((xi-f) <-> (xi-d) via-images normalization).**  With the
possible-image region as the q-side carrier, the corpus (xi-f) comparison
`-|log(q)| <= -|log(Theta)|` is equivalent to the real-part normalization
`sourceRealHullVolume = (image-union volume).toReal`: the hull log-volume is
computed by the possible images (III:10846-10848).  The tree proves the `>=`
half of the real-part equality by monotonicity; the corpus comparison supplies
the `<=` half.  Neither half is assumed here. -/
theorem sourceSignedImageComparison_iff_realParts_eq (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) :
    I.sourceSignedImageLogVolume v R n ≤ I.sourceSignedHullLogVolume v R n ↔
      I.sourceRealHullVolume v R n =
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal := by
  constructor
  · intro h
    have h1 : I.sourceRealHullVolume v R n ≤
        (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal := by
      unfold sourceSignedImageLogVolume sourceSignedHullLogVolume
        sourceRealHullVolume at h
      exact neg_le_neg_iff.mp h
    have h2 : (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal ≤
        I.sourceRealHullVolume v R n :=
      ENNReal.toReal_mono (ne_top_of_lt hfin)
        (I.sourceHullVolume_ge_imageVolume v R n)
    exact le_antisymm h1 h2
  · intro heq
    unfold sourceSignedImageLogVolume sourceSignedHullLogVolume sourceRealHullVolume
    unfold sourceRealHullVolume at heq
    rw [heq]

/-- **ENNReal form of the reduction.**  Under finiteness, the (xi-f)
comparison with the image-proxy carrier implies the `ENNReal`-level
normalization `sourceHullVolume = image-union volume` -- the (xi-d)
"computed via the possible images" identity, i.e. the Card-HULLREAL
hull-geometry content. -/
theorem sourceHullVolume_eq_imageVolume_of_signedImageComparison (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤)
    (hcomp : I.sourceSignedImageLogVolume v R n ≤ I.sourceSignedHullLogVolume v R n) :
    I.sourceHullVolume v R n =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) := by
  have heq := (sourceSignedImageComparison_iff_realParts_eq I v R n hfin).mp hcomp
  have hfinImg : I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) < ⊤ :=
    lt_of_le_of_lt (I.sourceHullVolume_ge_imageVolume v R n) hfin
  calc I.sourceHullVolume v R n = ENNReal.ofReal (I.sourceRealHullVolume v R n) :=
        I.sourceHullVolume_eq_ofReal v R n hfin
    _ = ENNReal.ofReal
          ((I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal) := by
        rw [heq]
    _ = I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) :=
        ENNReal.ofReal_toReal (ne_top_of_lt hfinImg)

/-- Converse of the reduction: the (xi-d) via-images normalization implies the
(xi-f) comparison with the image-proxy carrier (no finiteness needed). -/
theorem sourceSignedImageComparison_of_hullVolume_eq_imageVolume (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (heq : I.sourceHullVolume v R n =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :
    I.sourceSignedImageLogVolume v R n ≤ I.sourceSignedHullLogVolume v R n := by
  unfold sourceSignedImageLogVolume sourceSignedHullLogVolume sourceRealHullVolume
  have h : (I.sourceHullVolume v R n).toReal =
      (I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)).toReal :=
    congrArg ENNReal.toReal heq
  rw [h]

/-! ## 4. Finite vertex form of the image volume and of the comparison -/

/-- The image-union volume is at most `ofReal x` exactly when every signed
label's local log-degree is at most `x`: the finite vertex check (Card B's
`sourceSetVolume_possibleImageSet_eq_labelSup`) at the `ENNReal` layer. -/
theorem sourceSetVolume_possibleImageSet_le_ofReal_iff (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    {x : ℝ} (hx : 0 ≤ x) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n) ≤
        ENNReal.ofReal x ↔
      ∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ x := by
  rw [sourceSetVolume_possibleImageSet_eq_labelSup (I := I) v R n]
  constructor
  · intro h j
    have h1 := le_trans
      (le_iSup (fun j : SignedLabel l.value =>
        ENNReal.ofReal (I.sourceLocalLogDegree v
          (I.sourceThetaPilotPoint v R n j))) j) h
    exact (ENNReal.ofReal_le_ofReal_iff hx).mp h1
  · intro h
    exact iSup_le fun j =>
      (ENNReal.ofReal_le_ofReal_iff hx).mpr (h j)

/-- **Vertex form of the (xi-f) comparison** under the (xi-d) via-images
normalization: `-|log(q)| <= -|log(Theta)|` at `qSigned = -x` holds exactly
when every signed label's local log-degree is at most `x`.  The normalization
`sourceHullVolume = image-union volume` is an explicit hypothesis (its
geometric content is the Card-HULLREAL card), never an assumption. -/
theorem sourceXifSignedComparison_neg_iff_forall_labelDegree_le_of_hullVolume_eq_imageVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) {x : ℝ} (hx : 0 ≤ x)
    (heq : I.sourceHullVolume v R n =
      I.sourceSetVolume v (I.possibleThetaPilotImageSet v R n)) :
    SourceXifSignedComparison I v R n (-x) ↔
      ∀ j : SignedLabel l.value,
        I.sourceLocalLogDegree v (I.sourceThetaPilotPoint v R n j) ≤ x := by
  rw [sourceXifSignedComparison_neg_iff I v R n hfin hx, heq]
  exact sourceSetVolume_possibleImageSet_le_ofReal_iff I v R n hx

/-! ## 5. Discriminating power and the degree-faithful boundary -/

/-- On the signed surface the (xi-f) comparison is not forced by the sign
constraints alone: both sides negative does not give `qSigned <= hullSigned`.
This is the discriminating power restored by the wrapper, to be contrasted
with the automatic inclusion on the nonnegative layer
(`negativeValue_le_sourceRealHullVolume`,
`SourceProcessionStepXIInclusionResidual.lean:196`). -/
theorem sourceSignedSurface_comparison_not_forced_by_sign :
    ∃ qSigned hullSigned : ℝ, qSigned < 0 ∧ hullSigned < 0 ∧
      ¬ qSigned ≤ hullSigned :=
  ⟨-1, -2, by norm_num, by norm_num, by norm_num⟩

/-- Under pointwise degree faithfulness the value-realized hull volume is
`⊤`, so the signed hull carrier collapses to `0` (the top of its range).  The
empty-premise world is recorded here so that the trivial satisfaction below is
never cited as content. -/
theorem sourceSignedHullLogVolume_eq_zero_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    I.sourceSignedHullLogVolume v R n = 0 := by
  unfold sourceSignedHullLogVolume sourceRealHullVolume
  rw [I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg,
    ENNReal.toReal_top, neg_zero]

/-- In the degree-faithful world the (xi-f) comparison holds vacuously for
every negative signed q-value: a property of the collapsed carrier, not
evidence for the corpus comparison.  No degree-faithful premise may be used
as a nonempty-premise witness. -/
theorem sourceXifSignedComparison_trivial_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (qSigned : ℝ) (hqneg : qSigned < 0)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    SourceXifSignedComparison I v R n qSigned := by
  unfold SourceXifSignedComparison
  rw [sourceSignedHullLogVolume_eq_zero_of_degreeFaithful I v R n hdeg]
  exact le_of_lt hqneg

/-! ## 6. Consumer wiring: the signed certificate into the Step-XI bridge -/

/-- Canonical unit-weight data on the signed labels; the weights carry no
volume content.  All content sits in the comparison hypothesis of
`sourceSignedHullCertificate`. -/
def sourceSignedLabelUnitWeights (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    WeightedValues (SignedLabel l.value) where
  value := fun _ => I.sourceSignedHullLogVolume v R n
  weight := fun _ => 1
  weightTotal := Fintype.card (SignedLabel l.value)
  weightTotal_pos :=
    Nat.cast_pos.mpr (Fintype.card_pos_iff.mpr ⟨zeroSignedLabel (l := l)⟩)
  weightTotal_eq_sum := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

/-- The canonical signed finite hull over the signed labels: every label
volume equals the signed hull cap `-|log(Theta)|`.  Bookkeeping for the
certificate interface; the vertex-hull geometry is the Card-HULLREAL card,
not this shell. -/
def sourceSignedThetaPilotFiniteHull (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : FiniteHull (SignedLabel l.value) where
  volume := fun _ => I.sourceSignedHullLogVolume v R n
  hullVolume := I.sourceSignedHullLogVolume v R n
  contains := fun _ => le_rfl

/-- **Faithful signed certificate.**  The `StepXIFiniteCertificate` whose hull
volume is the signed cap `-|log(Theta)| <= 0` (not the nonnegative real hull
volume of `iqHullCertificate`), with `thetaSigned := 0` and the corpus
comparison supplied as the named hypothesis. -/
def sourceSignedHullCertificate (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (qSigned : ℝ)
    (hq : qSigned ≤ I.sourceSignedHullLogVolume v R n) (hqneg : qSigned < 0) :
    StepXIFiniteCertificate (SignedLabel l.value) where
  hull := sourceSignedThetaPilotFiniteHull I v R n
  weighted := sourceSignedLabelUnitWeights I v R n
  weighted_matches_hull := fun _ => rfl
  weights_nonnegative := fun _ => zero_le_one
  qSigned := qSigned
  thetaSigned := 0
  q_le_hull := hq
  hull_le_theta := I.sourceSignedHullLogVolume_nonpos v R n
  q_negative := hqneg

/-- Link evidence for the signed certificate with `targetSigned` the signed
hull cap. -/
def sourceSignedHullLinkEvidence (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) (qSigned : ℝ)
    (hq : qSigned ≤ I.sourceSignedHullLogVolume v R n) (hqneg : qSigned < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (sourceSignedHullCertificate I v R n qSigned hq hqneg) where
  targetSigned := I.sourceSignedHullLogVolume v R n
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := hq
  target_le_theta := I.sourceSignedHullLogVolume_nonpos v R n

/-- **Signed headline composition.**  Given the corpus (xi-f) comparison as
hypothesis (`hq`, the residual input), the signed certificate assembles
through the existing `FiniteCertificateBridge` to the Corollary 3.12 contract
conclusion on the signed surface. -/
theorem cor312OfSourceSignedHullComparison (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) (qSigned : ℝ)
    (hq : qSigned ≤ I.sourceSignedHullLogVolume v R n) (hqneg : qSigned < 0)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((sourceSignedHullCertificate I v R n qSigned hq hqneg).toContract
        (sourceSignedHullLinkEvidence I v R n qSigned hq hqneg ipl she apt
          hipl hshe hapt)) :=
  cor312_of_finite_certificate _ _

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the signed wrapper layer of the Card-HULLREAL `q <= hull`
face: the value-layer carriers `-|log(Theta)|` and the negative image-union
log-volume, the sign-conversion laws to the `ENNReal` layer, the (xi-f)
comparison as a named condition, its reductions (via-images normalization,
finite vertex form), and the signed certificate wiring into
`FiniteCertificateBridge`.  The corpus comparison itself remains a supplied
hypothesis; this is not the corpus `C_Theta >= -1` statement. -/
def cardHullRealSignedLogVolume : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-signed-log-volume"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-f) (III:10843-10898); " ++
        "definition of |log(Theta)| (III:990-993, 1051-1053)"
    status := VerificationStatus.interface
    note :=
      "Signed wrapper layer constructed: sourceSignedHullLogVolume = " ++
        "-|log(Theta)| (nonpositive; = -sourceRealHullVolume); sign-conversion " ++
        "laws to the ENNReal sourceHullVolume layer (at qSigned = -x the " ++
        "(xi-f) inequality is exactly sourceHullVolume <= ofReal x, restoring " ++
        "discriminating power); the (xi-f) comparison as the named condition " ++
        "SourceXifSignedComparison; reduction: with the possible-image region " ++
        "as q-side carrier the comparison is equivalent to " ++
        "sourceRealHullVolume = (image-union volume).toReal, i.e. the (xi-d) " ++
        "via-images normalization (Card-HULLREAL content), with the finite " ++
        "vertex form deg_j <= x; signed certificate wiring to Cor312Conclusion. " ++
        "NOT proved: the corpus comparison itself (supplied hypothesis; the " ++
        "residual of sourceProcessionStepXIXifInclusionResidual is reduced to " ++
        "this condition, not discharged); under degree faithfulness the signed " ++
        "carrier collapses to 0 and the comparison is vacuous (recorded, never " ++
        "used as evidence)."
    dependsOn :=
      [ "IUT-III.source-procession-stepXI-xif-inclusion"
      , "IUT-III.corollary-3.12-card-hullreal-geometry-gap-cards"
      , "IUT-III.corollary-3.12-card-hullreal-omodule-compactness"
      , "IUT-III.holomorphic-hull-determinant-log-volume" ] }

end LeanFormal.IUT.Audit