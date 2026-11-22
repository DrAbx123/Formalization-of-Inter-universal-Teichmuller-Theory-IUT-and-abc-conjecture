import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierHaarData

/-!
# Card-HULLREAL minimal bridge at the value-realized carrier

The consumer slots of `CertificateHullWiring.lean` (`iqHullCertificate`, :155;
`iqHullCor312Conclusion`, :204) at the *real* value carrier `I.ThetaPilotPoint v`
require a realization `W : IQHullLogVolumeInterface (I.ThetaPilotPoint v)`, a point
of its image union, and the slot values.  This module delivers the minimal bridge
that is actually provable at this level, and records exactly what is missing.

## 1. Object level: conditional supplies, unconditional impossibility

An interface realization at the value carrier whose `logVolume` is the source set
log-volume `I.sourceSetVolume v` and whose hull is the actual source holomorphic
hull exists **if and only if** the hull is bounded in log-degree
(`exists_iqHullLogVolumeInterface_hull_iff_exists_logDegree_le`).  Two conditional
supplies are used here:

* `D : I.SourceUnitRegionHaarData v R n` -- the genuine unit-region/Haar datum (unit
  region `O`, scaling `lambda`, log-degree bound on `O`, the paper-shaped containment
  `hull ⊆ lambda·O`, and the contraction `logDegree lambda <= 0`); this realizes the
  interface with `imageSet = possibleThetaPilotImageSet`, `hull = sourceHolomorphicHull`,
  `logVolume = sourceSetVolume` (`sourceUnitRegionHaarInterface`);
* `hfin : I.sourceHullVolume v R n < ⊤` -- the weaker supply used by the unit-scaling
  interface (`sourceHullUnitScalingInterface`), whose scaling field is degenerate.

Unconditionally, no faithful realization exists under pointwise degree faithfulness:
`not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful` and
`not_exists_iqHullLogVolumeInterface_hull_eq_of_degreeFaithful` (both via
`sourceHullVolume_eq_top_of_degreeFaithful`), together with
`not_exists_sourceHullLogDegreeBound_of_degreeFaithful` and
`not_nonempty_valueHullCompactnessInput_of_degreeFaithful`.  So the bridge below is
conditional on a named supply, and the missing input is source-geometry content
(compactness of the `1,circ U_{j,vQ}` / the `O`-module bound), not a Lean API gap.

## 2. What is bridged (one-point adapter pattern)

For the fixed procession `n` and the fixed label `j : SignedLabel l.value`, the
theta-pilot point `I.sourceThetaPilotPoint v R n j` lies in the image union
(`I.sourceThetaPilotPoint_mem`), so the one-point adapter pattern of the landed
`IQHullValueCarrierWiring` (its `iqHullPointWiring*` family) applies to each
conditional `W` and produces the full `StepXIFiniteCertificate Unit` and its
`Cor312Conclusion`.  The pattern is carried by route-local shims in
`SourceValueBridge` (shape-identical one-point weighted data, match lemma, and the
two slot lemmas over `iqHullCertificate` / `iqHullLinkEvidence`); they are kept
local so that this module depends only on the light `CertificateHullWiring` /
`IQCarrierHaarData` chain.  Deliverables:

* `sourceUnitRegionHaarPointWiringCertificate` /
  `sourceHullUnitScalingPointWiringCertificate` with canonical values `q = -1` and
  `theta = toReal` of the hull log-volume
  (`..._thetaSigned`, and tightness `..._theta_is_tight`);
* `sourceUnitRegionHaarNormalizedQ_certificate` /
  `sourceHullUnitScalingNormalizedQ_certificate`: the same construction carrying the
  **paper's** lower value `q = card * log (thetaValueAt (n.val) 0 j)`; the two Real
  hypotheses `hq` and `hq < 0` are *derived* from the single source inequality
  `thetaValueAt (n.val) 0 j < 1` through the existing equivalence
  `sourceThetaValue_neg_iff`, so the remaining contraction input is isolated as one
  real inequality (`OriginalInput` provides only `thetaValueAt_pos`).

## 3. Missing supplies (registered, not fabricated)

* `D : I.SourceUnitRegionHaarData v R n` (six fields, types as in
  `IQCarrierHaarData.lean:159-181`) or the weaker `hfin : I.sourceHullVolume v R n < ⊤`
  (equivalently a hull log-degree bound, `sourceHullVolume_lt_top_iff_exists_hullLogDegree_le`;
  obtainable from `hull ⊆ lambda·O` with bounded `O` via
  `sourceHullVolume_lt_top_of_scaledRegionImage`).  Quantifiers: `v`, `R`, `n` fixed;
  `D` at the same fixed `n`.
* `hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1` at the fixed label `j` (the packet
  contraction).  Not a consequence of `OriginalInput`; the conversion API already
  exists (`sourceThetaValue_neg_iff`).

Reductions (do not overclaim): the bridge is conditional on the named supplies; the
literal `IQ(S±_{j+1}; n,circ D^vdash_{vQ})` carrier is not realized; the unit-scaling
interface has a degenerate scaling field and only isolates the finiteness hypothesis;
nothing here proves the compactness of the `1,circ U_{j,vQ}`.

Consumer interface names (unchanged): `LeanFormal.IUT.iqHullCertificate`,
`LeanFormal.IUT.iqHullCor312Conclusion`, and the value-level consumer
`Theorem311Source.OriginalInput.sourceUnitRegionHaarData_cor312Conclusion`
(`IQCarrierHaarData.lean:353`).  Evidence: probe
`tmp/outsider-survey-iq-carrier-20261016/AxiomProbeBridge.lean` and the build logs in
the same directory; landing report
`logs/coordination/iq-hull-haar-logshell-landing-20261016.md`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

noncomputable section

universe u ua uv upi umon ui up um

namespace SourceValueBridge

/-! ## 0. Local one-point adapter shims (light-chain decoupling layer)

These four declarations have exactly the shape of the landed
`IQHullValueCarrierWiring.iqHullPointWeightedValues`,
`iqHullPointWeightedValues_matches`, `ofReal_neg_one_le_logVolume_imageSet`, and
`logVolume_hull_le_ofReal_toReal`; they are re-derived here so that this bridge
module depends only on `CertificateHullWiring` and `IQCarrierHaarData`.  The landed
module remains the canonical adapter for consumers on the full chain. -/

/-- One-point weighted data of a carrier point of an interface realization. -/
def pointWeightedValues {X : Type u} (W : IQHullLogVolumeInterface X) (p : X) :
    WeightedValues Unit where
  value := fun _ => (W.logVolume {p}).toReal
  weight := fun _ => 1
  weightTotal := 1
  weightTotal_pos := one_pos
  weightTotal_eq_sum := by simp

/-- The one-point weighted values match the consumer's finite-hull volumes. -/
theorem pointWeightedValues_matches {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : X) (hp : p ∈ W.imageSet) (i : Unit) :
    (pointWeightedValues W p).value i =
      (iqHullFiniteHull W (fun _ => p) (fun _ => hp)).volume i :=
  rfl

/-- The canonical lower slot value `q = -1` is interface-applicable for every
realization: `ofReal (-1) = 0`, and log-volume values are nonnegative. -/
theorem ofReal_neg_one_le_imageVolume {X : Type u} (W : IQHullLogVolumeInterface X) :
    ENNReal.ofReal (-1 : ℝ) ≤ W.logVolume W.imageSet := by
  rw [ENNReal.ofReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  exact zero_le

/-- The hull log-volume is bounded by the `ofReal` of its real part (the canonical
upper slot value `theta = toReal (logVolume hull)`). -/
theorem hull_le_ofReal_toReal {X : Type u} (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull ≤ ENNReal.ofReal (W.logVolume W.hull).toReal :=
  le_of_eq (ENNReal.ofReal_toReal (ne_top_of_lt W.hull_logVolume_lt_top)).symm

end SourceValueBridge

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Bridge from the unit-region/Haar data (genuine supply) -/

/-- The N14 certificate at the value carrier from the unit-region/Haar data: the
one-point adapter pattern fed by `sourceUnitRegionHaarInterface` and the theta-pilot
point of the fixed procession `n` at the fixed label `j` (canonical values `q = -1`
and `theta = toReal` of the hull log-volume). -/
def sourceUnitRegionHaarPointWiringCertificate (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value) :
    StepXIFiniteCertificate Unit :=
  iqHullCertificate (I.sourceUnitRegionHaarInterface v R n D)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    (-1) (iqHullRealVolume (I.sourceUnitRegionHaarInterface v R n D))
    (SourceValueBridge.ofReal_neg_one_le_imageVolume (I.sourceUnitRegionHaarInterface v R n D))
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceUnitRegionHaarInterface v R n D))
    (iqHullRealVolume_nonneg (I.sourceUnitRegionHaarInterface v R n D))
    (by norm_num)

/-- The certificate's lower slot carries `q = -1`. -/
theorem sourceUnitRegionHaarPointWiringCertificate_qSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value) :
    (I.sourceUnitRegionHaarPointWiringCertificate v R n D j).qSigned = -1 :=
  rfl

/-- The certificate's upper slot carries `theta = toReal` of the hull log-volume. -/
theorem sourceUnitRegionHaarPointWiringCertificate_thetaSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value) :
    (I.sourceUnitRegionHaarPointWiringCertificate v R n D j).thetaSigned =
      (I.sourceHullVolume v R n).toReal :=
  rfl

/-- The upper slot is tight at the interface level: the hull log-volume is exactly
the `ofReal` of the certificate's `theta`. -/
theorem sourceUnitRegionHaarPointWiring_theta_is_tight (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value) :
    I.sourceHullVolume v R n =
      ENNReal.ofReal
        (I.sourceUnitRegionHaarPointWiringCertificate v R n D j).thetaSigned := by
  rw [I.sourceUnitRegionHaarPointWiringCertificate_thetaSigned]
  exact iqHull_logVolume_hull_eq_ofReal (I.sourceUnitRegionHaarInterface v R n D)

/-- The link evidence at the unit-region/Haar route (IPL/SHE/APT supplied). -/
def sourceUnitRegionHaarPointWiringLinkEvidence (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence (I.sourceUnitRegionHaarPointWiringCertificate v R n D j) :=
  iqHullLinkEvidence (I.sourceUnitRegionHaarInterface v R n D)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    (-1) (iqHullRealVolume (I.sourceUnitRegionHaarInterface v R n D))
    (SourceValueBridge.ofReal_neg_one_le_imageVolume (I.sourceUnitRegionHaarInterface v R n D))
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceUnitRegionHaarInterface v R n D))
    (iqHullRealVolume_nonneg (I.sourceUnitRegionHaarInterface v R n D))
    (by norm_num) ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the unit-region/Haar route. -/
theorem sourceUnitRegionHaarPointWiringCor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceUnitRegionHaarPointWiringCertificate v R n D j).toContract
        (I.sourceUnitRegionHaarPointWiringLinkEvidence v R n D j
          ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate (I.sourceUnitRegionHaarPointWiringCertificate v R n D j)
    (I.sourceUnitRegionHaarPointWiringLinkEvidence v R n D j ipl she apt hipl hshe hapt)

/-- **Paper's `q` route.**  The certificate carrying the procession-normalized lower
value `q = card * log (thetaValueAt (n.val) 0 j)` in the signed lower slot; both Real
side conditions are derived from the single source contraction `thetaValueAt < 1`. -/
def sourceUnitRegionHaarNormalizedQ_certificate (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1) :
    StepXIFiniteCertificate Unit :=
  iqHullCertificate (I.sourceUnitRegionHaarInterface v R n D)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    ((Fintype.card (SourceVolumeIndex l) : ℝ) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j))
    ((I.sourceHullVolume v R n).toReal)
    (by
      have hneg : (Fintype.card (SourceVolumeIndex l) : ℝ) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
        (I.sourceThetaValue_neg_iff n j).mpr hθ1
      rw [ENNReal.ofReal_of_nonpos hneg.le]
      exact zero_le)
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceUnitRegionHaarInterface v R n D))
    ENNReal.toReal_nonneg
    ((I.sourceThetaValue_neg_iff n j).mpr hθ1)

/-- The normalized-`q` certificate's lower slot is the paper's value. -/
theorem sourceUnitRegionHaarNormalizedQ_certificate_qSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1) :
    (I.sourceUnitRegionHaarNormalizedQ_certificate v R n D j hθ1).qSigned =
      (Fintype.card (SourceVolumeIndex l) : ℝ) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j) :=
  rfl

/-- The link evidence at the normalized-`q` route. -/
def sourceUnitRegionHaarNormalizedQ_linkEvidence (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (I.sourceUnitRegionHaarNormalizedQ_certificate v R n D j hθ1) :=
  iqHullLinkEvidence (I.sourceUnitRegionHaarInterface v R n D)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceUnitRegionHaarInterface v R n D)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    ((Fintype.card (SourceVolumeIndex l) : ℝ) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j))
    ((I.sourceHullVolume v R n).toReal)
    (by
      have hneg : (Fintype.card (SourceVolumeIndex l) : ℝ) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
        (I.sourceThetaValue_neg_iff n j).mpr hθ1
      rw [ENNReal.ofReal_of_nonpos hneg.le]
      exact zero_le)
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceUnitRegionHaarInterface v R n D))
    ENNReal.toReal_nonneg
    ((I.sourceThetaValue_neg_iff n j).mpr hθ1)
    ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the normalized-`q` route. -/
theorem sourceUnitRegionHaarNormalizedQ_cor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (D : I.SourceUnitRegionHaarData v R n) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceUnitRegionHaarNormalizedQ_certificate v R n D j hθ1).toContract
        (I.sourceUnitRegionHaarNormalizedQ_linkEvidence v R n D j hθ1
          ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate (I.sourceUnitRegionHaarNormalizedQ_certificate v R n D j hθ1)
    (I.sourceUnitRegionHaarNormalizedQ_linkEvidence v R n D j hθ1
      ipl she apt hipl hshe hapt)

/-! ## 2. Bridge from the weaker finiteness supply (unit-scaling interface) -/

/-- The N14 certificate at the value carrier from the finiteness supply alone,
through the unit-scaling interface (`sourceHullUnitScalingInterface`). -/
def sourceHullUnitScalingPointWiringCertificate (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value) :
    StepXIFiniteCertificate Unit :=
  iqHullCertificate (I.sourceHullUnitScalingInterface v R n hfin)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    (-1) (iqHullRealVolume (I.sourceHullUnitScalingInterface v R n hfin))
    (SourceValueBridge.ofReal_neg_one_le_imageVolume (I.sourceHullUnitScalingInterface v R n hfin))
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceHullUnitScalingInterface v R n hfin))
    (iqHullRealVolume_nonneg (I.sourceHullUnitScalingInterface v R n hfin))
    (by norm_num)

/-- The certificate's lower slot carries `q = -1`. -/
theorem sourceHullUnitScalingPointWiringCertificate_qSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value) :
    (I.sourceHullUnitScalingPointWiringCertificate v R n hfin j).qSigned = -1 :=
  rfl

/-- The certificate's upper slot carries `theta = toReal` of the hull log-volume. -/
theorem sourceHullUnitScalingPointWiringCertificate_thetaSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value) :
    (I.sourceHullUnitScalingPointWiringCertificate v R n hfin j).thetaSigned =
      (I.sourceHullVolume v R n).toReal :=
  rfl

/-- The upper slot is tight at the interface level. -/
theorem sourceHullUnitScalingPointWiring_theta_is_tight (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value) :
    I.sourceHullVolume v R n =
      ENNReal.ofReal
        (I.sourceHullUnitScalingPointWiringCertificate v R n hfin j).thetaSigned := by
  rw [I.sourceHullUnitScalingPointWiringCertificate_thetaSigned]
  exact iqHull_logVolume_hull_eq_ofReal (I.sourceHullUnitScalingInterface v R n hfin)

/-- The link evidence at the unit-scaling route. -/
def sourceHullUnitScalingPointWiringLinkEvidence (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence (I.sourceHullUnitScalingPointWiringCertificate v R n hfin j) :=
  iqHullLinkEvidence (I.sourceHullUnitScalingInterface v R n hfin)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    (-1) (iqHullRealVolume (I.sourceHullUnitScalingInterface v R n hfin))
    (SourceValueBridge.ofReal_neg_one_le_imageVolume (I.sourceHullUnitScalingInterface v R n hfin))
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceHullUnitScalingInterface v R n hfin))
    (iqHullRealVolume_nonneg (I.sourceHullUnitScalingInterface v R n hfin))
    (by norm_num) ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the unit-scaling route. -/
theorem sourceHullUnitScalingPointWiringCor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceHullUnitScalingPointWiringCertificate v R n hfin j).toContract
        (I.sourceHullUnitScalingPointWiringLinkEvidence v R n hfin j
          ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate (I.sourceHullUnitScalingPointWiringCertificate v R n hfin j)
    (I.sourceHullUnitScalingPointWiringLinkEvidence v R n hfin j ipl she apt hipl hshe hapt)

/-- The paper's-`q` certificate at the unit-scaling route. -/
def sourceHullUnitScalingNormalizedQ_certificate (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1) :
    StepXIFiniteCertificate Unit :=
  iqHullCertificate (I.sourceHullUnitScalingInterface v R n hfin)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    ((Fintype.card (SourceVolumeIndex l) : ℝ) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j))
    ((I.sourceHullVolume v R n).toReal)
    (by
      have hneg : (Fintype.card (SourceVolumeIndex l) : ℝ) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
        (I.sourceThetaValue_neg_iff n j).mpr hθ1
      rw [ENNReal.ofReal_of_nonpos hneg.le]
      exact zero_le)
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceHullUnitScalingInterface v R n hfin))
    ENNReal.toReal_nonneg
    ((I.sourceThetaValue_neg_iff n j).mpr hθ1)

/-- The normalized-`q` certificate's lower slot is the paper's value. -/
theorem sourceHullUnitScalingNormalizedQ_certificate_qSigned (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1) :
    (I.sourceHullUnitScalingNormalizedQ_certificate v R n hfin j hθ1).qSigned =
      (Fintype.card (SourceVolumeIndex l) : ℝ) *
        Real.log (I.thetaValueAt (n.val : Int) 0 j) :=
  rfl

/-- The link evidence at the unit-scaling normalized-`q` route. -/
def sourceHullUnitScalingNormalizedQ_linkEvidence (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence
      (I.sourceHullUnitScalingNormalizedQ_certificate v R n hfin j hθ1) :=
  iqHullLinkEvidence (I.sourceHullUnitScalingInterface v R n hfin)
    (fun _ => I.sourceThetaPilotPoint v R n j)
    (fun _ => I.sourceThetaPilotPoint_mem v R n j)
    (SourceValueBridge.pointWeightedValues (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j))
    (SourceValueBridge.pointWeightedValues_matches (I.sourceHullUnitScalingInterface v R n hfin)
      (I.sourceThetaPilotPoint v R n j) (I.sourceThetaPilotPoint_mem v R n j))
    (fun _ => zero_le_one)
    ((Fintype.card (SourceVolumeIndex l) : ℝ) *
      Real.log (I.thetaValueAt (n.val : Int) 0 j))
    ((I.sourceHullVolume v R n).toReal)
    (by
      have hneg : (Fintype.card (SourceVolumeIndex l) : ℝ) *
          Real.log (I.thetaValueAt (n.val : Int) 0 j) < 0 :=
        (I.sourceThetaValue_neg_iff n j).mpr hθ1
      rw [ENNReal.ofReal_of_nonpos hneg.le]
      exact zero_le)
    (SourceValueBridge.hull_le_ofReal_toReal (I.sourceHullUnitScalingInterface v R n hfin))
    ENNReal.toReal_nonneg
    ((I.sourceThetaValue_neg_iff n j).mpr hθ1)
    ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the unit-scaling normalized-`q` route. -/
theorem sourceHullUnitScalingNormalizedQ_cor312Conclusion (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hfin : I.sourceHullVolume v R n < ⊤) (j : SignedLabel l.value)
    (hθ1 : I.thetaValueAt (n.val : Int) 0 j < 1)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((I.sourceHullUnitScalingNormalizedQ_certificate v R n hfin j hθ1).toContract
        (I.sourceHullUnitScalingNormalizedQ_linkEvidence v R n hfin j hθ1
          ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate
    (I.sourceHullUnitScalingNormalizedQ_certificate v R n hfin j hθ1)
    (I.sourceHullUnitScalingNormalizedQ_linkEvidence v R n hfin j hθ1
      ipl she apt hipl hshe hapt)

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the minimal Card-HULLREAL bridge at the value-realized
carrier: the conditional interface supplies, the one-point adapter wiring (light-chain
shims in `SourceValueBridge`), and the exact missing inputs. -/
def cardHullRealValueBridge : Obligation :=
  { id := "IUT-III.corollary-3.12-card-hullreal-value-bridge"
    source :=
      "IUT III, Corollary 3.12, Step (xi): value-carrier realization of the hull " ++
        "log-volume interface (Card-HULLREAL) -- conditional bridge and missing-input record"
    status := VerificationStatus.interface
    note :=
      "Conditional bridges at the real value carrier I.ThetaPilotPoint v, at a FIXED " ++
        "procession n. (1) From the unit-region/Haar data D : SourceUnitRegionHaarData " ++
        "v R n, the theta-pilot point of the image union, and the one-point adapter " ++
        "pattern (route-local SourceValueBridge shims, shape-identical to " ++
        "IQHullValueCarrierWiring), the canonical certificate (q = -1, theta tight at " ++
        "toReal of the hull log-volume) and its Cor312Conclusion are proved " ++
        "(sourceUnitRegionHaarPointWiring*). (2) The same from the weaker finiteness " ++
        "supply hfin : sourceHullVolume v R n < top through the unit-scaling interface " ++
        "(sourceHullUnitScalingPointWiring*). (3) With the paper's normalized q = " ++
        "card * log (thetaValueAt (n.val) 0 j) carried in the lower slot " ++
        "(sourceUnitRegionHaarNormalizedQ_certificate), the two Real hypotheses hq and " ++
        "q < 0 are DERIVED from the single source inequality thetaValueAt (n.val) 0 j < 1 " ++
        "via sourceThetaValue_neg_iff. MISSING SUPPLIES, not derivable at this level " ++
        "(proved: not_exists_sourceHullLogDegreeBound_of_degreeFaithful, " ++
        "not_exists_iqHullLogVolumeInterface_hull_subset_of_degreeFaithful, " ++
        "not_exists_iqHullLogVolumeInterface_hull_eq_of_degreeFaithful, " ++
        "not_nonempty_valueHullCompactnessInput_of_degreeFaithful): (a) D (six fields: " ++
        "unitRegion, scaling, degreeBound, hull_subset_scaledRegionImage, " ++
        "unitRegion_logDegree_le, scaling_logDegree_nonpos) or the weaker hfin " ++
        "(equivalently a hull log-degree bound, " ++
        "sourceHullVolume_lt_top_iff_exists_hullLogDegree_le); (b) thetaValueAt " ++
        "(n.val) 0 j < 1 at the fixed label j (OriginalInput gives only " ++
        "thetaValueAt_pos). Exact equivalence at the object level: " ++
        "exists_iqHullLogVolumeInterface_hull_iff_exists_logDegree_le. No new Lean API " ++
        "is needed: the gap is source-geometry content (compactness of the 1,circ " ++
        "U_{j,vQ} / the O-module bound), not an interface."
    dependsOn :=
      [ "IUT-III.corollary-3.12-iq-carrier-haar-data",
        "IUT-III.corollary-3.12-iq-hull-value-carrier-wiring",
        "IUT-III.corollary-3.12-source-image-hull-volume",
        "IUT-III.corollary-3.12-iq-hull-interface-discharge" ] }

end LeanFormal.IUT.Audit
