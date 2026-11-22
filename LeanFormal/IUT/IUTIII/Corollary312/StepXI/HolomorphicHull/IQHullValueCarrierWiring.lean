import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringRealization
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HaarTranslateInterface
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.PadicLogShellModel

/-!
# Wiring the landed test carriers into the N14 certificate slots (Card-HULLREAL)

`CertificateHullWiring.lean` wires any realization `W : IQHullLogVolumeInterface X`
into the Step-XI finite-certificate consumers but leaves the following slots as
supplied hypotheses (`iqHullCertificate`, :155; the composed terminal
`iqHullCor312Conclusion`, :204):

* the realization `W` itself (the value carrier);
* the interface-level bounds `ofReal q <= W.logVolume W.imageSet` and
  `W.logVolume W.hull <= ofReal theta`, with `0 <= theta` and `q < 0`.

This module wires the two landed test carriers into those slots, and registers the
value-carrier boundary instead of hiding it:

* `IQHullValueCarrierWiring.iqHullPointWiringCertificate`: for **any** realization
  `W` and any carrier point `p` of its image union, the canonical slot values
  `q = -1` and `theta = iqHullRealVolume W` satisfy all four hypotheses, and the
  full certificate, link evidence and `Cor312Conclusion` are constructed (all
  proved; IPL/SHE/APT stay supplied inputs);
* `haarTranslatePointWiring*`: instantiation at the Haar-translate model
  (`HaarTranslateInterface.lean`) on a locally compact group, conditional on a
  carrier point `p` of the hull region;
* `padicLogShellPointWiring*`: instantiation at the non-archimedean log-shell
  model (`PadicLogShellModel.lean`), unconditional in the scaling element `lam`
  (the point `lam` always lies in the translated unit ball), with the slot values
  computed: `q = -1` and `theta = 1` for the normalized unit ball.

At the value-realized carrier `I.ThetaPilotPoint v` the wiring boundary is
recorded in `Theorem311Source.OriginalInput`:

* `not_logVolume_eq_sourceHullVolume_of_degreeFaithful`: no realization at the
  value carrier can identify its hull log-volume with the value-realized hull
  log-volume of a procession that is pointwise degree-faithful (the interface
  field `hull_logVolume_lt_top` demands finiteness, while the value-realized hull
  volume is `⊤` by `sourceHullVolume_eq_top_of_degreeFaithful`); this is the
  log-volume-level form of the parked no-go at the exact N14 slot;
* `thetaPilotPointValueCarrierWiring_of_realization`: the exact missing supply
  typed at the consumer carrier — a realization plus one point of its image
  union; the hypotheses of that theorem are precisely the Card-HULLREAL gap, and
  no realization is constructed here.

Reductions (do not overclaim): the model instantiations are test-carrier
instances (`VerificationStatus.testCarrier`), not realizations of the literal
`IQ(S+-_{j+1}; n,circ D^vdash_{vQ})` carrier; the paper's normalized log-volume
of [AbsTopIII] Proposition 5.7 / Corollary 5.10 is not formalized; at the value
level the contraction slot `q < 0` is the packet condition `thetaValueAt < 1`,
not a consequence of `OriginalInput`.

Consumer interface names: `LeanFormal.IUT.iqHullCertificate` and
`LeanFormal.IUT.iqHullCor312Conclusion` (`CertificateHullWiring.lean`), consumed
unchanged.  Evidence: probe
`tmp/outsider-survey-iq-carrier-20261016/AxiomProbeWiring.lean` and the build logs
in the same directory; landing report
`logs/coordination/iq-hull-haar-logshell-landing-20261016.md`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u v ua uv upi umon ui

noncomputable section

namespace IQHullValueCarrierWiring

open MeasureTheory

/-! ## 1. Canonical N14 slot values for an arbitrary realization -/

/-- The canonical lower slot value `q = -1` is interface-admissible for every
realization: `ofReal (-1) = 0`, and log-volume values are nonnegative. -/
theorem ofReal_neg_one_le_logVolume_imageSet {X : Type u}
    (W : IQHullLogVolumeInterface X) :
    ENNReal.ofReal (-1 : ℝ) ≤ W.logVolume W.imageSet := by
  rw [ENNReal.ofReal_of_nonpos (by norm_num : (-1 : ℝ) ≤ 0)]
  exact zero_le

/-- The canonical upper slot value `theta = toReal (logVolume hull)` always bounds
the hull log-volume at the interface level, by the proved finiteness of the hull
log-volume (`IQHullLogVolumeInterface.hull_logVolume_lt_top`). -/
theorem logVolume_hull_le_ofReal_toReal {X : Type u}
    (W : IQHullLogVolumeInterface X) :
    W.logVolume W.hull ≤ ENNReal.ofReal (W.logVolume W.hull).toReal :=
  le_of_eq (ENNReal.ofReal_toReal (ne_top_of_lt W.hull_logVolume_lt_top)).symm

/-! ## 2. The generic one-point adapter (all four slots filled) -/

/-- One-point weighted data of a carrier point: unit weight, value the real
singleton log-volume at the point. -/
def iqHullPointWeightedValues {X : Type u} (W : IQHullLogVolumeInterface X) (p : X) :
    WeightedValues Unit where
  value := fun _ => (W.logVolume {p}).toReal
  weight := fun _ => 1
  weightTotal := 1
  weightTotal_pos := one_pos
  weightTotal_eq_sum := by simp

/-- The one-point weighted values match the consumer's finite-hull volumes. -/
theorem iqHullPointWeightedValues_matches {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : X) (hp : p ∈ W.imageSet) (i : Unit) :
    (iqHullPointWeightedValues W p).value i =
      (iqHullFiniteHull W (fun _ => p) (fun _ => hp)).volume i :=
  rfl

/-- **Generic N14 slot adapter.**  From any realization `W` and any carrier point
`p` of the image union, the full certificate is constructed with the canonical
values `q = -1` and `theta = iqHullRealVolume W`; all four slot hypotheses are
discharged by proved lemmas. -/
def iqHullPointWiringCertificate {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : X) (hp : p ∈ W.imageSet) : StepXIFiniteCertificate Unit :=
  iqHullCertificate W (fun _ => p) (fun _ => hp) (iqHullPointWeightedValues W p)
    (iqHullPointWeightedValues_matches W p hp) (fun _ => zero_le_one)
    (-1) (iqHullRealVolume W) (ofReal_neg_one_le_logVolume_imageSet W)
    (logVolume_hull_le_ofReal_toReal W) (iqHullRealVolume_nonneg W) (by norm_num)

/-- The certificate's lower slot carries `q = -1`. -/
theorem iqHullPointWiringCertificate_qSigned {X : Type u}
    (W : IQHullLogVolumeInterface X) (p : X) (hp : p ∈ W.imageSet) :
    (iqHullPointWiringCertificate W p hp).qSigned = -1 :=
  rfl

/-- The certificate's upper slot carries `theta = iqHullRealVolume W`. -/
theorem iqHullPointWiringCertificate_thetaSigned {X : Type u}
    (W : IQHullLogVolumeInterface X) (p : X) (hp : p ∈ W.imageSet) :
    (iqHullPointWiringCertificate W p hp).thetaSigned = iqHullRealVolume W :=
  rfl

/-- The certificate's hull volume is the real hull log-volume of the realization. -/
theorem iqHullPointWiringCertificate_hullVolume {X : Type u}
    (W : IQHullLogVolumeInterface X) (p : X) (hp : p ∈ W.imageSet) :
    (iqHullPointWiringCertificate W p hp).hull.hullVolume = iqHullRealVolume W :=
  rfl

/-- The canonical upper slot is tight at the interface level: the hull
log-volume is exactly the `ofReal` of the certificate's `theta`. -/
theorem iqHullPointWiring_theta_is_tight {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : X) (hp : p ∈ W.imageSet) :
    W.logVolume W.hull =
      ENNReal.ofReal (iqHullPointWiringCertificate W p hp).thetaSigned := by
  rw [iqHullPointWiringCertificate_thetaSigned]
  exact iqHull_logVolume_hull_eq_ofReal W

/-- The one-point weighted average is bounded by the real hull log-volume. -/
theorem iqHullPointWeightedValues_average_le {X : Type u}
    (W : IQHullLogVolumeInterface X) (p : X) (hp : p ∈ W.imageSet) :
    (iqHullPointWeightedValues W p).average ≤ iqHullRealVolume W :=
  iqHullFiniteHull_average_le W (fun _ => p) (fun _ => hp) (iqHullPointWeightedValues W p)
    (iqHullPointWeightedValues_matches W p hp) (fun _ => zero_le_one)

/-- The link evidence at the generic adapter; the IPL/SHE/APT propositions and
their evidence remain supplied inputs. -/
def iqHullPointWiringLinkEvidence {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : X) (hp : p ∈ W.imageSet) (ipl she apt : Prop) (hipl : ipl) (hshe : she)
    (hapt : apt) :
    FiniteStepXILinkEvidence (iqHullPointWiringCertificate W p hp) :=
  iqHullLinkEvidence W (fun _ => p) (fun _ => hp) (iqHullPointWeightedValues W p)
    (iqHullPointWeightedValues_matches W p hp) (fun _ => zero_le_one)
    (-1) (iqHullRealVolume W) (ofReal_neg_one_le_logVolume_imageSet W)
    (logVolume_hull_le_ofReal_toReal W) (iqHullRealVolume_nonneg W) (by norm_num)
    ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the generic adapter. -/
theorem iqHullPointWiringCor312Conclusion {X : Type u} (W : IQHullLogVolumeInterface X)
    (p : X) (hp : p ∈ W.imageSet) (ipl she apt : Prop) (hipl : ipl) (hshe : she)
    (hapt : apt) :
    Cor312Conclusion
      ((iqHullPointWiringCertificate W p hp).toContract
        (iqHullPointWiringLinkEvidence W p hp ipl she apt hipl hshe hapt)) :=
  cor312_of_finite_certificate (iqHullPointWiringCertificate W p hp)
    (iqHullPointWiringLinkEvidence W p hp ipl she apt hipl hshe hapt)

/-! ## 3. Instantiation at the Haar-translate model -/

namespace HaarTranslateWiring

variable {G : Type u} [Group G] [TopologicalSpace G] [MeasurableSpace G] [MeasurableMul G]

/-- The N14 certificate at the Haar-translate model: any carrier point of the hull
region fills the slots with `q = -1` and `theta = toReal (mu hull)`. -/
def haarTranslatePointWiringCertificate (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu]
    (gamma : HaarTranslateModel.HaarTranslateCarrier G) (p : G) (hp : p ∈ gamma.hull) :
    StepXIFiniteCertificate Unit :=
  iqHullPointWiringCertificate (gamma.toIQHullLogVolumeInterface mu) p hp

/-- The Haar-translate certificate's upper slot is the real hull measure. -/
theorem haarTranslatePointWiringCertificate_thetaSigned (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu]
    (gamma : HaarTranslateModel.HaarTranslateCarrier G) (p : G) (hp : p ∈ gamma.hull) :
    (haarTranslatePointWiringCertificate mu gamma p hp).thetaSigned =
      (mu gamma.hull).toReal :=
  rfl

/-- The link evidence at the Haar-translate model. -/
def haarTranslatePointWiringLinkEvidence (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu]
    (gamma : HaarTranslateModel.HaarTranslateCarrier G) (p : G) (hp : p ∈ gamma.hull)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence (haarTranslatePointWiringCertificate mu gamma p hp) :=
  iqHullPointWiringLinkEvidence (gamma.toIQHullLogVolumeInterface mu) p hp
    ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the Haar-translate model. -/
theorem haarTranslatePointWiringCor312Conclusion (mu : Measure G)
    [MeasureTheory.Measure.IsHaarMeasure mu]
    (gamma : HaarTranslateModel.HaarTranslateCarrier G) (p : G) (hp : p ∈ gamma.hull)
    (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((haarTranslatePointWiringCertificate mu gamma p hp).toContract
        (haarTranslatePointWiringLinkEvidence mu gamma p hp ipl she apt hipl hshe hapt)) :=
  iqHullPointWiringCor312Conclusion (gamma.toIQHullLogVolumeInterface mu) p hp
    ipl she apt hipl hshe hapt

end HaarTranslateWiring

/-! ## 4. Instantiation at the p-adic log-shell model -/

namespace PadicLogShellWiring

variable (p : ℕ) [Fact p.Prime]

/-- The scaling element lies in its own image union: it is the image of `0` under
the translation, and `0` lies in the unit ball. -/
theorem padicLogShell_self_mem_imageSet (lam : ℚ_[p]) :
    lam ∈ (PadicLogShellModel.padicLogShellInterface p lam).imageSet :=
  ⟨0, by rw [Metric.mem_closedBall, dist_self]; exact zero_le_one, by simp⟩

/-- The N14 certificate at the p-adic log-shell model, unconditional in the
scaling element `lam` (no slot hypothesis is needed). -/
def padicLogShellPointWiringCertificate (lam : ℚ_[p]) :
    StepXIFiniteCertificate Unit :=
  iqHullPointWiringCertificate (PadicLogShellModel.padicLogShellInterface p lam) lam
    (padicLogShell_self_mem_imageSet p lam)

/-- The p-adic certificate's lower slot carries `q = -1`. -/
theorem padicLogShellPointWiringCertificate_qSigned (lam : ℚ_[p]) :
    (padicLogShellPointWiringCertificate p lam).qSigned = -1 :=
  rfl

/-- The p-adic certificate's upper slot is the real log-volume of the translated
unit ball. -/
theorem padicLogShellPointWiringCertificate_thetaSigned_translatedBall (lam : ℚ_[p]) :
    (padicLogShellPointWiringCertificate p lam).thetaSigned =
      (PadicLogShellModel.padicLogVolume p
        ((fun x => lam + x) '' Metric.closedBall (0 : ℚ_[p]) 1)).toReal :=
  rfl

/-- By Haar translation invariance the translated unit ball carries exactly the
unit-ball log-volume. -/
theorem padicLogShellPointWiringCertificate_thetaSigned (lam : ℚ_[p]) :
    (padicLogShellPointWiringCertificate p lam).thetaSigned =
      (PadicLogShellModel.padicLogVolume p (Metric.closedBall (0 : ℚ_[p]) 1)).toReal := by
  rw [padicLogShellPointWiringCertificate_thetaSigned_translatedBall,
    PadicLogShellModel.padicLogShell_scaledUnitRegion_measure_eq p lam]

/-- The normalized unit-ball log-volume is one (the measure of the log-shell
model is normalized on `Z_p`). -/
theorem padicLogShell_unitRegion_logVolume_eq_one :
    PadicLogShellModel.padicLogVolume p (Metric.closedBall (0 : ℚ_[p]) 1) = 1 :=
  MeasureTheory.Measure.addHaarMeasure_self

/-- The p-adic certificate's upper slot computes to `theta = 1`: the concrete
slot value at the normalized non-archimedean model. -/
theorem padicLogShellPointWiringCertificate_thetaSigned_eq_one (lam : ℚ_[p]) :
    (padicLogShellPointWiringCertificate p lam).thetaSigned = 1 := by
  rw [padicLogShellPointWiringCertificate_thetaSigned,
    padicLogShell_unitRegion_logVolume_eq_one, ENNReal.toReal_one]

/-- The link evidence at the p-adic log-shell model. -/
def padicLogShellPointWiringLinkEvidence (lam : ℚ_[p]) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) :
    FiniteStepXILinkEvidence (padicLogShellPointWiringCertificate p lam) :=
  iqHullPointWiringLinkEvidence (PadicLogShellModel.padicLogShellInterface p lam) lam
    (padicLogShell_self_mem_imageSet p lam) ipl she apt hipl hshe hapt

/-- The composed Corollary 3.12 conclusion at the p-adic log-shell model. -/
theorem padicLogShellPointWiringCor312Conclusion (lam : ℚ_[p]) (ipl she apt : Prop)
    (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((padicLogShellPointWiringCertificate p lam).toContract
        (padicLogShellPointWiringLinkEvidence p lam ipl she apt hipl hshe hapt)) :=
  iqHullPointWiringCor312Conclusion (PadicLogShellModel.padicLogShellInterface p lam) lam
    (padicLogShell_self_mem_imageSet p lam) ipl she apt hipl hshe hapt

end PadicLogShellWiring

end IQHullValueCarrierWiring

/-! ## 5. The value-carrier boundary (Card-HULLREAL): obstruction and minimal typing -/

namespace Theorem311Source
namespace OriginalInput

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- **Bridge obstruction at the value carrier.**  Under pointwise degree
faithfulness, no realization at the value carrier can identify its hull
log-volume with the value-realized hull log-volume of a faithful procession: the
interface field `hull_logVolume_lt_top` demands finiteness, while the
value-realized hull volume is `⊤` (`sourceHullVolume_eq_top_of_degreeFaithful`).
This is the log-volume-level form of the parked no-go (pointwise degree
faithfulness with the value single-monad realization) stated at the exact N14
slot; the Card-HULLREAL supply therefore cannot be a plain volume identification
at a faithful procession. -/
theorem not_logVolume_eq_sourceHullVolume_of_degreeFaithful (v : V)
    (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (hdeg : ∀ b : ℝ,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b)
    (W : IQHullLogVolumeInterface (I.ThetaPilotPoint v))
    (hlink : W.logVolume W.hull = I.sourceHullVolume v R n) : False := by
  have htop := I.sourceHullVolume_eq_top_of_degreeFaithful v R n hdeg
  have hfin := W.hull_logVolume_lt_top
  rw [hlink, htop] at hfin
  exact lt_irrefl (⊤ : ENNReal) hfin

/-- **Minimal-bridge typing at the value carrier.**  If the Card-HULLREAL supply
provides a realization at the value carrier together with one point of its image
union, the entire N14 slot package follows from the proved generic adapter.  The
hypotheses of this theorem are exactly the missing supply; no realization is
constructed here, and the accompanying obstruction theorem constrains what any
faithful such realization can identify. -/
theorem thetaPilotPointValueCarrierWiring_of_realization (v : V)
    (W : IQHullLogVolumeInterface (I.ThetaPilotPoint v)) (p : I.ThetaPilotPoint v)
    (hp : p ∈ W.imageSet) (ipl she apt : Prop) (hipl : ipl) (hshe : she)
    (hapt : apt) :
    Cor312Conclusion
      ((IQHullValueCarrierWiring.iqHullPointWiringCertificate W p hp).toContract
        (IQHullValueCarrierWiring.iqHullPointWiringLinkEvidence W p hp
          ipl she apt hipl hshe hapt)) :=
  IQHullValueCarrierWiring.iqHullPointWiringCor312Conclusion W p hp
    ipl she apt hipl hshe hapt

end OriginalInput
end Theorem311Source

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the model-level wiring of the landed test carriers into the
N14 certificate slots, with the value-carrier boundary registered (Card-HULLREAL). -/
def iqHullValueCarrierWiring : Obligation :=
  { id := "IUT-III.corollary-3.12-iq-hull-value-carrier-wiring"
    source :=
      "IUT III, Corollary 3.12, Step (xi): N14 certificate slots (iqHullCertificate, " ++
        "CertificateHullWiring.lean:155; iqHullCor312Conclusion, :204) filled from " ++
        "the landed test carriers; value-carrier boundary registered"
    status := VerificationStatus.testCarrier
    note :=
      "For any realization W and any point p of its image union, " ++
        "iqHullPointWiringCertificate constructs the full StepXIFiniteCertificate " ++
        "with the canonical slot values q = -1 and theta = iqHullRealVolume W; all " ++
        "four slot hypotheses are proved (ofReal_neg_one_le_logVolume_imageSet, " ++
        "logVolume_hull_le_ofReal_toReal, iqHullRealVolume_nonneg, norm_num), the " ++
        "upper slot is tight at the interface level (iqHullPointWiring_theta_is_tight), " ++
        "and the link evidence and Cor312Conclusion wrappers are constructed " ++
        "(IPL/SHE/APT remain supplied inputs). Instantiated unconditionally at the " ++
        "p-adic log-shell model (padicLogShellPointWiringCertificate: the scaling " ++
        "element is always a carrier point; theta computes to 1 by " ++
        "addHaarMeasure_self) and conditionally at the Haar-translate model " ++
        "(haarTranslatePointWiringCertificate). Value-carrier gap registered, not " ++
        "hidden: at X = I.ThetaPilotPoint v a realization W of " ++
        "IQHullLogVolumeInterface, one point p of its image union, and (for " ++
        "faithfulness of the theta slot) a volume identification " ++
        "W.logVolume W.hull = I.sourceHullVolume v R n at a FIXED procession n are " ++
        "exactly the missing supply; thetaPilotPointValueCarrierWiring_of_realization " ++
        "proves sufficiency of (W, p), while " ++
        "not_logVolume_eq_sourceHullVolume_of_degreeFaithful proves that no such " ++
        "identification exists at a pointwise degree-faithful procession (interface " ++
        "finiteness vs sourceHullVolume_eq_top_of_degreeFaithful); the contraction " ++
        "input q < 0 at the value level is the packet condition thetaValueAt < 1 " ++
        "(sourceThetaValue_neg_iff), independent of the carrier. Reductions: " ++
        "test-carrier instances, not the literal IQ(S+-_{j+1}; n,circ D^vdash_{vQ}) " ++
        "carrier; no [AbsTopIII] 5.7/5.10 normalized log-volume."
    dependsOn :=
      [ "IUT-III.corollary-3.12-step-XI-certificate-hull-wiring-realization",
        "IUT-III.corollary-3.12-haar-translate-interface-model",
        "IUT-III.corollary-3.12-padic-log-shell-model" ] }

end LeanFormal.IUT.Audit
