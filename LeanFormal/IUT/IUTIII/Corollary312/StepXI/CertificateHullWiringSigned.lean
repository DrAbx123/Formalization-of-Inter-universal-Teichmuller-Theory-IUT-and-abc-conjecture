import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceQSideComparison

/-!
  # A signed-lower-bound contract variant for the Step-XI certificate

  The old interface path `iqHullCertificate` accepts
  `hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet` and then converts that
  *nonnegative* extended-real statement back to a real inequality.  When
  `q < 0`, `ENNReal.ofReal q = 0`, so `hq` is automatic and contains no
  information about the signed value of `q`.  The real field obtained from it,
  `q ≤ (W.logVolume W.hull).toReal`, is also automatic because `toReal` is
  nonnegative.

  This file separates two issues.  `StepXIFiniteCertificateSigned` records the
  signed lower bound directly as a real field
  `q_le_hull : qSigned ≤ hull.hullVolume`, without routing it through
  `ENNReal.ofReal`.  The lemmas `ofReal_eq_zero_of_neg` and
  `iqHullCertificate_q_le_hull_of_neg` record the precise degeneracy of the
  old interface certificate for negative `q`.

  The correction does not supply the genuine source comparison
  `q ≤` the signed normalized theta log-volume.  In particular, the
  `iqHullCertificate` real hull volume is `(logVolume hull).toReal ≥ 0`, so the
  direct field is still automatic in that particular instantiation when
  `q < 0`.  The old path also pins `q` to the negative side and `theta` to the
  nonnegative side, so its `q ≤ theta` conclusion is only a sign consequence,
  not a signed comparison.  A non-vacuous source certificate must instantiate
  `hull.hullVolume` and `thetaSigned` with genuinely signed quantities and prove
  the comparison there.  That source comparison remains unproved.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT

universe u v

/-! ## 1. The old `hq` slot and its real consequence for negative `q` -/

/-- For negative `q`, the extended-real encoding `ENNReal.ofReal q` is zero.
Consequently the `hq` premise of `iqHullCertificate` carries no signed
information about `q`. -/
theorem ofReal_eq_zero_of_neg {q : ℝ} (hq : q < 0) : ENNReal.ofReal q = 0 :=
  ENNReal.ofReal_of_nonpos hq.le

/-- The real hull volume of an interface is always nonnegative, so every
negative `q` is below it without using the `hq` premise at all. -/
theorem q_le_hullVolume_of_neg {X : Type u} (W : IQHullLogVolumeInterface X)
    {q : ℝ} (hqneg : q < 0) :
    q ≤ (W.logVolume W.hull).toReal :=
  le_trans hqneg.le ENNReal.toReal_nonneg

/-- The same conclusion in the shape used by the old certificate path.  The
hypothesis `_hq` is retained for comparison with `iqHullCertificate`; the proof
shows that it is not needed once `q < 0`. -/
theorem q_le_hull_of_neg_of_hq {X : Type u} (W : IQHullLogVolumeInterface X)
    {q : ℝ} (_hq : ENNReal.ofReal q ≤ W.logVolume W.hull) (hqneg : q < 0) :
    q ≤ (W.logVolume W.hull).toReal :=
  q_le_hullVolume_of_neg W hqneg

/-- The old `hq` slot is satisfied for every interface realization as soon as
`q < 0`; no comparison with the image-union volume is involved. -/
theorem hqSlot_automatic_of_neg {X : Type u} (W : IQHullLogVolumeInterface X)
    {q : ℝ} (hqneg : q < 0) :
    ENNReal.ofReal q ≤ W.logVolume W.imageSet := by
  rw [ofReal_eq_zero_of_neg hqneg]
  exact zero_le

/-- The real `q_le_hull` field produced by the old `iqHullCertificate` is
automatic for negative `q` as well: its hull volume is the nonnegative real part
of the hull log-volume, not a signed comparison. -/
theorem iqHullCertificate_q_le_hull_of_neg {X : Type u}
    (W : IQHullLogVolumeInterface X) {label : Type v} [Fintype label]
    (pt : label → X) (hpt : ∀ i, pt i ∈ W.imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) (q θ : ℝ)
    (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (hθ : W.logVolume W.hull ≤ ENNReal.ofReal θ) (hθ0 : 0 ≤ θ)
    (hqneg : q < 0) :
    q ≤
      (iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg).hull.hullVolume := by
  simpa [iqHullCertificate, iqHullFiniteHull, iqHullRealVolume] using
    q_le_hullVolume_of_neg W hqneg

/-- The old `iqHullCertificate` carries the externally supplied `theta` as its
`thetaSigned` field, so `0 ≤ theta` is forced by the old `hθ0` slot. -/
theorem iqHullCertificate_theta_nonneg {X : Type u}
    (W : IQHullLogVolumeInterface X) {label : Type v} [Fintype label]
    (pt : label → X) (hpt : ∀ i, pt i ∈ W.imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) (q θ : ℝ)
    (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (hθ : W.logVolume W.hull ≤ ENNReal.ofReal θ) (hθ0 : 0 ≤ θ)
    (hqneg : q < 0) :
    0 ≤
      (iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg).thetaSigned := by
  change 0 ≤ θ
  exact hθ0

/-- **The old path's conclusion is sign-automatic.**  The constructed contract
has `qSigned = q < 0` and `thetaSigned = θ ≥ 0`, hence `q ≤ θ` without using the
`hq` or `hθ` extended-real bounds.  This records that the old interface cannot
stand in for a genuine signed comparison. -/
theorem iqHullCertificate_cor312Conclusion_automatic {X : Type u}
    (W : IQHullLogVolumeInterface X) {label : Type v} [Fintype label]
    (pt : label → X) (hpt : ∀ i, pt i ∈ W.imageSet)
    (data : WeightedValues label)
    (hvalue : ∀ i, data.value i = (iqHullFiniteHull W pt hpt).volume i)
    (hw : ∀ i, 0 ≤ data.weight i) (q θ : ℝ)
    (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet)
    (hθ : W.logVolume W.hull ≤ ENNReal.ofReal θ) (hθ0 : 0 ≤ θ)
    (hqneg : q < 0) (ipl she apt : Prop) (hipl : ipl) (hshe : she) (hapt : apt) :
    Cor312Conclusion
      ((iqHullCertificate W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg).toContract
        (iqHullLinkEvidence W pt hpt data hvalue hw q θ hq hθ hθ0 hqneg
          ipl she apt hipl hshe hapt)) := by
  change q ≤ θ
  exact le_trans hqneg.le hθ0

/-! ## 2. The signed certificate contract -/

/-- A Step-XI finite certificate whose signed lower bound is a direct real
inequality.  Unlike the old interface construction, this structure has no
`ENNReal.ofReal q` input slot: a producer must supply
`qSigned ≤ hull.hullVolume` as a real statement. -/
structure StepXIFiniteCertificateSigned (label : Type*) [Fintype label] where
  hull : FiniteHull label
  weighted : WeightedValues label
  weighted_matches_hull : ∀ i, weighted.value i = hull.volume i
  weights_nonnegative : ∀ i, 0 ≤ weighted.weight i
  qSigned : ℝ
  thetaSigned : ℝ
  q_le_hull : qSigned ≤ hull.hullVolume
  hull_le_theta : hull.hullVolume ≤ thetaSigned
  q_negative : qSigned < 0

/-- Forget the signed presentation and recover the existing finite certificate
shape.  The two structures carry the same fields; this adapter exists so that
the established `FiniteCertificateBridge` assembly can be reused unchanged. -/
def StepXIFiniteCertificateSigned.toStepXIFiniteCertificate
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificateSigned label) :
    StepXIFiniteCertificate label where
  hull := certificate.hull
  weighted := certificate.weighted
  weighted_matches_hull := certificate.weighted_matches_hull
  weights_nonnegative := certificate.weights_nonnegative
  qSigned := certificate.qSigned
  thetaSigned := certificate.thetaSigned
  q_le_hull := certificate.q_le_hull
  hull_le_theta := certificate.hull_le_theta
  q_negative := certificate.q_negative

/-- Link evidence for the signed contract.  It is the same evidence shape as
`FiniteStepXILinkEvidence`, but its two comparison fields are stated directly
against the signed certificate. -/
structure SignedFiniteStepXILinkEvidence {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificateSigned label) where
  targetSigned : ℝ
  ipl : Prop
  she : Prop
  apt : Prop
  ipl_evidence : ipl
  she_evidence : she
  apt_evidence : apt
  q_le_target : certificate.qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ certificate.thetaSigned

/-- Reinterpret signed link evidence as the existing bridge's link evidence
after forgetting the signed presentation. -/
def SignedFiniteStepXILinkEvidence.toFiniteStepXILinkEvidence
    {label : Type*} [Fintype label]
    {certificate : StepXIFiniteCertificateSigned label}
    (links : SignedFiniteStepXILinkEvidence certificate) :
    FiniteStepXILinkEvidence certificate.toStepXIFiniteCertificate where
  targetSigned := links.targetSigned
  ipl := links.ipl
  she := links.she
  apt := links.apt
  ipl_evidence := links.ipl_evidence
  she_evidence := links.she_evidence
  apt_evidence := links.apt_evidence
  q_le_target := links.q_le_target
  target_le_theta := links.target_le_theta

/-- Assemble the signed certificate into the Step-XI contract through the
existing finite-certificate bridge. -/
def StepXIFiniteCertificateSigned.toContract
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificateSigned label)
    (links : SignedFiniteStepXILinkEvidence certificate) : StepXIContract :=
  certificate.toStepXIFiniteCertificate.toContract
    links.toFiniteStepXILinkEvidence

/-- Corollary 3.12 conclusion from the signed certificate and its link
evidence.  This reuses the established `cor312_of_finite_certificate`
assembly via the explicit adapters above. -/
theorem cor312_of_signed_finite_certificate
    {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificateSigned label)
    (links : SignedFiniteStepXILinkEvidence certificate) :
    Cor312Conclusion (certificate.toContract links) := by
  simpa [StepXIFiniteCertificateSigned.toContract] using
    cor312_of_finite_certificate certificate.toStepXIFiniteCertificate
      links.toFiniteStepXILinkEvidence

end LeanFormal.IUT
