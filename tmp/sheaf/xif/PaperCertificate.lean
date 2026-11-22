import tmp.sheaf.xif.PaperSignedHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiringSigned
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# Paper-level xi-f certificate / Cor312 consumption

Consumes the paper-level signed hull data (`PaperSignedHull`) and the actual
paper xi-f comparison card (`Cor312ComparisonData`) into the signed finite
certificate and then into Cor312Conclusion.

The certificate's `q_le_hull` field is exactly the paper inclusion
`data.qPilot_mem_ray` (after the exact theta-carrier alignment
`data.thetaHullLogVolume = P.signedHullLogVolume`). The certificate's
`hull_le_theta` field is the same alignment; the signed theta is
`P.signedHullLogVolume`, not a value-layer surrogate.

The Cor312Conclusion route takes an actual `FiniteStepXILinkEvidence`
(whose IPL/SHE/APT slots are evidence carried by that structure, not
`True`/toy) and adapts it to the signed certificate. A separate direct
`Cor312ComparisonData.final_bound` route is included, matching the existing
paper comparison card.

No sorry, axiom, or toy carrier is introduced. The finite hull below is the
certificate carrier for the paper signed hull scalar; it is not an assertion
that the paper per-label hull volumes have a constant value.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT

universe u v

variable {X : Type u} {label : Type v} [Fintype label]

/-- Paper-level inputs for the certificate: the signed hull data and the
actual paper xi-f comparison card, with the exact theta-carrier alignment
between the card and `PaperSignedHull.signedHullLogVolume`. -/
structure PaperXiFInput (P : PaperSignedHull X label) where
  /-- The paper comparison data: q-pilot log-volume, hull log-volume, xi-f
  ray membership, and q-parameter normalization. -/
  data : Cor312ComparisonData
  /-- Exact carrier alignment: the card's hull scalar is the paper signed
  hull log-volume. -/
  theta_eq : data.thetaHullLogVolume = P.signedHullLogVolume

variable [Nonempty label]
variable {P : PaperSignedHull X label}
variable (I : PaperXiFInput P)

/-- Finite certificate hull carrying the paper signed hull scalar. The
per-label value is the same signed hull scalar; this is the finite
certificate carrier, not a paper per-label hull assertion. -/
def paperCertificateFiniteHull : FiniteHull label where
  volume _ := I.data.thetaHullLogVolume
  hullVolume := I.data.thetaHullLogVolume
  contains _ := le_rfl

/-- Uniform finite weights over the certificate label type. -/
def paperCertificateWeightedValues : WeightedValues label where
  value _ := I.data.thetaHullLogVolume
  weight _ := 1
  weightTotal := (Fintype.card label : ℝ)
  weightTotal_pos := by
    exact_mod_cast (Fintype.card_pos_iff.mpr inferInstance)
  weightTotal_eq_sum := by
    simp

/-- The paper signed certificate. `q_le_hull` is the paper xi-f inclusion
`data.qPilot_mem_ray`; `thetaSigned` is the paper signed hull volume. -/
def paperCertificate : StepXIFiniteCertificateSigned label where
  hull := paperCertificateFiniteHull (I := I)
  weighted := paperCertificateWeightedValues (I := I)
  weighted_matches_hull := by
    intro i
    rfl
  weights_nonnegative := by
    intro _
    show (0 : ℝ) ≤ (1 : ℝ)
    norm_num
  qSigned := I.data.qPilotLogVolume
  thetaSigned := P.signedHullLogVolume
  q_le_hull := I.data.qPilot_mem_ray
  hull_le_theta := le_of_eq I.theta_eq
  q_negative := by
    rw [I.data.qPilotLogVolume_eq]
    exact neg_neg_of_pos (abs_pos.mpr I.data.qParameter_log_ne_zero)

@[simp] theorem paperCertificate_thetaSigned_eq :
    (paperCertificate (I := I)).thetaSigned = P.signedHullLogVolume := rfl

@[simp] theorem paperCertificate_hullVolume_eq :
    (paperCertificate (I := I)).hull.hullVolume =
      P.signedHullLogVolume := I.theta_eq

/-- The certificate's q_le_hull slot is exactly the paper xi-f inclusion. -/
theorem paperCertificate_q_le_hull :
    (paperCertificate (I := I)).qSigned ≤
      (paperCertificate (I := I)).hull.hullVolume := by
  change I.data.qPilotLogVolume ≤ I.data.thetaHullLogVolume
  exact I.data.qPilot_mem_ray

/-- The certificate's q <= theta conclusion: the paper signed inclusion. -/
theorem paperCertificate_q_le_theta :
    (paperCertificate (I := I)).qSigned ≤
      (paperCertificate (I := I)).thetaSigned := by
  exact le_trans (paperCertificate_q_le_hull (I := I))
    (paperCertificate (I := I)).hull_le_theta

/-- The direct numeric Corollary-3.12 conclusion from the paper comparison
card: `CTheta >= -1`. This does not use a vector of arbitrary IPL/SHE/APT
evidence; it is exactly `Cor312ComparisonData.final_bound`. -/
theorem paperCertificate_cTheta_lowerBound
    {cTheta : ℝ}
    (hc : P.signedHullLogVolume ≤ cTheta * |Real.log I.data.qParameter|) :
    -1 ≤ cTheta := by
  exact I.data.final_bound (by
    rw [I.theta_eq]
    exact hc)

/-- Adapt actual finite link evidence to the signed certificate. The
IPL/SHE/APT propositions and their evidence are the fields of the
supplied `FiniteStepXILinkEvidence`; no `True` is inserted. -/
def paperSignedLinkEvidence
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    SignedFiniteStepXILinkEvidence (paperCertificate (I := I)) where
  targetSigned := links.targetSigned
  ipl := links.ipl
  she := links.she
  apt := links.apt
  ipl_evidence := links.ipl_evidence
  she_evidence := links.she_evidence
  apt_evidence := links.apt_evidence
  q_le_target := links.q_le_target
  target_le_theta := links.target_le_theta

/-- Cor312Conclusion via the signed certificate and the actual finite link
evidence. -/
theorem paperCor312Conclusion
    (links : FiniteStepXILinkEvidence
      (paperCertificate (I := I)).toStepXIFiniteCertificate) :
    Cor312Conclusion
      ((paperCertificate (I := I)).toContract
        (paperSignedLinkEvidence (I := I) links)) :=
  cor312_of_signed_finite_certificate (paperCertificate (I := I))
    (paperSignedLinkEvidence (I := I) links)

end LeanFormal.IUT

end
