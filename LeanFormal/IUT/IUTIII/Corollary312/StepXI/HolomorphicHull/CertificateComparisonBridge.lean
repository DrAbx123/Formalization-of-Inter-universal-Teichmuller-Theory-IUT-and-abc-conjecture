import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction
import Mathlib.Tactic

/-!
# Bridge between the certificate face and the comparison-data face of Step (xi-f)

Root adjudication 2026-10-16: the reduction pass
`HullDeterminantLogVolumeReduction.lean` (Faraday; comparison-data face, frozen
delivery) and `CertificateCThetaTransfer.lean` (certificate face) are
orthogonal and are bridged here: a `StepXIFiniteCertificate` (`Volume.lean:152`)
together with the q-pilot identification canonically induces the comparison
datum `Cor312ComparisonData` (`HullDeterminantLogVolumeReduction.lean:517`),
whose ray field is the certificate chain `qSigned <= hull <= thetaSigned`.

Joint consumption shape: the terminal Step (xi-f) constraint `-1 <= C_Theta`
is consumed through the comparison face from certificate-supplied data
(`Cor312ComparisonData.final_bound_of_certificate`); the direct certificate-face
route is `CertificateCThetaTransfer.cTheta_lower_bound_of_finiteCertificate`.
No obligation status is changed by this module; the paper's source construction
remains with `IUT-III.holomorphic-hull-determinant-log-volume`.

Original-text anchor: Step (xi-f), lines 1136-1146 of the source-audit
transcription (full anchor sets in both parent files).
-/

namespace LeanFormal.IUT

noncomputable section

/-- The certificate face canonically induces the comparison-data face: the
hull log-volume is the certificate's `thetaSigned`, the q-pilot log-volume is
the certificate's `qSigned`, the ray membership is the certificate chain
`q_le_theta`, and the q-parameter is any `q` whose log is `-qSigned` (the
certificate's `q_negative` then supplies the paper's `|log(q)| > 0`). -/
def StepXIFiniteCertificate.toCor312ComparisonData {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) (q : Real)
    (hq : Real.log q = -certificate.qSigned) (hqpos : 0 < q) :
    Cor312ComparisonData where
  thetaHullLogVolume := certificate.thetaSigned
  qPilotLogVolume := certificate.qSigned
  qPilot_mem_ray := mem_hullLogVolumeRay_iff.mpr certificate.q_le_theta
  qParameter := q
  qParameter_pos := hqpos
  qParameter_log_ne_zero := by
    rw [hq]
    exact ne_of_gt (neg_pos.mpr certificate.q_negative)
  qPilotLogVolume_eq := by
    rw [hq, abs_of_pos (neg_pos.mpr certificate.q_negative)]
    ring

/-- The induced datum reads the certificate's `-|log(Theta)|` scalar. -/
@[simp] theorem StepXIFiniteCertificate.toCor312ComparisonData_thetaHullLogVolume
    {label : Type*} [Fintype label] (certificate : StepXIFiniteCertificate label)
    (q : Real) (hq : Real.log q = -certificate.qSigned) (hqpos : 0 < q) :
    (certificate.toCor312ComparisonData q hq hqpos).thetaHullLogVolume =
      certificate.thetaSigned := rfl

/-- The induced datum reads the certificate's `-|log(q)|` scalar. -/
@[simp] theorem StepXIFiniteCertificate.toCor312ComparisonData_qPilotLogVolume
    {label : Type*} [Fintype label] (certificate : StepXIFiniteCertificate label)
    (q : Real) (hq : Real.log q = -certificate.qSigned) (hqpos : 0 < q) :
    (certificate.toCor312ComparisonData q hq hqpos).qPilotLogVolume =
      certificate.qSigned := rfl

/-- The induced datum carries the q-parameter. -/
@[simp] theorem StepXIFiniteCertificate.toCor312ComparisonData_qParameter
    {label : Type*} [Fintype label] (certificate : StepXIFiniteCertificate label)
    (q : Real) (hq : Real.log q = -certificate.qSigned) (hqpos : 0 < q) :
    (certificate.toCor312ComparisonData q hq hqpos).qParameter = q := rfl

/-- Joint consumption of the two faces: the terminal Step (xi-f) constraint
follows through the induced comparison datum and its `final_bound`. -/
theorem Cor312ComparisonData.final_bound_of_certificate {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) {q : Real}
    (hq : Real.log q = -certificate.qSigned) (hqpos : 0 < q) {cTheta : Real}
    (hc : certificate.thetaSigned <= cTheta * |Real.log q|) :
    -1 <= cTheta :=
  Cor312ComparisonData.final_bound
    (certificate.toCor312ComparisonData q hq hqpos) hc

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the certificate/comparison-data face bridge. -/
def certificateComparisonFaceBridge : Obligation :=
  { id := "IUT-III.StepXI.certificate-comparison-face-bridge"
    source := "IUT III, Corollary 3.12 proof, Step (xi-f); union of " ++
      "Volume.lean:152 (certificate face) and " ++
      "HullDeterminantLogVolumeReduction.lean:517 (comparison-data face)"
    status := VerificationStatus.proved
    note :=
      "The certificate canonically induces the comparison datum " ++
        "(toCor312ComparisonData), whose ray field is the certificate " ++
        "chain; the terminal Step (xi-f) constraint is then consumed " ++
        "through the comparison face (final_bound_of_certificate). No " ++
        "existing obligation status is changed; the source construction " ++
        "remains with IUT-III.holomorphic-hull-determinant-log-volume."
    dependsOn :=
      [ "IUT-III.holomorphic-hull-determinant-log-volume",
        "IUT-III.holomorphic-hull-determinant-log-volume-reduction" ] }

end LeanFormal.IUT.Audit
