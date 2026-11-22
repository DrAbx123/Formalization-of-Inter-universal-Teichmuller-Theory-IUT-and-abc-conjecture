import LeanFormal.IUT.IUTIII.Corollary312.StepXI.CertificateHullWiring

noncomputable section
open scoped NNReal ENNReal
open MeasureTheory
open LeanFormal.IUT

namespace LeanFormal.IUT.XiFPaper.S3135CertificateHullConsumeActual

/-- Doc consumption of CertificateHullWiring: the hull_le_theta/target_le_theta slots
are exactly the iqHullRealVolume<=theta interface equivalence (prior art
CertificateHullWiring.lean:45/90/99/106/155/173), which supplies the (c) hull half
used in S3135RegionRelativeIQActual. -/
def s3135CertificateHullConsumeReport : Audit.Obligation :=
  { id := "IUT-IV.certificate-hull-wiring-consume"
    source :=
      "CertificateHullWiring.lean:45 (hull_le_theta/target_le_theta equivalence); " ++
        ":90 iqHullRealVolume; :99 iqHull_logVolume_hull_eq_ofReal; :106 " ++
        "iqHullRealVolume_le_theta_iff; :155 iqHullCertificate; IUT III Cor 3.12 " ++
        ":10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "CONSUMED PRIOR ART (reuse): CertificateHullWiring shows the hull_le_theta slot " ++
        "is exactly equivalent to the interface inequality and provides " ++
        "iqHull_logVolume_hull_eq_ofReal + iqHullRealVolume_le_theta_iff; our (c) " ++
        "instantiation s3135_regionRelative_iqCarrier uses the Card-AMPL supply for " ++
        "hull<=theta and finiteness; weight<=theta remains the exact input.  No new " ++
        "proof of the wiring; no registry edit."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems := [ "(c) weight <= theta input (paper normalization)" ] }

#check s3135CertificateHullConsumeReport
end LeanFormal.IUT.XiFPaper.S3135CertificateHullConsumeActual
end
