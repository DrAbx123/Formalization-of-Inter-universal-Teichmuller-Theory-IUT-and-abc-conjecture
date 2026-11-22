import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# ShehddStepXIFiniteCertificateConsumerActualAdapted — finite certificate consumer (Step (xi-d)-(xi-g))

STEP 0 prior-art (reuse only): HolomorphicHull/Volume.lean provides
* PositivePacket / packetDet / packetLogVolume / tensorPacket / rescalePacket;
* FiniteHull (volume, hullVolume, contains) and FiniteHull.average_le;
* StepXIFiniteCertificate (hull, weighted, weighted_matches_hull, weights_nonnegative,
  qSigned, thetaSigned, q_le_hull, hull_le_theta, q_negative) and
  its proved q_le_theta / q_positive;
* HullDeterminantLogVolumeReduction: frozen spec (det/log tensor+rescale, hull average).

This file exposes the finite certificate bounds as a consumer interface for the Cor 3.12
Step (xi-d)-(xi-g) hull/determinant bookkeeping: ordered q <= hull <= theta, q negative
(q-pilot positivity), and the hull-average sandwich.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddStepXIFiniteCertificateConsumerActualAdapted

open LeanFormal.IUT

/-- **PROVED consumer:** a finite certificate has the ordered chain q <= hull <= theta
and q negative (q-pilot positivity). -/
theorem finiteCertificate_ordered_chain {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) :
    certificate.qSigned ≤ certificate.thetaSigned ∧
      certificate.qSigned ≤ certificate.hull.hullVolume ∧
        certificate.hull.hullVolume ≤ certificate.thetaSigned ∧
          0 < -certificate.qSigned :=
  ⟨StepXIFiniteCertificate.q_le_theta certificate,
    certificate.q_le_hull,
    certificate.hull_le_theta,
    StepXIFiniteCertificate.q_positive certificate⟩

/-- **PROVED consumer:** the weighted average of the finite certificate is at most the
hull volume (Remark 3.9.5, (iii) finite form). -/
theorem finiteCertificate_average_le_hull {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) :
    certificate.weighted.average ≤ certificate.hull.hullVolume :=
  FiniteHull.average_le certificate.hull certificate.weighted
    certificate.weighted_matches_hull certificate.weights_nonnegative

/-- Row record: reused finite-certificate assets vs the consumer interface. -/
def finiteCertificateRows : List (String × String × String) :=
  [ ("FiniteHull + WeightedValues + average_le", "REUSED DEF/PROVED", "Volume.lean FiniteHull.average_le")
  , ("StepXIFiniteCertificate fields and q_le_theta/q_positive", "REUSED DEF/PROVED", "Volume.lean StepXIFiniteCertificate")
  , ("ordered q <= hull <= theta chain", "COMPOSED PROVED", "finiteCertificate_ordered_chain")
  , ("average <= hullVolume", "COMPOSED PROVED", "finiteCertificate_average_le_hull")
  , ("source-facing holomorphic hull / log-volume construction", "REPO-CURRENT-LIMIT (Obligation note)", "Volume.lean hullDeterminantLogVolume obligation") ]

theorem finiteCertificateRows_length : finiteCertificateRows.length = 5 := rfl

#check finiteCertificate_ordered_chain
#check finiteCertificate_average_le_hull
#check finiteCertificateRows_length

end LeanFormal.IUT.XiFPaper.ShehddStepXIFiniteCertificateConsumerActualAdapted
end
