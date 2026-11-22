import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

/-!
# ShehddHeightVolumeChainActual — finite certificate height-volume chain

New real chain on the compiled StepXI finite certificate / frozen hull-det spec assets:
the weighted average is bounded by the hull volume and hence by the signed theta readout,
while the signed q-pilot readout is negative.  This is the height-volume consumer for the
iut-skeleton:HeightVolume target; no new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddHeightVolumeChainActual

open LeanFormal.IUT

/-- **PROVED chain:** for a finite certificate, the weighted average is at most the hull
volume and hence at most the signed theta readout; q is negative and bounded above by
theta. -/
theorem finiteCertificate_average_le_theta {label : Type*} [Fintype label]
    (certificate : StepXIFiniteCertificate label) :
    certificate.weighted.average ≤ certificate.hull.hullVolume ∧
      certificate.weighted.average ≤ certificate.thetaSigned ∧
        certificate.qSigned ≤ certificate.thetaSigned ∧
          0 < -certificate.qSigned :=
  ⟨FiniteHull.average_le certificate.hull certificate.weighted
      certificate.weighted_matches_hull certificate.weights_nonnegative,
    le_trans (FiniteHull.average_le certificate.hull certificate.weighted
      certificate.weighted_matches_hull certificate.weights_nonnegative)
      certificate.hull_le_theta,
    StepXIFiniteCertificate.q_le_theta certificate,
    StepXIFiniteCertificate.q_positive certificate⟩

end LeanFormal.IUT.XiFPaper.ShehddHeightVolumeChainActual
end
