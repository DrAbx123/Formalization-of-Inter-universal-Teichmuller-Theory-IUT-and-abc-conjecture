import LeanFormal.IUT.IUTIII.Corollary312.StepXI.FiniteCertificateBridge
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.WeightedNormalization
import Mathlib.Order.WithBot

/-!
This audit isolates why the existing finite certificate cannot by itself
establish the finiteness assertion for the source's extended log-volume.
It does not identify a finite packet with the actual holomorphic hull.
-/

namespace LeanFormal.IUT.CoreVolumeAudit

#check WithTop.coe_ne_top
#check WithTop.map
#check WithTop.map_top
#check WithTop.coe_le_coe
#check WithTop.lt_top_iff_ne_top
#check WeightedDeterminantPacket.weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume
#check StepXIFiniteCertificate.toContract
#check cor312_of_finite_certificate

#print axioms packetLogVolume_eq_log_det
#print axioms packetLogVolume_tensor
#print axioms FiniteHull.average_le
#print axioms WeightedDeterminantPacket.weightedLogVolume_eq_commonTensorDegree_mul_normalizedLogVolume
#print axioms cor312_of_finite_certificate
#print axioms q_positive_of_finite_certificate

end LeanFormal.IUT.CoreVolumeAudit
