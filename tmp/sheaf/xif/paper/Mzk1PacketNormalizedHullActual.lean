import tmp.sheaf.xif.paper.Mzk1NormalizedHullVolumeActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137C3TensorBlockDimensionActual

/-!
# Packet-normalized hull log-volume (dimension-normalized Haar)

Complements the existing `Mzk1NormalizedHullVolumeActual.normalizedHullLogVolume`
(raw Haar log-volume of the hull region).  Here the hull log-volume is divided by
the actual Q_p-dimension of the C3 tensor block (IUT III, Proposition 3.9(i)):
`c3PacketNormalizedLogVolume = log (mu S) / [block : Q_p]`.

No sorry, axiom, True or placeholder.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedHullActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1NormalizedHullVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137C3TensorBlockDimensionActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance pktHullMeas : MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance pktHullBorel : BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Packet-normalized (dimension-normalized) hull log-volume. -/
noncomputable def packetNormalizedHullLogVolume : Real :=
  c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)

/-- The packet-normalized hull log-volume is the raw hull Haar log-volume
divided by the actual Q_p-dimension of the tensor block. -/
theorem packetNormalizedHullLogVolume_eq :
    packetNormalizedHullLogVolume C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal /
        (c3TensorBlockDimension C3 : Real) := by
  unfold packetNormalizedHullLogVolume
  rw [thetaPilotHull_eq_region]
  rfl

/-- Relation to the raw normalized hull log-volume: multiplication by the
Q_p-dimension recovers the raw Haar hull log-volume. -/
theorem packetNormalizedHullLogVolume_mul_dimension :
    packetNormalizedHullLogVolume C3 * (c3TensorBlockDimension C3 : Real) =
      normalizedHullLogVolume C3 := by
  rw [packetNormalizedHullLogVolume_eq, normalizedHullLogVolume_eq_region]
  have hdim : (c3TensorBlockDimension C3 : Real) ≠ 0 :=
    Nat.cast_ne_zero.mpr (ne_of_gt (c3TensorBlockDimension_pos (C3 := C3)))
  field_simp

/-- Packet-normalized hull log-volume p-scaling: `-log p` (IUT III, Prop 3.9(i)). -/
theorem packetNormalizedHullLogVolume_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3) =
      -Real.log (C3.p : Real) + packetNormalizedHullLogVolume C3 :=
  c3PacketNormalizedLogVolume_prime_smul (C3 := C3)
    (actualC3LogShellTensorHaar C3) hpos (thetaPilotHull_measure_lt_top (C3 := C3))

end

end LeanFormal.IUT.XiFPaper.Mzk1PacketNormalizedHullActual
