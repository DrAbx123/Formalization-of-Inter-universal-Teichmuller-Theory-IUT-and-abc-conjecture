import tmp.sheaf.xif.paper.Mzk1PacketVolumeConsumerGlueActual

/-! # Mzk1LogVolumeProportionalityActual — proportionality consequences for packet log-volumes

A523 small glue module (no new mathematics): derives the proportionality laws of the
positive-packet log-volume from the already-proved rescaling law
(packetLogVolume_rescale_eq): differences, iterated scalings and inverse scalings.
Registry frozen 14041. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1LogVolumeProportionalityActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.Mzk1PacketVolumeConsumerGlueActual

universe u

variable {label : Type u} [Fintype label] [DecidableEq label]

/-- Proportionality as a difference: rescaling adds one cardinal-times-log term. -/
theorem packetLogVolume_rescale_sub (c : Real) (hc : 0 < c)
    (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc packet) - packetLogVolume packet =
      (Fintype.card label : Real) * Real.log c :=
  by linarith [packetLogVolume_rescale_eq (label := label) c hc packet]

/-- Iterated rescaling: the scalar terms add. -/
theorem packetLogVolume_rescale_rescale (c d : Real) (hc : 0 < c) (hd : 0 < d)
    (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c hc (rescalePacket d hd packet)) =
      (Fintype.card label : Real) * Real.log c +
        (Fintype.card label : Real) * Real.log d + packetLogVolume packet :=
  by
  rw [packetLogVolume_rescale_eq c hc (rescalePacket d hd packet),
    packetLogVolume_rescale_eq d hd packet]
  ring

/-- Inverse rescaling: the proportionality term is subtracted. -/
theorem packetLogVolume_rescale_inv (c : Real) (hc : 0 < c)
    (packet : PositivePacket label) :
    packetLogVolume (rescalePacket c⁻¹ (inv_pos.mpr hc) packet) =
      -((Fintype.card label : Real) * Real.log c) + packetLogVolume packet :=
  by
  rw [packetLogVolume_rescale_eq c⁻¹ (inv_pos.mpr hc) packet, Real.log_inv]
  ring

/-- Rescaling with a product scalar: the two log terms add (direct form). -/
theorem packetLogVolume_rescale_mul (c d : Real) (hc : 0 < c) (hd : 0 < d)
    (packet : PositivePacket label) :
    packetLogVolume (rescalePacket (c * d) (mul_pos hc hd) packet) =
      (Fintype.card label : Real) * Real.log c +
        (Fintype.card label : Real) * Real.log d + packetLogVolume packet :=
  by
  rw [packetLogVolume_rescale_eq (c * d) (mul_pos hc hd) packet,
    Real.log_mul hc.ne' hd.ne']
  ring

#check packetLogVolume_rescale_sub
#check packetLogVolume_rescale_rescale
#check packetLogVolume_rescale_inv
#check packetLogVolume_rescale_mul

end LeanFormal.IUT.XiFPaper.Mzk1LogVolumeProportionalityActual
end
