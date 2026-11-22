import tmp.sheaf.xif.paper.C3LogShellTensorPacketActual
import tmp.sheaf.xif.paper.C3LogShellTensorHolomorphicHullActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual

/-!
# Actual 1,circ U_Q region carrier: Haar measure, dimension and normalization

Source: IUT III, p. 17 (iut3.txt lines 950-978) and p. 18 (iut3.txt 993-1013):
the multiradial representation lives in tensor packets of log-shells (1,circ U),
and the q-pilot object at (1,0) is represented by its action on the log-shells.
IUT III, Step (xi), p. 182-183 (iut3.txt 11017-11034): the normalized log-volume
of the region arising from the representation of the q-pilot object on
1,circ U_Q is -|log q|.

This file constructs the actual partial object at the actual C3 tensor packet of
local log-shells (C3LogShellTensorPacketActual):

* the actual 1,circ U region (the actual tensor integral region of the local
  log-shells), its compactness and finite actual additive Haar measure;
* the actual Q_p-dimension of the tensor packet;
* the actual packet-normalized log-volume (S3137 normalization);
* the actual p-scaled region (the q-pilot contraction candidate at the tensor
  place) and the actual one-step Haar measure/scaling law.

The remaining field-level Missing observation for the q-pilot reading
(place comparison, q_v action identification, procession weights, reading
-|log q|) is recorded in S3133QPilotOneColumnRegionActualPackaged; this file is
the actual carrier part only.  No arbitrary field, sorry or axiom.  WRITE-ONLY.
-/

noncomputable section
open scoped BigOperators ENNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option synthInstance.maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnRegionCarrierActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory
open scoped Pointwise

variable {l : PrimeGeFive} {V : Type}
variable {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance qPilotRegionMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance qPilotRegionBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual 1,circ U region of the C3 input: the actual tensor integral region
of the local log-shells (IUT III, Proposition 3.2, (ii)). -/
noncomputable def qPilotOneColumnRegion : Set (C3LogShellTensorBlock C3) :=
  actualUnitRegion C3

/-- The actual 1,circ U region is the actual tensor log-shell region. -/
theorem qPilotOneColumnRegion_eq :
    qPilotOneColumnRegion C3 = actualC3LogShellTensorRegion C3 := rfl

/-- The actual 1,circ U region is compact. -/
theorem qPilotOneColumnRegion_compact :
    IsCompact (qPilotOneColumnRegion C3) :=
  actualC3LogShellTensorRegion_compact C3

/-- The actual additive Haar measure of the tensor packet. -/
noncomputable def qPilotOneColumnHaar :
    Measure (C3LogShellTensorBlock C3) :=
  actualC3LogShellTensorHaar C3

/-- The actual 1,circ U region has finite Haar measure. -/
theorem qPilotOneColumnRegion_measure_lt_top :
    qPilotOneColumnHaar C3 (qPilotOneColumnRegion C3) < ⊤ := by
  unfold qPilotOneColumnHaar qPilotOneColumnRegion actualUnitRegion
  exact c3TensorRegion_measure_lt_top (C3 := C3)

/-- The actual Q_p-dimension of the 1,circ U tensor packet. -/
noncomputable def qPilotOneColumnDimension : Nat :=
  c3TensorBlockDimension C3

/-- The actual Q_p-dimension of the 1,circ U tensor packet is positive. -/
theorem qPilotOneColumnDimension_pos : 0 < qPilotOneColumnDimension C3 :=
  c3TensorBlockDimension_pos (C3 := C3)

/-- The actual packet-normalized log-volume on the 1,circ U region carrier. -/
noncomputable def qPilotOneColumnNormalizedLogVolume
    (S : Set (C3LogShellTensorBlock C3)) : Real :=
  c3PacketNormalizedLogVolume C3 (qPilotOneColumnHaar C3) S

/-- The actual p-scaled 1,circ U region: the q-pilot contraction candidate at the
C3 tensor place. -/
noncomputable def qPilotOneColumnScaledRegion :
    Set (C3LogShellTensorBlock C3) :=
  (C3.p : ℚ_[C3.p]) • qPilotOneColumnRegion C3

/-- The actual Haar measure of the p-scaled 1,circ U region: multiplication by p
scales the actual Haar measure by p^{-[block : Q_p]} (IUT III, Proposition 3.9,
(i)). -/
theorem qPilotOneColumnScaledRegion_measure :
    qPilotOneColumnHaar C3 (qPilotOneColumnScaledRegion C3) =
      ((C3.p : ENNReal) ^ qPilotOneColumnDimension C3)⁻¹ *
        qPilotOneColumnHaar C3 (qPilotOneColumnRegion C3) := by
  unfold qPilotOneColumnHaar qPilotOneColumnScaledRegion qPilotOneColumnRegion
    qPilotOneColumnDimension actualUnitRegion
  exact c3Tensor_measure_prime_smul (C3 := C3) (actualC3LogShellTensorHaar C3)
    (actualC3LogShellTensorRegion C3)

/-- The actual packet-normalized log-volume of the p-scaled 1,circ U region: the
one-step q-pilot log-volume shift -log p (IUT III, Proposition 3.9, (i)). -/
theorem qPilotOneColumnScaledRegion_normalizedLogVolume
    (hpos : 0 < qPilotOneColumnHaar C3 (qPilotOneColumnRegion C3)) :
    qPilotOneColumnNormalizedLogVolume C3 (qPilotOneColumnScaledRegion C3) =
      -Real.log (C3.p : Real) +
        qPilotOneColumnNormalizedLogVolume C3 (qPilotOneColumnRegion C3) := by
  unfold qPilotOneColumnNormalizedLogVolume qPilotOneColumnScaledRegion
    qPilotOneColumnHaar qPilotOneColumnRegion actualUnitRegion
  exact c3TensorRegion_packetNormalizedLogVolume_prime_smul (C3 := C3) hpos

end LeanFormal.IUT.XiFPaper.S3133QPilotOneColumnRegionCarrierActual
