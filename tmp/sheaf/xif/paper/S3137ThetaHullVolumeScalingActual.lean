import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual

/-!
# S3137: p-scaling of the actual Theta-pilot hull log-volume reading

IUT III, Proposition 3.9, (i) (p. 115): the p_v-adic log-volume is normalized so
that multiplication by p_v adds -log(p_v).  On the actual C3 input, the
Theta-side container of S3137QThetaPilotLogVolumeReadingsActual is the actual
lambda-O hull of the actual tensor log-shell region, which is the region itself.
This file proves that the actual hull log-volume reading scales by
-[block : Q_p] * log p under multiplication by p, using the packet p-scaling
law S3137C3LogShellPacketNormalizedLogVolumeActual; and it rewrites the Batch A
comparison candidate as an inequality between the actual q-pilot reading and
the actual region log-volume.  No carrier, no surrogate, no sorry, no axiom.
WRITE-ONLY.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000
set_option synthInstance.maxHeartbeats 1000000

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance thetaHullBlockMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance thetaHullBlockBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- The actual hull container has finite Haar measure (compactness). -/
theorem thetaPilotHull_measure_lt_top :
    (actualC3LogShellTensorHaar C3) (thetaPilotHull C3) < ⊤ := by
  rw [thetaPilotHull_eq_region]
  exact c3TensorRegion_measure_lt_top (C3 := C3)

/-- IUT III, Proposition 3.9, (i), at the actual Theta-side container:
multiplying the actual hull of the tensor log-shell region by p shifts its
actual Haar log-volume by -[block : Q_p] * log p. -/
theorem thetaPilotHull_log_measure_prime_smul
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -(c3TensorBlockDimension C3 : ℝ) * Real.log (C3.p : ℝ) +
        thetaPilotHullLogVolumeReal C3 :=
  c3Tensor_log_measure_prime_smul (C3 := C3) (actualC3LogShellTensorHaar C3)
    hpos (thetaPilotHull_measure_lt_top (C3 := C3))

/-- The Theta-hull reading is the actual Haar log-volume of the actual C3 tensor
log-shell region. -/
theorem thetaPilotHullLogVolumeReal_eq_actualRegion :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal := by
  unfold thetaPilotHullLogVolumeReal
  rw [thetaPilotHull_eq_region]

/-- The Batch A comparison candidate, rewritten as an inequality between the
actual q-pilot reading and the actual C3 region log-volume. -/
theorem qThetaPilotLogVolumeComparison_iff_actualRegion
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qThetaPilotLogVolumeComparison C3 P ↔
      qPilotLogVolumeReading P ≤
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal := by
  unfold qThetaPilotLogVolumeComparison
  rw [thetaPilotHullLogVolumeReal_eq_actualRegion]

end LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
