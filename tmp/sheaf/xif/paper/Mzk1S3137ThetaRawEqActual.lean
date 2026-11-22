/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import Mathlib.Tactic

/-!
# P6-B3: S3137 canonical Theta raw Haar log-volume (single declaration cluster)

Status: CONDITIONAL.  Re-exports the canonical S3137 raw reading
`thetaPilotHullLogVolumeReal = log Haar(actualC3LogShellTensorRegion)` and the
p-scaling identity with the block-dimension factor.  No packet/papers
normalization is asserted here; the packet-vs-raw gap is documented separately.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaRawEqActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open MeasureTheory
open scoped Pointwise ENNReal

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance rawThetaMeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _

local instance rawThetaBorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Canonical S3137 raw reading: log Haar of the actual C3 tensor region. -/
theorem thetaRaw_eq_log_actualRegion :
    thetaPilotHullLogVolumeReal C3 =
      Real.log ((actualC3LogShellTensorHaar C3)
        (actualC3LogShellTensorRegion C3)).toReal :=
  thetaPilotHullLogVolumeReal_eq_actualRegion (C3 := C3)

/-- The block-dimension log-p factor appearing in the S3137 p-scaling law. -/
noncomputable def thetaBlockLogFactor : Real :=
  -((c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real))

/-- S3137 p-scaling: multiplying the hull by p adds the block-dimension factor. -/
theorem thetaRaw_smul_p_eq_factor_add
    (hpos : 0 < (actualC3LogShellTensorHaar C3) (thetaPilotHull C3)) :
    Real.log ((actualC3LogShellTensorHaar C3)
        ((C3.p : ℚ_[C3.p]) • thetaPilotHull C3)).toReal =
      -((c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real)) +
        thetaPilotHullLogVolumeReal C3 := by
  simpa [neg_mul] using thetaPilotHull_log_measure_prime_smul (C3 := C3) hpos

/-- The factor is exactly the negative block-dimension times log p. -/
theorem thetaBlockLogFactor_eq :
    thetaBlockLogFactor C3 =
      -((c3TensorBlockDimension C3 : Real) * Real.log (C3.p : Real)) := rfl

def thetaRawRows : List (String × String × String) :=
  [ ("thetaRaw_eq_log_actualRegion", "raw theta = log Haar actual C3 region", "PROVED (re-export S3137)"),
    ("thetaBlockLogFactor", "block-dim * log p factor", "DEF"),
    ("thetaRaw_smul_p_eq_factor_add", "p-scaling by factor", "PROVED conditional on hpos") ]

theorem thetaRawRows_length : thetaRawRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1S3137ThetaRawEqActual
