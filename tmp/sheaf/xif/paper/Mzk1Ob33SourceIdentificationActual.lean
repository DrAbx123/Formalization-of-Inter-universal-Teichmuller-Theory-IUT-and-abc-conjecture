/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.n8.closure.SourcePilotRegion
import tmp.sheaf.xif.paper.ArithmeticLineBundleActual
import tmp.sheaf.xif.paper.S3137C3LogShellPacketNormalizedLogVolumeActual
import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.S3137ThetaHullVolumeScalingActual
import Mathlib.Tactic

/-!
# P7/#3 OB33-SRC: local det-normalized construction (avoids broken HullDetObjectActual)

Status: CONDITIONAL.  We locally restate the actual det-normalized C3 reading as
c3PacketNormalizedLogVolume of the actual Haar/region, then prove it equals the
S3137 raw Haar log-volume divided by the actual block Q_p-dimension.  The
remaining source identification (det(x)M arithmetic degree = this actual
det-normalized reading) is a named Prop.  No sorry/axiom.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Ob33SourceIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaperArithmeticLineBundle
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.XiFPaper.S3137C3LogShellPacketNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.XiFPaper.S3137ThetaHullVolumeScalingActual
open MeasureTheory

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

local instance ob33MeasurableSpace :
    MeasurableSpace (C3LogShellTensorBlock C3) := borel _
local instance ob33BorelSpace :
    BorelSpace (C3LogShellTensorBlock C3) := ⟨rfl⟩

/-- Local actual det-normalized C3 log-volume (same formula as HullDetObjectActual,
restated here to avoid its broken olean). -/
noncomputable def ob33DetNormalizedLogVolume
    (S : Set (C3LogShellTensorBlock C3)) : Real :=
  c3PacketNormalizedLogVolume C3 (actualC3LogShellTensorHaar C3) S

theorem ob33DetNormalizedLogVolume_apply
    (S : Set (C3LogShellTensorBlock C3)) :
    ob33DetNormalizedLogVolume C3 S =
      Real.log ((actualC3LogShellTensorHaar C3) S).toReal /
        (c3TensorBlockDimension C3 : Real) := rfl

/-- Actual det-normalized Theta-hull reading = raw S3137 Haar log / block dim. -/
theorem ob33_detNormalized_eq_raw_div :
    ob33DetNormalizedLogVolume C3 (thetaPilotHull C3) =
      thetaPilotHullLogVolumeReal C3 / (c3TensorBlockDimension C3 : Real) := by
  rw [ob33DetNormalizedLogVolume_apply, thetaPilotHull_eq_region,
    thetaPilotHullLogVolumeReal_eq_actualRegion]

/-- Named source identification: arithmetic degree of det(x)M output equals the
actual det-normalized reading. -/
def Ob33ArithmeticDegreeIdentification (detDegree : Real) : Prop :=
  detDegree = ob33DetNormalizedLogVolume C3 (thetaPilotHull C3)

theorem ob33_identification_iff (detDegree : Real) :
    Ob33ArithmeticDegreeIdentification C3 detDegree ↔
      detDegree = ob33DetNormalizedLogVolume C3 (thetaPilotHull C3) := Iff.rfl

/-- Conditional consumer: identification => degree = raw/blockdim. -/
theorem ob33_detDegree_eq_raw_div_of_identification
    {detDegree : Real}
    (h : Ob33ArithmeticDegreeIdentification C3 detDegree) :
    detDegree =
      thetaPilotHullLogVolumeReal C3 / (c3TensorBlockDimension C3 : Real) := by
  rw [h, ob33_detNormalized_eq_raw_div]

/-- Actual det(x)M arithmetic-degree object: the actual source unit determinant
line-bundle global log-volume (constructed, not an arbitrary Real parameter). -/
noncomputable def ob33ActualDetDegree
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Real :=
  (actualUnitLineBundleData (A := I.initial.arithmetic)).detData.globalLogVolume

/-- Actual source identification: the actual det(x)M arithmetic degree equals
the local det-normalized C3 hull reading. -/
def Ob33SourceIdentificationActual
    (C3 : SourcePilotRegionData (l := l) (V := V) I) : Prop :=
  ob33ActualDetDegree C3 = ob33DetNormalizedLogVolume C3 (thetaPilotHull C3)

/-- Conditional consumer using the actual det-degree object. -/
theorem ob33_actualDetDegree_eq_raw_div_of_identification
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (h : Ob33SourceIdentificationActual C3) :
    ob33ActualDetDegree C3 =
      thetaPilotHullLogVolumeReal C3 / (c3TensorBlockDimension C3 : Real) := by
  rw [show ob33ActualDetDegree C3 =
      ob33DetNormalizedLogVolume C3 (thetaPilotHull C3) from h]
  exact ob33_detNormalized_eq_raw_div C3


def ob33SourceRows : List (String × String × String) :=
  [ ("ob33_detNormalized_eq_raw_div", "local det-normalized = raw Haar log/block dim", "PROVED"),
    ("Ob33ArithmeticDegreeIdentification", "det(x)M arithmetic degree = local det-normalized", "CONDITIONAL named input"),
    ("ob33_detDegree_eq_raw_div_of_identification", "conditional consumer", "PROVED conditional") ]

theorem ob33SourceRows_length : ob33SourceRows.length = 3 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1Ob33SourceIdentificationActual
