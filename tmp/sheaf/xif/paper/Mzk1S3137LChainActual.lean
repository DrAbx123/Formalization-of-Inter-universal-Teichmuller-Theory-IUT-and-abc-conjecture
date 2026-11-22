/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.Mzk1RealifiedValueMonoidActual
import tmp.sheaf.xif.paper.S1391C3LSourcePilotActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual
import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual
import Mathlib.Tactic

/-! # A989: S3137 L-version minimal chain on the concrete S1487 input

CONDITIONAL on an explicit realification datum `RealifiedValueMonoidAt` at every
place.  Given that datum, this file builds `S1487R : ∀ v, SourceImageRealization v`
via the A986 producer, defines the L-version theta hull volume/global log-volume,
and records the S1487 concrete L-carrier and q-pilot scalar.

The realification datum is NOT constructed (actual p-adic value monoid ≃*
Multiplicative ℝ is the GAP).  No sorry/axiom/toy output. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1S3137LChainActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.Mzk1RealifiedValueMonoidActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual

variable (l : PrimeGeFive)
variable [Fintype S1487W]

/-- The concrete S1487 faithful original input. -/
abbrev S1487Input : OriginalInput.{0, 0, 0, 0, 0} l S1487W :=
  S1487FaithfulInput (l := l)

/-- The concrete S1487 L-carrier C3. -/
abbrev S1487C3L : SourcePilotRegionDataL (S1487Input (l := l)) :=
  S1487FaithfulC3 (l := l)

/-- Explicit realification datum at every place (the remaining source input). -/
def S1487RealificationHypothesis : Prop :=
  ∀ v : S1487W, Nonempty (RealifiedValueMonoidAt (S1487Input (l := l)) v)

variable (hreal : S1487RealificationHypothesis l)

/-- The producer: a source image realization at every place, from realification. -/
noncomputable def S1487R :
    ∀ v : S1487W, (S1487Input (l := l)).SourceImageRealization v :=
  fun v => (Classical.choice (hreal v)).sourceImageRealization

theorem S1487R_posRealAction (v : S1487W) :
    (S1487R l hreal v).posRealAction =
      (Classical.choice (hreal v)).posRealAction := rfl

/-- The L-version per-place Theta hull volume. -/
noncomputable def thetaHullVolumeAtL (n : ThetaPilotCarrier l) (v : S1487W) : ENNReal :=
  thetaHullVolumeAt (I := S1487Input (l := l)) (S1487R l hreal) n v

/-- The L-version global Theta hull log-volume. -/
noncomputable def globalThetaHullLogVolumeL (n : ThetaPilotCarrier l) : ℝ :=
  globalThetaHullLogVolume (I := S1487Input (l := l)) (S1487R l hreal) n

theorem globalThetaHullLogVolumeL_eq (n : ThetaPilotCarrier l) :
    globalThetaHullLogVolumeL l hreal n =
      ∑ v : S1487W, Real.log (thetaHullVolumeAtL l hreal n v).toReal := rfl

/-- The actual q-pilot signed log scalar of the S1487 input. -/
noncomputable def qPilotSignedLogL : ℝ :=
  sourceQPilotSignedLog (S1487Input (l := l)).initial

/-- The minimal S3137 L-version readout package. -/
structure S3137LReadout (n : ThetaPilotCarrier l) where
  C3L : SourcePilotRegionDataL (S1487Input (l := l))
  R : ∀ v : S1487W, (S1487Input (l := l)).SourceImageRealization v
  thetaHullVolumeAt : S1487W → ENNReal
  globalThetaHullLogVolume : ℝ
  qPilotSignedLog : ℝ

noncomputable def s3137LReadout (n : ThetaPilotCarrier l) : S3137LReadout l n where
  C3L := S1487C3L l
  R := S1487R l hreal
  thetaHullVolumeAt := thetaHullVolumeAtL l hreal n
  globalThetaHullLogVolume := globalThetaHullLogVolumeL l hreal n
  qPilotSignedLog := qPilotSignedLogL l

theorem s3137LReadout_volume_eq (n : ThetaPilotCarrier l) :
    (s3137LReadout l hreal n).globalThetaHullLogVolume =
      ∑ v : S1487W, Real.log ((s3137LReadout l hreal n).thetaHullVolumeAt v).toReal := rfl

def rows : List (String × String × String) :=
  [ ("S1487Input", "S1487FaithfulInput", "CONCRETE (green)"),
    ("S1487C3L", "S1487FaithfulC3 : SourcePilotRegionDataL", "CONCRETE (green)"),
    ("S1487RealificationHypothesis", "∀ v, Nonempty RealifiedValueMonoidAt", "EXPLICIT HYPOTHESIS (GAP)"),
    ("S1487R", "∀ v, SourceImageRealization via A986 producer", "PROVED (from hreal)"),
    ("thetaHullVolumeAtL", "sourceSetVolume sourceHolomorphicHull", "DEF"),
    ("globalThetaHullLogVolumeL", "Σ_v log per-place volume", "PROVED (rfl)"),
    ("s3137LReadout", "C3L + R + volumes + q log", "DEF (conditional)"),
    ("actual realification identification", "p-adic Mon ≃* Multiplicative ℝ", "GAP") ]

theorem rows_length : rows.length = 8 := rfl

#print axioms LeanFormal.IUT.XiFPaper.Mzk1S3137LChainActual.globalThetaHullLogVolumeL_eq
#print axioms LeanFormal.IUT.XiFPaper.Mzk1S3137LChainActual.s3137LReadout_volume_eq

end LeanFormal.IUT.XiFPaper.Mzk1S3137LChainActual

end