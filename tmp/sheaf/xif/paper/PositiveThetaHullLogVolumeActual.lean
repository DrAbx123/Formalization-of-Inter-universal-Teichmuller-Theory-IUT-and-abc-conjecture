import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume
import tmp.sheaf.xif.paper.ThetaPilotObjectActual

/-! # Positive Theta hull log-volume

The old sourceSetVolume is iSup of ENNReal.ofReal (sourceLocalLogDegree).
Since the actual theta log-degree is negative, converting through ENNReal
truncates it to 0; that is not the paper's positive hull magnitude.

This file constructs the positive scalar directly:

* the actual negative log of the source theta special value
    thetaValueAt (n.1 : Int) 0 j
  gives the positive image-point log-volume
    card(SourceVolumeIndex l) * (-log thetaValueAt ...);
* a positive point log-volume on the full value carrier is the positive part of
    -sourceLocalLogDegree v x;
* the actual positive Theta hull log-volume is the supremum of this positive
  point log-volume over the actual sourceHolomorphicHull.

No ENNReal.ofReal truncation of a negative value is used.  No inequality is
asserted.  No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PositiveThetaHullLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Positive point log-volume on the actual value carrier: the positive part of
the negative actual local log-degree. -/
noncomputable def positivePointLogVolume
    (v : V) (x : I.ThetaPilotPoint v) : Real :=
  max 0 (-(I.sourceLocalLogDegree v x))

/-- Positive log-volume of an actual source theta-pilot image point, built from
the actual negative log of thetaValueAt. -/
noncomputable def positiveThetaImageLogVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) : Real :=
  max 0 (-(Fintype.card (SourceVolumeIndex l) : Real) *
    Real.log (I.thetaValueAt (n.val : Int) 0 j))

/-- The positive image log-volume is the positive point log-volume of the actual
source theta-pilot point. -/
theorem positiveThetaImageLogVolume_eq_positivePoint
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value)
    (hdeg : ∀ b : Real,
      I.logDegreeAt 0 0 v (R.posRealAction (Multiplicative.ofAdd b)) = b) :
    positiveThetaImageLogVolume (I := I) v R n j =
      positivePointLogVolume (I := I) v (I.sourceThetaPilotPoint v R n j) := by
  unfold positiveThetaImageLogVolume positivePointLogVolume
  rw [I.sourceLocalLogDegree_thetaPilotPoint v R n j hdeg]

/-- The actual positive Theta hull log-volume: the supremum of the positive point
log-volume over the actual source holomorphic hull. -/
noncomputable def positiveThetaHullLogVolume
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  sSup {y : Real | ∃ x : I.ThetaPilotPoint v,
    x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
      y = positivePointLogVolume (I := I) v x}

/-- Actual positive Theta hull log-volume data at one place. -/
structure PositiveThetaHullLogVolumeData where
  imageLogVolume : SignedLabel l.value → Real
  imageLogVolume_eq : imageLogVolume =
    positiveThetaImageLogVolume (I := I) v R n
  hullLogVolume : Real
  hullLogVolume_eq : hullLogVolume = positiveThetaHullLogVolume (I := I) v R n

/-- The actual positive Theta hull log-volume data. -/
noncomputable def positiveThetaHullLogVolumeData
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    PositiveThetaHullLogVolumeData (I := I) v R n where
  imageLogVolume := positiveThetaImageLogVolume (I := I) v R n
  imageLogVolume_eq := rfl
  hullLogVolume := positiveThetaHullLogVolume (I := I) v R n
  hullLogVolume_eq := rfl

/-- This positive hull log-volume is not the old ENNReal.ofReal truncation: it
is a real supremum of positive point log-volumes. -/
theorem positiveThetaHullLogVolume_eq_sSup :
    positiveThetaHullLogVolume (I := I) v R n =
      sSup {y : Real | ∃ x : I.ThetaPilotPoint v,
        x ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)) ∧
          y = positivePointLogVolume (I := I) v x} := rfl

/-- The positive point log-volume is nonnegative. -/
theorem positivePointLogVolume_nonneg
    (v : V) (x : I.ThetaPilotPoint v) :
    0 ≤ positivePointLogVolume (I := I) v x :=
  le_max_left _ _

/-- The positive image log-volume is nonnegative. -/
theorem positiveThetaImageLogVolume_nonneg
    (v : V) (R : I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (j : SignedLabel l.value) :
    0 ≤ positiveThetaImageLogVolume (I := I) v R n j :=
  le_max_left _ _

section Global

variable [Fintype V]

/-- The positive global Theta hull log-volume: sum over the actual finite place
type V of the positive per-place hull log-volumes. -/
noncomputable def positiveGlobalThetaHullLogVolume
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  ∑ v : V, positiveThetaHullLogVolume (I := I) v (R v) n

/-- Actual positive global Theta hull log-volume data. -/
structure PositiveGlobalThetaHullLogVolumeData where
  perPlace : ∀ v : V, Real
  perPlace_eq : ∀ v, perPlace v =
    positiveThetaHullLogVolume (I := I) v (R v) n
  globalLogVolume : Real
  globalLogVolume_eq : globalLogVolume =
    positiveGlobalThetaHullLogVolume (I := I) R n

/-- The actual positive global data. -/
noncomputable def positiveGlobalThetaHullLogVolumeData
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    PositiveGlobalThetaHullLogVolumeData (I := I) R n where
  perPlace := fun v => positiveThetaHullLogVolume (I := I) v (R v) n
  perPlace_eq := fun _ => rfl
  globalLogVolume := positiveGlobalThetaHullLogVolume (I := I) R n
  globalLogVolume_eq := rfl

end Global

end LeanFormal.IUT.XiFPaper.PositiveThetaHullLogVolumeActual

end
