import tmp.sheaf.xif.paper.ThetaPilotObjectActual

/-!
# Positive Theta-hull log-volume from theta values

The old sourceSetVolume is a sup of sourceLocalLogDegree truncated at zero.
This file instead uses the actual positive theta log-volumes

  - Real.log (I.thetaValueAt n 0 j)

at the signed labels, together with the actual source holomorphic hull
membership of the theta-pilot points.

Per place v and pilot n, the positive hull log-volume is the sum of the
negative theta logarithms; globally it is the sum over the finite place type V.
No truncation at zero and no sourceSetVolume are used.

No PUnit/True, arbitrary data, axiom or sorry is used. -/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.ThetaPilotObjectActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

/-- Positive theta log-volume at one place and signed label. -/
def thetaPositiveLogVolumeAt
    (n : ThetaPilotCarrier l) (v : V) (j : SignedLabel l.value) : Real :=
  - Real.log (I.thetaValueAt (n.val : Int) 0 j)

/-- The positive theta log-volume is the negative logarithm of the actual theta
value. -/
theorem thetaPositiveLogVolumeAt_eq
    (n : ThetaPilotCarrier l) (v : V) (j : SignedLabel l.value) :
    thetaPositiveLogVolumeAt (I := I) n v j =
      - Real.log (I.thetaValueAt (n.val : Int) 0 j) := rfl

/-- The actual theta-pilot point at (n,j) lies in the actual source holomorphic
hull.  This is the hull membership used by the positive hull volume. -/
theorem thetaPositivePoint_mem_hull
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)
    (v : V) (j : SignedLabel l.value) :
    I.sourceThetaPilotPoint v (R v) n j ∈
      (I.sourceHolomorphicHull v (R v) n : Set (I.ThetaPilotPoint v)) :=
  I.sourceThetaPilotPoint_mem_sourceHolomorphicHull v (R v) n j

/-- Positive hull log-volume at one place: the sum of positive theta
log-volumes. -/
def thetaHullPositiveLogVolumeAt
    (n : ThetaPilotCarrier l) (v : V) : Real :=
  ∑ j : SignedLabel l.value, thetaPositiveLogVolumeAt (I := I) n v j

/-- The per-place positive hull log-volume is the negative of the actual theta
packet log-volume. -/
theorem thetaHullPositiveLogVolumeAt_eq
    (n : ThetaPilotCarrier l) (v : V) :
    thetaHullPositiveLogVolumeAt (I := I) n v =
      - (I.theaterAt (n.val : Int) 0).thetaPacket.logVolume := by
  unfold thetaHullPositiveLogVolumeAt thetaPositiveLogVolumeAt
  rw [FiniteThetaPacket.logVolume_eq_sum, Finset.sum_neg_distrib]
  rfl

/-- Global positive Theta-hull log-volume: sum over the actual finite places. -/
def globalThetaHullPositiveLogVolume
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) : Real :=
  ∑ v : V, thetaHullPositiveLogVolumeAt (I := I) n v

/-- Global positive hull log-volume is the per-place sum. -/
theorem globalThetaHullPositiveLogVolume_eq
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    globalThetaHullPositiveLogVolume (I := I) R n =
      ∑ v : V, thetaHullPositiveLogVolumeAt (I := I) n v := rfl

/-- Actual per-place/global positive hull log-volume data. -/
structure GlobalPositiveThetaHullLogVolumeData
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  thetaLogVolumeAt : V → SignedLabel l.value → Real
  thetaLogVolumeAt_eq : thetaLogVolumeAt =
    fun v j => thetaPositiveLogVolumeAt (I := I) n v j
  perPlaceHullVolume : V → Real
  perPlaceHullVolume_eq : perPlaceHullVolume =
    thetaHullPositiveLogVolumeAt (I := I) n
  globalHullVolume : Real
  globalHullVolume_eq : globalHullVolume =
    globalThetaHullPositiveLogVolume (I := I) R n

/-- The actual positive hull log-volume data. -/
noncomputable def globalPositiveThetaHullLogVolumeData
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    GlobalPositiveThetaHullLogVolumeData (I := I) R n where
  thetaLogVolumeAt := fun v j => thetaPositiveLogVolumeAt (I := I) n v j
  thetaLogVolumeAt_eq := rfl
  perPlaceHullVolume := thetaHullPositiveLogVolumeAt (I := I) n
  perPlaceHullVolume_eq := rfl
  globalHullVolume := globalThetaHullPositiveLogVolume (I := I) R n
  globalHullVolume_eq := rfl

/-- The constructed global hull volume is the sum over places of the negative
theta packet log-volumes. -/
@[simp] theorem globalPositiveThetaHullLogVolumeData_volume
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) :
    (globalPositiveThetaHullLogVolumeData (I := I) R n).globalHullVolume =
      ∑ v : V, thetaHullPositiveLogVolumeAt (I := I) n v := rfl

end LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual

end
