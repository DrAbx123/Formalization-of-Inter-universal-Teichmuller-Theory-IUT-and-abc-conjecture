import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual
import tmp.sheaf.xif.paper.GlobalThetaPilotHullLogVolumeActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceImageHullVolume

noncomputable section
set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1672GlobalThetaHullComparisonActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : forall v : V, I.SourceImageRealization v)
variable (n : ThetaPilotCarrier l)

/-- The global comparison in hull-log form:
    global theta hull log-volume <= q-pilot magnitude. -/
def S1672GlobalHullLogLeQPilot : Prop :=
  globalThetaHullLogVolume (I := I) R n <= qPilotMagnitude (I := I)

/-- Actual equivalence of the hull-log form with the paper signed comparison. -/
theorem s1672GlobalHullLogLeQPilot_iff :
    S1672GlobalHullLogLeQPilot (I := I) R n ↔
      qPilotThetaHullComparison (I := I) R n :=
  (qPilotThetaHullComparison_iff (I := I) R n).symm

/-- Exact first hull input: every per-place source holomorphic hull has finite
source log-volume. -/
def S1672PerPlaceHullFinite
    (R : forall v : V, I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  forall v : V, I.sourceHullVolume v (R v) n < ⊤

/-- Exact global readout input: the actual global theta hull log-volume is at
most the actual q-pilot magnitude.  This is the missing readout comparison,
not a lattice inclusion. -/
def S1672GlobalReadoutLe
    (R : forall v : V, I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) : Prop :=
  S1672GlobalHullLogLeQPilot (I := I) R n

/-- The exact first missing input package: per-place hull finiteness plus the
global hull/q readout comparison.  No lattice or S841/S853 condition is used. -/
structure S1672GlobalReadoutInput where
  hull_finite : S1672PerPlaceHullFinite (I := I) R n
  readout_le : S1672GlobalReadoutLe (I := I) R n

/-- Actual per-place monotonicity: each possible theta-pilot image has source
volume at most the source holomorphic hull volume. -/
theorem s1672ImageVolume_le_hullVolume (v : V) :
    I.sourceSetVolume v (I.possibleThetaPilotImageSet v (R v) n) <=
      I.sourceHullVolume v (R v) n :=
  I.sourceHullVolume_ge_imageVolume v (R v) n

/-- Conditional global comparison from the exact readout input. -/
theorem s1672GlobalComparison_of_readoutInput
    (D : S1672GlobalReadoutInput (I := I) R n) :
    qPilotThetaHullComparison (I := I) R n :=
  (s1672GlobalHullLogLeQPilot_iff (I := I) R n).mp D.readout_le

/-- The global comparison is exactly the missing global readout input. -/
theorem s1672GlobalComparison_iff_readoutLe :
    qPilotThetaHullComparison (I := I) R n ↔
      S1672GlobalReadoutLe (I := I) R n :=
  (s1672GlobalHullLogLeQPilot_iff (I := I) R n).symm

end LeanFormal.IUT.XiFPaper.S1672GlobalThetaHullComparisonActual

end
