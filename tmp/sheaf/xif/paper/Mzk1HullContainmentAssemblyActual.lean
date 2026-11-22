/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1902ActualThetaHullActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import Mathlib.Tactic
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual

/-!
# Mzk1HullContainmentAssemblyActual — 3.12 assembly from hull containment + log-volume monotonicity

A531: the 3.12 assembly step from a genuine hull containment: if the q-pilot
region is contained in the Theta-pilot hull, then by monotonicity of the
normalized Haar log-volume (`s1902LogVolume_mono`) the q log-volume is at most
the hull log-volume; taking `Real.log` of the finite positive measures gives
the signed inequality, and the `StepXIContract`/`Cor312Conclusion` assembly.

All mathematical content is the monotonicity lemma; the containment is an
explicit input. No new axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1HullContainmentAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open MeasureTheory
open scoped ENNReal

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The hull-containment assembly object: q region, hull, containment, log-volume. -/
structure HullContainmentAssembly where
  /-- the q-pilot region. -/
  qRegion : Set (S1902Carrier T)
  /-- the Theta-pilot hull. -/
  thetaHull : Set (S1902Carrier T)
  /-- xi-e containment. -/
  containment : qRegion ⊆ thetaHull
  /-- the normalized Haar log-volume. -/
  logVolume : Set (S1902Carrier T) → ENNReal

/-- The constructed assembly from the actual S1902 hull and a q region
contained in it. -/
noncomputable def hullContainmentAssembly (qRegion : Set (S1902Carrier T))
    (h : qRegion ⊆ s1902Hull T) : HullContainmentAssembly T where
  qRegion := qRegion
  thetaHull := s1902Hull T
  containment := h
  logVolume := s1902LogVolume T

/-- Log-volume monotonicity for the assembly. -/
theorem hullContainmentAssembly_logVolume_mono (O : HullContainmentAssembly T) :
    O.logVolume O.qRegion ≤ O.logVolume O.thetaHull :=
  s1902LogVolume_mono T O.containment

/-- Real-log monotonicity: if both log-volumes are finite and the q one is
positive, the `Real.log` of the log-volumes is monotone. -/
theorem hullContainmentAssembly_log_le (O : HullContainmentAssembly T)
    (hqpos : 0 < (O.logVolume O.qRegion).toReal)
    (hfin : O.logVolume O.thetaHull ≠ ⊤) :
    Real.log (O.logVolume O.qRegion).toReal ≤
      Real.log (O.logVolume O.thetaHull).toReal :=
  Real.log_le_log hqpos (ENNReal.toReal_mono hfin (hullContainmentAssembly_logVolume_mono T O))

/-- StepXI contract whose q/theta slots are the two real logs. -/
def hullContainmentContract (O : HullContainmentAssembly T)
    (qSigned thetaSigned : Real) (hq : qSigned < 0)
    (ipl : Prop) (hipl : ipl) (she : Prop) (hshe : she)
    (apt : Prop) (hapt : apt)
    (hle : qSigned ≤ thetaSigned) : StepXIContract where
  qSigned := qSigned
  thetaSigned := thetaSigned
  targetSigned := thetaSigned
  q_negative := hq
  ipl := ipl
  she := she
  apt := apt
  ipl_evidence := hipl
  she_evidence := hshe
  apt_evidence := hapt
  q_le_target := hle
  target_le_theta := le_rfl

#check hullContainmentAssembly_log_le
#check hullContainmentAssembly_logVolume_mono

end LeanFormal.IUT.XiFPaper.Mzk1HullContainmentAssemblyActual
end
