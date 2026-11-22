/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.GlobalPositiveThetaHullLogVolumeActual
import tmp.sheaf.xif.paper.S1929LiteralIQCarrierActual
import tmp.sheaf.takkun.IutLean.Theta.ThetaValues
import tmp.sheaf.n8.closure.NativeSourceReductionActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlacePartitionReduction
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-!
# ThetaReadoutFromQActual — independent Θ readout object from actual q_v/θ values

A511 object file: reuses the actual theta values `thetaValueFromQ = q_v^{j²}`
(GlobalThetaPilotLogVolumeActual) and the positive theta-hull log-volumes
(GlobalPositiveThetaHullLogVolumeActual) to build an *independent* Θ readout
`thetaReadoutFromQ = -log(thetaValueFromQ)`, with the exact formula
`thetaReadoutFromQ = gaussExp j * baseQLogMagnitude` and its global sum.

Not the q/(2ℓ) definition; no comparison; no sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.ThetaReadoutFromQActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open IUT.Theta
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalQPilotProcessionLogVolumeActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- Independent Theta readout at one bad place: `-log(q_v^{j²})`. -/
noncomputable def thetaReadoutFromQ (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) : Real := -Real.log (thetaValueFromQ T b j)

/-- The independent Theta readout is `gaussExp j * |log q_v|`. -/
theorem thetaReadoutFromQ_eq (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    thetaReadoutFromQ T b j =
      ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b := by
  unfold thetaReadoutFromQ
  rw [log_thetaValueFromQ, baseQLogMagnitude_eq_neg_log_baseQReal]
  ring

/-- Global Theta readout: sum over V_bad. -/
noncomputable def globalThetaReadoutFromQ
    [Fintype (Bad (nativePlaceSelection T))]
    (j : SignedLabel l.value) : Real :=
  ∑ b : Bad (nativePlaceSelection T), thetaReadoutFromQ T b j

/-- Global normalization: the sum is `gaussExp j * (∑ |log q_v|)`. -/
theorem globalThetaReadoutFromQ_eq
    [Fintype (Bad (nativePlaceSelection T))] (j : SignedLabel l.value) :
    globalThetaReadoutFromQ T j =
      ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQTotalLogMagnitude T := by
  unfold globalThetaReadoutFromQ baseQTotalLogMagnitude
  apply Finset.sum_congr rfl
  intro b _
  rw [thetaReadoutFromQ_eq]
  rw [Finset.mul_sum]

/-- The global Theta readout in terms of the actual global q-pilot magnitude. -/
theorem globalThetaReadoutFromQ_eq_globalQPilot
    [Fintype (Bad (nativePlaceSelection T))] (j : SignedLabel l.value) :
    globalThetaReadoutFromQ T j =
      ((IUT.Theta.gaussExp j.1).toNat : Real) * globalQPilotLogMagnitude T := by
  rw [globalThetaReadoutFromQ_eq, globalQPilotLogMagnitude_eq_totalLogMagnitude]

/-- `_constructed`: the readout object is the actual theta value formula. -/
theorem thetaReadoutFromQ_constructed
    (b : Bad (nativePlaceSelection T)) (j : SignedLabel l.value) :
    thetaReadoutFromQ T b j = -Real.log (thetaValueFromQ T b j) ∧
      thetaReadoutFromQ T b j =
        ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b :=
  ⟨rfl, thetaReadoutFromQ_eq T b j⟩

#check thetaReadoutFromQ_eq
#check globalThetaReadoutFromQ_eq
#check thetaReadoutFromQ_constructed

end LeanFormal.IUT.XiFPaper.ThetaReadoutFromQActual
end
