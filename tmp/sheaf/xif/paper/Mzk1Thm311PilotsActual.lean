import tmp.sheaf.xif.paper.Mzk1QPilotSHEDoubleImageActual
import tmp.sheaf.xif.paper.O2ThetaObjectActual

/-! Mainline (A517-2): Theorem 3.11 q/Theta pilot objects, referenced from our own real
objects: the literal q-pilot image (`Mzk1QPilotSHEDoubleImageActual.qPilotLogImage` =
`Real.log ‖q_V‖`, the actual completion log; `she_arrow_apply` = the SHE root relation
`q = θ^(2ℓ)`), and the independent Theta-pilot object (`O2ThetaObjectActual.qroot`,
`thetaPilotValue = thetaValueMon qroot j`, `thetaPilotLogVolume = gaussExp j * logVol(qroot)`;
no q/(2ℓ)).  This is the q/Θ-pilot input of the multiradial algorithm. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1Thm311PilotsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.PaperThetaRootObstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.Mzk1QPilotSHEDoubleImageActual
open LeanFormal.IUT.XiFPaper.O2ThetaObjectActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- **O1/O3 pilot pair object**: a chosen bad place at which the q-pilot readout is taken;
  the Theta-pilot data (`qroot`, `thetaPilotValue`, readouts) is attached to the same `T`. -/
structure Thm311PilotObjects where
  /-- A bad place `v ∈ V^bad` at which the q-pilot log-volume is read. -/
  place : Bad (nativePlaceSelection T)

/-- The q-pilot log-volume `-|log q|` at the chosen bad place (literal completion log). -/
def Thm311PilotObjects.qPilotLogVolume (O : Thm311PilotObjects T) : ℝ :=
  qPilotLogImage T O.place

/-- The q-pilot readout is negative (`|log q| > 0`). -/
theorem Thm311PilotObjects.qPilotLogVolume_neg (O : Thm311PilotObjects T) :
    O.qPilotLogVolume < 0 :=
  qPilotLogImage_neg T O.place

/-- The q-pilot image satisfies the SHE root relation `q = θ^(2ℓ)` at every bad place
  (our real theorem `she_arrow_apply`). -/
theorem thm311_she_root_relation (b : Bad (nativePlaceSelection T)) :
    completionToRootExtension T (qPilotCompletionImage T) b =
      (thetaPilotImage T (oneThetaLabel l) b) ^ (2 * l.value) :=
  she_arrow_apply T b

/-- The 2ℓ-th root relation `qroot^(2ℓ) = q` (real theorem from our O2 object). -/
theorem thm311_qroot_pow (b : Bad (nativePlaceSelection T)) :
    (qroot T b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) :=
  qroot_pow T b

/-- The Theta-pilot value at a signed label (independent of qroot by construction;
  `thetaValueMon qroot j`). -/
def thm311ThetaPilotValue (j : SignedLabel l.value) : S1902Carrier T :=
  thetaPilotValue T j

/-- The Theta value is `qroot` to the Gaussian exponent (real theorem). -/
theorem thm311ThetaPilotValue_def (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    thm311ThetaPilotValue T j b = (qroot T b) ^ (IUT.Theta.gaussExp j.1).toNat :=
  thetaPilotValue_def T j b

/-- The `±1` symmetry of the Theta values (real theorem). -/
theorem thm311ThetaPilotValue_neg (j : SignedLabel l.value) :
    thm311ThetaPilotValue T (SignedLabel.neg j) = thm311ThetaPilotValue T j :=
  thetaPilotValue_neg T j

/-- The independent Theta-pilot log-volume `gaussExp j * logVol(qroot)` at a place. -/
def thm311ThetaPilotLogVolume (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) : ℝ :=
  thetaPilotLogVolume T j b

/-- The Theta-pilot readout equals the log-norm of the Theta value (real theorem). -/
theorem thm311ThetaPilotLogVolume_eq_log_norm (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    thm311ThetaPilotLogVolume T j b =
      Real.log ‖(thetaPilotValue T j b : rootNormedExtension T b)‖ :=
  thetaPilotLogVolume_eq_log_norm T j b

/-- The Theta-pilot readout equals `gaussExp j * logVol(qroot)` (real theorem; explicitly
  no `q/(2ℓ)`). -/
theorem thm311ThetaPilotLogVolume_eq_gaussExp_mul (j : SignedLabel l.value)
    (b : Bad (nativePlaceSelection T)) :
    thm311ThetaPilotLogVolume T j b =
      (IUT.Theta.gaussExp j.1 : ℝ) * localQrootLogVolume T b :=
  thetaPilotLogVolume_eq_gaussExp_mul T j b

/-- The global Theta-pilot log-volume (sum over the bad locus), when the locus is finite. -/
def thm311GlobalThetaPilotLogVolume [Fintype (Bad (nativePlaceSelection T))]
    (j : SignedLabel l.value) : ℝ :=
  globalThetaLogVolume T j

/-- The global readout is the sum of the log-norms of the theta values (real theorem). -/
theorem thm311GlobalThetaPilotLogVolume_eq [Fintype (Bad (nativePlaceSelection T))]
    (j : SignedLabel l.value) :
    thm311GlobalThetaPilotLogVolume T j =
      ∑ b : Bad (nativePlaceSelection T),
        Real.log ‖(thetaPilotValue T j b : rootNormedExtension T b)‖ :=
  globalThetaLogVolume_eq T j

end

end LeanFormal.IUT.XiFPaper.Mzk1Thm311PilotsActual