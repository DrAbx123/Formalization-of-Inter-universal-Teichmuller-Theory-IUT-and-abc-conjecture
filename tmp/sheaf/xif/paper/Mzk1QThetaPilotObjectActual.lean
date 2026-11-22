/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.O2QrootGlueActual
import tmp.sheaf.xif.paper.GlobalThetaPilotLogVolumeActual
import tmp.sheaf.xif.paper.GlobalPositiveThetaHullLogVolumeActual

/-!
# Mzk1QThetaPilotObjectActual — q-pilot / Theta-pilot object (green assets only)

A517: reference object combining our green O2 qroot object
(`O2QrootGlueActual.qrootElem`, `qrootElem_pow`) with the actual theta values
(`GlobalThetaPilotLogVolumeActual.thetaValueFromQ`, `= q_v^{j^2}`) and the
positive theta-hull volume asset (`GlobalPositiveThetaHullLogVolumeActual`).

Fields are the actual definitions; the theta readout is the independent
`-log(thetaValueFromQ) = gaussExp j * |log q_v|` (no q/(2ℓ) definition).
No new axiom, no comparison. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Mzk1QThetaPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S1929LiteralIQCarrierActual
open LeanFormal.IUT.XiFPaper.O2QrootGlueActual
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.BaseQLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalPositiveThetaHullLogVolumeActual
open scoped BigOperators

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)

/-- The q-pilot / Theta-pilot object: the actual qroot, the actual theta values,
and their readouts. -/
structure QThetaPilotObject where
  /-- the q-pilot root at each bad place. -/
  qroot : ∀ b : Bad (nativePlaceSelection T), rootNormedExtension T b
  /-- the qroot is the O2 root-system element. -/
  qroot_eq : ∀ b, qroot b = qrootElem T b
  /-- the Theta values `q_v^{j^2}`. -/
  thetaValue : ∀ b : Bad (nativePlaceSelection T), SignedLabel l.value → Real
  /-- the theta values are the actual `thetaValueFromQ`. -/
  thetaValue_eq : ∀ b j, thetaValue b j = thetaValueFromQ T b j
  /-- the Theta readout `gaussExp j * |log q_v|`. -/
  thetaReadout : ∀ b, SignedLabel l.value → Real
  thetaReadout_eq : ∀ b j,
    thetaReadout b j = ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b

/-- The constructed object from the actual assets. -/
noncomputable def qThetaPilotObject : QThetaPilotObject T where
  qroot := qrootElem T
  qroot_eq := fun _ => rfl
  thetaValue := fun b j => thetaValueFromQ T b j
  thetaValue_eq := fun _ _ => rfl
  thetaReadout := fun b j =>
    ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b
  thetaReadout_eq := fun _ _ => rfl

/-- `_constructed`: qroot is the O2 root-system element. -/
theorem qThetaPilotObject_qroot :
    (qThetaPilotObject T).qroot = qrootElem T := rfl

/-- `_constructed`: theta values are the actual `thetaValueFromQ`. -/
theorem qThetaPilotObject_thetaValue :
    (qThetaPilotObject T).thetaValue = fun b j => thetaValueFromQ T b j := rfl

/-- The qroot satisfies `qroot^(2ℓ) = q` (reusing O2). -/
theorem qThetaPilotObject_qroot_pow (b : Bad (nativePlaceSelection T)) :
    ((qThetaPilotObject T).qroot b) ^ (2 * l.value) =
      algebraMap (rootBase T b) (rootNormedExtension T b)
        ((qVFamily T b).q : rootBase T b) := by
  rw [show (qThetaPilotObject T).qroot b = qrootElem T b from rfl]
  exact qrootElem_pow T b

/-- The Theta readout is the negative log of the actual theta value. -/
theorem qThetaPilotObject_thetaReadout_eq_log (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    (qThetaPilotObject T).thetaReadout b j = -Real.log ((qThetaPilotObject T).thetaValue b j) :=
  rfl

/-- The Theta readout has the Gaussian `j^2` scaling. -/
theorem qThetaPilotObject_thetaReadout_eq (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    (qThetaPilotObject T).thetaReadout b j =
      ((IUT.Theta.gaussExp j.1).toNat : Real) * baseQLogMagnitude T b := rfl

#check qThetaPilotObject_qroot
#check qThetaPilotObject_thetaReadout_eq

end LeanFormal.IUT.XiFPaper.Mzk1QThetaPilotObjectActual
end
