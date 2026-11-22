/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual

/-!
# Ind123ActionObjectActual — Ind1/2/3 action object glued to actual Kummer data

A511 object file: packages the actual global Kummer/Ind1/Ind2/Ind3 action
fields of `GlobalKummerIndActionsActual` as one object, with projection
theorems.  Reuses the existing actual tensor actions (`PrcAutomorphismTensorAction`,
`ind2TensorEquiv`), the actual Ind3 data (`actualInd3DataV`) and the actual source
Theta packet; no new action is postulated.

No comparison, no interface, no sorry/axiom. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.Ind123ActionObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.FPrimeStrip
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open scoped TensorProduct

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The Ind1/2/3 action object: the actual Kummer/Ind data plus the source Theta
packet, with a definitional provenance field. -/
structure Ind123ActionObject where
  data : GlobalKummerIndActionsData I A C C3
  data_eq : data = globalKummerIndActionsData I A C C3

/-- The constructed object from the actual data. -/
noncomputable def ind123ActionObject : Ind123ActionObject I A C C3 where
  data := globalKummerIndActionsData I A C C3
  data_eq := rfl

/-- `_constructed`: the object is exactly the actual global Kummer/Ind data. -/
theorem ind123ActionObject_constructed :
    (ind123ActionObject I A C C3).data = globalKummerIndActionsData I A C C3 := rfl

/-- Ind1 projection: the actual tensor-packet action. -/
theorem ind123ActionObject_ind1
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (P : PrcAutomorphism A j) :
    (ind123ActionObject I A C C3).data.ind1 j vQ P =
      (globalKummerIndActionsData I A C C3).ind1 j vQ P := rfl

/-- Ind2 projection: the actual independent unit-copy action. -/
theorem ind123ActionObject_ind2
    (j : Fin (capsuleLevels l)) (vQ : C.VQ) (f : Capsule j.val → Realˣ) :
    (ind123ActionObject I A C C3).data.ind2 j vQ f =
      (globalKummerIndActionsData I A C C3).ind2 j vQ f := rfl

/-- Ind3 projection: the actual x-mu stage data. -/
theorem ind123ActionObject_ind3 (v : V) :
    (ind123ActionObject I A C C3).data.ind3 v = actualInd3DataV I v := rfl

/-- The global Theta packet carried by the object is the actual source packet. -/
theorem ind123ActionObject_globalThetaPacket :
    (ind123ActionObject I A C C3).data.globalThetaPacket = C3.thetaPacket := rfl

#check ind123ActionObject_constructed
#check ind123ActionObject_ind1
#check ind123ActionObject_ind3

end LeanFormal.IUT.XiFPaper.Ind123ActionObjectActual
end
