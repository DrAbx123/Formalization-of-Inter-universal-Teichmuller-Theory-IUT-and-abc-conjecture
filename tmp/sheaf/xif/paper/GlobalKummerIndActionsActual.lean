import tmp.sheaf.xif.paper.Ind1AutomorphismTensorActionActual
import tmp.sheaf.xif.paper.Ind2TensorActionActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import tmp.sheaf.n8.closure.SourcePilotRegion

/-!
# Actual global Kummer / Ind1 / Ind2 / Ind3 action fields

This file connects the existing actual Kummer arrow/layer and the partial
Ind1/Ind2/Ind3 actions to the global Theta-pilot packet, as actual action fields:

* kummerArrow/kummerLayer: actual vertical Kummer arrow/layer;
* ind1: actual PrcAutomorphismTensorAction on the actual tensor packet;
* ind2: actual generic ind2TensorEquiv action of independent unit copies;
* ind3: actual x-mu stage/times-mu action/comparison data built directly from
  the actual F-prime-strip links and TimesMuQuotient.congr;
* globalThetaPacket: the actual source Theta packet.

Exact gap: no compatibility among Ind1/2/3, the Kummer layer and the global
Theta-pilot tensor packet; multiradial/LGP action and its compatibility are
absent.  No fake compatibility/inequality.

No empty type, no True/PUnit/axiom/sorry.  WRITE-ONLY; no local compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.FPrimeStrip
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open scoped TensorProduct

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, 0, ui} l V)
variable (A : CapsuleTheaterAssignment l V I)
variable (C : SourceProcessionCapsuleContract Real l V I)
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual Ind3 x-mu stage at column m and place v. -/
abbrev ActualInd3Stage (v : V) (m : Int) : Type :=
  TimesMuQuotient ((I.fPrimeStripAt 1 m).Mon v)ˣ

/-- The actual Ind3 times-mu action on the stage. -/
def actualInd3StageAction (v : V) (m : Int) :
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →*
      MulAut (ActualInd3Stage (I := I) v m) :=
  (I.fPrimeStripAt 1 m).timesMuAction v

/-- The actual Ind3 comparison stage m -> core stage 0. -/
noncomputable def actualInd3StageComparison (v : V) (m : Int) :
    ActualInd3Stage (I := I) v m ≃* ActualInd3Stage (I := I) v 0 :=
  TimesMuQuotient.congr (Units.mapEquiv ((I.fLinkAt 1 m 1 0).isoMon v))

/-- Actual Ind3 stage/action/comparison data. -/
structure ActualInd3Data (v : V) where
  stage : Int → Type
  [stageGroup : ∀ m, Group (stage m)]
  stageAction : ∀ m : Int,
    (I.fPrimeStripAt 1 m).toDPrimeStrip.Pi v →* MulAut (stage m)
  stageComparison : ∀ m : Int, stage m ≃* stage 0

/-- The actual Ind3 data from actual links and times-mu actions. -/
noncomputable def actualInd3Data (v : V) : ActualInd3Data (I := I) v where
  stage m := ActualInd3Stage (I := I) v m
  stageAction m := actualInd3StageAction (I := I) v m
  stageComparison m := actualInd3StageComparison (I := I) v m

/-- Pointwise actual Ind3 data at a fixed source input. -/
noncomputable def actualInd3DataV (v : V) : ActualInd3Data I v :=
  actualInd3Data I v

/-- Actual global Kummer/Ind action fields plus the source Theta packet. -/
structure GlobalKummerIndActionsData where
  kummerArrow :
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  kummerLayer :
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)
  ind1 : ∀ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j),
    ActualTensorPacket C j vQ ≃ₗ[Real]
      (⨂[Real] (i : Capsule j.val),
        DirectSumFactor (C.logShell j) vQ (P.perm.symm i))
  ind2 : ∀ (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ),
    SourceProcessionCapsuleContract.tensorPacket Real C j vQ ≃ₗ[Real]
      SourceProcessionCapsuleContract.tensorPacket Real C j vQ
  ind3 : (v : V) → ActualInd3Data I v
  globalThetaPacket : FiniteThetaPacket l
  kummerArrow_eq : kummerArrow = actualKummerArrow I 0
  kummerLayer_eq : kummerLayer = actualVerticalKummerLayer I 0
  ind3_eq : ind3 = fun v => actualInd3DataV I v
  globalThetaPacket_eq : globalThetaPacket = C3.thetaPacket

/-- Actual global Kummer/Ind fields. -/
noncomputable def globalKummerIndActionsData :
    GlobalKummerIndActionsData I A C C3 where
  kummerArrow := actualKummerArrow I 0
  kummerLayer := actualVerticalKummerLayer I 0
  ind1 := fun j vQ P => PrcAutomorphismTensorAction A C j vQ P
  ind2 := fun j vQ f => ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
  ind3 := fun v => actualInd3DataV I v
  globalThetaPacket := C3.thetaPacket
  kummerArrow_eq := rfl
  kummerLayer_eq := rfl
  ind3_eq := rfl
  globalThetaPacket_eq := rfl

/-- Kummer arrow projection. -/
theorem globalKummerIndActionsData_kummerArrow :
    (globalKummerIndActionsData I A C C3).kummerArrow =
      actualKummerArrow I 0 := rfl

/-- Kummer layer projection. -/
theorem globalKummerIndActionsData_kummerLayer :
    (globalKummerIndActionsData I A C C3).kummerLayer =
      actualVerticalKummerLayer I 0 := rfl

/-- Ind1 action projection. -/
theorem globalKummerIndActionsData_ind1
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) :
    (globalKummerIndActionsData I A C C3).ind1 j vQ P =
      PrcAutomorphismTensorAction A C j vQ P := rfl

/-- Ind2 action projection. -/
theorem globalKummerIndActionsData_ind2
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ) :
    (globalKummerIndActionsData I A C C3).ind2 j vQ f =
      ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f := rfl

/-- Ind3 data projection. -/
theorem globalKummerIndActionsData_ind3 (v : V) :
    (globalKummerIndActionsData I A C C3).ind3 v =
      actualInd3Data (I := I) v := rfl

/-- Global Theta-packet projection. -/
theorem globalKummerIndActionsData_globalThetaPacket :
    (globalKummerIndActionsData I A C C3).globalThetaPacket = C3.thetaPacket := rfl

end LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
