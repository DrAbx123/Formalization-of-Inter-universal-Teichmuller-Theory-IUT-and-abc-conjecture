import tmp.sheaf.xif.paper.GlobalKummerIndActionsActual
import tmp.sheaf.xif.paper.ThetaLinkActual
import tmp.sheaf.xif.paper.IndActionsActual
import tmp.sheaf.xif.paper.IndeterminaciesActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource

/-!
# Ind1/Ind2/Ind3 actions attached to the final tensor packet and ThetaLink

GlobalKummerIndActionsActual already supplies actual actions:

* ind1: actual PrcAutomorphismTensorAction on the actual tensor packet;
* ind2: actual ind2TensorEquiv action on the source procession capsule tensor;
* ind3: actual x-mu stage/action/comparison data from the F-prime-strip links.

This file attaches those actual actions to the final tensor packet and to an
explicit ThetaLinkActual.  The ThetaLinkActual itself is not asserted: its
link identification and log-volume comparison remain its own fields.

What is supplied actually:

* GlobalKummerIndActionsData;
* its ind1/ind2/ind3 projections;
* a record carrying those actions together with a supplied ThetaLinkActual.

What remains exact gap: compatibility of the Ind actions with the ThetaLink
q-pilot scalar, the global Theta packet, and the xi-f comparison.  The gap is
recorded as Prop fields, not assumed.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.IndActionsThetaLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.GlobalKummerIndActionsActual
open LeanFormal.IUT.XiFPaper.MultiradialProcessionActual
open LeanFormal.IUT.XiFPaper.Ind1AutomorphismTensorActionActual
open LeanFormal.IUT.XiFPaper.Ind2TensorActionActual
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open scoped TensorProduct

universe ua uv upi umon ui uG uX uLabel uL uC

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
variable {I : OriginalInput.{ua, uv, upi, 0, ui} l V}
variable {A : CapsuleTheaterAssignment l V I}
variable {C : SourceProcessionCapsuleContract Real l V I}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)
variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {envStrip : FPrimeStrip V}
variable {X : Type uX} {label : Type uLabel} [Fintype label] [Nonempty label]

/-- Actual Ind1/Ind2/Ind3 actions on the final tensor packet, together with the
global Theta packet. -/
structure FinalTensorPacketIndActions where
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
  ind1_eq : ind1 = fun j vQ P => PrcAutomorphismTensorAction A C j vQ P
  ind2_eq : ind2 = fun j vQ f => ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
  ind3_eq : ind3 = fun v => actualInd3DataV I v
  globalThetaPacket_eq : globalThetaPacket = C3.thetaPacket

/-- Actual final-tensor-packet Ind action data. -/
noncomputable def finalTensorPacketIndActions :
    FinalTensorPacketIndActions (I := I) (A := A) (C := C) C3 where
  ind1 := fun j vQ P => PrcAutomorphismTensorAction A C j vQ P
  ind2 := fun j vQ f => ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f
  ind3 := fun v => actualInd3DataV I v
  globalThetaPacket := C3.thetaPacket
  ind1_eq := rfl
  ind2_eq := rfl
  ind3_eq := rfl
  globalThetaPacket_eq := rfl

/-- Ind1 projection is the actual tensor automorphism action. -/
theorem finalTensorPacketIndActions_ind1
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (P : PrcAutomorphism A j) :
    (finalTensorPacketIndActions (I := I) (A := A) (C := C) C3).ind1 j vQ P =
      PrcAutomorphismTensorAction A C j vQ P := rfl

/-- Ind2 projection is the actual independent-copy tensor action. -/
theorem finalTensorPacketIndActions_ind2
    (j : Fin (capsuleLevels l)) (vQ : C.VQ)
    (f : Capsule j.val → Realˣ) :
    (finalTensorPacketIndActions (I := I) (A := A) (C := C) C3).ind2 j vQ f =
      ind2TensorEquiv (C := C) (j := j) (vQ := vQ) f := rfl

/-- Ind3 projection is the actual stage/times-mu action data. -/
theorem finalTensorPacketIndActions_ind3 (v : V) :
    (finalTensorPacketIndActions (I := I) (A := A) (C := C) C3).ind3 v =
      actualInd3DataV I v := rfl

/-- Exact compatibility gap between the actual Ind actions and an explicit
ThetaLink: action compatibility with the link identification, q-pilot scalar,
global Theta packet, and log-volume comparison. -/
structure IndThetaLinkCompatibilityGap
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) : Type where
  ind1_preserves_qPilot : Prop
  ind2_preserves_qPilot : Prop
  ind3_preserves_qPilot : Prop
  ind1_preserves_thetaPacket : Prop
  ind2_preserves_thetaPacket : Prop
  ind3_preserves_thetaPacket : Prop
  ind_compatible_link_identification : Prop
  ind_compatible_logVolume_comparison : Prop

/-- Exact missing compatibility object. -/
def IndThetaLinkCompatibilityGapRequired
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) : Prop :=
  Nonempty (IndThetaLinkCompatibilityGap (l := l) (V := V) (I := I)
    (Label := Label) (Choice := Choice) (G := G) (envStrip := envStrip)
    (X := X) (label := label) O P)

/-- Actual multiradial comparison data: the actual final tensor packet actions,
the actual global Theta packet, and an explicit ThetaLinkActual.  The
compatibility of the actions with the link remains the exact Prop gap above. -/
structure ActualMultiradialComparisonData
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label) where
  actions : FinalTensorPacketIndActions (I := I) (A := A) (C := C) C3
  actions_eq : actions = finalTensorPacketIndActions (I := I) (A := A) (C := C) C3
  thetaLink : ThetaLinkActual O P C3
  compatibilityGap : Prop
  compatibilityGap_eq : compatibilityGap =
    IndThetaLinkCompatibilityGapRequired (l := l) (V := V) (I := I)
      (Label := Label) (Choice := Choice) (G := G) (envStrip := envStrip)
      (X := X) (label := label) O P

/-- The actual multiradial comparison record, conditional on an explicit
ThetaLinkActual.  No link identification or comparison is asserted here. -/
noncomputable def actualMultiradialComparisonData
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (L : ThetaLinkActual O P C3) :
    ActualMultiradialComparisonData (I := I) (A := A) (C := C) C3 O P where
  actions := finalTensorPacketIndActions (I := I) (A := A) (C := C) C3
  actions_eq := rfl
  thetaLink := L
  compatibilityGap := IndThetaLinkCompatibilityGapRequired (l := l) (V := V)
    (I := I) (Label := Label) (Choice := Choice) (G := G)
    (envStrip := envStrip) (X := X) (label := label) O P
  compatibilityGap_eq := rfl

/-- The actual actions are those of GlobalKummerIndActionsActual, not a new
action layer. -/
theorem actualMultiradialComparisonData_actions_eq_global
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (L : ThetaLinkActual O P C3) :
    (actualMultiradialComparisonData (I := I) (A := A) (C := C) C3 O P L).actions =
      finalTensorPacketIndActions (I := I) (A := A) (C := C) C3 := rfl


variable (v : V) (R : I.SourceImageRealization v)

/-- Actual Ind3 upper-semi and log-Kummer data: the actual value-layer
upper-semi correspondence, the actual vertical Kummer layers/arrows, and the
actual stage comparison. -/
structure Ind3UpperSemiLogKummerData where
  valueUpperSemi : UpperSemiCorrespondence (ThetaPilotCarrier l)
    (I.ThetaPilotPoint v)
  valueUpperSemi_eq : valueUpperSemi = I.ind3UpperSemi v R
  kummerLayer : ∀ m : Int,
    SourceTimesMuKummerLayer (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0)
  kummerLayer_eq : kummerLayer = actualVerticalKummerLayer (I := I)
  kummerArrow : ∀ m : Int,
    SourceKummerArrow (ActualKummerGroup (I := I))
      (I.fPrimeStripAt 1 m) (I.fPrimeStripAt 1 0)
  kummerArrow_eq : kummerArrow = actualKummerArrow (I := I)
  stageComparison : ∀ m : Int,
    ActualInd3Stage (I := I) v m ≃* ActualInd3Stage (I := I) v 0
  stageComparison_eq : stageComparison = actualInd3StageComparison (I := I) v

/-- Actual Ind3 upper-semi log-Kummer data from the actual value-stage
correspondence and actual vertical Kummer layers. -/
noncomputable def ind3UpperSemiLogKummerData :
    Ind3UpperSemiLogKummerData (I := I) v R where
  valueUpperSemi := I.ind3UpperSemi v R
  valueUpperSemi_eq := rfl
  kummerLayer := actualVerticalKummerLayer (I := I)
  kummerLayer_eq := rfl
  kummerArrow := actualKummerArrow (I := I)
  kummerArrow_eq := rfl
  stageComparison := actualInd3StageComparison (I := I) v
  stageComparison_eq := rfl

/-- Exact compatibility gap between the actual Ind3 value upper-semi
correspondence and the actual log-Kummer layers: a log-Kummer upper-semi
comparison identifying the two families is not supplied by either object
separately. -/
structure Ind3UpperSemiLogKummerGap : Type where
  valueImage_eq_logKummerImage : Prop
  stageComparison_compatible_kummerArrow : Prop
  upperSemi_preserved_by_kummerLayer : Prop
  logVolume_upperSemi_compatible : Prop

/-- Exact missing Ind3 upper-semi/log-Kummer compatibility object. -/
def Ind3UpperSemiLogKummerGapRequired : Prop :=
  Nonempty Ind3UpperSemiLogKummerGap

/-- The actual Ind3 upper-semi log-Kummer data, with the compatibility gap
carried separately. -/
structure ActualInd3UpperSemiLogKummerData where
  data : Ind3UpperSemiLogKummerData (I := I) v R
  data_eq : data = ind3UpperSemiLogKummerData (I := I) v R
  compatibilityGap : Prop
  compatibilityGap_eq : compatibilityGap =
    Ind3UpperSemiLogKummerGapRequired

/-- Actual Ind3 upper-semi log-Kummer record. -/
noncomputable def actualInd3UpperSemiLogKummerData :
    ActualInd3UpperSemiLogKummerData (I := I) v R where
  data := ind3UpperSemiLogKummerData (I := I) v R
  data_eq := rfl
  compatibilityGap := Ind3UpperSemiLogKummerGapRequired
  compatibilityGap_eq := rfl

end LeanFormal.IUT.XiFPaper.IndActionsThetaLinkActual
end
