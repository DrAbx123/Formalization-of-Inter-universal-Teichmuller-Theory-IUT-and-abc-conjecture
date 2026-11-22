import tmp.sheaf.xif.paper.S2040ActualThetaLinkActual
import tmp.sheaf.xif.paper.LGPThetaActionActual

/-! # S2040 root-stack Θ-pilot object and paper O obligations

This file defines the actual root-stack Θ-pilot object on `hodgeTwoLthRoot`,
the actual algebraic-closure 2l-th root (not a completion root; S342 rules out
the completion root).  It records the paper O^×/O^×μ/ambient-value carrier as
exact missing data: S1967 proves the available source-strip unit group is
trivial and cannot be the paper local O^×.  No completion root and no reduced
surrogate is used. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.LGPThetaActionActual
open LeanFormal.IUT.XiFPaper.S2040ActualThetaLinkActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.ThetaLink
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open WeierstrassCurve WeierstrassCurve.Affine

universe u ua uv upi umon uL uC uG uX ulab

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- Actual root-stack Θ-pilot object on the algebraic-closure root
`hodgeTwoLthRoot`, not on a completion root. -/
structure S2040RootStackThetaPilotObject where
  /-- The actual Hodge-theater root system. -/
  rootSystem : NatRootSystem (qVAlgClosedUnit (l := l) T b)
  /-- The actual 2l-th root in the algebraic closure. -/
  root : (AlgebraicClosure (Completion (qVPlace (l := l) T b)))ˣ
  root_eq_rootSystem : root = rootSystem.root (2 * l.value)
  root_pow : root ^ (2 * l.value) = qVAlgClosedUnit (l := l) T b
  /-- The actual LGP theta action/index data on this root. -/
  thetaAction : LGPThetaActionData T b
  thetaAction_root_eq : thetaAction.root = root

/-- The actual root-stack Θ-pilot object exists: use the actual Hodge root
system and the actual LGP theta action. -/
noncomputable def s2040RootStackThetaPilotObject :
    S2040RootStackThetaPilotObject (l := l) T b where
  rootSystem := hodgeTwoLRootSystem T b
  root := hodgeTwoLthRoot T b
  root_eq_rootSystem := rfl
  root_pow := hodgeTwoLthRoot_pow T b
  thetaAction := lgpThetaActionData T b
  thetaAction_root_eq := rfl

theorem s2040RootStackThetaPilotObject_available :
    Nonempty (S2040RootStackThetaPilotObject (l := l) T b) :=
  ⟨s2040RootStackThetaPilotObject T b⟩

theorem s2040Root_pow :
    (s2040RootStackThetaPilotObject T b).root ^ (2 * l.value) =
      qVAlgClosedUnit (l := l) T b :=
  (s2040RootStackThetaPilotObject T b).root_pow

theorem s2040Root_theta_value (j : LGPThetaIndex l) :
    (s2040RootStackThetaPilotObject T b).thetaAction.value j =
      lgpThetaValue T b j :=
  (s2040RootStackThetaPilotObject T b).thetaAction.value_eq_hodge j

/-- Exact missing paper O^×/O^×μ/ambient-value carrier for the root-stack
Θ-pilot object.  S1967 proves the available source-strip O^× is unit-trivial
and cannot be the paper local O^×; no inhabitant is asserted. -/
structure S2040PaperOUnitsMuAmbient where
  /-- Actual local-field O^× carrier attached to the source input. -/
  OUnits : Type
  /-- Actual O^×μ torsion-quotient carrier. -/
  OUnitsMu : Type
  /-- Actual ambient theta values. -/
  ambientValues : Type
  /-- The quotient/action compatibility expected of the paper O^×μ. -/
  quotient_compatible : Prop
  /-- The ambient values are the paper's values, not a reduced surrogate. -/
  ambient_values_paper : Prop
  /-- The local O^× carrier is nontrivial (the S1967 obstruction is absent). -/
  OUnits_nontrivial : Prop

/-- Exact missing chain for the actual paper Θ-pilot object: root-stack object
plus paper O^×/O^×μ/ambient data, the four q-pilot identifications, the
q-pilot/O^×μ link compatibilities, paper hull normalization, and the log-volume
comparison. -/
structure S2040RootStackThetaPilotPaperObligations
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    {X : Type uX} {label : Type ulab} [Fintype label]
    (O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip)
    (P : PaperSignedHull X label)
    (C3 : SourcePilotRegionData I) where
  rootObject : S2040RootStackThetaPilotObject T b
  paperOUnitsAmbient : S2040PaperOUnitsMuAmbient
  qPilot_identifications : thetaLinkQPilotPaperIdentifications O
  qPilotLogVolume_eq_paper : O.qPilotLogVolume = paperQPilotLogVolume C3
  qPilotLogVolume_eq_neg_abs :
    ∃ qParameter : Real,
      0 < qParameter ∧ Real.log qParameter ≠ 0 ∧
        O.qPilotLogVolume = -|Real.log qParameter|
  qPilotLinkCompatibility : Prop
  omuLinkCompatibility : Prop
  paperHullNormalization : Prop
  logVolumeComparison : O.qPilotLogVolume ≤ P.signedHullLogVolume

/-- Obligations give the S2040 actual Theta-link. -/
noncomputable def S2040ThetaLinkOfRootStackObligations
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    {X : Type uX} {label : Type ulab} [Fintype label]
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData I}
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (S : S2040RootStackThetaPilotPaperObligations T b O P C3)
    (left right : HodgeTheater (l := l) (FinitePrimePlace 2 7))
    (theaterLink : HodgeTheaterLink left right) :
    S2040ActualThetaLink left right O P where
  theaterLink := theaterLink
  qPilotLinkCompatibility := S.qPilotLinkCompatibility
  omuLinkCompatibility := S.omuLinkCompatibility
  logVolumeComparison := S.logVolumeComparison

/-- The obligations imply the paper 3.12 inequality. -/
theorem S2040Paper312OfRootStackObligations
    {Label : Type uL} {Choice : Type uC} [AddGroup Label] [Preorder Choice]
    {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
    {G : Type uG} [Group G] [TopologicalSpace G]
    {envStrip : FPrimeStrip (FinitePrimePlace 2 7)}
    {X : Type uX} {label : Type ulab} [Fintype label]
    {O : PaperQPilotObject (Label := Label) (Choice := Choice) I G envStrip}
    {P : PaperSignedHull X label}
    {C3 : SourcePilotRegionData I}
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T))
    (S : S2040RootStackThetaPilotPaperObligations T b O P C3)
    (left right : HodgeTheater (l := l) (FinitePrimePlace 2 7))
    (theaterLink : HodgeTheaterLink left right) :
    O.qPilotLogVolume ≤ P.signedHullLogVolume :=
  S.logVolumeComparison

#check S2040RootStackThetaPilotObject
#check s2040RootStackThetaPilotObject
#check S2040PaperOUnitsMuAmbient
#check S2040RootStackThetaPilotPaperObligations
#check S2040Paper312OfRootStackObligations

end LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual
end
