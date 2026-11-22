import tmp.sheaf.xif.paper.S991S983LinkInputsActual
import tmp.sheaf.xif.paper.S994FiniteCarrierCor312Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S999HQHC3Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S994FiniteCarrierCor312Actual

universe uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)
variable (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
  (l := l) (V := FinitePrimePlace 2 7) (I := I))

/-- Exact hC3 condition: the actual object's line C3 is the chosen C3. -/
def S999LineC3Identification : Prop :=
  Oa.line.C3 = C3

/-- Exact hQ condition for the concrete object. -/
def S999QPilotLogVolumeIdentification : Prop :=
  (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3

/-- Exact minimum for both hQ and hC3. -/
def S999ExactMinimum : Prop :=
  S999LineC3Identification (l := l) I C3 Oa ∧
    S999QPilotLogVolumeIdentification (l := l) I C3

/-- S991 link inputs from the two exact conditions. -/
noncomputable def s999LinkInputs
    (hC3 : S999LineC3Identification (l := l) I C3 Oa)
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    S983LinkInputs (l := l) (V := FinitePrimePlace 2 7) (I := I)
      (O := concreteO (l := l) I) (Oa := Oa) (C3 := C3) :=
  s991LinkInputs (l := l) I C3 Oa hC3 hQ

/-- Actual source link from the two exact conditions. -/
noncomputable def s999PaperXiFSourceLink
    (hC3 : S999LineC3Identification (l := l) I C3 Oa)
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    PaperXiFSourceLink (concreteO (l := l) I) P C3 :=
  s991PaperXiFSourceLink (l := l) I P C3 Oa hC3 hQ

/-- The exact minimum suffices for the S994 concrete link. -/
theorem s999Minimum_implies_S994Link
    (h : S999ExactMinimum (l := l) I C3 Oa) :
    Nonempty (PaperXiFSourceLink (concreteO (l := l) I) P C3) :=
  ⟨s999PaperXiFSourceLink (l := l) I P C3 Oa h.1 h.2⟩

/-- Exact hQ field separately. -/
def S999HQExactMinimum : Prop :=
  S999QPilotLogVolumeIdentification (l := l) I C3

/-- Exact hC3 field separately. -/
def S999HC3ExactMinimum : Prop :=
  S999LineC3Identification (l := l) I C3 Oa

end LeanFormal.IUT.XiFPaper.S999HQHC3Actual

end
