import tmp.sheaf.xif.paper.S999HQHC3Actual
import tmp.sheaf.xif.paper.QPilotObjectFromSource
import tmp.sheaf.xif.paper.QPilotCanonicalConstruction
import tmp.sheaf.xif.paper.OneColumnFinitePrimePlaceActual
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.S622PaperXiFFieldAuditActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1009HQHC3Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual
open LeanFormal.IUT.XiFPaper.S999HQHC3Actual

universe uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- Canonical actual qPilot object on FinitePrimePlace 2 7 with line C3 fixed
to the chosen C3. -/
noncomputable def s1009CanonicalOa :
    PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) (I := I) :=
  paperQPilotObjectActualOfLine
    (qPilotLineOfSource C1 C2 C3)
    (SourceFTimesMuPrimeStrip.canonical.{0,0,0} (I.primeStripAt 0 0))
    actualOneColumnFinitePrimePlace

/-- The canonical actual object has hC3 definitionally. -/
theorem s1009Canonical_hC3 :
    S999LineC3Identification (l := l) I C3
      (s1009CanonicalOa (l := l) I C1 C2 C3) := by
  unfold S999LineC3Identification s1009CanonicalOa
  simp [paperQPilotObjectActualOfLine, qPilotLineOfSource]

/-- Exact source-q identification. -/
def S1009SourceQIdentification
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I) : Prop :=
  sourceQPilotSignedLog I.initial = localSignedLog C3.q

/-- hQ is exactly the source-q identification. -/
theorem s1009HQ_iff_sourceQ :
    S999QPilotLogVolumeIdentification (l := l) I C3 ↔
      S1009SourceQIdentification I C3 := by
  unfold S999QPilotLogVolumeIdentification S1009SourceQIdentification concreteO
  rw [LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual.paperQPilotObjectConcrete_qPilotLogVolume (l := l) I]
  rfl

/-- For the canonical actual object, S999ExactMinimum reduces to the single
source-q identification. -/
theorem s1009ExactMinimum_canonical_iff_sourceQ :
    S999ExactMinimum (l := l) I C3
      (s1009CanonicalOa (l := l) I C1 C2 C3) ↔
      S1009SourceQIdentification I C3 := by
  constructor
  · intro h
    exact (s1009HQ_iff_sourceQ (l := l) I C3).mp h.2
  · intro h
    exact ⟨s1009Canonical_hC3 (l := l) I C1 C2 C3,
      (s1009HQ_iff_sourceQ (l := l) I C3).mpr h⟩

/-- Exact single source-q condition. -/
def S1009ExactSourceQCondition : Prop :=
  S1009SourceQIdentification I C3

end LeanFormal.IUT.XiFPaper.S1009HQHC3Actual

end
