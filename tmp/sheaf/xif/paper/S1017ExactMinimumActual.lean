import tmp.sheaf.xif.paper.S1009HQHC3Actual

/-! # S1017: S999ExactMinimum via the canonical actual qPilot object

S1009 constructs the canonical actual PaperQPilotObjectActual with line C3
fixed, proving hC3 definitionally.  The hQ component reduces exactly to the
source-q identification sourceQPilotSignedLog I.initial = localSignedLog C3.q.
S999ExactMinimum is therefore actual precisely under this single exact
source condition. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1017ExactMinimumActual

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
open LeanFormal.IUT.XiFPaper.S999HQHC3Actual
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual

universe uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- hC3 is actual for the canonical actual object. -/
theorem s1017HC3_actual :
    S999LineC3Identification (l := l) I C3
      (s1009CanonicalOa (l := l) I C1 C2 C3) :=
  s1009Canonical_hC3 (l := l) I C1 C2 C3

/-- hQ is exactly the source-q identification. -/
theorem s1017HQ_iff_sourceQ :
    S999QPilotLogVolumeIdentification (l := l) I C3 ↔
      S1009SourceQIdentification I C3 :=
  s1009HQ_iff_sourceQ (l := l) I C3

/-- S999ExactMinimum for the canonical actual object is equivalent to the
single source-q identification. -/
theorem s1017ExactMinimum_iff_sourceQ :
    S999ExactMinimum (l := l) I C3
      (s1009CanonicalOa (l := l) I C1 C2 C3) ↔
      S1009SourceQIdentification I C3 :=
  s1009ExactMinimum_canonical_iff_sourceQ (l := l) I C1 C2 C3

/-- Conditional S999ExactMinimum from the exact source-q identification. -/
theorem s1017ExactMinimum_of_sourceQ
    (h : S1009SourceQIdentification I C3) :
    S999ExactMinimum (l := l) I C3
      (s1009CanonicalOa (l := l) I C1 C2 C3) :=
  (s1017ExactMinimum_iff_sourceQ (l := l) I C1 C2 C3).mpr h

/-- Exact minimal hQ condition. -/
def S1017HQExactMinimum : Prop :=
  S1009SourceQIdentification I C3

/-- Full exact minimum: hC3 is actual, so only hQ/source-q remains. -/
def S1017ExactMinimumRequired : Prop :=
  S1009SourceQIdentification I C3

end LeanFormal.IUT.XiFPaper.S1017ExactMinimumActual
end
