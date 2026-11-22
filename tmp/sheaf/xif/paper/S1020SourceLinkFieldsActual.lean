import tmp.sheaf.xif.paper.S999HQHC3Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S1020SourceLinkFieldsActual

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
open LeanFormal.IUT.XiFPaper.S999HQHC3Actual
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

universe uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)
variable (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
  (l := l) (V := FinitePrimePlace 2 7) (I := I))

/-- Actual constructed link from the two exact source conditions. -/
abbrev s1020Link
    (P : PaperSignedHull X label)
    (hC3 : S999LineC3Identification (l := l) I C3 Oa)
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    PaperXiFSourceLink (concreteO (l := l) I) P C3 :=
  s999PaperXiFSourceLink (l := l) I P C3 Oa hC3 hQ

/-- qPilotLogVolume_eq_paper is exactly the hQ source identification. -/
theorem s1020QPilotLogVolume_eq_paper
    (hC3 : S999LineC3Identification (l := l) I C3 Oa)
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3 :=
  (s1020Link (l := l) I P C3 Oa hC3 hQ).qPilotLogVolume_eq_paper

/-- link_identification is the actual theta source comparison. -/
theorem s1020LinkIdentification
    (hC3 : S999LineC3Identification (l := l) I C3 Oa)
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3) :
    (s1020Link (l := l) I P C3 Oa hC3 hQ).link_identification =
      thetaSourceComparison Oa P := by
  unfold s1020Link s999PaperXiFSourceLink s991PaperXiFSourceLink
  exact paperXiFSourceLinkOfActualTheta_link_identification
    (l := l) (V := FinitePrimePlace 2 7) (I := I)
    (O := concreteO (l := l) I) Oa P C3
    (s991SourceIdentifications (l := l) I) hQ
    (s991SignedQIdentification (l := l) I C3 Oa hC3 hQ)

/-- link_implies_inclusion is actual for the constructed link. -/
theorem s1020LinkImpliesInclusion
    (hC3 : S999LineC3Identification (l := l) I C3 Oa)
    (hQ : S999QPilotLogVolumeIdentification (l := l) I C3)
    (h : (s1020Link (l := l) I P C3 Oa hC3 hQ).link_identification) :
    (concreteO (l := l) I).qPilotLogVolume ∈
      hullLogVolumeRay P.signedHullLogVolume :=
  (s1020Link (l := l) I P C3 Oa hC3 hQ).link_implies_inclusion h

/-- Exact minimum: hC3 and hQ are the only source-link conditions. -/
def S1020ExactMinimum : Prop :=
  S999LineC3Identification (l := l) I C3 Oa ∧
    S999QPilotLogVolumeIdentification (l := l) I C3

theorem s1020ExactMinimum_suffices
    (h : S1020ExactMinimum (l := l) I C3 Oa) :
    Nonempty (PaperXiFSourceLink (concreteO (l := l) I) P C3) :=
  ⟨s1020Link (l := l) I P C3 Oa h.1 h.2⟩

end LeanFormal.IUT.XiFPaper.S1020SourceLinkFieldsActual

end
