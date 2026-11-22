import tmp.sheaf.xif.paper.S1009HQHC3Actual
import tmp.sheaf.xif.paper.S983PaperXiFSourceLinkConstructionActual
import tmp.sheaf.xif.paper.S991S983LinkInputsActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1028LinkActual

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
open LeanFormal.IUT.XiFPaper.S1009HQHC3Actual
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.XiFPaper.ThetaLinkFromSource

universe uX uLabel uC3 uD3 uM uP
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C1 : SourceInputBinding I)
variable (C2 : SourceLogKummerData I C1)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

/-- Canonical actual object used for the link. -/
abbrev s1028Oa :
    PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, 0, 0}
      (l := l) (V := FinitePrimePlace 2 7) (I := I) :=
  s1009CanonicalOa (l := l) I C1 C2 C3

/-- The link from sourceQ alone: hC3 is actual, hQ is sourceQ. -/
noncomputable def s1028Link
    (hsrc : S1009SourceQIdentification I C3) :
    PaperXiFSourceLink (concreteO (l := l) I) P C3 :=
  s991PaperXiFSourceLink (l := l) I P C3 (s1028Oa (l := l) I C1 C2 C3)
    (s1009Canonical_hC3 (l := l) I C1 C2 C3)
    ((s1009HQ_iff_sourceQ (l := l) I C3).mpr hsrc)

/-- Exact hlink condition for the constructed link. -/
def S1028HLink
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (P : PaperSignedHull X label)
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)
    (hsrc : S1009SourceQIdentification I C3) : Prop :=
  (s1028Link (l := l) (I := I) (P := P) (C1 := C1) (C2 := C2) (C3 := C3) hsrc).link_identification

/-- The link's identification is the actual theta source comparison. -/
theorem s1028HLink_iff_theta
    (hsrc : S1009SourceQIdentification I C3) :
    S1028HLink (l := l) (I := I) (P := P) (C1 := C1) (C2 := C2) (C3 := C3) hsrc ↔
      thetaSourceComparison (s1028Oa (l := l) I C1 C2 C3) P := by
  rfl

/-- Inclusion from sourceQ and the exact hlink. -/
noncomputable def s1028Inclusion
    (hsrc : S1009SourceQIdentification I C3)
    (hlink : S1028HLink (l := l) (I := I) (P := P) (C1 := C1) (C2 := C2) (C3 := C3) hsrc) :
    PaperXiFInclusion (concreteO (l := l) I) P C3 where
  link := s1028Link (l := l) (I := I) (P := P) (C1 := C1) (C2 := C2) (C3 := C3) hsrc
  link_holds := hlink

/-- SourceQ alone constructs the link; hlink is its exact identification field. -/
theorem s1028Link_actual
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (hsrc : S1009SourceQIdentification I C3) :
    Nonempty (PaperXiFSourceLink (concreteO (l := l) I) P C3) :=
  ⟨s1028Link (l := l) (I := I) (P := P) (C1 := C1) (C2 := C2) (C3 := C3) hsrc⟩

/-- Exact minimum for a full inclusion: sourceQ plus the link identification. -/
def S1028ExactMinimum
    (C1 : SourceInputBinding I)
    (C2 : SourceLogKummerData I C1)
    (hsrc : S1009SourceQIdentification I C3) : Prop :=
  S1028HLink (l := l) (I := I) (P := P) (C1 := C1) (C2 := C2) (C3 := C3) hsrc

end LeanFormal.IUT.XiFPaper.S1028LinkActual

end
