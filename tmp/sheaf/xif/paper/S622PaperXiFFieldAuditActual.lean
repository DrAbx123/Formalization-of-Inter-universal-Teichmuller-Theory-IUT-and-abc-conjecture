import tmp.sheaf.xif.PaperXiFInclusion
import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.PaperSignedHullSignedActual

-- S622: field-level audit of PaperXiFSourceLink.
-- Field 1 (source identifications) is actual for the concrete q-pilot.
-- Fields 2-4 are the exact paper q-normalization and xi-f link obligations.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion

universe uX uLabel

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)

abbrev concreteO : PaperQPilotObject
    (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
    I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l)) :=
  paperQPilotObjectConcrete (l := l) I

theorem concrete_source_identifications :
    (concreteO (l := l) I).paper_strip_identification ∧
      (concreteO (l := l) I).paper_lineBundle_identification ∧
      (concreteO (l := l) I).paper_logKummer_identification ∧
      (concreteO (l := l) I).paper_qPilot_log_identification := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rfl

def concreteQIdentificationGap : Prop :=
  (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3

structure concreteLinkFieldGap where
  q_identification : concreteQIdentificationGap (l := l) I C3
  link_identification : Prop
  link_implies_inclusion :
    link_identification →
      (concreteO (l := l) I).qPilotLogVolume ∈
        hullLogVolumeRay P.signedHullLogVolume

noncomputable def concretePaperXiFSourceLink
    (hQ : concreteQIdentificationGap (l := l) I C3)
    (L : Prop)
    (himp : L → (concreteO (l := l) I).qPilotLogVolume ∈
      hullLogVolumeRay P.signedHullLogVolume) :
    PaperXiFSourceLink (O := concreteO (l := l) I) (P := P) (C3 := C3) where
  source_identifications := concrete_source_identifications (l := l) I
  qPilotLogVolume_eq_paper := hQ
  link_identification := L
  link_implies_inclusion := himp

#check concrete_source_identifications
#check concreteQIdentificationGap
#check concreteLinkFieldGap
#check concretePaperXiFSourceLink

end LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual

end