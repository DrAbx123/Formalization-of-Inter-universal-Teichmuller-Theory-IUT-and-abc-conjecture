import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual

/-! # S629: audit of concrete paper_*_identification fields -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S629SourceIdentificationAuditActual
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.XiFPaper

universe ua upi umon ui
variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))

/-- The concrete strip "identification" is only the source-anchor equality,
not an identification with the paper q-pilot prime-strip. -/
theorem concrete_strip_identification_eq :
    (paperQPilotObjectConcrete (l := l) I).paper_strip_identification =
      (concreteQPilotStrip (l := l) =
        sourceQPilotStrip (concreteBoundary (l := l))) := rfl

/-- The concrete line-bundle "identification" is a self-equality. -/
theorem concrete_lineBundle_identification_eq :
    (paperQPilotObjectConcrete (l := l) I).paper_lineBundle_identification =
      (concretePaperLineBundleCarrier (I := I) =
        concretePaperLineBundleCarrier (I := I)) := rfl

/-- The concrete log-Kummer "identification" is a self-equality. -/
theorem concrete_logKummer_identification_eq :
    (paperQPilotObjectConcrete (l := l) I).paper_logKummer_identification =
      (concreteKummerArrow (l := l) = concreteKummerArrow (l := l)) := rfl

/-- The concrete q-pilot log "identification" is a self-equality. -/
theorem concrete_qPilot_log_identification_eq :
    (paperQPilotObjectConcrete (l := l) I).paper_qPilot_log_identification =
      (sourceQPilotSignedLog I.initial = sourceQPilotSignedLog I.initial) := rfl

/-- Exact missing paper-side source objects and identifications. -/
structure PaperSourceIdentificationGap where
  paperStripCarrier : Type u
  paperStripIdentification : Prop
  paperLineBundleCarrier : Type u
  paperLineBundleIdentification : Prop
  paperLogKummerCarrier : Type u
  paperLogKummerIdentification : Prop
  paperQLogVolume : Real
  paperQLogIdentification : Prop

end LeanFormal.IUT.XiFPaper.S629SourceIdentificationAuditActual
end