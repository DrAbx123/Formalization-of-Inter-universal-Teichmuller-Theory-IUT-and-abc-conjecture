import tmp.sheaf.xif.paper.S983PaperXiFSourceLinkConstructionActual
import tmp.sheaf.xif.paper.S622PaperXiFFieldAuditActual
import tmp.sheaf.xif.paper.QPilotScalarIdentificationActual

/-! # S991: fill S983LinkInputs with actual components

For the concrete paper qPilot object O:
* source_identifications is actual (S622 concrete_source_identifications);
* signed_q_identification is actual from QPilotScalarIdentification once
  Oa.line.C3 = C3 and O.qPilotLogVolume = paperQPilotLogVolume C3;
* qPilotLogVolume_eq_paper remains the exact source-q identification hQ
  (the concrete actual theorem is conditional on ConcreteSourceQIdentification).
Hence PaperXiFSourceLink is constructed with only hQ and hC3 as exact inputs.
No fake link field. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.S622PaperXiFFieldAuditActual
open LeanFormal.IUT.XiFPaper.S983PaperXiFSourceLinkConstructionActual

universe uX uLabel ua uv upi umon ui uC3 uD3 uM uP

variable {l : PrimeGeFive}
variable (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
variable {X : Type uX} {label : Type uLabel} [Fintype label]
variable (P : PaperSignedHull X label)
variable (C3 : SourcePilotRegionData (l := l) (V := FinitePrimePlace 2 7) I)
variable (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
  (l := l) (V := FinitePrimePlace 2 7) (I := I))

/-- Actual source identifications of the concrete object. -/
theorem s991SourceIdentifications :
    (concreteO (l := l) I).paper_strip_identification ∧
      (concreteO (l := l) I).paper_lineBundle_identification ∧
      (concreteO (l := l) I).paper_logKummer_identification ∧
      (concreteO (l := l) I).paper_qPilot_log_identification :=
  concrete_source_identifications (l := l) I

/-- Signed-q identification from the actual scalar theorem. -/
theorem s991SignedQIdentification
    (hC3 : Oa.line.C3 = C3)
    (hQ : (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3) :
    (concreteO (l := l) I).qPilotLogVolume = Oa.signedQPilotLogVolume := by
  have hsigned : Oa.signedQPilotLogVolume = paperQPilotLogVolume C3 := by
    rw [signedQPilotLogVolume_eq_paperQPilotLogVolume Oa, hC3]
  rw [hQ, hsigned]

/-- Fill S983LinkInputs for the concrete object; only hQ and hC3 are exact. -/
noncomputable def s991LinkInputs
    (hC3 : Oa.line.C3 = C3)
    (hQ : (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3) :
    S983LinkInputs (l := l) (V := FinitePrimePlace 2 7) (I := I)
      (O := concreteO (l := l) I) (Oa := Oa) (C3 := C3) where
  source_identifications := s991SourceIdentifications (l := l) I
  qPilotLogVolume_eq_paper := hQ
  signed_q_identification := s991SignedQIdentification (l := l) I C3 Oa hC3 hQ

/-- Actual PaperXiFSourceLink for the concrete object, conditional only on
hQ (source-q identification) and hC3. -/
noncomputable def s991PaperXiFSourceLink
    (hC3 : Oa.line.C3 = C3)
    (hQ : (concreteO (l := l) I).qPilotLogVolume = paperQPilotLogVolume C3) :
    PaperXiFSourceLink (concreteO (l := l) I) P C3 :=
  paperXiFSourceLink_of_inputs (l := l) (V := FinitePrimePlace 2 7) (I := I)
    (O := concreteO (l := l) I) (Oa := Oa) (P := P) (C3 := C3)
    (s991LinkInputs (l := l) I C3 Oa hC3 hQ)

/-- Exact minimal conditions kept: hQ and hC3. -/
def S991LinkInputsRequired : Prop :=
  ∃ (Oa : PaperQPilotObjectActual.{0, 0, 0, 0, 0, uC3, uD3, uM, uP}
      (l := l) (V := FinitePrimePlace 2 7) (I := I)),
    Nonempty (S983LinkInputs (l := l) (V := FinitePrimePlace 2 7) (I := I)
      (O := concreteO (l := l) I) (Oa := Oa) (C3 := C3))

end LeanFormal.IUT.XiFPaper.S991S983LinkInputsActual

end
