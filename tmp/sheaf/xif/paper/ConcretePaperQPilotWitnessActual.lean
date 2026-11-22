import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import tmp.sheaf.xif.paper.PaperQPilotIdentificationsActual

-- Actual concrete q-pilot witness
--
-- Packages the actual paperQPilotObjectConcrete with its four actual
-- identification evidences, plus the actual strip target and actual
-- log-Kummer target as referenced actual objects (with equality to the
-- object's fields). No True/empty type/PUnit/toy. WRITE-ONLY.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.ConcretePaperQPilotWitnessActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperQPilotIdentificationsActual

variable {l : PrimeGeFive}

abbrev ConcreteObjectType
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) : Type _ :=
  PaperQPilotObject (l := l) (V := FinitePrimePlace 2 7)
    (Label := ConcreteFiniteTheorem311.finiteLabel l)
    (Choice := ConcreteFiniteTheorem311.ProcessionChoice l)
    I (ConcreteKummerGroup (l := l)) (concreteQPilotStrip (l := l))

structure ConcretePaperQPilotWitness
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) where
  /-- The actual concrete q-pilot object. -/
  object : ConcreteObjectType (l := l) I
  /-- The actual strip target: the source q-pilot strip of the boundary. -/
  stripTarget : FPrimeStrip (FinitePrimePlace 2 7)
  stripTarget_eq : stripTarget = object.strip
  /-- The actual log-Kummer target: the object's concrete Kummer arrow. -/
  logKummerTarget :
    SourceKummerArrow (ConcreteKummerGroup (l := l))
      (concreteQPilotStrip (l := l)) object.strip
  logKummerTarget_eq : logKummerTarget = object.logKummer
  /-- The actual q-pilot scalar target. -/
  qPilotLogTarget : Real
  qPilotLogTarget_eq : qPilotLogTarget = object.qPilotLogVolume
  /-- Actual evidence for the four paper_*_identification fields. -/
  identifications : PaperQPilotIdentificationsActual (l := l) I

noncomputable def concretePaperQPilotWitness
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    ConcretePaperQPilotWitness (l := l) I where
  object := paperQPilotObjectConcrete (l := l) I
  stripTarget := (paperQPilotObjectConcrete (l := l) I).strip
  stripTarget_eq := rfl
  logKummerTarget := (paperQPilotObjectConcrete (l := l) I).logKummer
  logKummerTarget_eq := rfl
  qPilotLogTarget := (paperQPilotObjectConcrete (l := l) I).qPilotLogVolume
  qPilotLogTarget_eq := rfl
  identifications := paperQPilotIdentificationsActual (l := l) I

theorem concretePaperQPilotWitness_strip
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (concretePaperQPilotWitness (l := l) I).stripTarget =
      (concretePaperQPilotWitness (l := l) I).object.strip :=
  (concretePaperQPilotWitness (l := l) I).stripTarget_eq

theorem concretePaperQPilotWitness_logKummer
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (concretePaperQPilotWitness (l := l) I).logKummerTarget =
      (concretePaperQPilotWitness (l := l) I).object.logKummer :=
  (concretePaperQPilotWitness (l := l) I).logKummerTarget_eq

theorem concretePaperQPilotWitness_qPilotLog
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (concretePaperQPilotWitness (l := l) I).qPilotLogTarget =
      (concretePaperQPilotWitness (l := l) I).object.qPilotLogVolume :=
  (concretePaperQPilotWitness (l := l) I).qPilotLogTarget_eq

#check ConcretePaperQPilotWitness
#check concretePaperQPilotWitness
#check concretePaperQPilotWitness_strip
#check concretePaperQPilotWitness_logKummer
#check concretePaperQPilotWitness_qPilotLog

end LeanFormal.IUT.XiFPaper.ConcretePaperQPilotWitnessActual

end