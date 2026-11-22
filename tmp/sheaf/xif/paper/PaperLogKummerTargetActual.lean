import tmp.sheaf.xif.paper.PaperQPilotObjectConcreteActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows

/-!
# Actual paper log-Kummer representation target for the concrete q-pilot object

IUT III, Theorem 3.11, (ii), and Remark 3.10.2: the log-Kummer correspondence
supplies the source-level vertical Kummer arrow between the q-pilot strip and
the vertically coric strip.  The reduced source target is the actual
SourceKummerArrow record: one F-prime-strip equivalence representative plus the
Definition 4.9(i) x-mu Kummer layer.

This file constructs, for the concrete q-pilot object of
PaperQPilotObjectConcreteActual:

* PaperLogKummerTarget: the actual paper-facing target record with the concrete
  object's logKummer, its stripIso and layer, and the definitional equalities;
* paperLogKummerTarget: the actual inhabitant from concreteKummerArrow;
* paperQPilotObjectConcrete_logKummer_eq_target: actual equality between the
  concrete PaperQPilotObject.logKummer and the target object's logKummer;
* projections for stripIso and layer.

No empty type, no True/PUnit, no toy.  No inequality.  WRITE-ONLY; no local
compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.Theorem311Source.PaperLogKummerTargetActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual

universe ua upi umon ui

variable {l : PrimeGeFive}

/-- The actual paper-facing log-Kummer representation target for the concrete
q-pilot object: the concrete q-pilot strip, its actual Kummer arrow, and the
actual stripIso/layer components of that arrow. -/
structure PaperLogKummerTarget (l : PrimeGeFive) where
  objectLogKummer :
    SourceKummerArrow (ConcreteKummerGroup (l := l))
      (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l))
  representationStripIso :
    FPrimeStripEquiv (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l))
  representationLayer :
    SourceTimesMuKummerLayer (ConcreteKummerGroup (l := l))
      (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l))
  stripIso_eq : representationStripIso = objectLogKummer.stripIso
  layer_eq : representationLayer = objectLogKummer.layer

/-- The actual target constructed from the concrete self Kummer arrow. -/
noncomputable def paperLogKummerTarget (l : PrimeGeFive) : PaperLogKummerTarget l where
  objectLogKummer := concreteKummerArrow (l := l)
  representationStripIso := (concreteKummerArrow (l := l)).stripIso
  representationLayer := (concreteKummerArrow (l := l)).layer
  stripIso_eq := rfl
  layer_eq := rfl

/-- The target's log-Kummer arrow is the actual concrete Kummer arrow. -/
theorem paperLogKummerTarget_objectLogKummer :
    (paperLogKummerTarget l).objectLogKummer = concreteKummerArrow (l := l) := rfl

/-- The concrete paper q-pilot object's logKummer is exactly the target arrow. -/
theorem paperQPilotObjectConcrete_logKummer_eq_target
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :
    (paperQPilotObjectConcrete (l := l) I).logKummer =
      (paperLogKummerTarget l).objectLogKummer := rfl

/-- The target's strip representative is the concrete arrow's stripIso. -/
theorem paperLogKummerTarget_stripIso :
    (paperLogKummerTarget l).representationStripIso =
      (concreteKummerArrow (l := l)).stripIso := rfl

/-- The target's x-mu layer is the concrete arrow's layer. -/
theorem paperLogKummerTarget_layer :
    (paperLogKummerTarget l).representationLayer =
      (concreteKummerArrow (l := l)).layer := rfl

/-- The target's strip representative is the F-prime-strip equivalence
component of the actual object logKummer. -/
theorem paperLogKummerTarget_stripIso_eq :
    (paperLogKummerTarget l).representationStripIso =
      (paperLogKummerTarget l).objectLogKummer.stripIso := rfl

/-- The target's x-mu layer is the layer component of the actual object
logKummer. -/
theorem paperLogKummerTarget_layer_eq :
    (paperLogKummerTarget l).representationLayer =
      (paperLogKummerTarget l).objectLogKummer.layer := rfl

end LeanFormal.IUT.Theorem311Source.PaperLogKummerTargetActual
