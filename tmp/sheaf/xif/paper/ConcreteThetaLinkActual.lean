import tmp.sheaf.xif.paper.PaperLogKummerTargetActual
import tmp.sheaf.xif.paper.ConcreteC3DonorActual
import tmp.sheaf.xif.paper.IPLAPTDataActual

/-!
# Concrete Theta-link / Kummer-evaluation actual evidence

IUT III, Theorem 3.11, (ii), (iii) and Remark 3.10.2: the Theta-link is
accompanied by the log-Kummer vertical Kummer arrow and the Kummer-evaluation
square.  For the concrete q-pilot strip this file constructs the actual
evidence available from the tree:

* the concrete q-pilot strip and its actual SourceKummerArrow
  (concreteKummerArrow);
* the actual paper log-Kummer target PaperLogKummerTarget;
* the actual KummerEvaluationActual self square of IPLAPTDataActual,
  including its two-path equality;
* the actual concrete theta packet ConcreteC3DonorActual.concreteThetaPacket.

The record ConcreteThetaLinkKummerEvidence collects these actual objects with
definitional equalities.  It does NOT assert a link_identification or
link_implies_inclusion; those remain the separate ConcreteThetaLink fields and
are not faked here.

No empty type, no True/PUnit, no toy.  No inequality.  WRITE-ONLY; no local
compile; queued.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.ConcreteThetaLinkActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.PaperQPilotConcreteActual
open LeanFormal.IUT.Theorem311Source.PaperLogKummerTargetActual
open LeanFormal.IUT.Theorem311Source.IPLAPTDataActual
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual

universe ua upi umon ui uC3 uD3

variable {l : PrimeGeFive}

/-- Actual concrete Theta-link / Kummer-evaluation evidence for the concrete
q-pilot strip. -/
structure ConcreteThetaLinkKummerEvidence
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) where
  strip : FPrimeStrip (FinitePrimePlace 2 7)
  thetaPacket : FiniteThetaPacket l
  kummerArrow : SourceKummerArrow (ConcreteKummerGroup (l := l))
    (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l))
  logKummerTarget : PaperLogKummerTarget l
  evaluation : KummerEvaluationActual (G := ConcreteKummerGroup (l := l))
    (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l))
    (concreteQPilotStrip (l := l)) (concreteQPilotStrip (l := l))
  strip_eq : strip = concreteQPilotStrip (l := l)
  thetaPacket_eq : thetaPacket = concreteThetaPacket I
  kummerArrow_eq : kummerArrow = concreteKummerArrow (l := l)
  logKummerTarget_eq : logKummerTarget = paperLogKummerTarget l
  evaluation_eq :
    evaluation = selfKummerEvaluationActual (concreteQPilotStrip (l := l))

/-- The actual evidence built from the concrete q-pilot strip, its Kummer arrow,
the paper log-Kummer target, the actual theta packet, and the actual
Kummer-evaluation self square. -/
noncomputable def concreteThetaLinkKummerEvidence
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    ConcreteThetaLinkKummerEvidence I where
  strip := concreteQPilotStrip (l := l)
  thetaPacket := concreteThetaPacket I
  kummerArrow := concreteKummerArrow (l := l)
  logKummerTarget := paperLogKummerTarget l
  evaluation := selfKummerEvaluationActual (concreteQPilotStrip (l := l))
  strip_eq := rfl
  thetaPacket_eq := rfl
  kummerArrow_eq := rfl
  logKummerTarget_eq := rfl
  evaluation_eq := rfl

/-- The evidence's strip is the concrete q-pilot strip. -/
theorem concreteThetaLinkKummerEvidence_strip
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaLinkKummerEvidence I).strip = concreteQPilotStrip (l := l) := rfl

/-- The evidence's theta packet is the actual concrete theta packet. -/
theorem concreteThetaLinkKummerEvidence_thetaPacket
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaLinkKummerEvidence I).thetaPacket = concreteThetaPacket I := rfl

/-- The evidence's Kummer arrow is the concrete actual arrow. -/
theorem concreteThetaLinkKummerEvidence_kummerArrow
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaLinkKummerEvidence I).kummerArrow = concreteKummerArrow (l := l) := rfl

/-- The evidence's log-Kummer target is the actual paper target. -/
theorem concreteThetaLinkKummerEvidence_logKummerTarget
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaLinkKummerEvidence I).logKummerTarget =
      paperLogKummerTarget l := rfl

/-- The evidence's Kummer-evaluation square is the actual self square. -/
theorem concreteThetaLinkKummerEvidence_evaluation
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaLinkKummerEvidence I).evaluation =
      selfKummerEvaluationActual (concreteQPilotStrip (l := l)) := rfl

/-- The actual Kummer-evaluation two-path equality carried by the evidence. -/
theorem concreteThetaLinkKummerEvidence_twoPath
    (I : OriginalInput.{0, 0, upi, umon, ui} l (FinitePrimePlace 2 7)) :
    (concreteThetaLinkKummerEvidence I).evaluation.square.domainExpression =
      (concreteThetaLinkKummerEvidence I).evaluation.square.codomainExpression :=
  selfKummerEvaluationActual_twoPath (concreteQPilotStrip (l := l))

end LeanFormal.IUT.XiFPaper.ConcreteThetaLinkActual
