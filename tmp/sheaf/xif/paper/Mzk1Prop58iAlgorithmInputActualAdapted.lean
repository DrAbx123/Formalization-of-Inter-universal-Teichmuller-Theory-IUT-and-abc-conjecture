import tmp.sheaf.xif.paper.Mzk1Prop58iConcreteActual
import tmp.sheaf.xif.paper.Mzk1Prop58iTargetActual

/-!
# Mzk1Prop58iAlgorithmInputActualAdapted (adapted copy, A475 reuse) — Prop 5.8(i) group-theoretic algorithm as an explicit
named hypothesis, with derivation of the reconstruction target

STEP 0 prior-art: Mzk1Prop58iConcreteActual (concrete invariants), Mzk1Prop58iTargetActual
(prop58iReconstructionTarget and its bridge equivalence) -> REUSE.
This file packages the paper's group-theoretic reconstruction algorithm as a named input
(algorithm plus an implication to the model target) and derives the target conditionally; the
algorithm itself is not constructed.
No axiom/sorry; registry frozen 14041.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Prop58iAlgorithmInputActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.SourceLogShellDatum
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iConcreteActual
open LeanFormal.IUT.XiFPaper.Mzk1Prop58iTargetActual

universe u

/-- The Prop 5.8(i) group-theoretic algorithm as an explicit named input: a statement
together with its implication to the reconstruction target and the named proof. -/
structure Prop58iAlgorithmInput (D : SourceLogShellDatum.{u}) where
  /-- the paper's group-theoretic algorithm statement. -/
  algorithm : Prop
  /-- the algorithm implies the reconstruction target (paper implication). -/
  algorithm_implies_target : algorithm → prop58iReconstructionTarget D
  /-- the named algorithm/proof. -/
  named : algorithm

/-- Conditional derivation of the Prop 5.8(i) reconstruction target from the named input. -/
theorem prop58iTarget_of_algorithmInput {D : SourceLogShellDatum.{u}}
    (I : Prop58iAlgorithmInput D) : prop58iReconstructionTarget D :=
  I.algorithm_implies_target I.named

/-- Rows: (item, formal asset, status). -/
def prop58iAlgorithmRows : List (String × String × String) :=
  [ ("concrete invariants", "Prop58iConcreteInvariants (P58I)", "PROVED"),
    ("reconstruction target", "prop58iReconstructionTarget; calibration_reconstructionTarget", "PROVED (model/calibration)"),
    ("group-theoretic algorithm", "Prop58iAlgorithmInput.algorithm (explicit named hypothesis)", "NAMED"),
    ("algorithm => target", "prop58iTarget_of_algorithmInput", "PROVED (conditional)") ]

/-- The algorithm row record has four rows. -/
theorem prop58iAlgorithmRows_length : prop58iAlgorithmRows.length = 4 := rfl

#check Prop58iAlgorithmInput
#check prop58iTarget_of_algorithmInput
#check prop58iAlgorithmRows_length

end LeanFormal.IUT.XiFPaper.Mzk1Prop58iAlgorithmInputActualAdapted
end
