import LeanFormal.IUT.IUTIV.Estimates.DifferentTowerEstimate
import LeanFormal.IUT.IUTIV.Estimates.DifferentDegreeUpperBound
import tmp.sheaf.xif.paper.GenEll04bProp17ChainActual
import tmp.sheaf.xif.paper.S3136BDClassChainToolActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3136BDClassChainToolActual
open LeanFormal.IUT.XiFPaper.GenEll04Prop17Actual
open LeanFormal.IUT.XiFPaper.GenEll04bChainActual

namespace LeanFormal.IUT.XiFPaper.GenEll04cDifferentInputsActual

/-- **Exact paper-input registration for Prop 1.7's different theory**: the elementary
different/conductor inequalities of Prop 1.7(i) are supplied by the paper's different
theory (corpus 565-602); the IUT-side reusable anchors are the tree's
DifferentTowerEstimate.iutIVProp13i_normalizedDifferent_ge and
DifferentDegreeUpperBound.  This Prop records the exact remaining input to the
assembly `prop17_logDiff_inequality_of_inputs` (no discharge claim). -/
def Prop17DifferentTheoryInput (X : Type) (UQ : Set X)
    (logCondE logCondD logDiffY logDiffZ : X → Real) : Prop :=
  IsBDLe (fun x => logDiffY x - logDiffZ x)
      (fun x => logCondE x - logCondD x) UQ ∧
    ∃ (e : Nat), 0 < e

/-- The registered input together with the (1-1/e) bound yields the Prop 1.7(i)
assembly (via the citable prop17_logDiff_inequality_of_inputs). -/
theorem prop17_of_differentTheoryInput {X : Type} {UQ : Set X}
    {logCondE logCondD logDiffY logDiffZ : X → Real}
    (h : Prop17DifferentTheoryInput X UQ logCondE logCondD logDiffY logDiffZ)
    (e : Nat)
    (h2 : IsBDLe (fun y => ((1 : Real) - 1 / (e : Real)) * logCondE y)
      (fun y => logDiffY y - logDiffZ y) UQ) :
    Prop17LogDiffInequality UQ logCondE logCondD logDiffY logDiffZ e :=
  prop17_logDiff_inequality_of_inputs h.1 h2

def s3135Prop17InputCitations : List (String × String) :=
  [ ("Prop 1.7 different theory", "corpus 565-602: separated wildly/tamely ramified; wild claim p^n O_L in different via Kummer theory; bounded over Sigma"),
    ("tree anchors", "IUTIV/Estimates/DifferentTowerEstimate.lean iutIVProp13i_normalizedDifferent_ge; DifferentDegreeUpperBound.lean") ]

theorem s3135Prop17InputCitations_length : s3135Prop17InputCitations.length = 2 := rfl

#check Prop17DifferentTheoryInput
#check prop17_of_differentTheoryInput
end LeanFormal.IUT.XiFPaper.GenEll04cDifferentInputsActual
end