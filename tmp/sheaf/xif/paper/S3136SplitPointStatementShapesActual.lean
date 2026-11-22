import Mathlib.Data.Real.Basic
import Mathlib.Tactic

/-! # Stage-4 host: split-point statement shapes ((R1)-(R3), Theorem 1.10 Step (ii))

TEXT: papers/motizuki_corpus/text/Inter-universal Teichmuller Theory IV.txt,
Theorem 1.10, Step (ii) (R1)-(R3) p.1523-1545: bounds for log(e_v) depending on the
divisibility of v by 2,3,5,l.  These are the prime-splitting/rounding estimates =
the SPLIT POINT BOUND side of the (c) estimate; CLASS B formalization target (proved
in the paper).  The (R4) exceptional-term estimate is already formalized in
IUTIV/Estimates/StepVProcessionAverage.lean:100 exceptionalSum_le_r4 (prior art,
reused in S3136WeightedAveragePriorArtReuseActual).

CONSUMER: mainline's Theorem 1.10 statement skeleton (class B target slots).
Definitional shapes only; no estimate is claimed.

LABEL: statement shapes (class A definitions of class B targets). Registry frozen;
new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136SplitPointStatementShapesActual

/-- (R1) shape: v divides l. -/
noncomputable def LGPR1Shape (ev emod el : ℝ) : Prop :=
  Real.log ev ≤ Real.log ((2 : ℝ) ^ 11 * (3 : ℝ) ^ 3 * 5 * emod * el ^ 4)

/-- (R2) shape: v divides 2*3*5 or lies in the support of q. -/
noncomputable def LGPR2Shape (ev emod el : ℝ) : Prop :=
  Real.log ev ≤ Real.log ((2 : ℝ) ^ 11 * (3 : ℝ) ^ 3 * 5 * emod * el)

/-- (R3) shape: v divides none of 2,3,5,l. -/
noncomputable def LGPR3Shape (ev emod : ℝ) : Prop :=
  Real.log ev ≤ Real.log ((2 : ℝ) ^ 11 * (3 : ℝ) ^ 3 * 5 * emod)

/-- The statement labels (data rows): shape -> citation. -/
def lgpSplitPointShapeCitations : List (String × String) :=
  [ ("LGPR1Shape", "IUT IV Thm 1.10 Step (ii), (R1) p.1523-1524 (v | l)"),
    ("LGPR2Shape", "IUT IV Thm 1.10 Step (ii), (R2) p.1524-1527 (v | 2*3*5 or v in Supp(q_...))"),
    ("LGPR3Shape", "IUT IV Thm 1.10 Step (ii), (R3) p.1527-1545 (v not dividing 2*3*5*l)"),
    ("(R4)", "IUTIV/Estimates/StepVProcessionAverage.lean:100 exceptionalSum_le_r4 (prior art, FORMALIZED)") ]

theorem lgpSplitPointShapeCitations_length : lgpSplitPointShapeCitations.length = 4 := rfl

#check LGPR1Shape
#check LGPR2Shape
#check LGPR3Shape
#check lgpSplitPointShapeCitations_length

end LeanFormal.IUT.XiFPaper.S3136SplitPointStatementShapesActual
end