import tmp.sheaf.xif.paper.S3132IVGenEllShadowAdapterActual
import tmp.sheaf.xif.paper.GenEll01BasicActual
import tmp.sheaf.xif.paper.GenEll05Theorem21Actual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# GenEll10: H6 closure — GenEll transfer field closed (interface level)

Route residual H6 is the GenEll transfer: the IV §2 inequality
(1+eps)(log-diff + log-cond) - height >= L on the compact subset.  The
source-adapted GenEll shadow record (S3132IVGenEllShadowAdapterActual, adapted
from vendor IUTStage1IUTIVAlgebra:9887-9928) keeps exactly this as its explicit
genEll_transfer field; H6 therefore closes at the INTERFACE level:
AdaptedIVGenEllShadow.exists_lowerBound supplies the lower bound, and the
BD-class form consumed by GenEll Theorem 2.1 follows.

HONESTY: this closes H6 as a structured interface (the field is an input of the
shadow record), NOT by proving the GenEll statement itself; the deep GenEll
inputs remain the exact named paper-inputs of GenEll09/GenEll05.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual

universe u

open LeanFormal.IUT.XiFPaper.S3132IVGenEllShadowAdapterActual
open LeanFormal.IUT.XiFPaper.GenEll01BasicActual
open LeanFormal.IUT.XiFPaper.GenEll05Theorem21Actual

/-- **H6 closed (interface level):** the GenEll transfer gives the explicit
discrepancy lower bound. -/
theorem h6_genEll_transfer
    {Point : Type u} (data : AdaptedIVGenEllShadow Point) :
    ∃ lowerBound : ℝ, ∀ x : Point,
      lowerBound ≤ (1 + data.epsilon) * (data.logDiff x + data.logCond x) -
        data.height x :=
  data.exists_lowerBound

/-- **H6 in BD-class form:** the GenEll transfer is exactly the BDClassOn shape
of GenEll Def 1.2(ii) on all points. -/
theorem h6_genEll_BDClassOn
    {Point : Type u} (data : AdaptedIVGenEllShadow Point) :
    BDClassOn (fun _ => True) data.height data.logDiff data.logCond data.epsilon := by
  obtain ⟨L, hL⟩ := data.exists_lowerBound
  refine ⟨-L, ?_⟩
  intro x _
  have h := hL x
  unfold AdaptedIVGenEllShadow.discrepancy at h
  linarith

/-- H6 closed for the compactly-bounded case of GenEll Theorem 2.1 (K = all points
here; the compact-subset predicate is the source record's own field). -/
theorem h6_genEll_caseII
    {Point : Type u} (data : AdaptedIVGenEllShadow Point) :
    CaseII (fun _ : Point => True) data.height data.logDiff data.logCond
      data.epsilon :=
  h6_genEll_BDClassOn data

/-- The H6 closure status record: (route slot, evidence, exact scope). -/
def h6ClosureRecord : List (String × String × String) :=
  [ ("H6", "genEll_transfer (interface level)", "S3132IVGenEllShadowAdapterActual.genEll_transfer:43"),
    ("H6.bdclass-form", "h6_genEll_BDClassOn (this file)", "BDClassOn GenEll Def 1.2(ii)"),
    ("H6.caseII", "h6_genEll_caseII (this file)", "GenEll Thm 2.1 (ii) compactly-bounded case"),
    ("H6.deep-inputs", "PAPER-INPUT (class B)", "GenEll Thm 2.1 (ii)=>(i) + [Mzk1] + Thm 3.8 + Cor 4.3/4.4 stay named in GenEll09") ]

end LeanFormal.IUT.XiFPaper.GenEll10H6ClosureActual

end
