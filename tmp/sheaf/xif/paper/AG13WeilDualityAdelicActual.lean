import tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

/-!
# AG13: Weil duality (adelic) consumer (A-class ported COMPLETE proof)

Consumes the green ported module
tmp.external.ported.flt_core.P2M.Sol.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists
(EXIT=0; Apache-2.0 attribution retained): its theorem
P2MW....solution has a COMPLETE ported proof and is conditional exactly on the paper
RR rows FunctionFieldRiemannRoch + StichtenothGenusExists, concluding
WeilDualityAdelic K F (the adelic Serre-duality form used by the RR reduction).
This file only re-exposes that complete proof in the AG layer (AG13 Serde/RR bridge);
no re-proof, no axiom.

NOTE: imports only the flt_core ported universe (no adapted promotion in the same
file) to avoid the documented duplicate-namespace clash.

**Component, not paper object.**  Registry frozen 14041; no registry edits.
No sorry/axiom/True/PUnit/toy carrier.
-/

namespace LeanFormal.IUT.XiFPaper.AG13WeilDualityAdelicActual

open AlgebraicCurve

universe u

/-- A-class Weil-duality-adlic consumer (complete ported proof; conditional exactly
on the paper RR rows). -/
theorem ag13_weilDualityAdelic {K F : Type u} [Field K] [Field F] [Algebra K F]
    (hRR : AlgebraicCurve.FunctionFieldRiemannRoch K F)
    (hSG : AlgebraicCurve.StichtenothGenusExists K F) :
    AlgebraicCurve.WeilDualityAdelic K F :=
  P2MW.S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.solution
    hRR hSG

/-- A-class reuse record. -/
def ag13Reuse : List (String × String × String) :=
  [ ("WeilDualityAdelic (adelic Serre duality form)", "tmp/external/ported/flt_core P2M/Sol/S_AlgebraicCurve_weilDualityAdelic_of_functionFieldRiemannRoch_of_stichtenothGenusExists.lean (EXIT=0; COMPLETE ported proof)", "A (reused complete proof)"),
    ("paper rows consumed", "FunctionFieldRiemannRoch + StichtenothGenusExists", "class-B paper rows exactly as source"),
    ("Serde layer consumers", "AG11SerrePairingConsumerActual; AG06bRRInterfaceActual (RR reductions)", "A (reuse)") ]

end LeanFormal.IUT.XiFPaper.AG13WeilDualityAdelicActual

end
