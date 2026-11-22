import tmp.sheaf.xif.paper.Mzk1P3DictDLogDiscActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # CONDITIONAL: Mestre-Oesterle bounds the log discriminant by 5 log p -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscBoundActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Mestre-Oesterle e<=5 gives log disc <= 5 log p. -/
theorem primeConductorLogDisc_le_five_logp
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve) :
    primeConductorLogDisc C <= 5 * Real.log (C.p : Real) := by
  have he5 : (C.e : Real) <= 5 := by exact_mod_cast (hMO C).1
  have hlogp : 0 <= Real.log (C.p : Real) := by
    have hp1 : (1 : Real) <= (C.p : Real) := by exact_mod_cast C.hp.one_lt.le
    exact Real.log_nonneg hp1
  unfold primeConductorLogDisc
  nlinarith

#check primeConductorLogDisc_le_five_logp
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscBoundActual
end
