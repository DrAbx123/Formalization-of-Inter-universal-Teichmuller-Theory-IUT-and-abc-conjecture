import tmp.sheaf.xif.paper.Mzk1P3DictDLogDiscBoundActual
import Mathlib.Tactic

/-! # GAP: actual minimal-discriminant source object for D_arith -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscSourceActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Exact missing source: an actual minimal discriminant whose log-absolute
value is the prime-conductor log disc e*log p.  PrimeConductorCurve only stores
e=ord_p(Delta_min), not Delta_min itself. -/
structure PrimeConductorDeltaMinSource (C : PrimeConductorCurve) where
  deltaMin : Int
  deltaMin_ne_zero : deltaMin ≠ 0
  log_abs_eq : Real.log |(deltaMin : Real)| = primeConductorLogDisc C

/-- The named D-side source gap. -/
def PrimeConductorDeltaMinGap (C : PrimeConductorCurve) : Prop :=
  Nonempty (PrimeConductorDeltaMinSource C)

/-- If the source exists, its log is bounded by 5 log p via Mestre-Oesterle. -/
theorem deltaMin_log_le_five_logp
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (S : PrimeConductorDeltaMinSource C) :
    Real.log |(S.deltaMin : Real)| <= 5 * Real.log (C.p : Real) := by
  rw [S.log_abs_eq]
  exact primeConductorLogDisc_le_five_logp hMO C

#check PrimeConductorDeltaMinSource
#check PrimeConductorDeltaMinGap
#check deltaMin_log_le_five_logp
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscSourceActual
end
