import tmp.sheaf.xif.paper.Mzk1P3DictDLogDiscSourceActual
import Mathlib.Tactic

/-! # GAP: refined D-side source with nonnegative absolute discriminant -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDSourceRefinedActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscBoundActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscSourceActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Refined source: actual minimal discriminant as an Int, its absolute real
value, and the exact log identification with e*log p. -/
structure PrimeConductorDeltaMinSourceRefined (C : PrimeConductorCurve) where
  deltaMin : Int
  deltaMin_ne_zero : deltaMin ≠ 0
  absValue : Real
  absValue_nonneg : 0 <= absValue
  absValue_eq : absValue = |(deltaMin : Real)|
  log_abs_eq : Real.log absValue = primeConductorLogDisc C

/-- The refined source gives the earlier source (drop absValue). -/
def PrimeConductorDeltaMinSourceRefined.toSource
    {C : PrimeConductorCurve} (S : PrimeConductorDeltaMinSourceRefined C) :
    PrimeConductorDeltaMinSource C where
  deltaMin := S.deltaMin
  deltaMin_ne_zero := S.deltaMin_ne_zero
  log_abs_eq := by
    rw [← S.absValue_eq]
    exact S.log_abs_eq

/-- Refined source log bound. -/
theorem refined_deltaMin_log_le_five_logp
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (S : PrimeConductorDeltaMinSourceRefined C) :
    Real.log S.absValue <= 5 * Real.log (C.p : Real) := by
  rw [S.log_abs_eq]
  exact primeConductorLogDisc_le_five_logp hMO C

#check PrimeConductorDeltaMinSourceRefined
#check PrimeConductorDeltaMinSourceRefined.toSource
#check refined_deltaMin_log_le_five_logp
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDSourceRefinedActual
end
