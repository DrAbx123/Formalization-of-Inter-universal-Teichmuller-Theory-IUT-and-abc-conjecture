import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # DICT-B D-side actual interface: log disc = e log p -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual

open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- The prime-conductor log discriminant interface. -/
noncomputable def primeConductorLogDisc (C : PrimeConductorCurve) : Real :=
  (C.e : Real) * Real.log (C.p : Real)

theorem primeConductorLogDisc_eq (C : PrimeConductorCurve) :
    primeConductorLogDisc C = (C.e : Real) * Real.log (C.p : Real) := rfl

theorem primeConductorLogDisc_nonneg (C : PrimeConductorCurve) :
    0 <= primeConductorLogDisc C := by
  unfold primeConductorLogDisc
  have hp1 : (1 : Real) <= (C.p : Real) := by exact_mod_cast C.hp.one_lt.le
  exact mul_nonneg (by positivity) (Real.log_nonneg hp1)

theorem primeConductorLogDisc_pos (C : PrimeConductorCurve) (he : 0 < C.e) :
    0 < primeConductorLogDisc C := by
  unfold primeConductorLogDisc
  have hp1 : (1 : Real) < (C.p : Real) := by exact_mod_cast C.hp.one_lt
  exact mul_pos (by exact_mod_cast he) (Real.log_pos hp1)

#check primeConductorLogDisc
#check primeConductorLogDisc_eq
#check primeConductorLogDisc_nonneg
#check primeConductorLogDisc_pos
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDLogDiscActual
end
