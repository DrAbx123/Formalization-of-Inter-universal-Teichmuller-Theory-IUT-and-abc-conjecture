import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-! # GAP: ord/e interface for PrimeConductorCurve -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDOrdInterfaceActual

open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Explicit ord/e interface: p,e and the actual delta-min ordinal value.
The curve carrier does not store Delta_min; ordValue is the named external
input that must equal C.e. -/
structure PrimeConductorOrdSource (C : PrimeConductorCurve) where
  p : Nat
  e : Nat
  ordValue : Int
  p_eq : p = C.p
  e_eq : e = C.e
  e_eq_ord : (ordValue : Int) = (C.e : Int)

/-- e is nonnegative. -/
theorem primeConductor_e_nonneg (C : PrimeConductorCurve) : 0 <= C.e :=
  Nat.zero_le C.e

/-- Mestre-Oesterle e<=5. -/
theorem primeConductor_e_le_five
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve) : C.e <= 5 :=
  (hMO C).1

/-- From an ord source, the ord value equals C.e. -/
theorem ordSource_e_eq (C : PrimeConductorCurve) (S : PrimeConductorOrdSource C) :
    (S.ordValue : Int) = (C.e : Int) :=
  S.e_eq_ord

#check PrimeConductorOrdSource
#check primeConductor_e_nonneg
#check primeConductor_e_le_five
#check ordSource_e_eq
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDOrdInterfaceActual
end
