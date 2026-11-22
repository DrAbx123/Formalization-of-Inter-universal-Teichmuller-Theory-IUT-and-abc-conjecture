import tmp.sheaf.xif.paper.Mzk1P3DictDOrdInterfaceActual
import Mathlib.Tactic

/-! # GREEN: PrimeConductorOrdSource constructor and field conversions -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictDOrdConvertActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictDOrdInterfaceActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual

/-- Canonical ord source built from the curve fields. -/
def PrimeConductorOrdSource.ofCurve (C : PrimeConductorCurve) :
    PrimeConductorOrdSource C where
  p := C.p
  e := C.e
  ordValue := (C.e : Int)
  p_eq := rfl
  e_eq := rfl
  e_eq_ord := rfl

/-- The canonical source has p=C.p. -/
theorem ordSource_ofCurve_p (C : PrimeConductorCurve) :
    (PrimeConductorOrdSource.ofCurve C).p = C.p := rfl

/-- The canonical source has e=C.e. -/
theorem ordSource_ofCurve_e (C : PrimeConductorCurve) :
    (PrimeConductorOrdSource.ofCurve C).e = C.e := rfl

/-- The canonical source ord value equals C.e. -/
theorem ordSource_ofCurve_ord (C : PrimeConductorCurve) :
    (PrimeConductorOrdSource.ofCurve C).ordValue = (C.e : Int) := rfl

/-- Any ord source can be transported to the canonical one. -/
theorem ordSource_eq_ofCurve (C : PrimeConductorCurve) (S : PrimeConductorOrdSource C) :
    S.ordValue = (PrimeConductorOrdSource.ofCurve C).ordValue := by
  rw [ordSource_ofCurve_ord, S.e_eq_ord]

#check PrimeConductorOrdSource.ofCurve
#check ordSource_ofCurve_p
#check ordSource_ofCurve_e
#check ordSource_ofCurve_ord
#check ordSource_eq_ofCurve
end LeanFormal.IUT.XiFPaper.Mzk1P3DictDOrdConvertActual
end
