/- R0.2 crosswalk hypothesis (Lead clarification): explicit, no double e.
   cPFullFiber_b = ([Fmod_b:Q_p]/[Fmod:Q]) * cP_local_b, where cP_local = v_P/e_abs.
   This file provides the Prop + projection; instantiation by caller (R0.1/R0.2). -/
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR0CrosswalkActual

/-- R0.2 crosswalk: full-fiber coefficient = local degree ratio * local cP (v_P/e_abs). -/
def CPlocalCrosswalk (cPFullFiber cP_local localDeg dmod : Real) : Prop :=
  cPFullFiber = (localDeg / dmod) * cP_local

/-- Projection of the crosswalk (definitional). -/
theorem CPlocalCrosswalk.eq {cPFullFiber cP_local localDeg dmod : Real}
    (h : CPlocalCrosswalk cPFullFiber cP_local localDeg dmod) :
    cPFullFiber = (localDeg / dmod) * cP_local := h

/-- Cross-multiplied form (no division). -/
theorem CPlocalCrosswalk.mul {cPFullFiber cP_local localDeg dmod : Real}
    (h : CPlocalCrosswalk cPFullFiber cP_local localDeg dmod) (hd : dmod ≠ 0) :
    cPFullFiber * dmod = localDeg * cP_local := by
  rw [CPlocalCrosswalk.eq h]
  field_simp

#print axioms CPlocalCrosswalk.eq
#print axioms CPlocalCrosswalk.mul

end LeanFormal.IUT.XiFPaper.Mzk1ULR0CrosswalkActual
