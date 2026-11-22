import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntInjActual

theorem halfInt_injective : Function.Injective halfInt := by
  intro n m h
  unfold halfInt at h
  have h' : (n : Rat) = (m : Rat) := by linarith
  exact_mod_cast h'

theorem halfInt_eq_iff {n m : Int} :
    halfInt n = halfInt m ↔ n = m := by
  constructor
  · intro h; exact halfInt_injective h
  · intro h; rw [h]

#check halfInt_injective
#check halfInt_eq_iff

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntInjActual
