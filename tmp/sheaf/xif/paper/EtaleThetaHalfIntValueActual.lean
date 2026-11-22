import Mathlib
import tmp.sheaf.xif.paper.EtaleThetaHalfIntType
import tmp.sheaf.xif.paper.EtaleThetaCoeffPairing

noncomputable section

open LeanFormal.IUT.XiFPaper.EtaleThetaHalfInt
open LeanFormal.IUT.XiFPaper.EtaleThetaCoeffPairing

namespace LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntValueActual

@[simp] theorem halfInt_zero : halfInt 0 = 0 := by
  unfold halfInt
  norm_num

@[simp] theorem halfInt_one : halfInt 1 = (1 / 2 : Rat) := by
  unfold halfInt
  norm_num

@[simp] theorem halfInt_two : halfInt 2 = (1 : Rat) := by
  unfold halfInt
  norm_num

@[simp] theorem halfInt_neg_one : halfInt (-1) = (-1 / 2 : Rat) := by
  unfold halfInt
  norm_num

#check halfInt_zero
#check halfInt_one
#check halfInt_two
#check halfInt_neg_one

end LeanFormal.IUT.XiFPaper.EtaleThetaHalfIntValueActual
