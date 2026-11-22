import LeanFormal.IUT.Foundations.Geometry.ConcreteSplitCurveFivePlace
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import Mathlib.Tactic

noncomputable section
open WeierstrassCurve

namespace Probe

local instance : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

example : ‖(61/64 : ℚ_[5])‖ = 1 := by norm_num
example : ‖(-125/64 : ℚ_[5])‖ = 1 := by norm_num
example : ‖(27721/256 : ℚ_[5])‖ = 1 := by norm_num
example : ‖(558140625/1048576 : ℚ_[5])‖ < 1 := by norm_num

def z : ℤ_[5] := ⟨(61/64 : ℚ_[5]), by norm_num⟩
example : ((z : ℚ_[5])) = 61/64 := rfl

#check PadicInt.residueField
#check PadicInt.toZMod
#check PadicInt.toZMod_eq_residueField_comp_residue
#check IsLocalRing.residue
#check IsLocalRing.ResidueField.map
#check Polynomial.Splits.map
#check Polynomial.Splits.X_sub_C

end Probe
