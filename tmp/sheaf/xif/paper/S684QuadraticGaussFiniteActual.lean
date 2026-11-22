import Mathlib.Analysis.SpecialFunctions.Complex.CircleAddChar
import Mathlib.NumberTheory.LegendreSymbol.AddCharacter

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S684QuadraticGaussFiniteActual

variable {N : Nat} [NeZero N]

noncomputable def quadraticGaussSum (psi : AddChar (ZMod N) ℂ) (a : ZMod N) : ℂ :=
  Finset.univ.sum (fun j : ZMod N => psi (a * j ^ 2))

theorem quadraticGaussSum_zero (psi : AddChar (ZMod N) ℂ) :
    quadraticGaussSum psi 0 = (N : ℂ) := by
  unfold quadraticGaussSum
  simp

theorem quadraticGaussSum_neg_of_even (psi : AddChar (ZMod N) ℂ)
    (h : forall a j : ZMod N, psi (-(a * j ^ 2)) = psi (a * j ^ 2))
    (a : ZMod N) :
    quadraticGaussSum psi (-a) = quadraticGaussSum psi a := by
  unfold quadraticGaussSum
  apply Fintype.sum_bijective (fun j : ZMod N => -j)
  · exact neg_bijective
  · intro j
    have h1 : -a * j ^ 2 = -(a * j ^ 2) := by ring
    have h2 : a * (-j) ^ 2 = a * j ^ 2 := by ring
    rw [h1, h2]
    exact h a j

end LeanFormal.IUT.XiFPaper.S684QuadraticGaussFiniteActual
end