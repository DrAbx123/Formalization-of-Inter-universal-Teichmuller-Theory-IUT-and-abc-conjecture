import tmp.sheaf.xif.paper.S1506ConcreteQNormActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1507ConcreteQNormOrderActual

universe u
variable {l : PrimeGeFive}
variable {I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)}
variable {place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) 5}

/-- Exact norm formula for the concrete q candidate above 5: it is
5^(-exponent).  This is the actual reduction of the norm to the DVR order. -/
theorem S1507ConcreteQNorm_eq_five_zpow
    (h5 : residueNormBase place.val = 5) :
    ‖(concreteQCandidate I place).q‖ =
      (5 : Real) ^ (-(concreteQCandidate I place).exponent) := by
  rw [qNorm_eq_residueNormBase_zpow, h5]

/-- The q-candidate law gives a strictly positive actual order. -/
theorem S1507ConcreteQOrder_pos :
    0 < (concreteQCandidate I place).order :=
  (concreteQCandidate I place).order_pos

/-- Exact norm 1/5 is equivalent to unit DVR order.  The q-candidate law
alone gives only order > 0, so this is the exact residual condition. -/
theorem S1507ConcreteQNorm_eq_inv_five_iff_order_one
    (h5 : residueNormBase place.val = 5) :
    ‖(concreteQCandidate I place).q‖ = ((5 : Real)⁻¹) ↔
      (concreteQCandidate I place).order = 1 := by
  rw [S1507ConcreteQNorm_eq_five_zpow h5]
  have hinj : Function.Injective (fun n : Int => (5 : Real) ^ n) :=
    zpow_right_injective₀ (by norm_num : (0 : Real) < 5) (by norm_num)
  constructor
  · intro h
    have hpow : (5 : Real) ^ (-(concreteQCandidate I place).exponent) =
        (5 : Real) ^ (-1 : Int) := by
      simpa using h
    have he : -(concreteQCandidate I place).exponent = -1 := hinj hpow
    have hexp : (concreteQCandidate I place).exponent = 1 := by omega
    rw [FinitePlaceQCandidate.order, hexp]
    norm_num
  · intro h
    have hexp : (concreteQCandidate I place).exponent = 1 := by
      have hcast := qOrder_cast_eq_exponent_cast (concreteQCandidate I place)
      rw [h] at hcast
      norm_num at hcast
      exact_mod_cast hcast.symm
    rw [hexp]
    norm_num

/-- Exact D4 Tate-q residual condition: the concrete q has the normalized
uniformizer order 1 (equivalently norm 1/5). -/
def S1507ConcreteQOrderOne : Prop :=
  (concreteQCandidate I place).order = 1

#print axioms S1507ConcreteQNorm_eq_five_zpow
#print axioms S1507ConcreteQNorm_eq_inv_five_iff_order_one

end LeanFormal.IUT.XiFPaper.S1507ConcreteQNormOrderActual
end
