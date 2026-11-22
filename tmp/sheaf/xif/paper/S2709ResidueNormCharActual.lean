import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2709ResidueNormCharActual

variable {K : Type} [Field K] [NumberField K]
variable (place : NumberField.FinitePlace K)
variable (p : Nat) [Fact p.Prime]

/-- If the residue field at `place` is `ZMod p` by an actual ring
equivalence, then both the arithmetic residue norm and the residue
characteristic are `p`, hence equal. -/
theorem S2709ResidueNormBase_eq_residueCharacteristic_of_ringEquiv
    (e : (NumberField.RingOfIntegers K ⧸ place.maximalIdeal.asIdeal) ≃+* ZMod p) :
    residueNormBase place = residueCharacteristic place := by
  have hcard : residueNormBase place = p := by
    unfold residueNormBase
    rw [Ideal.absNorm_apply, Submodule.cardQuot_apply,
      Nat.card_congr e.toEquiv, Nat.card_zmod]
  have hchar : residueCharacteristic place = p := by
    unfold residueCharacteristic ResidueField
    change ringChar (NumberField.RingOfIntegers K ⧸
      place.maximalIdeal.asIdeal) = p
    have hzero : (p : NumberField.RingOfIntegers K ⧸
        place.maximalIdeal.asIdeal) = 0 := by
      apply e.injective
      rw [map_zero]
      change e ((p : ℕ) : NumberField.RingOfIntegers K ⧸
        place.maximalIdeal.asIdeal) = 0
      rw [map_natCast, ZMod.natCast_self]
    exact CharP.ringChar_of_prime_eq_zero Fact.out hzero
  rw [hcard, hchar]

#print axioms S2709ResidueNormBase_eq_residueCharacteristic_of_ringEquiv

end LeanFormal.IUT.XiFPaper.S2709ResidueNormCharActual
end
