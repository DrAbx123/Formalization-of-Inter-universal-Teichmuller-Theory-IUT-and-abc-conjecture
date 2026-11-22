import tmp.sheaf.xif.paper.S2698Two2161ResidueActual
import tmp.sheaf.xif.paper.S2709ResidueNormCharActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
open LeanFormal.IUT.XiFPaper.S2698Two2161ResidueActual
open LeanFormal.IUT.XiFPaper.S2709ResidueNormCharActual
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2713ResidueNorm2161Actual

local instance s2713Fact2161 : Fact (Nat.Prime 2161) := ⟨S2697Prime2161⟩
local instance s2713GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2713ResidueNormBasePlus :
    residueNormBase S2697GaussianPlacePlus = 2161 := by
  have e : (NumberField.RingOfIntegers GaussianField ⧸
      S2697GaussianPlacePlus.maximalIdeal.asIdeal) ≃+* ZMod 2161 := by
    rw [S2698PlacePlus_maximalIdeal]
    exact S2698FieldResidueEquivPlus
  have h := S2709ResidueNormBase_eq_residueCharacteristic_of_ringEquiv
    (K := GaussianField) (place := S2697GaussianPlacePlus) (p := 2161) e
  rw [S2698ResidueCharacteristicPlus] at h
  simpa using h

theorem S2713ResidueNormBaseMinus :
    residueNormBase S2697GaussianPlaceMinus = 2161 := by
  have e : (NumberField.RingOfIntegers GaussianField ⧸
      S2697GaussianPlaceMinus.maximalIdeal.asIdeal) ≃+* ZMod 2161 := by
    rw [S2698PlaceMinus_maximalIdeal]
    exact S2698FieldResidueEquivMinus
  have h := S2709ResidueNormBase_eq_residueCharacteristic_of_ringEquiv
    (K := GaussianField) (place := S2697GaussianPlaceMinus) (p := 2161) e
  rw [S2698ResidueCharacteristicMinus] at h
  simpa using h

theorem S2713AbsNormPlus :
    Ideal.absNorm S2697GaussianPlacePlus.maximalIdeal.asIdeal = 2161 := by
  rw [S2698PlacePlus_maximalIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr S2698FieldResidueEquivPlus.toEquiv, Nat.card_zmod]

theorem S2713AbsNormMinus :
    Ideal.absNorm S2697GaussianPlaceMinus.maximalIdeal.asIdeal = 2161 := by
  rw [S2698PlaceMinus_maximalIdeal, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  rw [Nat.card_congr S2698FieldResidueEquivMinus.toEquiv, Nat.card_zmod]

#print axioms S2713ResidueNormBasePlus
#print axioms S2713AbsNormPlus

end LeanFormal.IUT.XiFPaper.S2713ResidueNorm2161Actual
end
