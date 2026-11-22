import LeanFormal.IUT.IUTII.Frobenioid.Example36GaussianSplitPlaceArithmetic
import LeanFormal.IUT.IUTI.InitialTheta.ConcreteArithmeticExample
import Mathlib.RingTheory.PrincipalIdealDomain

noncomputable section
open LeanFormal.IUT
set_option maxRecDepth 100000
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual

open LeanFormal.IUT.IUTII.Frobenioid.Example36

local instance s2697GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

theorem S2697Prime2161 : Nat.Prime 2161 := by decide

def S2697GaussianIntPlus : GaussianInt := ⟨44, 15⟩
def S2697GaussianIntMinus : GaussianInt := ⟨44, -15⟩

theorem S2697GaussianIntPlus_norm :
    Zsqrtd.norm S2697GaussianIntPlus = 2161 := by
  simp [S2697GaussianIntPlus, Zsqrtd.norm_def]

theorem S2697GaussianIntMinus_norm :
    Zsqrtd.norm S2697GaussianIntMinus = 2161 := by
  simp [S2697GaussianIntMinus, Zsqrtd.norm_def]

theorem S2697GaussianIntPlus_irreducible :
    Irreducible S2697GaussianIntPlus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm S2697GaussianIntPlus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [S2697GaussianIntPlus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm S2697GaussianIntPlus).natAbs := by rw [hab]
        _ = 2161 := by rw [S2697GaussianIntPlus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := (S2697Prime2161).eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

theorem S2697GaussianIntMinus_irreducible :
    Irreducible S2697GaussianIntMinus := by
  rw [irreducible_iff]
  constructor
  · intro hunit
    have hnorm : (Zsqrtd.norm S2697GaussianIntMinus).natAbs = 1 :=
      Zsqrtd.norm_eq_one_iff.mpr hunit
    rw [S2697GaussianIntMinus_norm] at hnorm
    norm_num at hnorm
  · intro a b hab
    have hnorm : (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs = 2161 := by
      calc (Zsqrtd.norm a).natAbs * (Zsqrtd.norm b).natAbs
          = (Zsqrtd.norm (a * b)).natAbs := by rw [Zsqrtd.norm_mul, Int.natAbs_mul]
        _ = (Zsqrtd.norm S2697GaussianIntMinus).natAbs := by rw [hab]
        _ = 2161 := by rw [S2697GaussianIntMinus_norm]; norm_num
    have hdvd : (Zsqrtd.norm a).natAbs ∣ 2161 := ⟨(Zsqrtd.norm b).natAbs, hnorm.symm⟩
    have hcases := (S2697Prime2161).eq_one_or_self_of_dvd
      ((Zsqrtd.norm a).natAbs) hdvd
    rcases hcases with ha | ha
    · left
      exact Zsqrtd.norm_eq_one_iff.mp ha
    · right
      have hb : (Zsqrtd.norm b).natAbs = 1 := by
        rw [ha] at hnorm
        omega
      exact Zsqrtd.norm_eq_one_iff.mp hb

instance S2697GaussianIntPlus_ideal_isMaximal :
    (Ideal.span {S2697GaussianIntPlus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible S2697GaussianIntPlus_irreducible

instance S2697GaussianIntMinus_ideal_isMaximal :
    (Ideal.span {S2697GaussianIntMinus}).IsMaximal :=
  PrincipalIdealRing.isMaximal_of_irreducible S2697GaussianIntMinus_irreducible

noncomputable def S2697GaussianFieldPrimePlus : Ideal gaussianRingOfIntegers :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {S2697GaussianIntPlus})

noncomputable def S2697GaussianFieldPrimeMinus : Ideal gaussianRingOfIntegers :=
  Ideal.comap gaussianRingOfIntegersEquivGaussianInt.toRingHom
    (Ideal.span {S2697GaussianIntMinus})

instance S2697GaussianFieldPrimePlus_isMaximal :
    S2697GaussianFieldPrimePlus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

instance S2697GaussianFieldPrimeMinus_isMaximal :
    S2697GaussianFieldPrimeMinus.IsMaximal :=
  Ideal.comap_isMaximal_of_equiv gaussianRingOfIntegersEquivGaussianInt

noncomputable def S2697GaussianPlacePlus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := S2697GaussianFieldPrimePlus
      isPrime := S2697GaussianFieldPrimePlus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        S2697GaussianFieldPrimePlus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

noncomputable def S2697GaussianPlaceMinus : NumberField.FinitePlace GaussianField :=
  NumberField.FinitePlace.mk
    { asIdeal := S2697GaussianFieldPrimeMinus
      isPrime := S2697GaussianFieldPrimeMinus_isMaximal.isPrime
      ne_bot := Ring.ne_bot_of_isMaximal_of_not_isField
        S2697GaussianFieldPrimeMinus_isMaximal
        (NumberField.RingOfIntegers.not_isField GaussianField) }

/-- Exact residual input for the D structure: the residue characteristic of
these explicit Gaussian places is 2161 (equivalently the residue fields are
ZMod 2161), hence odd. -/
def S2697ResidueCharacteristic2161 : Prop :=
  NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlacePlus = 2161 ∧
  NumberFieldFinitePlace.residueCharacteristic S2697GaussianPlaceMinus = 2161

#print axioms S2697GaussianIntPlus_irreducible
#print axioms S2697GaussianPlacePlus

end LeanFormal.IUT.XiFPaper.S2697Two2161PlacesActual
end
