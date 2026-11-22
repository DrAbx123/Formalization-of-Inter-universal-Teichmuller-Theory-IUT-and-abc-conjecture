/- generic bridge: (completionRationalPrime place).val = residueCharacteristic place。

路线: v := (comap (k:=ℚ) place).maximalIdeal;
Rat.HeightOneSpectrum.span_natGenerator v 给 span{(natGenerator v : ℤ)} = v.asIdeal.map e
(e := Rat.ringOfIntegersEquiv : 𝓞ℚ ≃+* ℤ); 用 e.symm.toRingHom = algebraMap ℤ (𝓞ℚ) 与
Ideal.comap_symm 得该 = P.under ℤ; 而 under_eq_span_residueCharacteristic 给
P.under ℤ = span{(residueCharacteristic : ℤ)}; 两边 span 相等 ⇒ natAbs 相等 ⇒ pNat = RC。 -/
import Mathlib.Tactic
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import LeanFormal.IUT.Foundations.NumberField.FinitePlaces
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT82CompletionPrimeResidueActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open NumberField

universe u

variable {K : Type u} [Field K] [NumberField K]

/-- **generic bridge**: completionRationalPrime 的 val（有理素数）等于该 K-place 的 residueCharacteristic。 -/
theorem completionRationalPrime_val_eq_residueCharacteristic
    (place : NumberField.FinitePlace K) :
    (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val =
      residueCharacteristic place := by
  let v := (comap (k := ℚ) place).maximalIdeal
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hgen : Rat.HeightOneSpectrum.natGenerator v =
      (LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val := rfl
  have heq : e = Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ) := by
    ext x
    exact (Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x).symm
  have hspan : Ideal.span {((LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val : ℤ)} =
      v.asIdeal.map e := by
    rw [← hgen, Rat.HeightOneSpectrum.span_natGenerator, heq]
  have hinv : (e.symm : ℤ →+* NumberField.RingOfIntegers ℚ) =
      algebraMap ℤ (NumberField.RingOfIntegers ℚ) := by
    apply RingHom.ext_int <;> simp [e]
  -- v.asIdeal = P.under (𝓞ℚ)
  have hv : v.asIdeal = place.maximalIdeal.asIdeal.under (NumberField.RingOfIntegers ℚ) := by
    simp [v, LeanFormal.IUT.NumberFieldFinitePlace.comap_maximalIdeal]
  -- map e (P.under 𝓞ℚ) = P.under ℤ
  have hmap : v.asIdeal.map e = place.maximalIdeal.asIdeal.under ℤ := by
    rw [hv]
    change Ideal.map (e : NumberField.RingOfIntegers ℚ →+* ℤ)
        (place.maximalIdeal.asIdeal.under (NumberField.RingOfIntegers ℚ)) =
      place.maximalIdeal.asIdeal.under ℤ
    rw [Ideal.map_comap_of_equiv]
    change (place.maximalIdeal.asIdeal.under (NumberField.RingOfIntegers ℚ)).comap
        (e.symm : ℤ →+* NumberField.RingOfIntegers ℚ) =
      place.maximalIdeal.asIdeal.comap (algebraMap ℤ (NumberField.RingOfIntegers K))
    rw [Ideal.comap_comap]
    congr 1
    rw [hinv]
    exact (IsScalarTower.algebraMap_eq ℤ (NumberField.RingOfIntegers ℚ) (NumberField.RingOfIntegers K)).symm
  have hunder : place.maximalIdeal.asIdeal.under ℤ =
      Ideal.span {((residueCharacteristic place : ℕ) : ℤ)} :=
    under_eq_span_residueCharacteristic (K := K) place
  have hspan' : Ideal.span {((LeanFormal.IUT.NumberFieldFinitePlace.completionRationalPrime place).val : ℤ)} =
      Ideal.span {((residueCharacteristic place : ℕ) : ℤ)} := by
    rw [hspan, hmap, hunder]
  have hassoc := Ideal.span_singleton_eq_span_singleton.mp hspan'
  have hnat := Int.associated_iff_natAbs.mp hassoc
  simpa using hnat

end LeanFormal.IUT.XiFPaper.Mzk1HT82CompletionPrimeResidueActual