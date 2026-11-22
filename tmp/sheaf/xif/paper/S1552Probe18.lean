import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual
import LeanFormal.IUT.ABCBridge.Geometry.RationalCommonPrimeFinrank

noncomputable section
open MeasureTheory
open scoped Pointwise ENNReal NNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual

namespace S1552Probe18
local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) : MeasurableSpace (Completion P) := borel (Completion P)
local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) : BorelSpace (Completion P) := ⟨rfl⟩
local instance instAlgebraRatCompletionAux (P : NumberField.FinitePlace ℚ) : Algebra ℚ (Completion P) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ P.maximalIdeal (Algebra.id ℚ)
local instance factTargetPrime (P : NumberField.FinitePlace ℚ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩

theorem comap_rat_self (P : NumberField.FinitePlace ℚ) : comap (k := ℚ) P = P := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  change Ideal.comap (RingHom.id (NumberField.RingOfIntegers ℚ)) P.maximalIdeal.asIdeal =
    P.maximalIdeal.asIdeal
  rw [Ideal.comap_id]

theorem completionRationalPrime_eq_primesEquiv (P : NumberField.FinitePlace ℚ) :
    completionRationalPrime P = Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal := by
  unfold completionRationalPrime
  apply congrArg Rat.HeightOneSpectrum.primesEquiv
  exact congrArg NumberField.FinitePlace.maximalIdeal (comap_rat_self P)

theorem dependentPlacePrime_eq (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    dependentPlacePrime s v =
      (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val := by
  unfold dependentPlacePrime
  rw [completionRationalPrime_eq_primesEquiv]

noncomputable def ringEquivCompletionPadic (P : NumberField.FinitePlace ℚ) :
    Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val] :=
  (Rat.HeightOneSpectrum.adicCompletion.padicEquiv P.maximalIdeal :
    Completion P ≃+* ℚ_[(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val])

example (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    Units.map (ringEquivCompletionPadic v.1).toMonoidHom
        (dependentPrimeInverseUnit s v) =
      Units.mk0
        (((Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val : ℚ_[
            (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val])⁻¹)
        (inv_ne_zero (Nat.cast_ne_zero.mpr
          (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).property.ne_zero)) := by
  ext
  simp only [Units.coe_map, Units.val_mk0, dependentPrimeInverseUnit]
  change (ringEquivCompletionPadic v.1) ((dependentPlacePrime s v : Completion v.1)⁻¹) =
    ((Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val : ℚ_[
      (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val])⁻¹
  rw [map_inv₀]
  congr 1
  rw [dependentPlacePrime_eq]
  exact map_natCast (ringEquivCompletionPadic v.1)
    (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val

end S1552Probe18
