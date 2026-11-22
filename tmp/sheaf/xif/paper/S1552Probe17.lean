import tmp.sheaf.xif.paper.S1552Probe15
import tmp.sheaf.xif.paper.S1552Probe16
import tmp.sheaf.xif.paper.S1512ProductHaarScalingActual

noncomputable section
open MeasureTheory
open scoped Pointwise ENNReal NNReal
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual

namespace S1552Probe17

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 8000000

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

local instance factTargetPrime (P : NumberField.FinitePlace ℚ) :
    Fact (Nat.Prime (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val) :=
  ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩

theorem hcomap (P : NumberField.FinitePlace ℚ) : comap (k := ℚ) P = P := by
  apply NumberField.FinitePlace.maximalIdeal_injective
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [NumberFieldFinitePlace.comap_maximalIdeal]
  simpa using Ideal.comap_id (R := NumberField.RingOfIntegers ℚ)
    (I := P.maximalIdeal.asIdeal)

theorem completionRationalPrime_eq (P : NumberField.FinitePlace ℚ) :
    completionRationalPrime P = Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal := by
  unfold completionRationalPrime
  rw [hcomap]

theorem dependentPlacePrime_eq (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) :
    dependentPlacePrime s v =
      (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val := by
  unfold dependentPlacePrime
  rw [completionRationalPrime_eq]

theorem unit_map_dependentPrimeInverseUnit
    (s : Finset (NumberField.FinitePlace ℚ)) (v : {v // v ∈ s}) :
    Units.map (S1552Probe15.ringEquivCompletionPadic v.1).toMonoidHom
        (dependentPrimeInverseUnit s v) =
      Units.mk0
        (((Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val : ℚ_[
            (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val])⁻¹)
        (inv_ne_zero (Nat.cast_ne_zero.mpr
          (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).property.ne_zero)) := by
  ext
  simp only [Units.coe_map, Units.coe_mk0, MonoidHom.coe_coe]
  rw [map_inv₀]
  congr 1
  rw [dependentPlacePrime_eq]
  exact map_natCast (S1552Probe15.ringEquivCompletionPadic v.1)
    (Rat.HeightOneSpectrum.primesEquiv v.1.maximalIdeal).val

theorem localScaling (s : Finset (NumberField.FinitePlace ℚ))
    (v : {v // v ∈ s}) : S1502LocalPrimeScaling s v := by
  unfold S1502LocalPrimeScaling
  let P := v.1
  let pP : ℕ := (Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).val
  letI : Fact (Nat.Prime pP) :=
    ⟨(Rat.HeightOneSpectrum.primesEquiv P.maximalIdeal).property⟩
  have hchar := S1552Probe15.distribHaarChar_completionPadic P
    (dependentPrimeInverseUnit s v)
  have hpad := S1552Probe16.distribHaarChar_padicPrimeInv pP
  have hunit := unit_map_dependentPrimeInverseUnit s v
  have hval : pP = dependentPlacePrime s v := (dependentPlacePrime_eq s v).symm
  have hmain : distribHaarChar (Completion P) (dependentPrimeInverseUnit s v) =
      (dependentPlacePrime s v : ℝ≥0) := by
    rw [hchar, hunit, hpad, hval]
  exact_mod_cast hmain

end S1552Probe17
