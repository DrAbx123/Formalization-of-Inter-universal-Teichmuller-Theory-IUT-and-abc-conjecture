import tmp.sheaf.xif.paper.S2763ResidueCharacteristicUnitActual
import tmp.sheaf.xif.paper.S2764GoodReductionOfUnitDeltaActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange
import LeanFormal.IUT.IUTII.Frobenioid.Example36EllipticCurveAnabelioid

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2763ResidueCharacteristicUnitActual
open LeanFormal.IUT.XiFPaper.S2764GoodReductionOfUnitDeltaActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2765CurveOutsideTwoActual

variable (v : NumberField.FinitePlace ℚ)

abbrev K (v : NumberField.FinitePlace ℚ) : Type := IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v.maximalIdeal
abbrev R (v : NumberField.FinitePlace ℚ) : Type := IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v.maximalIdeal

/-- The integral model of y^2 = x^3 - x in the local integer ring. -/
def localIntegralModel : WeierstrassCurve (R v) where
  a₁ := 0
  a₂ := 0
  a₃ := 0
  a₄ := -1
  a₆ := 0

/-- The local base-changed curve over the completed field. -/
def localCurve : WeierstrassCurve (K v) :=
  localIntegralModel v |>.map (algebraMap (R v) (K v))

theorem localCurve_isIntegral : localCurve v |>.IsIntegral (R v) := by
  apply WeierstrassCurve.isIntegral_of_exists_lift
  · exact ⟨0, by simp [localCurve, localIntegralModel]⟩
  · exact ⟨0, by simp [localCurve, localIntegralModel]⟩
  · exact ⟨0, by simp [localCurve, localIntegralModel]⟩
  · exact ⟨-1, by simp [localCurve, localIntegralModel]⟩
  · exact ⟨0, by simp [localCurve, localIntegralModel]⟩

theorem localIntegralModel_delta :
    (localIntegralModel v).Δ = (64 : R v) := by
  norm_num [localIntegralModel, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem localCurve_delta :
    (localCurve v).Δ = algebraMap (R v) (K v) (64 : R v) := by
  rw [localCurve, WeierstrassCurve.map_Δ, localIntegralModel_delta]

theorem localCurve_delta_isUnit
    (h2 : residueCharacteristic v ≠ 2) :
    IsUnit (localCurve v).Δ := by
  rw [localCurve_delta]
  exact IsUnit.map (algebraMap (R v) (K v))
    (isUnit_sixtyFour_of_residueCharacteristic_ne_two (K := ℚ) v h2)

theorem localCurve_hasGoodReduction
    (h2 : residueCharacteristic v ≠ 2) :
    (localCurve v).HasGoodReduction (R v) := by
  letI : (localCurve v).IsIntegral (R v) := localCurve_isIntegral v
  have hval : (IsDiscreteValuationRing.maximalIdeal (R v)).valuation (K v)
      (localCurve v).Δ = 1 := by
    rw [localCurve_delta]
    exact (IsDiscreteValuationRing.maximalIdeal (R v)).valuation_eq_one_iff_notMem
      (K := K v) |>.mpr
        (IsLocalRing.notMem_maximalIdeal.mpr
          (isUnit_sixtyFour_of_residueCharacteristic_ne_two (K := ℚ) v h2))
  letI : (localCurve v).IsMinimal (R v) :=
    isMinimal_of_isIntegral_valuation_Δ_eq_one (R v) (localCurve v) hval
  exact { goodReduction := hval }

theorem localCurve_hasGoodReductionOnMinimalModel
    (h2 : residueCharacteristic v ≠ 2) :
    HasGoodReductionOnMinimalModel (R v) (localCurve v) := by
  exact ⟨1, by simpa using localCurve_hasGoodReduction v h2⟩

#check localCurve
#check localCurve_isIntegral
#check localCurve_delta
#check localCurve_delta_isUnit
#check localCurve_hasGoodReduction
#check localCurve_hasGoodReductionOnMinimalModel
#print axioms localCurve_hasGoodReductionOnMinimalModel

end LeanFormal.IUT.XiFPaper.S2765CurveOutsideTwoActual
end
