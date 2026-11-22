import tmp.sheaf.xif.paper.S2763ResidueCharacteristicUnitActual
import tmp.sheaf.xif.paper.S2764GoodReductionOfUnitDeltaActual
import LeanFormal.IUT.Foundations.Geometry.ReductionBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S2763ResidueCharacteristicUnitActual
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2782Semistable37a1Actual

/-- The rational curve 37a1: y^2 + y = x^3 - x. -/
def curve37 : WeierstrassCurve ℚ where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := -1
  a₆ := 0

theorem curve37_delta : curve37.Δ = (37 : ℚ) := by
  norm_num [curve37, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem curve37_c4 : curve37.c₄ = (48 : ℚ) := by
  norm_num [curve37, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]

theorem curve37_c6 : curve37.c₆ = (-216 : ℚ) := by
  norm_num [curve37, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]

variable (v : NumberField.FinitePlace ℚ)

abbrev K (v : NumberField.FinitePlace ℚ) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletion ℚ v.maximalIdeal

abbrev R (v : NumberField.FinitePlace ℚ) : Type :=
  IsDedekindDomain.HeightOneSpectrum.adicCompletionIntegers ℚ v.maximalIdeal

/-- Integral model of 37a1 in the local integer ring. -/
def localIntegralModel37 : WeierstrassCurve (R v) where
  a₁ := 0
  a₂ := 0
  a₃ := 1
  a₄ := -1
  a₆ := 0

/-- Local base-changed curve. -/
def localCurve37 : WeierstrassCurve (K v) :=
  (localIntegralModel37 v).map (algebraMap (R v) (K v))

theorem localCurve37_isIntegral : (localCurve37 v).IsIntegral (R v) := by
  apply WeierstrassCurve.isIntegral_of_exists_lift
  · exact ⟨0, by simp [localCurve37, localIntegralModel37]⟩
  · exact ⟨0, by simp [localCurve37, localIntegralModel37]⟩
  · exact ⟨1, by simp [localCurve37, localIntegralModel37]⟩
  · exact ⟨-1, by simp [localCurve37, localIntegralModel37]⟩
  · exact ⟨0, by simp [localCurve37, localIntegralModel37]⟩

theorem localIntegralModel37_delta :
    (localIntegralModel37 v).Δ = (37 : R v) := by
  norm_num [localIntegralModel37, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

theorem localIntegralModel37_c4 :
    (localIntegralModel37 v).c₄ = (48 : R v) := by
  norm_num [localIntegralModel37, WeierstrassCurve.c₄, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄]

theorem localIntegralModel37_c6 :
    (localIntegralModel37 v).c₆ = (-216 : R v) := by
  norm_num [localIntegralModel37, WeierstrassCurve.c₆, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆]

theorem localCurve37_delta :
    (localCurve37 v).Δ = algebraMap (R v) (K v) (37 : R v) := by
  rw [localCurve37, WeierstrassCurve.map_Δ, localIntegralModel37_delta]

theorem not_dvd_thirtyseven_of_ne
    (h37 : residueCharacteristic v ≠ 37) :
    ¬ residueCharacteristic v ∣ (37 : Nat) := by
  intro hd
  have hp : Nat.Prime (residueCharacteristic v) := residueCharacteristic_prime v
  have h37prime : Nat.Prime (37 : Nat) := by decide
  have heq : (37 : Nat) = residueCharacteristic v :=
    (h37prime.dvd_iff_eq hp.ne_one).mp hd
  exact h37 heq.symm

theorem localCurve37_delta_isUnit
    (h37 : residueCharacteristic v ≠ 37) :
    IsUnit (localCurve37 v).Δ := by
  rw [localCurve37_delta]
  exact IsUnit.map (algebraMap (R v) (K v))
    ((isUnit_natCast_adicCompletionIntegers_iff_not_dvd (K := ℚ) v 37).mpr (not_dvd_thirtyseven_of_ne v h37))

theorem localCurve37_hasGoodReduction
    (h37 : residueCharacteristic v ≠ 37) :
    (localCurve37 v).HasGoodReduction (R v) := by
  letI : (localCurve37 v).IsIntegral (R v) := localCurve37_isIntegral v
  have hval : (IsDiscreteValuationRing.maximalIdeal (R v)).valuation (K v)
      (localCurve37 v).Δ = 1 := by
    rw [localCurve37_delta]
    exact (IsDiscreteValuationRing.maximalIdeal (R v)).valuation_eq_one_iff_notMem
      (K := K v) |>.mpr
        (IsLocalRing.notMem_maximalIdeal.mpr
          ((isUnit_natCast_adicCompletionIntegers_iff_not_dvd (K := ℚ) v 37).mpr (not_dvd_thirtyseven_of_ne v h37)))
  letI : (localCurve37 v).IsMinimal (R v) :=
    isMinimal_of_isIntegral_valuation_Δ_eq_one (R v) (localCurve37 v) hval
  exact { goodReduction := hval }

theorem localCurve37_hasGoodReductionOnMinimalModel
    (h37 : residueCharacteristic v ≠ 37) :
    HasGoodReductionOnMinimalModel (R v) (localCurve37 v) :=
  ⟨1, by simpa using localCurve37_hasGoodReduction v h37⟩

#check curve37
#check curve37_delta
#check curve37_c4
#check curve37_c6
#check localCurve37
#check localCurve37_isIntegral
#check localCurve37_delta
#check localCurve37_hasGoodReduction
#check localCurve37_hasGoodReductionOnMinimalModel
#print axioms localCurve37_hasGoodReductionOnMinimalModel

end LeanFormal.IUT.XiFPaper.S2782Semistable37a1Actual
end
