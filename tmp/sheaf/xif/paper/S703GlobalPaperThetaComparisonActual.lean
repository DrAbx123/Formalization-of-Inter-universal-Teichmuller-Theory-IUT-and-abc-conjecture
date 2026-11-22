import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual
import tmp.sheaf.xif.paper.S657RootSignedHullIndependentActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S703GlobalPaperThetaComparisonActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.S657RootSignedHullIndependentActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Positive signed label j = i+1 for i : Fin l*. -/
noncomputable def paperThetaPositiveLabel (i : Fin (lStar l.value)) :
    SignedLabel l.value :=
  ⟨(i.1 + 1 : Int), by
    constructor
    · have h0 : (0 : Int) ≤ (i.1 : Int) := by exact_mod_cast Nat.zero_le i.1
      have hs : (0 : Int) ≤ (lStar l.value : Int) := by
        exact_mod_cast Nat.zero_le (lStar l.value)
      omega
    · have hi : i.1 + 1 ≤ lStar l.value := Nat.succ_le_of_lt i.2
      exact_mod_cast hi⟩

/-- Paper theta average at b: l* positive labels, uniform weight 1/l*. -/
noncomputable def paperThetaAverageValue (b : Bad (nativePlaceSelection T)) : Real :=
  paperThetaLabelWeight l *
    ∑ i : Fin (lStar l.value),
      rootThetaMagnitudeValue T b (paperThetaPositiveLabel (l := l) i)

/-- Global paper theta average with native bad-place weights. -/
noncomputable def globalPaperThetaAverage : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b * paperThetaAverageValue T b

/-- Global paper q-pilot log magnitude: weighted order(q_v) log p_v. -/
noncomputable def globalPaperQPilotLog : Real :=
  ∑ b : Bad (nativePlaceSelection T),
    nativeBadLocalWeight T b *
      (((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real))

/-- Exact coefficient of the paper theta average against q-pilot magnitude. -/
noncomputable def paperThetaAverageCoefficient : Real :=
  paperThetaLabelWeight l *
    ∑ i : Fin (lStar l.value),
      (((i.1 + 1 : Real) ^ 2) / (2 * (l.value : Real)))

/-- Exact reduction of the global comparison to the coefficient. -/
theorem globalPaperThetaAverage_eq_coefficient_mul_qPilot :
    globalPaperThetaAverage T =
      paperThetaAverageCoefficient l * globalPaperQPilotLog T := by
  unfold globalPaperThetaAverage paperThetaAverageValue paperThetaAverageCoefficient
    globalPaperQPilotLog
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  have hterm : ∀ i : Fin (lStar l.value),
      rootThetaMagnitudeValue T b (paperThetaPositiveLabel (l := l) i) =
        (((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)) *
          (((i.1 + 1 : Real) ^ 2) / (2 * (l.value : Real))) := by
    intro i
    unfold rootThetaMagnitudeValue
    rw [show (paperThetaPositiveLabel (l := l) i).1 = (i.1 + 1 : Int) from rfl]
    unfold qVFamPaperThetaTensorCoefficient qVFamPaperRootCoefficient
    rw [show (gaussExponent ((i.1 + 1 : Int))).toNat = (i.1 + 1) ^ 2 from by
      unfold gaussExponent
      rw [Int.toNat_natCast]
      ring]
    simp only [qVFamTensorV, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    ring
  rw [Finset.sum_congr rfl (fun i _ => hterm i)]
  rw [← Finset.mul_sum]
  ring

/-- The exact global comparison proposition. -/
def GlobalPaperThetaComparison : Prop :=
  globalPaperThetaAverage T ≤ globalPaperQPilotLog T

/-- The global comparison is exactly the coefficient comparison when the
q-pilot scalar is positive. -/
theorem globalPaperThetaComparison_iff_coefficient
    (hq : 0 < globalPaperQPilotLog T) :
    GlobalPaperThetaComparison T ↔ paperThetaAverageCoefficient l ≤ 1 := by
  unfold GlobalPaperThetaComparison
  rw [globalPaperThetaAverage_eq_coefficient_mul_qPilot]
  constructor
  · intro h
    have h' : paperThetaAverageCoefficient l * globalPaperQPilotLog T ≤
        1 * globalPaperQPilotLog T := by simpa using h
    exact (mul_le_mul_right hq).mp h'
  · intro h
    exact (mul_le_mul_right hq).mpr h

/-- Exact gap: the paper-label average coefficient is the only remaining
scalar condition for this linear root-theta model. -/
def GlobalPaperThetaComparisonGap : Prop :=
  paperThetaAverageCoefficient l ≤ 1

end LeanFormal.IUT.XiFPaper.S703GlobalPaperThetaComparisonActual
end
