import tmp.sheaf.xif.paper.S1576ProductHaarDecompositionActual

noncomputable section
open MeasureTheory
open scoped Pointwise BigOperators ENNReal NNReal
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S1584ProductUnitBallScalingActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1512ProductHaarScalingActual
open LeanFormal.IUT.XiFPaper.S1502DependentScalingCharActual
open LeanFormal.IUT.XiFPaper.S1422HDDDetActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1520LocalCompletionHaarActual
open LeanFormal.IUT.XiFPaper.S1576ProductHaarDecompositionActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldProductHull

local instance completionMeasurableSpace (P : NumberField.FinitePlace ℚ) :
    MeasurableSpace (Completion P) := borel (Completion P)

local instance completionBorelSpace (P : NumberField.FinitePlace ℚ) :
    BorelSpace (Completion P) := ⟨rfl⟩

variable (s : Finset (NumberField.FinitePlace ℚ))

local instance localDependentHaarIsAddHaar
    (v : {v // v ∈ s}) :
    Measure.IsAddHaarMeasure
      (Measure.addHaar : Measure (S1402DependentE s v)) :=
  Measure.isAddHaarMeasure_addHaarMeasure (K₀ := Classical.arbitrary _)

/-- Exact local measure scaling at one place: the inverse residue unit scales
the local unit ball by the residue characteristic. -/
theorem s1584LocalUnitBallScaling (v : {v // v ∈ s}) :
    (Measure.addHaar : Measure (S1402DependentE s v))
        ((dependentPrimeInverseUnit s v) •
          Metric.closedBall (0 : S1402DependentE s v) 1) =
      (dependentPlacePrime s v : ENNReal) *
        (Measure.addHaar : Measure (S1402DependentE s v))
          (Metric.closedBall (0 : S1402DependentE s v) 1) := by
  have hcharENN : (distribHaarChar (S1402DependentE s v)
      (dependentPrimeInverseUnit s v) : ENNReal) =
      (dependentPlacePrime s v : ENNReal) :=
    s1520LocalCompletionScaling s v
  have hcharNN : distribHaarChar (S1402DependentE s v)
      (dependentPrimeInverseUnit s v) = (dependentPlacePrime s v : NNReal) := by
    exact_mod_cast hcharENN
  have h := distribHaarChar_mul
    (μ := (Measure.addHaar : Measure (S1402DependentE s v)))
    (g := dependentPrimeInverseUnit s v)
    (s := Metric.closedBall (0 : S1402DependentE s v) 1)
  rw [hcharNN] at h
  exact h.symm

/-- Exact product unit-ball scaling from the local scalings. -/
theorem s1584ProductUnitBallScaling :
    S1576ProductUnitBallScaling s := by
  unfold S1576ProductUnitBallScaling
  let μ : (v : {v // v ∈ s}) → Measure (S1402DependentE s v) :=
    fun v => Measure.addHaar
  have hunit : dependentUnitRegion s =
      Set.univ.pi (fun v => Metric.closedBall (0 : S1402DependentE s v) 1) := by
    ext x
    simp [dependentUnitRegion, LocalFieldProductHull.unitRegion,
      Metric.mem_closedBall, dist_zero_right, Set.mem_pi]
  have hscaled : dependentPrimeUnit s • dependentUnitRegion s =
      Set.univ.pi (fun v =>
        (dependentPrimeInverseUnit s v) •
          Metric.closedBall (0 : S1402DependentE s v) 1) := by
    ext x
    constructor
    · intro hx
      rcases (Set.mem_smul_set).mp hx with ⟨y, hy, rfl⟩
      intro v _
      refine ⟨y v, ?_, ?_⟩
      · simpa [dependentUnitRegion, LocalFieldProductHull.unitRegion,
          Metric.mem_closedBall, dist_zero_right] using hy v
      · rfl
    · intro hx
      apply (Set.mem_smul_set).mpr
      refine ⟨fun v =>
        ((dependentPrimeInverseUnit s v)⁻¹) * x v, ?_, ?_⟩
      · intro v
        have h := hx v trivial
        rcases h with ⟨z, hz, hzx⟩
        have hzx' : (dependentPrimeInverseUnit s v : S1402DependentE s v) * z = x v := by
          simpa [Units.smul_def] using hzx
        change ‖((dependentPrimeInverseUnit s v : S1402DependentE s v))⁻¹ *
          x v‖ ≤ 1
        rw [← hzx']
        change ‖((dependentPrimeInverseUnit s v : S1402DependentE s v))⁻¹ *
          ((dependentPrimeInverseUnit s v : S1402DependentE s v) * z)‖ ≤ 1
        rw [← mul_assoc, inv_mul_cancel₀ (Units.ne_zero (dependentPrimeInverseUnit s v)),
          one_mul]
        simpa [Metric.mem_closedBall, dist_zero_right] using hz
      · ext v
        simp [dependentPrimeUnit, Units.smul_def]
  rw [hscaled, hunit]
  rw [show productLocalHaar s = Measure.pi μ from rfl]
  rw [Measure.pi_pi, Measure.pi_pi]
  rw [Finset.prod_congr rfl (fun v _ => s1584LocalUnitBallScaling s v)]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [← Nat.cast_prod]
  rfl

/-- Actual S1502 product scaling measure. -/
theorem s1584ProductScalingMeasure :
    S1502ProductScalingMeasure s :=
  s1576ProductScalingMeasure_of_unitBallScaling s
    (s1584ProductUnitBallScaling s)

/-- Exact next measure lemma: the dependent unit ball has positive finite
canonical Haar mass. -/
def S1584UnitBallPositiveFinite : Prop :=
  0 < dependentHaar s (dependentUnitRegion s) ∧
    dependentHaar s (dependentUnitRegion s) < ⊤

/-- Product scaling measure plus positive finite unit ball gives the dependent
character identity. -/
theorem s1584DependentProductScalingChar_of_posFin
    (h : S1584UnitBallPositiveFinite s) :
    DependentProductScalingChar s :=
  s1502DependentProductScalingChar_of_measure s
    (s1584ProductScalingMeasure s) h.1 h.2

end LeanFormal.IUT.XiFPaper.S1584ProductUnitBallScalingActual

end
