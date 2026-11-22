import tmp.sheaf.xif.paper.S1072CanonicalQ1URegionActual
import tmp.sheaf.xif.paper.S1084IntegerWitnessActual
import tmp.sheaf.xif.paper.S1082LambdaOPositivityExactActual
import tmp.sheaf.xif.paper.UnitSmulCanonicalUnitReferenceActual
import tmp.sheaf.xif.paper.RootHullMeasureActual

/-! # S1091: positivity/finiteness of qPilotQ1URegion

qPilotQ1URegion = F(qVFamPureCoefficient) * O_hol.  The coefficient is a
positive constant, so the region is contained in O_hol and has finite Haar.
Positivity follows from the S1084 integer-witness pattern: choose N=ceil(cPure),
build the constant-N pure scaling datum with generator p^N, and use S1082's
scaled-unit containment.  Both sides are actual; no fake lattice positivity. -/

noncomputable section
open scoped BigOperators TensorProduct Topology Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 12000000

namespace LeanFormal.IUT.XiFPaper.S1091QPilotQ1UPositivityActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1081LambdaODomainHaarActual
open LeanFormal.IUT.XiFPaper.S1082LambdaOPositivityExactActual
open LeanFormal.IUT.XiFPaper.S1083ScaledUnitWitnessActual
open LeanFormal.IUT.XiFPaper.S1084IntegerWitnessActual
open LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual
open LeanFormal.IUT.XiFPaper.S1079RootStackMeasureAuditActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual
open MeasureTheory Topology

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- N = ceil(qVFamPureCoefficient). -/
noncomputable def s1091N : Nat :=
  Nat.ceil (qVFamPureCoefficient (l := l) T b ())

noncomputable def s1091Generator :
    (i : qVFamTensorV) →
      CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)) :=
  fun i => (qVFamTensorP T b : CommonPrimeCompletion
    ((qVFamTensorPlaces T b) i (qVFamTensorTuple i))) ^ (s1091N (l := l) T b : ℤ)

theorem s1091Generator_norm (i : qVFamTensorV) :
    ‖s1091Generator (l := l) T b i‖ =
      (qVFamTensorP T b : ℝ) ^ (-((s1091N (l := l) T b : ℝ))) := by
  unfold s1091Generator
  rw [norm_prime_zpow_commonPrimeCompletion]
  rw [Padic.norm_p]
  rw [zpow_natCast, inv_pow, Real.rpow_neg (by positivity), Real.rpow_natCast]

noncomputable def s1091Data :
    ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun _ => (s1091N (l := l) T b : ℝ)) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple (fun _ => (s1091N (l := l) T b : ℝ))
    (s1091Generator (l := l) T b) (s1091Generator_norm (l := l) T b)

theorem s1091Bound (i : qVFamTensorV) :
    qVFamPureCoefficient (l := l) T b i ≤ (s1091N (l := l) T b : ℝ) := by
  change qVFamPureCoefficient (l := l) T b () ≤ (s1091N (l := l) T b : ℝ)
  exact Nat.le_ceil _

/-- Scaled-unit containment into qPilotQ1URegion. -/
theorem s1091ScaledUnitContainment :
    ∃ u : (qVFamTensorBlock T b)ˣ,
      ((u : qVFamTensorBlock T b) •
        arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple) ⊆
        qPilotQ1URegion (l := l) T b := by
  refine ⟨arithmeticTupleFractionalGeneratorUnit (qVFamTensorPlaces T b)
    qVFamTensorTuple (s1091Data (l := l) T b), ?_⟩
  intro x hx
  have hgen := arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
    (qVFamTensorPlaces T b) qVFamTensorTuple (s1091Data (l := l) T b)
  rw [arithmeticTupleFractionalGeneratorUnit_coe] at hx
  have hxN : x ∈ ((arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun _ => (s1091N (l := l) T b : ℝ)) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :
      Submodule ℤ_[(qVFamTensorP T b)] (qVFamTensorBlock T b)) :
      Set (qVFamTensorBlock T b)) := by
    rw [hgen]
    exact hx
  unfold qPilotQ1URegion
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun _ => (s1091N (l := l) T b : ℝ)) ≤
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (qVFamPureCoefficient (l := l) T b) := by
    apply arithmeticTupleFractionalLattice_mono
    intro i
    exact s1091Bound (l := l) T b i
  exact (mul_le_mul' hlat le_rfl) hxN

/-- Positivity of qPilotQ1URegion under qVFam addHaar. -/
theorem s1091QPilotQ1U_measure_pos :
    0 < (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) := by
  rcases s1091ScaledUnitContainment (l := l) T b with ⟨u, hu⟩
  exact lt_of_lt_of_le
    (measure_unit_smul_canonicalUnitReference_pos_lt_top
      (p := qVFamTensorP T b) (qVFamTensorPlaces T b) qVFamTensorTuple
      (Measure.addHaar) u).1
    (measure_mono hu)

/-- qPilotQ1URegion is contained in O_hol. -/
theorem s1091_subset_holomorphic :
    qPilotQ1URegion (l := l) T b ⊆
      arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple := by
  intro x hx
  unfold qPilotQ1URegion at hx
  have hnonneg : ∀ i : qVFamTensorV, 0 ≤ qVFamPureCoefficient (l := l) T b i := by
    intro i
    change 0 ≤ qVFamPureCoefficient (l := l) T b ()
    exact le_of_lt (qVFamPureCoefficient_pos (l := l) T b)
  have hlat : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (qVFamPureCoefficient (l := l) T b) ≤
      arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleFractionalLattice_le_valuationInteger (qVFamTensorPlaces T b)
      qVFamTensorTuple hnonneg
  have hmul : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple (qVFamPureCoefficient (l := l) T b) *
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple ≤
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple := by
    calc
      _ ≤ arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple * arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
          qVFamTensorTuple := mul_le_mul' hlat le_rfl
      _ = _ := arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
        (qVFamTensorPlaces T b) qVFamTensorTuple
  rw [← coefficient_arithmeticTupleHolomorphicLattice
    (qVFamTensorPlaces T b) qVFamTensorTuple]
  exact hmul hx

/-- Finiteness of qPilotQ1URegion under qVFam addHaar. -/
theorem s1091QPilotQ1U_measure_lt_top :
    (Measure.addHaar : Measure (qVFamTensorBlock T b))
      (qPilotQ1URegion (l := l) T b) < ⊤ := by
  exact lt_of_le_of_lt (measure_mono (s1091_subset_holomorphic (l := l) T b))
    ((isCompact_arithmeticTupleCanonicalRegions
      (qVFamTensorPlaces T b) qVFamTensorTuple).2.measure_lt_top)

end LeanFormal.IUT.XiFPaper.S1091QPilotQ1UPositivityActual

end
