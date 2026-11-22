import tmp.sheaf.n8.Group6Normalization
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic

/-!
# N8 C6 stage2: paper normalized-volume data

This file defines the C6 stage-2 numerical data using the actual Group6 donors:
local L/V, the Group6 local identity, lambda_v weights, tuple weights with a
common positive denominator, the procession average, and the global normalized
volume.  The Group6 local identity is consumed, not reproved.  The single named
theorem-level gap is the paper global normalization/procession identity.
-/

open LeanFormal.IUT.NumberFieldFinitePlace
open MeasureTheory BigOperators

namespace LeanFormal.IUT.N8C6.PaperNormalizedVolume

universe u v w

/-- Local L/V data pinned to the actual Group6 normalization functions. -/
structure PaperLocalVolumeData
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] where
  haarLog : ℝ
  normalizedVolume : ℝ
  degree : ℕ
  unitReferenceLog : ℝ
  haarLog_eq : haarLog = arithmeticTupleCanonicalHullHaarLog places tuple mu
  normalizedVolume_eq : normalizedVolume =
    arithmeticTupleNormalizedLogVolume places tuple mu
      (arithmeticTupleCanonicalHull places tuple)
  degree_eq : degree =
    Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
  unitReferenceLog_eq : unitReferenceLog =
    Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal

/-- The actual local L/V data from Group6Normalization. -/
noncomputable def PaperLocalVolumeData.actual
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] :
    PaperLocalVolumeData places tuple mu where
  haarLog := arithmeticTupleCanonicalHullHaarLog places tuple mu
  normalizedVolume :=
    arithmeticTupleNormalizedLogVolume places tuple mu
      (arithmeticTupleCanonicalHull places tuple)
  degree := Module.finrank ℚ_[p] (ArithmeticTensorTupleBlock places tuple)
  unitReferenceLog :=
    Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  haarLog_eq := rfl
  normalizedVolume_eq := rfl
  degree_eq := rfl
  unitReferenceLog_eq := rfl

/-- The local L-V identity, consumed from Group6Normalization. -/
theorem PaperLocalVolumeData.local_identity
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    {places : (i : iota) → V i → FinitePlaceAtPrime K p}
    {tuple : (i : iota) → V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
    [Measure.IsAddHaarMeasure mu]
    (D : PaperLocalVolumeData places tuple mu) :
    D.haarLog = (D.degree : ℝ) * D.normalizedVolume + D.unitReferenceLog := by
  rcases D with ⟨h, v, d, u, hh, hv, hd, hu⟩
  change h = (d : ℝ) * v + u
  rw [hh, hv, hd, hu]
  exact n8g6_canonicalHullHaarLog_eq_finrank_mul_normalizedLogVolume_add_log_unitReference
    places tuple mu

/-- Lambda weights lambda_v, with positivity. -/
structure PaperLambdaData (iota : Type v) where
  lambda : iota → ℝ
  positive : ∀ i : iota, 0 < lambda i

/-- Tuple weights with a common positive denominator. -/
structure PaperTupleWeightData (iota : Type v) where
  weight : iota → ℚ
  denominator : ℕ
  denominator_pos : 0 < denominator
  integral_numerator : ∀ i : iota, ∃ z : ℤ, weight i = (z : ℚ) / denominator

/-- The paper procession average: arithmetic mean over a finite procession. -/
noncomputable def processionAverage {n : ℕ} (w : Fin n → ℝ) : ℝ :=
  (∑ i : Fin n, w i) / (n : ℝ)

/-- C6 stage-2 data. -/
structure PaperNormalizedVolumeData
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    (places : (i : iota) → V i → FinitePlaceAtPrime K p)
    (tuple : (i : iota) → V i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu] where
  localVolume : PaperLocalVolumeData places tuple mu
  lambdaData : PaperLambdaData iota
  tupleWeights : PaperTupleWeightData iota
  processionLength : ℕ
  processionLength_pos : 0 < processionLength
  processionWeights : Fin processionLength → ℝ
  processionAverageValue : ℝ
  globalVolume : ℝ

/-- Stage-2 gap: paper global normalization/procession identity. -/
theorem paperNormalizedVolume_global_normalization
    {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
    {iota : Type v} [Fintype iota] {V : iota → Type w}
    {places : (i : iota) → V i → FinitePlaceAtPrime K p}
    {tuple : (i : iota) → V i}
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
    [Measure.IsAddHaarMeasure mu]
    (D : PaperNormalizedVolumeData places tuple mu) :
    D.globalVolume =
      D.localVolume.normalizedVolume * (∑ i : iota, D.lambdaData.lambda i) := by
  sorry

end LeanFormal.IUT.N8C6.PaperNormalizedVolume
