import tmp.sheaf.n8.closure.PaperInitialThetaData
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTupleHullVolume

/-!
# C7 paper divisor from paper initial Theta data: exact conversion gap

Paper input is SourceInitialThetaData (actual places, curve and clauses).  Its
actual projections are in PaperInitialThetaData.lean.

C7 still needs an actual C6 tensor region: a finite bad-place index, actual
FinitePlaceAtPrime places/tuple over one rational prime, measurable structure
and additive Haar measure.  SourceInitialThetaData gives actual VbadMod and
V/place/curve data, but no such C6 tensor places/tuple/measure conversion is
produced by the source clauses or by PaperInitialThetaData.lean.

This file records the paper-input C6 conversion gap and the missing A,Z law;
no shell SourceDefinition31Data gap is used and no arbitrary A,Z/region is
instantiated.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.checkUnivs false
set_option linter.overlappingInstances false
set_option linter.unusedVariables false

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure.PaperInitialThetaData
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.N8C6ActualIQ
open MeasureTheory
open scoped NumberField

namespace LeanFormal.IUT.N8Closure.C7PaperInitialThetaData

universe u v w

/-- Exact paper C6 region input: actual bad-place tensor places/tuple/measure
compatible with the paper initial Theta candidate. -/
structure PaperC6RegionInput (l : PrimeGeFive) (S : SourceInitialThetaData.{u} l) where
  K : Type u
  [fieldK : Field K]
  [numberFieldK : NumberField K]
  p : Nat
  [factP : Fact p.Prime]
  ι : Type v
  [fintypeι : Fintype ι]
  V : ι → Type w
  [fintypeV : ∀ i, Fintype (V i)]
  places : (i : ι) → V i → FinitePlaceAtPrime K p
  tuple : (i : ι) → V i
  [meas : MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [borel : BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  mu : Measure (ArithmeticTensorTupleBlock places tuple)
  [haar : Measure.IsAddHaarMeasure mu]
  c6 : C6ActualIQData places tuple mu

/-- Exact C7 paper divisor data: actual paper C6 region plus local multiplier
and effective zero divisors satisfying the model law. -/
structure PaperC7Divisors (l : PrimeGeFive) (S : SourceInitialThetaData.{u} l) where
  region : PaperC6RegionInput (l := l) S
  h : ℝ
  Q : ℝ
  A : ℝ
  Z : ℝ
  kappa : ℝ
  Sdeg : ℝ
  d : Nat
  kappa_eq_A : kappa = A
  S_eq_Z : Sdeg = Z
  identity : h - (d : ℝ) * Q = Sdeg - kappa
  S_nonneg : 0 ≤ Sdeg

end LeanFormal.IUT.N8Closure.C7PaperInitialThetaData
