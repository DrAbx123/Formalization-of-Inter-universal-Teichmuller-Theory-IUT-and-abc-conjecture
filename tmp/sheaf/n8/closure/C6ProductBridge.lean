import tmp.sheaf.n8.closure.PaperNormalizedVolume
import tmp.sheaf.n8.closure.C7Interface

/-!
# C6 product bridge for C7

Stage-2 handoff from C6 PaperNormalizedVolumeData to the C7 product/measure
interface C6ProductVolumeData.  The bridge extends the C7 product data and adds
the actual C6 paper data together with exact consistency fields.  It imports
C7Interface only, breaking the former C7 import cycle.
-/

open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open ABCBridge.N8.C7Actual
open MeasureTheory

namespace ABCBridge.N8.C6ProductBridge

universe uK uV uP uI uY

/-- Bridge from C6 normalized data to the C7 product/measure interface. -/
structure C6ProductBridge
    {K0 : Type uK} [Field K0] [NumberField K0]
    {p0 : ℕ} [Fact p0.Prime]
    {iota0 : Type uI} [Fintype iota0]
    {V0 : iota0 → Type uV}
    (places : (i : iota0) → V0 i →
      LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K0 p0)
    (tuple : (i : iota0) → V0 i)
    [MeasurableSpace
      (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace
      (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple)]
    (mu0 : Measure
      (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu0]
    (Y : Type uY) extends C6ProductVolumeData (Y := Y) where
  /-- Actual C6 normalized-volume data. -/
  paper : PaperNormalizedVolumeData (K := K0) (p := p0) (V := V0) places tuple mu0
  /-- Actual equivalence between product index and C6 local index. -/
  indexEquiv : ι ≃ iota0
  /-- C6 lambda weights transported to the product index. -/
  lambda : ι → ℝ
  /-- Exact lambda compatibility with C6. -/
  lambda_eq : ∀ i : ι, lambda i = paper.lambdaData.lambda (indexEquiv i)
  /-- C6 tuple weights transported to the product index. -/
  tupleWeight : ι → ℚ
  /-- Exact tuple-weight compatibility with C6. -/
  tupleWeight_eq : ∀ i : ι, tupleWeight i = paper.tupleWeights.weight (indexEquiv i)
  /-- Common tuple denominator for the product index. -/
  tupleDenominator : ℕ
  /-- Exact denominator compatibility with C6. -/
  tupleDenominator_eq : tupleDenominator = paper.tupleWeights.denominator
  /-- C6 normalized volume equals the product total-measure volume. -/
  volume_eq : paper.localVolume.normalizedVolume = (μ Set.univ).toReal
  /-- C6 raw Haar log equals the logarithm of the product total measure. -/
  haarLog_eq : paper.localVolume.haarLog = Real.log (μ Set.univ).toReal
  /-- C6 procession average transported to the product side. -/
  processionAverageValue : ℝ
  /-- Exact procession-average compatibility with C6. -/
  processionAverage_eq : processionAverageValue = paper.processionAverageValue

end ABCBridge.N8.C6ProductBridge
