import LeanFormal.IUT.Foundations.LocalFields.FinitePadicTensorTopology
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import Mathlib.MeasureTheory.Measure.Haar.Basic
import tmp.sheaf.n8.closure.SourcePilotRegion

noncomputable section
open MeasureTheory
open LeanFormal.IUT.LocalFieldPadicTensor
open LeanFormal.IUT.NumberFieldFinitePlace

namespace LeanFormal.IUT.XiFPaper.S2560TensorHaarActual

variable {p : ℕ} [Fact p.Prime] {ι : Type*} [Fintype ι]
variable (M : ι → Type*) [∀ i, NormedAddCommGroup (M i)]
variable [∀ i, NormedSpace ℚ_[p] (M i)] [∀ i, FiniteDimensional ℚ_[p] (M i)]

noncomputable instance S2560TensorMeasurableSpace :
    MeasurableSpace (FinitePadicTensor (p := p) M) :=
  borel (FinitePadicTensor (p := p) M)

noncomputable instance S2560TensorBorelSpace :
    BorelSpace (FinitePadicTensor (p := p) M) := ⟨rfl⟩

noncomputable def S2560TensorPositiveCompacts :
    TopologicalSpace.PositiveCompacts (FinitePadicTensor (p := p) M) where
  carrier := Metric.closedBall (0 : FinitePadicTensor (p := p) M) 1
  isCompact' := ProperSpace.isCompact_closedBall 0 1
  interior_nonempty' := by
    refine ⟨0, ?_⟩
    exact interior_maximal Metric.ball_subset_closedBall Metric.isOpen_ball
      (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))

noncomputable def S2560TensorHaarMeasure :
    Measure (FinitePadicTensor (p := p) M) :=
  Measure.addHaarMeasure (S2560TensorPositiveCompacts M)

noncomputable instance S2560TensorHaarMeasure_isAddHaar :
    Measure.IsAddHaarMeasure (S2560TensorHaarMeasure (p := p) M) :=
  Measure.isAddHaarMeasure_addHaarMeasure (S2560TensorPositiveCompacts (p := p) M)

/-- Actual Haar measure on the arithmetic tensor tuple block. -/
noncomputable def S2560ArithmeticTensorHaarMeasure
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) :
    Measure (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple) :=
  S2560TensorHaarMeasure
    (fun i => LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion (places i (tuple i)))

noncomputable instance S2560ArithmeticTensorMeasurableSpace
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) :
    MeasurableSpace (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple) :=
  inferInstanceAs (MeasurableSpace (FinitePadicTensor
    (p := p) (fun i => LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion (places i (tuple i)))))

noncomputable instance S2560ArithmeticTensorBorelSpace
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) :
    BorelSpace (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple) :=
  inferInstanceAs (BorelSpace (FinitePadicTensor
    (p := p) (fun i => LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion (places i (tuple i)))))

noncomputable instance S2560ArithmeticTensorHaarMeasure_isAddHaar
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) :
    Measure.IsAddHaarMeasure (S2560ArithmeticTensorHaarMeasure places tuple) :=
  inferInstanceAs (Measure.IsAddHaarMeasure (S2560TensorHaarMeasure
    (p := p) (fun i => LeanFormal.IUT.NumberFieldFinitePlace.CommonPrimeCompletion (places i (tuple i)))))

/-- Concrete measured tensor carrier: actual measurable/Borel structure and Haar measure. -/
structure S2560TensorMeasureDonor
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) where
  mu : Measure (LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock places tuple)
  addHaar : Measure.IsAddHaarMeasure mu

noncomputable def S2560TensorMeasureDonor_actual
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) :
    S2560TensorMeasureDonor places tuple :=
  { mu := S2560ArithmeticTensorHaarMeasure places tuple
    addHaar := S2560ArithmeticTensorHaarMeasure_isAddHaar places tuple }

theorem S2560TensorMeasureDonor_nonempty
    {K : Type*} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime]
    {ι : Type*} [Fintype ι] {V : ι → Type*}
    (places : (i : ι) → V i → LeanFormal.IUT.NumberFieldFinitePlace.FinitePlaceAtPrime K p)
    (tuple : (i : ι) → V i) :
    Nonempty (S2560TensorMeasureDonor places tuple) :=
  ⟨S2560TensorMeasureDonor_actual places tuple⟩

/-- Measure donor for the tensor block carried by a C3 source-pilot datum. -/
noncomputable def S2560C3TensorMeasureDonor
    {l : PrimeGeFive} {V : Type*} {I : LeanFormal.IUT.Theorem311Source.OriginalInput l V}
    (C3 : LeanFormal.IUT.N8Closure.SourcePilotRegion.SourcePilotRegionData I) :
    S2560TensorMeasureDonor (K := I.initial.arithmetic.Fmod) (p := C3.p)
      (ι := C3.tensorIndex) (V := C3.tensorPlaceIndex)
      C3.tensorPlaces C3.tensorTuple :=
  S2560TensorMeasureDonor_actual C3.tensorPlaces C3.tensorTuple

#check S2560TensorHaarMeasure
#check S2560ArithmeticTensorHaarMeasure
#check S2560TensorMeasureDonor_nonempty
#check S2560C3TensorMeasureDonor
#print axioms S2560C3TensorMeasureDonor
#print axioms S2560TensorMeasureDonor_nonempty
#print axioms S2560TensorHaarMeasure
#print axioms S2560ArithmeticTensorHaarMeasure
#print axioms S2560ArithmeticTensorHaarMeasure_isAddHaar
#print axioms S2560TensorHaarMeasure_isAddHaar
end LeanFormal.IUT.XiFPaper.S2560TensorHaarActual
end