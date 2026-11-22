import tmp.sheaf.n8.closure.PaperNormalizedVolume
import tmp.sheaf.n8.closure.SourceHolomorphicHull
import tmp.sheaf.n8.closure.C7Interface
import tmp.sheaf.n8.closure.C6ActualIQData
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.HullDeterminantLogVolumeReduction

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false

/-!
# C8 SourceDegreeComparison -- stage 2 (actual C6/C7 types)

The determinant/tensor-power readout is built from the actual C6
`PaperNormalizedVolumeData` weights and the actual C7 `SourceHolomorphicHullData`
common hull/measure.  The tensor exponent is C6's actual `tupleWeights.denominator`,
not a local field; the arithmetic degree is the donor
`profileArithmeticDegree` of the `M`-th adjusted determinant profile.  No
`DetTensorPowerLogVolumeBookkeeping` and no local weight/hull/measure interface
is introduced. The former theorem-level `sorry` is replaced by the exact
`SourceDegreeComparisonResidual` plus `c8RelativeDetDegree_eq_mul_sum`; the
unconditional equality is false for arbitrary independent C6/C7 (Ob3-3 gap).
-/

noncomputable section

open MeasureTheory BigOperators
open LeanFormal.IUT.N8C6.PaperNormalizedVolume
open ABCBridge.N8.C7Actual
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceAlgorithmCompatibility
open LeanFormal.IUT.N8Closure.SourceThetaToIQ
open LeanFormal.IUT.N8C6ActualIQ

namespace LeanFormal.IUT.N8Closure.C8

universe ua uv upi umon ui uL uY uι uK uG u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
  {iota : Type v} [Fintype iota] {V : iota → Type w}
  {places : (i : iota) → V i → FinitePlaceAtPrime K p}
  {tuple : (i : iota) → V i}
  [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
  [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
  {mu : Measure (ArithmeticTensorTupleBlock places tuple)}
  [Measure.IsAddHaarMeasure mu]

variable {l : PrimeGeFive} {V0 : Type uv} {Label : Type uL} [Group Label]
  {I : OriginalInput.{ua, uv, upi, umon, ui} l V0}
  {D : SourceWitnessedOutputData (l := l) (V := V0) I Label}
  {C5 : C5PermittedFamilyData (l := l)}
  {C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v)}
  {C1 : SourceInputBinding I}
  {C2 : SourceLogKummerData I C1}
  {C3 : SourcePilotRegionData (l := l) (V := V0) I}
  [MeasurableSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  [BorelSpace (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)]
  {LAdd : Type uG} [AddGroup LAdd]
  {Dalg : SourceWitnessedOutputData (l := l) (V := V0) I (Multiplicative LAdd)}
  {C5Alg : SourceAlgorithmCompatibilityData I C1 C2 C3 Dalg}
  {muIQ : Measure (ArithmeticTensorTupleBlock C3.tensorPlaces C3.tensorTuple)}
  [Measure.IsAddHaarMeasure muIQ]
  {B : C6ActualIQData C3.tensorPlaces C3.tensorTuple muIQ}
  {T : SourceThetaIQInterface (I := I) C3}
  {n : ThetaPilotCarrier l} {x : I.ThetaPilotPoint D.place.v}

/-- The actual C6 tuple exponent `M = prod N_v`, taken from C6
`PaperNormalizedVolumeData`; it is not a local field and is not defined by C8. -/
def c8TupleExponent (C6 : PaperNormalizedVolumeData places tuple mu) : ℕ :=
  C6.tupleWeights.denominator

/-- The actual C6 lambda-weight profile of the determinant bundle. -/
def c8BundleProfile (C6 : PaperNormalizedVolumeData places tuple mu) (i : iota) : ℝ :=
  C6.lambdaData.lambda i

/-- The structure-sheaf adjustment of (Ob3-1-2) at degree level. -/
def c8StructureSheafProfile (C6 : PaperNormalizedVolumeData places tuple mu) (_ : iota) : ℝ :=
  0

/-- Arithmetic degree of the weighted tensor power `det^{tensor M}`: the donor
`profileArithmeticDegree` of `M` times the adjusted determinant profile. -/
def c8RelativeDetDegree (C6 : PaperNormalizedVolumeData places tuple mu) : ℝ :=
  profileArithmeticDegree ((c8TupleExponent C6) •
    (c8BundleProfile C6 - c8StructureSheafProfile C6))

/-- C7-normalized log-volume of the actual common hull, using C6's actual
normalization degree and unit-reference log. -/
def c8HullLogVolume (C6 : PaperNormalizedVolumeData places tuple mu)
    (_C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n) : ℝ :=
  (1 / (C6.localVolume.degree : ℝ)) *
    (Real.log (muIQ (commonHull (C3 := C3) muIQ B)).toReal -
      C6.localVolume.unitReferenceLog)

/-- The production degree donor is the finite sum of the realified profile. -/
theorem profileArithmeticDegree_eq_sum
    {Place : Type*} [Fintype Place] (profile : Place -> Real) :
    profileArithmeticDegree profile = Finset.univ.sum profile := rfl

/-- The weighted determinant degree is the C6 tuple exponent times the sum
of the actual C6 lambda weights. -/

theorem c8RelativeDetDegree_eq_mul_sum
    (C6 : PaperNormalizedVolumeData places tuple mu) :
    c8RelativeDetDegree (V := V) (places := places) (tuple := tuple) C6 =
      (∑ i : iota, C6.lambdaData.lambda i) *
        (c8TupleExponent C6 : Real) := by
  unfold c8RelativeDetDegree c8TupleExponent c8BundleProfile c8StructureSheafProfile
  rw [profileArithmeticDegree_eq_sum]
  simp only [Pi.smul_apply, Pi.sub_apply, Pi.zero_apply, sub_zero, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Exact residual of the missing (Ob3-3) degree/log-volume identification. -/
def SourceDegreeComparisonResidual
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n) : Prop :=
  c8RelativeDetDegree (V := V) (places := places) (tuple := tuple) C6 =
    c8HullLogVolume (V := V) (places := places) (tuple := tuple) C6 C6Prod C7

/-- Conditional consumer: the residual is exactly the missing Ob3-3 identity. -/
theorem sourceDegreeComparison_of_residual
    (C6 : PaperNormalizedVolumeData places tuple mu)
    (C6Prod : C6ProductVolumeData (Y := I.ThetaPilotPoint D.place.v))
    (C7 : SourceHolomorphicHullData (C1 := C1) (C2 := C2) (C3 := C3)
      (D := Dalg) (C5 := C5Alg) (mu := muIQ) (B := B) (T := T) n)
    (h : SourceDegreeComparisonResidual (V := V) (places := places)
      (tuple := tuple) C6 C6Prod C7) :
    c8RelativeDetDegree (V := V) (places := places) (tuple := tuple) C6 =
      c8HullLogVolume (V := V) (places := places) (tuple := tuple) C6 C6Prod C7 := h

end LeanFormal.IUT.N8Closure.C8

end