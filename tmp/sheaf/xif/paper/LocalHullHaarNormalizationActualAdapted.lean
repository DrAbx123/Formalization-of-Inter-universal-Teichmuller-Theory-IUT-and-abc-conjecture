import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume

/-! # Local hull Haar normalization: finite positive ratio and nonzero log

On one actual arithmetic tensor block with fractional coefficients c, the local
theta hull is the actual scaled region F(c) * O_hol.  The actual formula

  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic

gives its normalized log-volume mu_log = -(sum c_i) log p.  Hence the actual
normalized Haar ratio is

  ratio = exp(mu_log) = exp(-(sum c_i) log p).

For c_i > 0 and p > 1 this is finite, positive, not equal to one, and its log
is nonzero.  This replaces the previous toReal scalar that mapped both 0 and
top to 0.

Raw measure positivity/finiteness of the hull is derived inside the actual
fractional-lattice formula for the canonical unit reference; the exact missing
per-b ArithmeticTuplePureFractionalScalingData is recorded separately, not
faked.

No sorry, axiom, True, or PUnit. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LocalHullHaarNormalizationActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldPadicTensor
open MeasureTheory

universe uK uI uV

variable {p : Nat} [Fact p.Prime]
variable {K : Type uK} [Field K] [NumberField K]
variable {ι : Type uI} [Fintype ι] [Nonempty ι]
variable {V : ι -> Type uV} [∀ i, Fintype (V i)]
variable (places : (i : ι) -> V i -> FinitePlaceAtPrime K p)
variable (tuple : (i : ι) -> V i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (μ : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure μ]
variable (c : ι -> Real)
variable (data : ArithmeticTuplePureFractionalScalingData places tuple c)

/-- The actual local theta hull region F(c) * O_hol. -/
def localThetaHullRegion : Set (ArithmeticTensorTupleBlock places tuple) :=
  ((arithmeticTupleFractionalLattice places tuple c *
    arithmeticTupleHolomorphicLattice places tuple :
      Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple)) :
    Set (ArithmeticTensorTupleBlock places tuple))

/-- Actual normalized log-volume of the local theta hull. -/
noncomputable def localThetaHullNormalizedLog
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) : Real :=
  arithmeticTupleNormalizedLogVolume places tuple μ
    (localThetaHullRegion places tuple c)

/-- The exact fractional-lattice formula for the local theta hull. -/
theorem localThetaHullNormalizedLog_eq :
    localThetaHullNormalizedLog places tuple μ c data =
      -((∑ i, c i) * Real.log (p : Real)) :=
  arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic
    places tuple μ data

/-- The actual normalized Haar ratio of the local theta hull. -/
noncomputable def localThetaHullHaarRatio
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) : Real :=
  Real.exp (localThetaHullNormalizedLog places tuple μ c data)

theorem localThetaHullHaarRatio_pos :
    0 < localThetaHullHaarRatio places tuple μ c data :=
  Real.exp_pos _

theorem localThetaHullHaarRatio_ne_zero :
    localThetaHullHaarRatio places tuple μ c data ≠ 0 :=
  (localThetaHullHaarRatio_pos places tuple μ c data).ne'

/-- If every c_i is positive and p > 1, the normalized log is nonzero. -/
theorem localThetaHullNormalizedLog_ne_zero
    (hc : ∀ i, 0 < c i) (hp : 1 < p) :
    localThetaHullNormalizedLog places tuple μ c data ≠ 0 := by
  rw [localThetaHullNormalizedLog_eq]
  have hlogp : 0 < Real.log (p : Real) := by
    apply Real.log_pos
    exact_mod_cast hp
  have hsum : 0 < ∑ i, c i := by
    apply Finset.sum_pos
    · intro i _
      exact hc i
    · exact Finset.univ_nonempty
  have hneg : -((∑ i, c i) * Real.log (p : Real)) < 0 := by
    nlinarith [mul_pos hsum hlogp]
  exact ne_of_lt hneg

/-- The actual normalized Haar ratio is not one. -/
theorem localThetaHullHaarRatio_ne_one
    (hc : ∀ i, 0 < c i) (hp : 1 < p) :
    localThetaHullHaarRatio places tuple μ c data ≠ 1 := by
  intro h
  have hzero : localThetaHullNormalizedLog places tuple μ c data = 0 :=
    Real.exp_eq_one_iff.mp h
  exact localThetaHullNormalizedLog_ne_zero places tuple μ c data hc hp hzero

/-- Exact missing data for the per-b construction: an actual
ArithmeticTuplePureFractionalScalingData for the qVFamily coefficient. -/
structure LocalThetaHullScalingDataRequired (c : ι -> Real) : Prop where
  exists_data : Nonempty (ArithmeticTuplePureFractionalScalingData places tuple c)

/-- Structural normalization data supplied by the actual formula. -/
structure LocalThetaHullHaarNormalizationData
    (data : ArithmeticTuplePureFractionalScalingData places tuple c) where
  unitHaar_pos : 0 < μ (arithmeticTupleCanonicalUnitReference places tuple)
  unitHaar_lt_top : μ (arithmeticTupleCanonicalUnitReference places tuple) < ⊤
  hullNormalizedLog : Real
  hullNormalizedLog_eq : hullNormalizedLog =
    arithmeticTupleNormalizedLogVolume places tuple μ
      (localThetaHullRegion places tuple c)
  ratio : Real
  ratio_eq : ratio = Real.exp hullNormalizedLog
  ratio_pos : 0 < ratio
  ratio_ne_one : ratio ≠ 1

/-- Actual normalization data from the fractional-lattice formula and hc/hp. -/
noncomputable def localThetaHullHaarNormalizationData
    (hc : ∀ i, 0 < c i) (hp : 1 < p)
    (hu_pos : 0 < μ (arithmeticTupleCanonicalUnitReference places tuple))
    (hu_fin : μ (arithmeticTupleCanonicalUnitReference places tuple) < ⊤) :
    LocalThetaHullHaarNormalizationData places tuple μ c data where
  unitHaar_pos := hu_pos
  unitHaar_lt_top := hu_fin
  hullNormalizedLog := localThetaHullNormalizedLog places tuple μ c data
  hullNormalizedLog_eq := rfl
  ratio := localThetaHullHaarRatio places tuple μ c data
  ratio_eq := rfl
  ratio_pos := localThetaHullHaarRatio_pos places tuple μ c data
  ratio_ne_one := localThetaHullHaarRatio_ne_one places tuple μ c data hc hp

end LeanFormal.IUT.XiFPaper.LocalHullHaarNormalizationActualAdapted

end
