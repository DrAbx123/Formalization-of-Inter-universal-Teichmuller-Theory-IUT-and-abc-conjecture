import tmp.sheaf.xif.paper.HaarSignedAverageProof
import tmp.sheaf.xif.paper.S1904ProcessionBridgeActual
import Mathlib

/-!
# S1916: the actual arithmetic Haar signed-average identity and its exact missing

S1904 reduced the paper's procession bridge (IUT III, Step (xi-d)/(xi-e)) to the
signed unit-factor identity HaarSignedAverageProof.SignedUnitFactorThetaComparison:

  arithmeticTupleHullUnitLogVolume places tuple
    + Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal
  = (c3ThetaSignedProcession C3).average.

This file does not assume that identity.  It proves:

1. the identity is exactly the statement that the actual canonical-hull Haar
   mass is exp (signed average) (so the unit-factor form is only the
   decomposition of Real.log (mu canonicalHull).toReal);
2. the identity is not invariant under scaling mu by a positive finite
   ENNReal: for every mu and C3 there is a unique normalization scalar that
   makes it true, and every other scalar makes it false;
3. consequently the identity is not a consequence of the in-tree Haar
   interface for an arbitrary additive Haar measure.  The exact first missing
   is the source-selected normalization
   mu canonicalHull = ofReal (exp (signed average)), equivalently the unique
   positive scaling of the actual arithmetic Haar measure;
4. if a theta hull T and a determinant P have the same hull readout and
   procession average as the C6 data, the identity implies S1904's
   S1904FirstMissing T P; conversely S1904's bridge plus nonnegativity of the
   two real readouts gives the identity.

No sorry, admit, axiom, True, PUnit, or arbitrary inhabitant is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S1916HaarSignedAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.HaarSignedAverageProof
open LeanFormal.IUT.XiFPaper.S1904ProcessionBridgeActual
open LeanFormal.IUT.XiFPaperThetaHull
open MeasureTheory
open MeasureTheory.Measure
open scoped BigOperators

universe ua uv upi umon ui uX

variable {l : PrimeGeFive} {V : Type uv}
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
variable (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
variable (tuple : (i : iota) -> W i)
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
variable (mu : Measure (ArithmeticTensorTupleBlock places tuple))
variable [Measure.IsAddHaarMeasure mu]
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-! ## 1. The target and its Haar-mass form -/

/-- The S1916 target: exactly the S1904 first missing in its C6 arithmetic
Haar readout form. -/
def S1916FirstMissing : Prop :=
  SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3

/-- The same equation written at an arbitrary additive Haar measure.  This is
definitionally the body of SignedUnitFactorThetaComparison, but keeping it as
a separate def lets the scaling lemmas avoid any typeclass dependency on the
chosen measure. -/
def S1916EquationAt
    (nu : Measure (ArithmeticTensorTupleBlock places tuple)) : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    (c3ThetaSignedProcession C3).average

/-- The named first missing is the target comparison at the given mu. -/
theorem s1916_firstMissing_iff_comparison :
    S1916FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 ↔
      SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 :=
  Iff.rfl

/-- The target comparison is the equation at mu. -/
theorem s1916_firstMissing_iff_equationAt :
    S1916FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 ↔
      S1916EquationAt (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 mu :=
  Iff.rfl

/-- The unit-factor identity is just the logarithm of the actual hull mass.
The unit-reference term is not an independent normalization: it cancels the
relative unit factor and leaves the Haar log of the canonical hull. -/
theorem s1916_comparison_iff_hullLog :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 ↔
      Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (c3ThetaSignedProcession C3).average := by
  change arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
        (c3ThetaSignedProcession C3).average ↔
      Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (c3ThetaSignedProcession C3).average
  rw [arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) mu]

/-- The comparison is equivalent to the concrete normalization of the actual
canonical-hull Haar mass. -/
theorem s1916_comparison_iff_hull_measure_exp :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 ↔
      mu (arithmeticTupleCanonicalHull places tuple) =
        ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average)) := by
  rw [s1916_comparison_iff_hullLog (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3]
  have hpos : 0 < mu (arithmeticTupleCanonicalHull places tuple) :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.1
  have hfin : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  constructor
  · intro h
    have h_exp := congrArg Real.exp h
    rw [Real.exp_log (ENNReal.toReal_pos hpos.ne' hfin.ne)] at h_exp
    rw [← ENNReal.ofReal_toReal hfin.ne, h_exp]
  · intro h
    have hx : (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
        Real.exp ((c3ThetaSignedProcession C3).average) := by
      rw [h, ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))]
    rw [hx, Real.log_exp]

/-- The first missing stated as the explicit Haar normalization equation. -/
theorem s1916_firstMissing_iff_haarHull_measure_exp :
    S1916FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 ↔
      mu (arithmeticTupleCanonicalHull places tuple) =
        ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average)) := by
  rw [s1916_firstMissing_iff_comparison (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3]
  exact s1916_comparison_iff_hull_measure_exp (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) mu C3

/-! ## 2. The equation at an arbitrary additive Haar measure -/

/-- The equation at an arbitrary additive Haar measure is the log of its
canonical-hull mass. -/
theorem s1916_equationAt_iff_hullLog
    (nu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure nu] :
    S1916EquationAt (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 nu ↔
      Real.log (nu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (c3ThetaSignedProcession C3).average := by
  change arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (nu (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
        (c3ThetaSignedProcession C3).average ↔
      Real.log (nu (arithmeticTupleCanonicalHull places tuple)).toReal =
        (c3ThetaSignedProcession C3).average
  rw [arithmeticTupleIQHullLogVolumeInterface_hull_logVolume_toReal
    (places := places) (tuple := tuple) nu]

/-! ## 3. Scaling of the additive Haar measure -/

/-- Scaling an additive Haar measure by a positive finite ENNReal adds the
logarithm of the scalar to the real logarithm of every positive finite region. -/
theorem s1916_log_smul_apply
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (S : Set (ArithmeticTensorTupleBlock places tuple))
    (hS0 : mu S ≠ 0) (hSfin : mu S ≠ ⊤) :
    Real.log (((c • mu) S).toReal) =
      Real.log c.toReal + Real.log ((mu S).toReal) := by
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul]
  exact Real.log_mul (ENNReal.toReal_pos hc0 hct).ne'
    (ENNReal.toReal_pos hS0 hSfin).ne'

/-- Scaling by a positive finite scalar shifts the unit-reference logarithm
additively. -/
theorem s1916_log_smul_reference
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    Real.log (((c • mu) (arithmeticTupleCanonicalUnitReference places tuple)).toReal) =
      Real.log c.toReal +
        Real.log ((mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal) := by
  exact s1916_log_smul_apply (places := places) (tuple := tuple) (mu := mu) c hc0 hct _
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.1.ne'
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).2.2.ne

/-- Scaling by a positive finite scalar shifts the canonical-hull logarithm
additively. -/
theorem s1916_log_smul_hull
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    Real.log (((c • mu) (arithmeticTupleCanonicalHull places tuple)).toReal) =
      Real.log c.toReal +
        Real.log ((mu (arithmeticTupleCanonicalHull places tuple)).toReal) := by
  exact s1916_log_smul_apply (places := places) (tuple := tuple) (mu := mu) c hc0 hct _
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.1.ne'
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2.ne

/-- The equation after scaling mu by c is the original equation with log c
added. -/
theorem s1916_equationAt_smul_iff
    (c : ENNReal) (hc0 : c ≠ 0) (hct : c ≠ ⊤) :
    S1916EquationAt (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 (c • mu) ↔
      arithmeticTupleHullUnitLogVolume places tuple +
          (Real.log ((mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal) +
            Real.log c.toReal) =
        (c3ThetaSignedProcession C3).average := by
  change arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (((c • mu) (arithmeticTupleCanonicalUnitReference places tuple)).toReal) =
        (c3ThetaSignedProcession C3).average ↔
      arithmeticTupleHullUnitLogVolume places tuple +
          (Real.log ((mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal) +
            Real.log c.toReal) =
        (c3ThetaSignedProcession C3).average
  rw [s1916_log_smul_reference (places := places) (tuple := tuple) (mu := mu) c hc0 hct]
  constructor <;> intro h <;> linarith

/-! ## 4. The unique normalizing scalar -/

/-- ENNReal.ofReal (exp a), the positive finite scalar with logarithm a. -/
noncomputable def s1916ExpScalar (a : Real) : ENNReal :=
  ENNReal.ofReal (Real.exp a)

theorem s1916ExpScalar_ne_zero (a : Real) : s1916ExpScalar a ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos a)).ne'

theorem s1916ExpScalar_ne_top (a : Real) : s1916ExpScalar a ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem s1916ExpScalar_toReal (a : Real) :
    (s1916ExpScalar a).toReal = Real.exp a :=
  ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos a))

theorem s1916ExpScalar_log (a : Real) :
    Real.log (s1916ExpScalar a).toReal = a := by
  rw [s1916ExpScalar_toReal, Real.log_exp]

/-- The positive scalar that makes the actual canonical-hull mass equal exp a. -/
noncomputable def s1916NormalizingScalar (a : Real) : ENNReal :=
  ENNReal.ofReal
    (Real.exp (a - Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal))

theorem s1916NormalizingScalar_ne_zero (a : Real) :
    s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a ≠ 0 :=
  (ENNReal.ofReal_pos.mpr (Real.exp_pos _)).ne'

theorem s1916NormalizingScalar_ne_top (a : Real) :
    s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a ≠ ⊤ :=
  ENNReal.ofReal_ne_top

theorem s1916NormalizingScalar_toReal (a : Real) :
    (s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a).toReal =
      Real.exp (a - Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal) :=
  ENNReal.toReal_ofReal (le_of_lt (Real.exp_pos _))

/-- The normalized measure has canonical-hull mass exp a. -/
theorem s1916NormalizingScalar_hull_toReal (a : Real) :
    ((s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a • mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal = Real.exp a := by
  have hpos : 0 < mu (arithmeticTupleCanonicalHull places tuple) :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.1
  have hfin : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  rw [Measure.smul_apply, smul_eq_mul, ENNReal.toReal_mul,
    s1916NormalizingScalar_toReal]
  set x : Real := (mu (arithmeticTupleCanonicalHull places tuple)).toReal with hx
  have hxpos : 0 < x := ENNReal.toReal_pos hpos.ne' hfin.ne
  rw [Real.exp_sub, Real.exp_log hxpos]
  field_simp [ne_of_gt hxpos]

/-- The logarithm of the normalized canonical-hull mass is a. -/
theorem s1916NormalizingScalar_hull_log (a : Real) :
    Real.log (((s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a • mu)
        (arithmeticTupleCanonicalHull places tuple)).toReal) = a := by
  rw [s1916NormalizingScalar_hull_toReal (places := places) (tuple := tuple)
    (mu := mu) a, Real.log_exp]

/-- At the normalizing scalar, the equation is equivalent to the signed
average being a. -/
theorem s1916_equationAt_at_normalizingScalar (a : Real) :
    S1916EquationAt (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3
        (s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a • mu) ↔
      (c3ThetaSignedProcession C3).average = a := by
  haveI : Measure.IsAddHaarMeasure
      (s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a • mu) :=
    IsAddHaarMeasure.smul mu (s1916NormalizingScalar_ne_zero (places := places)
      (tuple := tuple) (mu := mu) a) (s1916NormalizingScalar_ne_top (places := places)
      (tuple := tuple) (mu := mu) a)
  rw [s1916_equationAt_iff_hullLog (places := places) (tuple := tuple) C3
    (s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a • mu)]
  rw [s1916NormalizingScalar_hull_log (places := places) (tuple := tuple) (mu := mu) a]
  exact eq_comm

include mu

/-- There is an additive Haar measure satisfying the equation: scale mu by the
unique normalizing scalar. -/
theorem s1916_exists_equationAt :
    ∃ nu : Measure (ArithmeticTensorTupleBlock places tuple),
      Measure.IsAddHaarMeasure nu ∧
        S1916EquationAt (l := l) (V := V) (I := I)
          (places := places) (tuple := tuple) C3 nu := by
  refine ⟨s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu)
      ((c3ThetaSignedProcession C3).average) • mu, ?_, ?_⟩
  · exact IsAddHaarMeasure.smul mu
      (s1916NormalizingScalar_ne_zero (places := places) (tuple := tuple) (mu := mu) _)
      (s1916NormalizingScalar_ne_top (places := places) (tuple := tuple) (mu := mu) _)
  · exact (s1916_equationAt_at_normalizingScalar (places := places) (tuple := tuple)
      (mu := mu) C3 ((c3ThetaSignedProcession C3).average)).mpr rfl

/-- If an additive Haar measure satisfies the equation, its scalar relative to
mu is the normalizing scalar: the equation determines the Haar normalization
uniquely. -/
theorem s1916_normalizingScalar_unique
    {c : ENNReal} (hc0 : c ≠ 0) (hct : c ≠ ⊤)
    (h : S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 (c • mu)) :
    c = s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu)
      ((c3ThetaSignedProcession C3).average) := by
  haveI : Measure.IsAddHaarMeasure (c • mu) := IsAddHaarMeasure.smul mu hc0 hct
  have hhull : Real.log (((c • mu) (arithmeticTupleCanonicalHull places tuple)).toReal) =
      (c3ThetaSignedProcession C3).average :=
    (s1916_equationAt_iff_hullLog (places := places) (tuple := tuple) C3 (c • mu)).mp h
  have hlog := s1916_log_smul_hull (places := places) (tuple := tuple) (mu := mu) c hc0 hct
  rw [hhull] at hlog
  have hlogc : Real.log c.toReal =
      (c3ThetaSignedProcession C3).average -
        Real.log ((mu (arithmeticTupleCanonicalHull places tuple)).toReal) := by
    linarith
  have hcpos : 0 < c.toReal := ENNReal.toReal_pos hc0 hct
  have hexp : c.toReal =
      Real.exp ((c3ThetaSignedProcession C3).average -
        Real.log ((mu (arithmeticTupleCanonicalHull places tuple)).toReal)) := by
    rw [← Real.exp_log hcpos, hlogc]
  calc
    c = ENNReal.ofReal c.toReal := (ENNReal.ofReal_toReal hct).symm
    _ = ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average -
          Real.log ((mu (arithmeticTupleCanonicalHull places tuple)).toReal))) := by
        rw [hexp]
    _ = s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu)
          ((c3ThetaSignedProcession C3).average) := rfl

/-- Scaling an equation that holds by exp 1 makes it false: the equation is
not invariant under the additive Haar rescaling. -/
theorem s1916_equationAt_shift_one_false
    (h : S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 mu) :
    ¬ S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 (s1916ExpScalar 1 • mu) := by
  intro h2
  have hlog := s1916_log_smul_reference (places := places) (tuple := tuple)
    (mu := mu) (s1916ExpScalar 1) (s1916ExpScalar_ne_zero 1) (s1916ExpScalar_ne_top 1)
  change arithmeticTupleHullUnitLogVolume places tuple +
      Real.log (((s1916ExpScalar 1 • mu)
        (arithmeticTupleCanonicalUnitReference places tuple)).toReal) =
      (c3ThetaSignedProcession C3).average at h2
  rw [hlog] at h2
  change arithmeticTupleHullUnitLogVolume places tuple +
      (Real.log (s1916ExpScalar 1).toReal +
        Real.log ((mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal)) =
      (c3ThetaSignedProcession C3).average at h2
  change arithmeticTupleHullUnitLogVolume places tuple +
      Real.log ((mu (arithmeticTupleCanonicalUnitReference places tuple)).toReal) =
      (c3ThetaSignedProcession C3).average at h
  have hc : Real.log (s1916ExpScalar 1).toReal = 0 := by linarith
  rw [s1916ExpScalar_log] at hc
  norm_num at hc

/-- The equation is not a consequence of the in-tree Haar interface: it is
false for some additive Haar measure (for every C3). -/
theorem s1916_not_forall_equationAt :
    ¬ ∀ nu : Measure (ArithmeticTensorTupleBlock places tuple),
        Measure.IsAddHaarMeasure nu →
          S1916EquationAt (l := l) (V := V) (I := I)
            (places := places) (tuple := tuple) C3 nu := by
  intro hall
  let a : Real := (c3ThetaSignedProcession C3).average
  let c : ENNReal := s1916NormalizingScalar (places := places) (tuple := tuple) (mu := mu) a
  have hcAdd : Measure.IsAddHaarMeasure (c • mu) :=
    IsAddHaarMeasure.smul mu
      (s1916NormalizingScalar_ne_zero (places := places) (tuple := tuple) (mu := mu) a)
      (s1916NormalizingScalar_ne_top (places := places) (tuple := tuple) (mu := mu) a)
  haveI : Measure.IsAddHaarMeasure (c • mu) := hcAdd
  have h0 : S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 (c • mu) :=
    (s1916_equationAt_at_normalizingScalar (places := places) (tuple := tuple)
      (mu := mu) C3 a).mpr rfl
  have hbad : ¬ S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 (s1916ExpScalar 1 • (c • mu)) :=
    s1916_equationAt_shift_one_false (places := places) (tuple := tuple)
      (mu := c • mu) (C3 := C3) h0
  have hshiftAdd : Measure.IsAddHaarMeasure (s1916ExpScalar 1 • (c • mu)) :=
    IsAddHaarMeasure.smul (c • mu) (s1916ExpScalar_ne_zero 1) (s1916ExpScalar_ne_top 1)
  exact hbad (hall (s1916ExpScalar 1 • (c • mu)) hshiftAdd)

/-- The exact first missing is a normalization, not an algebraic law.  It is
equivalent to the concrete Haar-mass equation, it is satisfiable by a unique
rescaling, and it is not forced by the arbitrary additive Haar measure. -/
theorem s1916_firstMissing_exact_content :
    (S1916FirstMissing (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) mu C3 ↔
      mu (arithmeticTupleCanonicalHull places tuple) =
        ENNReal.ofReal (Real.exp ((c3ThetaSignedProcession C3).average))) ∧
    (∃ nu : Measure (ArithmeticTensorTupleBlock places tuple),
      Measure.IsAddHaarMeasure nu ∧
        S1916EquationAt (l := l) (V := V) (I := I)
          (places := places) (tuple := tuple) C3 nu) ∧
    (¬ ∀ nu : Measure (ArithmeticTensorTupleBlock places tuple),
        Measure.IsAddHaarMeasure nu →
          S1916EquationAt (l := l) (V := V) (I := I)
            (places := places) (tuple := tuple) C3 nu) :=
  ⟨s1916_firstMissing_iff_haarHull_measure_exp (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) mu C3,
    s1916_exists_equationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (mu := mu) (C3 := C3),
    s1916_not_forall_equationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) (mu := mu) (C3 := C3)⟩

/-! ## 5. Connection to S1904 -/

/-- S1916 implies the S1904 first missing.  If a theta hull T has the actual
C6 canonical-hull Haar readout and a determinant P has the signed C3
procession average, then the S1916 comparison is exactly the S1904 procession
bridge at (T, P). -/
theorem s1916_comparison_implies_s1904
    {X : Type uX} [TopologicalSpace X]
    (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (hT : T.haar.logVolume T.compactHull.hull =
      haarLogVolume mu (arithmeticTupleCanonicalHull places tuple))
    (hP : P.procession.average = (c3ThetaSignedProcession C3).average)
    (hfactor : S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 mu) :
    S1904FirstMissing T P := by
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  have hreal : Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      (c3ThetaSignedProcession C3).average :=
    (s1916_equationAt_iff_hullLog (places := places) (tuple := tuple) C3 mu).mp hfactor
  unfold S1904FirstMissing S1904ProcessionBridge s1904HullLogVolume s1904ProcessionAverage
  rw [hT, hP, haarLogVolume_of_lt_top hmeasure, hreal]

/-- S1904 plus nonnegativity gives the S1916 identity.  This is the converse of
s1916_comparison_implies_s1904 under the two natural nonnegativity hypotheses
on the real readouts. -/
theorem s1904_implies_comparison_of_nonneg
    {X : Type uX} [TopologicalSpace X]
    (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (hT : T.haar.logVolume T.compactHull.hull =
      haarLogVolume mu (arithmeticTupleCanonicalHull places tuple))
    (hP : P.procession.average = (c3ThetaSignedProcession C3).average)
    (hbridge : S1904FirstMissing T P)
    (hlog : 0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal)
    (hnonneg : 0 <= (c3ThetaSignedProcession C3).average) :
    S1916EquationAt (l := l) (V := V) (I := I)
      (places := places) (tuple := tuple) C3 mu := by
  have hmeasure : mu (arithmeticTupleCanonicalHull places tuple) < ⊤ :=
    (measure_arithmeticTupleCanonicalRegions_pos_lt_top places tuple mu).1.2
  have hbridge' : T.haar.logVolume T.compactHull.hull =
      ENNReal.ofReal (c3ThetaSignedProcession C3).average := by
    simpa only [S1904FirstMissing, S1904ProcessionBridge, s1904HullLogVolume,
      s1904ProcessionAverage, hP] using hbridge
  have hof : ENNReal.ofReal
        (Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal) =
      ENNReal.ofReal (c3ThetaSignedProcession C3).average := by
    calc
      ENNReal.ofReal
          (Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal) =
          haarLogVolume mu (arithmeticTupleCanonicalHull places tuple) :=
        (haarLogVolume_of_lt_top hmeasure).symm
      _ = T.haar.logVolume T.compactHull.hull := hT.symm
      _ = ENNReal.ofReal (c3ThetaSignedProcession C3).average := hbridge'
  have hreal : Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal =
      (c3ThetaSignedProcession C3).average :=
    (ENNReal.ofReal_eq_ofReal_iff hlog hnonneg).mp hof
  exact (s1916_equationAt_iff_hullLog (places := places) (tuple := tuple) C3 mu).mpr hreal

/-- The exact relation to S1904.  Under the matching readout hypotheses and the
two nonnegativity hypotheses, the S1904 bridge at the C6 theta hull and
determinant is equivalent to the S1916 arithmetic identity. -/
theorem s1916_s1904_iff_of_nonneg
    {X : Type uX} [TopologicalSpace X]
    (T : ActualThetaHull X l)
    (P : SignedHullLogActual (SignedLabel l.value))
    (hT : T.haar.logVolume T.compactHull.hull =
      haarLogVolume mu (arithmeticTupleCanonicalHull places tuple))
    (hP : P.procession.average = (c3ThetaSignedProcession C3).average)
    (hlog : 0 <= Real.log (mu (arithmeticTupleCanonicalHull places tuple)).toReal)
    (hnonneg : 0 <= (c3ThetaSignedProcession C3).average) :
    S1904FirstMissing T P ↔
      S1916EquationAt (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple) C3 mu := by
  constructor
  · intro hbridge
    exact s1904_implies_comparison_of_nonneg (places := places) (tuple := tuple)
      (mu := mu) (C3 := C3) T P hT hP hbridge hlog hnonneg
  · intro hfactor
    exact s1916_comparison_implies_s1904 (places := places) (tuple := tuple)
      (mu := mu) (C3 := C3) T P hT hP hfactor

/-! ## 6. Axiom probes -/

#print axioms s1916_comparison_iff_hullLog
#print axioms s1916_comparison_iff_hull_measure_exp
#print axioms s1916_equationAt_at_normalizingScalar
#print axioms s1916_normalizingScalar_unique
#print axioms s1916_not_forall_equationAt
#print axioms s1916_comparison_implies_s1904
#print axioms s1904_implies_comparison_of_nonneg
#print axioms s1916_s1904_iff_of_nonneg

end LeanFormal.IUT.XiFPaper.S1916HaarSignedAverageActual

end
