import tmp.sheaf.xif.paper.S799LeastLambdaOPaperTargetActual
import tmp.sheaf.xif.paper.RootHullMeasureActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly

/-! # S814: non-Archimedean value-group skeleton / Tate-period computation of
the least lambda*O paper hull

The paper Theta side of Cor 3.12 is the degree-normalized Haar log-volume of
the *least* lambda*O hull (S793), not of the old union/closure hull.  This file
upgrades the Task-I "skeleton length is auxiliary" verdict to an exact
computation, in the only sense that is actually true in the tree:

1. In the non-Archimedean local factor the least lambda*O hull at exponent c is
   the norm ball F c = {x | ||x|| <= p^(-c)}; under the value-group
   identification it is exactly the segment [c, infinity) of the skeleton of the
   local valuation.  The additive p-log skeleton length of that segment is
   valueGroupSkeletonLength c = c * log p.

2. The q-pilot itself is a Tate-period length: the local q has exponential order
   ord, the Tate skeleton R / ord Z has length ord * log p, and the q-pilot
   region F ord has *actual* normalized Haar log - ord * log p (the exact
   generator p^ord supplies the value-group data).  This gives the concrete
   Tate-period identity paperSkeletonQPilotLog = - valueGroupSkeletonLength ord.

3. The least hull at the paper coefficient c_root = ord/(2 l) contains the
   q-pilot ball because c_root <= ord; monotonicity of the normalized log then
   gives the paper inequality

     paperSkeletonQPilotLog <= paperLeastLambdaOHullLog

   *unconditionally* (no fractional-scaling-data hypothesis).  This is the
   skeleton-length-to-hull comparison: the q-pilot skeleton length bounds the
   Theta-hull log.

4. Exact hull computation and the quantization phenomenon: if some exponent
   vector c' realizes the same fractional lattice, F c' = F c_root, and admits
   exact local generators, then the hull log is exactly - sum c' * log p.  This
   includes the value-group ceiling of c_root; it also shows that if such a c'
   is strictly larger than c_root coordinatewise, the naive formula
   - sum c_root * log p is *false* and the true hull log is strictly smaller.
   In the finite root extension L = K(q[2u]) (S782) the coefficient c_root is
   realized by the actual root, so the ceiling is exact there; the base
   completion sees only the quantized value.  The transport to the finite
   root-stack carrier remains the exact bridge recorded in S812.

No fake hull, no surrogate measure, no target change.  No sorry/axiom/True/
PUnit. -/

noncomputable section
open scoped BigOperators Pointwise
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S814SkeletonQuantizedLeastHullActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.UnitSmulCanonicalUnitReferenceActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [forall b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [forall b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-! ## 1. The additive skeleton length functional -/

/-- Additive p-log length of the value-group segment [0, c]: the Tate-period
normalization of the local skeleton. -/
noncomputable def valueGroupSkeletonLength (c : Real) : Real :=
  c * Real.log (qVFamTensorP T b : Real)

/-! ## 2. The q-pilot Tate period: region, log, and skeleton length -/

/-- The paper q-pilot exponent at b: the exponential order of the local q_v,
i.e. the length v(q) of the Tate skeleton circle in p-log units. -/
noncomputable def paperQPilotExponentFamily : qVFamTensorV -> Real :=
  fun _ => ((qVFamily T b).order : Real)

theorem paperQPilotExponentFamily_nonneg (i : qVFamTensorV) :
    0 <= paperQPilotExponentFamily T b i := by
  unfold paperQPilotExponentFamily
  exact Nat.cast_nonneg _

/-- The paper coefficient is at most the q-pilot exponent; this is exactly
ord/(2l) <= ord and is the coefficient form of the corollary's 2l-root factor. -/
theorem paperRootCoefficientFamily_le_qPilot (i : qVFamTensorV) :
    paperRootCoefficientFamily T b i <= paperQPilotExponentFamily T b i := by
  unfold paperRootCoefficientFamily qVFamPaperRootCoefficient paperQPilotExponentFamily
  have h2l : (1 : Real) <= 2 * (l.value : Real) := by
    have : (5 : Real) <= l.value := by exact_mod_cast l.ge_five
    nlinarith
  have hpos : 0 < 2 * (l.value : Real) := by positivity
  have ho : 0 <= ((qVFamily T b).order : Real) := Nat.cast_nonneg _
  calc ((qVFamily T b).order : Real) / (2 * (l.value : Real)) <=
        ((qVFamily T b).order : Real) / 1 :=
        div_le_div_of_nonneg_left ho zero_lt_one h2l
    _ = ((qVFamily T b).order : Real) := by ring

/-- An exact local generator at the q-pilot exponent: the integral power p^ord
of the local prime has normalized norm p^(-ord). -/
noncomputable def paperQPilotGenerator (i : qVFamTensorV) :
    CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)) :=
  (qVFamTensorP T b : CommonPrimeCompletion
      ((qVFamTensorPlaces T b) i (qVFamTensorTuple i))) ^ ((qVFamily T b).order : Int)

theorem paperQPilotGenerator_norm (i : qVFamTensorV) :
    ‖paperQPilotGenerator T b i‖ =
      (qVFamTensorP T b : Real) ^ (-(paperQPilotExponentFamily T b i)) := by
  unfold paperQPilotGenerator paperQPilotExponentFamily
  rw [norm_prime_zpow_commonPrimeCompletion, Padic.norm_p, inv_zpow']
  rw [← Real.rpow_intCast]
  congr 1
  push_cast
  ring

/-- The q-pilot region: the norm ball F(ord) * O_hol at the Tate-period length
ord. -/
noncomputable def paperSkeletonQPilotRegion : Set (qVFamTensorBlock T b) :=
  paperLambdaORegion (l := l) T b (paperQPilotExponentFamily T b)

/-- The exact value-group scaling data at the q-pilot exponent. -/
noncomputable def paperQPilotScalingData :
    ArithmeticTuplePureFractionalScalingData (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperQPilotExponentFamily T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator (qVFamTensorPlaces T b)
    qVFamTensorTuple (paperQPilotExponentFamily T b)
    (paperQPilotGenerator T b) (paperQPilotGenerator_norm T b)

/-- The q-pilot region is a unit translate of the canonical unit reference;
hence it has positive finite Haar mass for every additive Haar measure. -/
theorem paperSkeletonQPilotRegion_measure_pos_lt_top
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    0 < mu (paperSkeletonQPilotRegion T b) ∧
      mu (paperSkeletonQPilotRegion T b) < ⊤ := by
  have hset : paperSkeletonQPilotRegion T b =
      (((arithmeticTupleFractionalGeneratorUnit (qVFamTensorPlaces T b)
          qVFamTensorTuple (paperQPilotScalingData T b)) : qVFamTensorBlock T b) •
        arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b)
          qVFamTensorTuple) := by
    unfold paperSkeletonQPilotRegion paperLambdaORegion
    rw [arithmeticTupleFractionalLattice_mul_holomorphic_eq_pureGenerator_smul
      (qVFamTensorPlaces T b) qVFamTensorTuple (paperQPilotScalingData T b)]
    rw [arithmeticTupleFractionalGeneratorUnit_coe]
  rw [hset]
  exact measure_unit_smul_canonicalUnitReference_pos_lt_top (p := qVFamTensorP T b)
    (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (arithmeticTupleFractionalGeneratorUnit (qVFamTensorPlaces T b)
      qVFamTensorTuple (paperQPilotScalingData T b))

/-- The q-pilot normalized log, read off the actual Haar measure of the ball. -/
noncomputable def paperSkeletonQPilotLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] : Real :=
  arithmeticTupleNormalizedLogVolume (qVFamTensorPlaces T b) qVFamTensorTuple mu
    (paperSkeletonQPilotRegion T b)

/-- Exact Tate-period computation: the q-pilot ball has normalized Haar log
- ord * log p, the negative skeleton length of the local q. -/
theorem paperSkeletonQPilotLog_eq
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    paperSkeletonQPilotLog (l := l) T b mu =
      -(((qVFamily T b).order : Real) * Real.log (qVFamTensorP T b : Real)) := by
  unfold paperSkeletonQPilotLog paperSkeletonQPilotRegion paperLambdaORegion
  rw [arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
    (qVFamTensorPlaces T b) qVFamTensorTuple mu (paperQPilotExponentFamily T b)
    (paperQPilotGenerator T b) (paperQPilotGenerator_norm T b)]
  rw [show (∑ i, paperQPilotExponentFamily T b i) = ((qVFamily T b).order : Real) by
    simp [paperQPilotExponentFamily]]

/-- The same identity in skeleton-length form. -/
theorem paperSkeletonQPilotLog_eq_neg_valueGroupSkeletonLength
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    paperSkeletonQPilotLog (l := l) T b mu =
      - valueGroupSkeletonLength (l := l) T b ((qVFamily T b).order : Real) := by
  rw [paperSkeletonQPilotLog_eq]
  unfold valueGroupSkeletonLength
  rfl

/-! ## 3. The least hull lies in the canonical unit reference and has finite
Haar mass; its log is at most 0. -/

theorem paperLeastLambdaOHull_subset_holomorphic :
    paperLeastLambdaOHull (l := l) T b ⊆
      arithmeticTupleCanonicalUnitReference (qVFamTensorPlaces T b) qVFamTensorTuple := by
  rw [paperLeastLambdaOHull_eq_minimal]
  intro x hx
  unfold paperLambdaORegion at hx
  have hle : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b) <=
      arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
    arithmeticTupleFractionalLattice_le_valuationInteger (qVFamTensorPlaces T b)
      qVFamTensorTuple (fun i => paperRootCoefficientFamily_nonneg_local (l := l) T b i)
  have hmul : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b) *
        arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple <=
      arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple := by
    calc arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
          (paperRootCoefficientFamily T b) *
          arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        <= arithmeticTupleValuationIntegerLattice (qVFamTensorPlaces T b) qVFamTensorTuple *
          arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
          mul_le_mul' hle le_rfl
      _ = arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b) qVFamTensorTuple :=
          arithmeticTupleValuationIntegerLattice_mul_holomorphicLattice
            (qVFamTensorPlaces T b) qVFamTensorTuple
  have hx' : x ∈ (arithmeticTupleHolomorphicLattice (qVFamTensorPlaces T b)
      qVFamTensorTuple : Set (qVFamTensorBlock T b)) := hmul hx
  rw [← coefficient_arithmeticTupleHolomorphicLattice]
  exact hx'

theorem paperLeastLambdaOHull_measure_lt_top
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    mu (paperLeastLambdaOHull (l := l) T b) < ⊤ :=
  lt_of_le_of_lt (measure_mono (paperLeastLambdaOHull_subset_holomorphic (l := l) T b))
    ((isCompact_arithmeticTupleCanonicalRegions (qVFamTensorPlaces T b)
      qVFamTensorTuple).2.measure_lt_top)

/-! ## 4. The skeleton-length-to-hull comparison -/

/-- The q-pilot ball is contained in the least lambda*O hull at the paper
coefficient ord/(2l). -/
theorem paperSkeletonQPilotRegion_subset_leastHull :
    paperSkeletonQPilotRegion T b ⊆ paperLeastLambdaOHull (l := l) T b := by
  rw [paperLeastLambdaOHull_eq_minimal]
  intro x hx
  unfold paperSkeletonQPilotRegion at hx
  unfold paperLambdaORegion at hx ⊢
  have hmono : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple (paperQPilotExponentFamily T b) <=
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b) :=
    arithmeticTupleFractionalLattice_mono (qVFamTensorPlaces T b) qVFamTensorTuple
      (fun i => paperRootCoefficientFamily_le_qPilot (l := l) T b i)
  exact (mul_le_mul' hmono le_rfl) hx

theorem paperLeastLambdaOHull_measure_pos
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    0 < mu (paperLeastLambdaOHull (l := l) T b) :=
  lt_of_lt_of_le (paperSkeletonQPilotRegion_measure_pos_lt_top (l := l) T b mu).1
    (measure_mono (paperSkeletonQPilotRegion_subset_leastHull (l := l) T b))

/-- **Skeleton length vs. least hull.**  The negative q-pilot Tate-period length
is bounded by the normalized Haar log of the least lambda*O paper hull.  This is
the paper inequality -|log q| <= -|log Theta| on the least-hull carrier, with
the q-pilot coefficient ord and the Theta coefficient ord/(2l).  It requires
no fractional-scaling-data hypothesis. -/
theorem paperSkeletonQPilotLog_le_paperLeastLambdaOHullLog
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    paperSkeletonQPilotLog (l := l) T b mu <=
      paperLeastLambdaOHullLog (l := l) T b mu := by
  unfold paperSkeletonQPilotLog paperLeastLambdaOHullLog
  exact arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (paperSkeletonQPilotRegion_subset_leastHull (l := l) T b)
    (paperSkeletonQPilotRegion_measure_pos_lt_top (l := l) T b mu).1
    (paperLeastLambdaOHull_measure_lt_top (l := l) T b mu)

/-- Companion bound: the least hull is contained in the canonical unit
reference, so its normalized log is at most 0. -/
theorem paperLeastLambdaOHullLog_le_zero
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu] :
    paperLeastLambdaOHullLog (l := l) T b mu <= 0 := by
  unfold paperLeastLambdaOHullLog
  rw [← arithmeticTupleNormalizedLogVolume_canonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple mu]
  exact arithmeticTupleNormalizedLogVolume_mono (qVFamTensorPlaces T b)
    qVFamTensorTuple mu (paperLeastLambdaOHull_subset_holomorphic (l := l) T b)
    (paperLeastLambdaOHull_measure_pos (l := l) T b mu)
    ((isCompact_arithmeticTupleCanonicalRegions (qVFamTensorPlaces T b)
      qVFamTensorTuple).2.measure_lt_top)

/-! ## 5. Exact hull computation: quantization invariance

The hull log depends only on the fractional lattice, not on the chosen exponent.
Any exponent vector with the same norm-ball lattice and an exact local generator
computes the hull log.  This covers the value-group ceiling of the paper
coefficient; in the finite root extension it covers the actual root exponent. -/

theorem paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (c' : qVFamTensorV -> Real)
    (hball : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple c' =
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b))
    (g : (i : qVFamTensorV) ->
      CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
    (hg : forall i, ‖g i‖ = (qVFamTensorP T b : Real) ^ (-(c' i))) :
    paperLeastLambdaOHullLog (l := l) T b mu =
      -((∑ i, c' i) * Real.log (qVFamTensorP T b : Real)) := by
  unfold paperLeastLambdaOHullLog
  rw [paperLeastLambdaOHull_eq_minimal]
  unfold paperLambdaORegion
  rw [← hball]
  exact arithmeticTupleNormalizedLogVolume_fractionalLattice_mul_holomorphic_of_generator
    (qVFamTensorPlaces T b) qVFamTensorTuple mu c' g hg

/-- **Strict quantization defect.**  If the paper coefficient's ball is already
the ball at a strictly larger exponent vector which admits exact generators,
then the naive value - sum c_root * log p is not attained: the actual hull log
is strictly smaller.  This is the exact sense in which the coefficient formula
holds only after the value group realizes c_root (the root-stack/extension
step). -/
theorem paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization
    (mu : Measure (qVFamTensorBlock T b)) [Measure.IsAddHaarMeasure mu]
    (c' : qVFamTensorV -> Real)
    (hball : arithmeticTupleFractionalLattice (qVFamTensorPlaces T b)
        qVFamTensorTuple c' =
      arithmeticTupleFractionalLattice (qVFamTensorPlaces T b) qVFamTensorTuple
        (paperRootCoefficientFamily T b))
    (hstrict : forall i, paperRootCoefficientFamily T b i < c' i)
    (g : (i : qVFamTensorV) ->
      CommonPrimeCompletion ((qVFamTensorPlaces T b) i (qVFamTensorTuple i)))
    (hg : forall i, ‖g i‖ = (qVFamTensorP T b : Real) ^ (-(c' i))) :
    paperLeastLambdaOHullLog (l := l) T b mu <
      -((∑ i, paperRootCoefficientFamily T b i) *
        Real.log (qVFamTensorP T b : Real)) := by
  rw [paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator
    (l := l) T b mu c' hball g hg]
  have hsum : (∑ i, paperRootCoefficientFamily T b i) < (∑ i, c' i) := by
    apply Finset.sum_lt_sum
    · intro i _
      exact (hstrict i).le
    · exact ⟨(), Finset.mem_univ _, hstrict ()⟩
  have hlog : 0 < Real.log (qVFamTensorP T b : Real) :=
    Real.log_pos (by exact_mod_cast (Fact.out (p := Nat.Prime (qVFamTensorP T b))).one_lt)
  have hmul : (∑ i, paperRootCoefficientFamily T b i) *
        Real.log (qVFamTensorP T b : Real) <
      (∑ i, c' i) * Real.log (qVFamTensorP T b : Real) :=
    mul_lt_mul_of_pos_right hsum hlog
  linarith

#check paperSkeletonQPilotLog_le_paperLeastLambdaOHullLog
#check paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator
#check paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization
#print axioms paperSkeletonQPilotLog_eq
#print axioms paperSkeletonQPilotLog_le_paperLeastLambdaOHullLog
#print axioms paperLeastLambdaOHullLog_eq_neg_sum_of_quantized_generator
#print axioms paperLeastLambdaOHullLog_lt_neg_sum_of_strict_quantization

end LeanFormal.IUT.XiFPaper.S814SkeletonQuantizedLeastHullActual

end
