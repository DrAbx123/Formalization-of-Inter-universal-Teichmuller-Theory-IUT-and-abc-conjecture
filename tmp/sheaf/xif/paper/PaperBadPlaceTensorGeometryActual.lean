import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceNormalizedUnitScalingLogVolume
import tmp.sheaf.xif.paper.PaperC3TensorGeometryActual
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Haar.Basic
import tmp.sheaf.xif.paper.CompletionValuedThetaHullMuLogActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import tmp.sheaf.xif.paper.RootHullMeasureActual

/-! # Nondegenerate bad-place/C3 tensor geometry (new model)

The new model does not use the concrete C3 q = 1/5 data.  It takes the actual
native bad places Bad (nativePlaceSelection T) as the source-place index and as
the C3 tensor index.  Each bad place b carries its own rational prime p_b and
its actual completion place (qVFamTensorPlaces T b).  This is the dependent-p
refinement of PaperC3TensorGeometryActual, which uses a fixed p.

The equivalence source places = bad places = C3 tensor index is the actual
identity equivalence; the tensor place map sends b to its own completion place.
No arbitrary equivalence, no q=1/5 object, no fake place identification.

No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open MeasureTheory
open LeanFormal.IUT.XiFPaper.CompletionValuedThetaHullMuLogActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.RootHullContainmentInequalityActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open LeanFormal.IUT.XiFPaper.RootNormalizedContainmentActual
open LeanFormal.IUT.XiFPaper.RootHullMeasureActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- A finite place together with its own rational primes. -/
structure DependentFinitePlace (K : Type u) [Field K] [NumberField K] where
  p : Nat
  [hp : Fact p.Prime]
  place : FinitePlaceAtPrime K p

attribute [instance] DependentFinitePlace.hp

/-- Dependent completion-valued source geometry: one place per source index. -/
structure DependentCompletionValuedGeometry (K : Type u) [Field K] [NumberField K] where
  index : Type
  [indexFintype : Fintype index]
  place : index → DependentFinitePlace K

attribute [instance] DependentCompletionValuedGeometry.indexFintype

/-- Actual dependent finite place of a native bad place. -/
noncomputable def badDependentPlace (b : Bad (nativePlaceSelection T)) :
    DependentFinitePlace T.arithmetic.F where
  p := qVFamTensorP T b
  place := qVFamTensorPlaces T b () (qVFamTensorTuple ())

/-- Actual bad-place geometry in the new model. -/
noncomputable def badPlaceGeometry :
    DependentCompletionValuedGeometry T.arithmetic.F where
  index := Bad (nativePlaceSelection T)
  place := badDependentPlace T

/-- The actual source-place index in the new model. -/
abbrev badSourcePlaceIndex : Type :=
  Bad (nativePlaceSelection T)

/-- The actual C3 tensor index in the new model. -/
abbrev badC3TensorIndex : Type :=
  Bad (nativePlaceSelection T)

/-- Actual source places = bad places equivalence. -/
def sourcePlaceEquiv : badSourcePlaceIndex T ≃ badSourcePlaceIndex T :=
  Equiv.refl _

/-- Actual bad places = C3 tensor index equivalence. -/
def c3TensorIndexEquiv : badC3TensorIndex T ≃ badSourcePlaceIndex T :=
  Equiv.refl _

/-- Actual tensor place index: one factor per bad place. -/
abbrev badTensorPlaceIndex : badC3TensorIndex T → Type := fun _ => Unit

/-- Actual tensor places: the bad place's own completion place. -/
noncomputable def badTensorPlaces (i : badC3TensorIndex T) (_ : Unit) :
    FinitePlaceAtPrime T.arithmetic.F (badDependentPlace T i).p :=
  (badPlaceGeometry T).place i |>.place

/-- Actual tensor tuple. -/
def badTensorTuple (i : badC3TensorIndex T) : badTensorPlaceIndex T i := ()

/-- Actual nondegenerate bad-place/C3 tensor geometry data. -/
structure PaperBadPlaceTensorGeometryData where
  tensorIndex : Type
  tensorFintype : Fintype tensorIndex
  tensorPlaceIndex : tensorIndex → Type
  tensorPlaces : (i : tensorIndex) → tensorPlaceIndex i →
    (p : Nat) × FinitePlaceAtPrime T.arithmetic.F p
  tensorTuple : (i : tensorIndex) → tensorPlaceIndex i
  sourcePlaceEquiv : badSourcePlaceIndex T ≃ badSourcePlaceIndex T
  c3TensorIndexEquiv : tensorIndex ≃ badSourcePlaceIndex T
  place_eq : ∀ (i : tensorIndex),
    tensorPlaces i (tensorTuple i) =
      ⟨(badDependentPlace T (c3TensorIndexEquiv i)).p,
        (badDependentPlace T (c3TensorIndexEquiv i)).place⟩

/-- The actual new-model tensor geometry, with identity index equivalences. -/
noncomputable def paperBadPlaceTensorGeometryData :
    PaperBadPlaceTensorGeometryData T where
  tensorIndex := badC3TensorIndex T
  tensorFintype := inferInstance
  tensorPlaceIndex := badTensorPlaceIndex T
  tensorPlaces := fun i _ =>
    ⟨(badDependentPlace T i).p, (badDependentPlace T i).place⟩
  tensorTuple := badTensorTuple T
  sourcePlaceEquiv := sourcePlaceEquiv T
  c3TensorIndexEquiv := c3TensorIndexEquiv T
  place_eq := fun _ => rfl



/-- The actual per-b qVFamily tensor block: the one-factor arithmetic tensor
block at the bad place's own completion and its own rational prime. -/
abbrev badPlaceTensorBlock (b : badC3TensorIndex T) : Type _ :=
  ArithmeticTensorTupleBlock
    (qVFamTensorPlaces T b) qVFamTensorTuple

/-! ## Per-b product carrier and product Haar / mu_log -/

/-- The dependent product carrier: one actual qVFamily tensor block per bad
place, each with its own rational prime p_b.  No single
ArithmeticTensorTupleBlock over varying p is used. -/
abbrev badPlaceProductCarrier : Type _ :=
  (b : badC3TensorIndex T) → badPlaceTensorBlock T b

/-- The actual product Haar measure: product of the actual Haar measures of the
per-b qVFamily tensor blocks. -/
noncomputable def badPlaceProductHaarMeasure
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)] :
    Measure (badPlaceProductCarrier T) :=
  Measure.pi (fun b => Measure.addHaar)

/-- The actual per-b product normalized log volume: sum of the per-block
arithmetic-tuple normalized log volumes. -/
noncomputable def badPlaceProductMuLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    (S : (b : badC3TensorIndex T) → Set (badPlaceTensorBlock T b)) : Real :=
  ∑ b : badC3TensorIndex T,
    arithmeticTupleNormalizedLogVolume
      (qVFamTensorPlaces T b) qVFamTensorTuple (μ b) (S b)

/-- The product mu_log is exactly the finite sum of the per-b mu_logs. -/
theorem badPlaceProductMuLog_eq_sum
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    (S : (b : badC3TensorIndex T) → Set (badPlaceTensorBlock T b)) :
    badPlaceProductMuLog T μ S =
      ∑ b : badC3TensorIndex T,
        arithmeticTupleNormalizedLogVolume
          (qVFamTensorPlaces T b) qVFamTensorTuple (μ b) (S b) := rfl

/-- The actual per-b product canonical unit reference set. -/
def badPlaceProductCanonicalUnitReference :
    Set (badPlaceProductCarrier T) :=
  {x | ∀ b, x b ∈ arithmeticTupleCanonicalUnitReference
    (qVFamTensorPlaces T b) qVFamTensorTuple}

/-- The product normalized log volume of the product canonical unit reference
is zero. -/
theorem badPlaceProductMuLog_canonicalUnitReference
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b)) :
    badPlaceProductMuLog T μ
        (fun b => arithmeticTupleCanonicalUnitReference
          (qVFamTensorPlaces T b) qVFamTensorTuple) = 0 := by
  unfold badPlaceProductMuLog
  simp [arithmeticTupleNormalizedLogVolume_canonicalUnitReference]

/-! ## Product root-coefficient completion hull and product mu_log -/

/-- Actual product root-coefficient completion hull: product of the per-b actual root hulls. -/
def badPlaceProductPaperRootCoefficientCompletionHull :
    Set (badPlaceProductCarrier T) :=
  {x | ∀ b, x b ∈ paperRootCoefficientCompletionHull (l := l) T b}

/-- Actual per-b root-coefficient completion hull normalized log-volume. -/
noncomputable def badPlacePerBThetaHullLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) : Real :=
  paperRootCoefficientCompletionHullNormalizedLog (l := l) T b (μ b)

/-- The product normalized log-volume: sum of the per-b root-coefficient completion hull
normalized log-volumes. -/
noncomputable def badPlaceProductThetaHullMuLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] : Real :=
  ∑ b : badC3TensorIndex T,
    badPlacePerBThetaHullLog T μ b

/-- The product mu_log is exactly the sum of the per-b normalized logs. -/
theorem badPlaceProductThetaHullMuLog_eq_sum
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    badPlaceProductThetaHullMuLog T μ =
      ∑ b : badC3TensorIndex T,
        badPlacePerBThetaHullLog T μ b := rfl

/-- The actual weighted global Theta hull log: weighted sum of per-b normalized
logs, with the actual nativeBadLocalWeight. -/
noncomputable def badPlaceWeightedThetaHullMuLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] : Real :=
  ∑ b : badC3TensorIndex T,
    nativeBadLocalWeight T b * badPlacePerBThetaHullLog T μ b

/-- The weighted log is exactly the sum_b weighted per-b normalized log. -/
theorem badPlaceWeightedThetaHullMuLog_eq_sum
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    badPlaceWeightedThetaHullMuLog T μ =
      ∑ b : badC3TensorIndex T,
        nativeBadLocalWeight T b * badPlacePerBThetaHullLog T μ b := rfl

/-- Per-b actual positivity of the root-coefficient completion hull measure. -/
theorem badPlacePaperRootCoefficientCompletionHull_measure_pos
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) :
    0 < μ b (paperRootCoefficientCompletionHull (l := l) T b) :=
  paperRootCoefficientCompletionHull_measure_pos (l := l) T b (μ b)

/-- Per-b actual finiteness of the root-coefficient completion hull measure. -/
theorem badPlacePaperRootCoefficientCompletionHull_measure_lt_top
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) :
    μ b (paperRootCoefficientCompletionHull (l := l) T b) < ⊤ :=
  paperRootCoefficientCompletionHull_measure_lt_top (l := l) T b (μ b)

/-! ## Product qPilot and global comparison -/

/-- Actual native bad-place weight is nonnegative. -/
theorem badPlaceNativeBadLocalWeight_nonneg
    (b : badC3TensorIndex T) :
    0 ≤ nativeBadLocalWeight T b := by
  unfold nativeBadLocalWeight localNormalizedWeight
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- A finite product of positive ENNReal factors is positive. -/
theorem badPlaceENNReal_finsetProd_pos {ι : Type*} [Fintype ι]
    (f : ι → ENNReal) (h : ∀ i, 0 < f i) :
    0 < ∏ i, f i := by
  classical
  rw [pos_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro i _
  exact ne_of_gt (h i)

/-- Actual per-b qPilot signed log from the root-normalized q-pilot region. -/
noncomputable def badPlacePerBQPilotSignedLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) : Real :=
  qPilotClassicalLog
    (qVFamTensorPlaces T b) qVFamTensorTuple (μ b)
    (rootNormCoefficient (l := l) T b)
    (rootNormScalingData (l := l) T b)

/-- Actual per-b root Theta hull log. -/
noncomputable def badPlacePerBThetaHullLogRoot
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) : Real :=
  rootThetaHullLog (l := l) (qVFamTensorPlaces T b) qVFamTensorTuple
    (μ b) (rootHalfCoefficient (l := l) T b)

/-- The paper hull log and the root Theta hull log agree definitionally. -/
theorem badPlacePerBThetaHullLogRoot_eq_paper
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) :
    badPlacePerBThetaHullLogRoot T μ b = badPlacePerBThetaHullLog T μ b := by
  unfold badPlacePerBThetaHullLogRoot badPlacePerBThetaHullLog
  rfl

/-- Actual per-b qPilot <= root Theta hull comparison. -/
theorem badPlacePerBQPilotLog_le_thetaHullLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)]
    (b : badC3TensorIndex T) :
    badPlacePerBQPilotSignedLog T μ b ≤
      badPlacePerBThetaHullLogRoot T μ b :=
  qPilotNormLog_le_rootNormHullLog (l := l) T b (μ b)
    (qPilotNormRegion_measure_pos_lt_top (l := l) T b (μ b)).1
    (rootNormHull_measure_lt_top (l := l) T b (μ b))

/-- The product qPilot signed log: sum of per-b qPilot signed logs. -/
noncomputable def badPlaceProductQPilotSignedLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] : Real :=
  ∑ b : badC3TensorIndex T, badPlacePerBQPilotSignedLog T μ b

/-- The weighted product qPilot signed log. -/
noncomputable def badPlaceWeightedProductQPilotSignedLog
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] : Real :=
  ∑ b : badC3TensorIndex T,
    nativeBadLocalWeight T b * badPlacePerBQPilotSignedLog T μ b

/-- The product qPilot signed log is exactly the sum of the per-b logs. -/
theorem badPlaceProductQPilotSignedLog_eq_sum
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    badPlaceProductQPilotSignedLog T μ =
      ∑ b : badC3TensorIndex T, badPlacePerBQPilotSignedLog T μ b := rfl

/-- Global weighted qPilot <= weighted Theta hull comparison. -/
theorem badPlaceWeightedQPilot_le_weightedThetaHull
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    badPlaceWeightedProductQPilotSignedLog T μ ≤
      badPlaceWeightedThetaHullMuLog T μ := by
  unfold badPlaceWeightedProductQPilotSignedLog badPlaceWeightedThetaHullMuLog
  apply Finset.sum_le_sum
  intro b _
  have hper := badPlacePerBQPilotLog_le_thetaHullLog T μ b
  rw [badPlacePerBThetaHullLogRoot_eq_paper T μ b] at hper
  exact mul_le_mul_of_nonneg_left hper (badPlaceNativeBadLocalWeight_nonneg T b)

/-- Product hull measure value: finite product of the per-b paper hull
measures.  This is the product-measure mass without choosing a single global
block. -/
noncomputable def badPlaceProductPaperRootCoefficientCompletionHullMeasure
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b)) : ENNReal :=
  ∏ b : badC3TensorIndex T, μ b (paperRootCoefficientCompletionHull (l := l) T b)

/-- The product hull measure is positive: finite product of the per-b positive
hull measures. -/
theorem badPlaceProductPaperRootCoefficientCompletionHullMeasure_pos
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    0 < badPlaceProductPaperRootCoefficientCompletionHullMeasure T μ := by
  unfold badPlaceProductPaperRootCoefficientCompletionHullMeasure
  exact badPlaceENNReal_finsetProd_pos _ (fun b => badPlacePaperRootCoefficientCompletionHull_measure_pos T μ b)

/-- The product hull measure is finite: finite product of the per-b finite hull
measures. -/
theorem badPlaceProductPaperRootCoefficientCompletionHullMeasure_lt_top
    [∀ b, MeasurableSpace (badPlaceTensorBlock T b)]
    [∀ b, BorelSpace (badPlaceTensorBlock T b)]
    (μ : (b : badC3TensorIndex T) → Measure (badPlaceTensorBlock T b))
    [∀ b, Measure.IsAddHaarMeasure (μ b)] :
    badPlaceProductPaperRootCoefficientCompletionHullMeasure T μ < ⊤ := by
  unfold badPlaceProductPaperRootCoefficientCompletionHullMeasure
  exact ENNReal.prod_lt_top fun b _ => badPlacePaperRootCoefficientCompletionHull_measure_lt_top T μ b

end LeanFormal.IUT.XiFPaper.PaperBadPlaceTensorGeometryActual

end
