import tmp.sheaf.xif.paper.PaperC3QPilotLogComparisonActual
import tmp.sheaf.xif.paper.PaperC3SourceDataQConsistencyActual

/-!
# S237: corrected source tensor hull is proper, not univ

The corrected sourceQTensorLambdaOHull is the image of the canonical compact
unit reference under multiplication by the actual tensor unit.  Multiplication
by a unit is continuous, so the hull is compact.

The source tensor block is a nontrivial normed vector space; its ambient space
is noncompact.  Hence the compact hull cannot be univ.

We also construct actual Borel/measurable/Haar/mu_log objects for the hull.
No inequality is stated.
-/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S237SourceHullProperActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.PaperC3TensorBlockActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceQHullRelationActual
open LeanFormal.IUT.XiFPaper.GenericQPilotCompletionPowerActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3SourceDataQConsistencyActual
open LeanFormal.IUT.XiFPaper.PaperC3QPilotLogComparisonActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The corrected source tensor hull is compact: image of the compact canonical
unit reference under multiplication by the tensor unit. -/
theorem sourceQTensorLambdaOHull_compact :
    IsCompact (sourceQTensorLambdaOHull T b) := by
  rw [sourceQTensorLambdaOHull_eq_image_unitReference T b]
  have hO : IsCompact (sourceQTensorUnitReference T b) :=
    (isCompact_arithmeticTupleCanonicalRegions
      (fun _ (_ : Unit) => sourceThetaPlace T b) (fun _ => ())).2
  have hmul : Continuous (fun o : SourceQTensorBlock T b =>
      Units.val (sourceQTensorUnit T b) * o) :=
    continuous_const_mul (Units.val (sourceQTensorUnit T b))
  exact hO.image hmul

/-- Actual Borel structure on the source tensor block. -/
noncomputable instance sourceQTensorHullBorel :
    BorelSpace (SourceQTensorBlock T b) := ⟨rfl⟩

/-- Actual Haar measure on the source tensor block. -/
noncomputable def sourceQTensorHullHaar : Measure (SourceQTensorBlock T b) :=
  Measure.addHaar

/-- Actual mu_log of the corrected hull. -/
noncomputable def sourceQTensorHullMuLog : ENNReal :=
  haarLogVolume (sourceQTensorHullHaar T b) (sourceQTensorLambdaOHull T b)

/-- Exact condition form: if the ambient carrier is known noncompact, the
compact unit-scaled hull is proper. -/
theorem sourceQTensorLambdaOHull_ne_univ_of_noncompact
    (h : NoncompactSpace (SourceQTensorBlock T b)) :
    sourceQTensorLambdaOHull T b ≠ Set.univ := by
  intro huniv
  apply h.noncompact_univ
  rw [← huniv]
  exact sourceQTensorLambdaOHull_compact T b

/-- Actual compact hull/Borel/Haar/mu_log object. -/
structure SourceQTensorHullObjectActual where
  hull : Set (SourceQTensorBlock T b)
  hull_eq : hull = sourceQTensorLambdaOHull T b
  hull_compact : IsCompact hull
  haar : Measure (SourceQTensorBlock T b)
  haar_eq : haar = sourceQTensorHullHaar T b
  muLog : ENNReal
  muLog_eq : muLog = sourceQTensorHullMuLog T b

/-- Actual hull object constructor. -/
noncomputable def sourceQTensorHullObjectActual :
    SourceQTensorHullObjectActual T b where
  hull := sourceQTensorLambdaOHull T b
  hull_eq := rfl
  hull_compact := sourceQTensorLambdaOHull_compact T b
  haar := sourceQTensorHullHaar T b
  haar_eq := rfl
  muLog := sourceQTensorHullMuLog T b
  muLog_eq := rfl

end LeanFormal.IUT.XiFPaper.S237SourceHullProperActual

end
