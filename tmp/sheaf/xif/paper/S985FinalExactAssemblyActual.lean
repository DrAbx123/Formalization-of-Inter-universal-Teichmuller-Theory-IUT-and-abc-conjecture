import tmp.sheaf.xif.paper.S979TensorRegionHullInequalityActual
import tmp.sheaf.xif.paper.S981TensorRegionHullFiniteActual
import tmp.sheaf.xif.paper.S982FinalLTensorFromFiniteQuotientActual
import tmp.sheaf.xif.paper.S945TensorPacketPaperSActual

noncomputable section
open scoped BigOperators TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 5000000

namespace LeanFormal.IUT.XiFPaper.S985FinalExactAssemblyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S945TensorPacketPaperSActual
open LeanFormal.IUT.XiFPaper.S956TensorPacketLogVolumeExactActual
open LeanFormal.IUT.XiFPaper.S979TensorRegionHullInequalityActual
open LeanFormal.IUT.XiFPaper.S981TensorRegionHullFiniteActual
open LeanFormal.IUT.XiFPaper.S982FinalLTensorFromFiniteQuotientActual
open MeasureTheory

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- Final exact inputs after deleting the actual density. -/
structure S985FinalExactInputs where
  finiteQuotient : ∀ b : Bad (nativePlaceSelection T), S982FiniteQuotientBridge T b
  D : ∀ b : Bad (nativePlaceSelection T), FinalLTensorLogVolumeData T b
  imagePositivity : ∀ b : Bad (nativePlaceSelection T),
    0 < (D b).measure (qPilotPaperImageInLValued T b)
  hullSubset : ∀ b : Bad (nativePlaceSelection T),
    S981TensorRegionHullSubsetUnitRegion T b (D b)

/-- The exact inputs give S979's positivity/finiteness hypotheses. -/
theorem s979Hypotheses_of_finalInputs
    (X : S985FinalExactInputs T) :
    S979TensorRegionHypotheses T X.D := by
  constructor
  · exact X.imagePositivity
  · intro b
    exact tensorRegionHull_measure_lt_top_of_subset T b (X.D b) (X.hullSubset b)

/-- Global weighted inequality from S979 + S981, with the S982 finite-quotient
bridge as an explicit input and no density hypothesis. -/
theorem tensorRegionHullPaperWeightedInequality_of_finalInputs
    (X : S985FinalExactInputs T) :
    tensorRegionHullPaperWeightedInequality T X.D :=
  tensorRegionHullPaperWeightedInequality_of_perB T X.D
    (s979Hypotheses_of_finalInputs T X)

/-- Final exact list: no density; only finite quotient bridge, positivity,
hull-unit subset, plus the source link/finite link evidence used by S979's
Cor312 assembly. -/
structure S985FinalExactList where
  finiteQuotient : ∀ b : Bad (nativePlaceSelection T),
    S982FiniteQuotientBridge T b
  D : ∀ b : Bad (nativePlaceSelection T), FinalLTensorLogVolumeData T b
  imagePositivity : ∀ b : Bad (nativePlaceSelection T),
    0 < (D b).measure (qPilotPaperImageInLValued T b)
  hullSubset : ∀ b : Bad (nativePlaceSelection T),
    S981TensorRegionHullSubsetUnitRegion T b (D b)
  sourceLink : Prop
  finiteLinks : Prop

end LeanFormal.IUT.XiFPaper.S985FinalExactAssemblyActual
end