import tmp.sheaf.xif.paper.S1649RouteCReadoutActual
import tmp.sheaf.xif.paper.QVFamPureFractionalScalingDataGapActual
import tmp.sheaf.xif.PaperQPilotObject
import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Quantifiers

/-! # S1663: source readout identification

S1649 constructed the intrinsic-measure transport of the actual qVFam source
readout.  This file compares that readout with the paper source q scalar and
records the exact missing source-readout identification.

The qVFam readout is indexed by `T : SourceNativeInitialThetaData` and by one
bad place `b`; the paper source q scalar `sourceQPilotSignedLog` is indexed by
`I : OriginalInput` and sums over all bad places.  The tree has no common-C
bridge between these two source objects (S1497 records the missing native
donor), so no equality is asserted.  The qVFam pure coefficient is a one-factor
normalization coefficient, not the source scalar; this is proved by definition,
not identified. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1663SourceReadoutIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1414NormalizedReadoutActual
open LeanFormal.IUT.XiFPaper.S1649RouteCReadoutActual
open LeanFormal.IUT.XiFPaper.S1072CanonicalQ1URegionActual
open LeanFormal.IUT.XiFPaper.S1073RootStackPaperThetaHullActual
open LeanFormal.IUT.XiFPaper.S1086PerBQ1URootHullActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open MeasureTheory
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]

/-- The source readout is the qVFam normalized relative Haar readout. -/
theorem s1663SourceReadout_eq_qVFam :
    ∀ b : Bad (nativePlaceSelection T),
      s1414SourceReadout T b =
        (1 / (Module.finrank ℚ_[qVFamTensorP T b] (qVFamTensorBlock T b) : ℝ)) *
          s1414RelativeReadout (Measure.addHaar : Measure (qVFamTensorBlock T b))
            (qPilotQ1URegion (l := l) T b) (s1414SourceReference T b) :=
  fun b => s1649SourceReadout_eq_relativeReadout T b

/-- The qVFam pure coefficient is the one-factor pure normalization coefficient. -/
theorem s1663PureCoefficient_def :
    ∀ b : Bad (nativePlaceSelection T),
      qVFamPureCoefficient T b () =
        -Real.logb (qVFamTensorP T b : Real)
          ‖(qVFamDefaultCompletionUnit T b : Completion ((nativeBadLift T).lift b))‖ :=
  fun b => rfl

/-- A common source carrying both the paper input and the native initial-theta
data.  This is the first missing bridge itself; no inhabitant is asserted. -/
structure S1663CommonSource where
  I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)
  T : SourceNativeInitialThetaData.{0} l
  arithmetic_eq : T.arithmetic = I.initial.arithmetic

/-- The exact missing source-readout comparison: the total qVFam readout over
the bad places equals the paper source q scalar on the same common source. -/
def S1663SourceReadoutMatchesPaper (C : S1663CommonSource (l := l))
    [Fintype (Bad (nativePlaceSelection C.T))] : Prop :=
  (∑ b : Bad (nativePlaceSelection C.T), s1414SourceReadout C.T b) =
    sourceQPilotSignedLog C.I.initial

/-- The pure coefficient is **not** by itself the source q scalar: it is a
one-factor normalization coefficient, while the source scalar sums over all
bad places.  This records the exact comparison obligation without asserting it. -/
def S1663PureCoefficientSourceComparison (C : S1663CommonSource (l := l))
    [Fintype (Bad (nativePlaceSelection C.T))] : Prop :=
  (∑ b : Bad (nativePlaceSelection C.T), qVFamPureCoefficient C.T b ()) =
    sourceQPilotSignedLog C.I.initial

#check s1663SourceReadout_eq_qVFam
#check s1663PureCoefficient_def
#check S1663CommonSource
#check S1663SourceReadoutMatchesPaper
#check S1663PureCoefficientSourceComparison

end LeanFormal.IUT.XiFPaper.S1663SourceReadoutIdentificationActual
end
