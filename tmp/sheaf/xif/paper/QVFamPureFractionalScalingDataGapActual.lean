import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly
import Mathlib.Analysis.SpecialFunctions.Log.Base

/-! # qVFamily completion unit versus normalized fractional scaling data

The qVFamily q is an element of Completion(place) with the default valuation
norm.  ArithmeticTuplePureFractionalScalingData (via
arithmeticTuplePureFractionalScalingData_ofGenerator) requires a local generator
in CommonPrimeCompletion with the *normalized* norm

  ||g|| = p ^ (-(c))

for the coefficient vector c.  On the same underlying completed field the two
norm instances are the valuation norm and the normalized spectral norm.

This file constructs the actual qVFamily completion unit and the actual
coefficient c = -logb_p ||q||, and proves the conditional construction of the
pure fractional scaling data from an explicit normalized generator supply.
The exact missing datum is a generator in CommonPrimeCompletion with the
normalized norm; it is NOT fabricated from the qVFamily unit, because the tree
does not identify the two norm instances on the qVFamily element.

No fake equality/inequality; no sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual qVFamily q as a unit of its (default-norm) completion. -/
noncomputable def qVFamDefaultCompletionUnit :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  Units.mk0 (qVFamily T b).q (qVFamily T b).q_ne_zero

/-- The actual coefficient c b = -logb_p ||q||. -/
noncomputable def qVFamPureCoefficient :
    qVFamTensorV → Real :=
  fun _ => -Real.logb (qVFamTensorP T b : Real)
    ‖(qVFamDefaultCompletionUnit T b : Completion ((nativeBadLift T).lift b))‖

/-- Exact normalized-generator supply for the qVFamily tensor block: a generator
in the normalized CommonPrimeCompletion with the required p^{-c} norm. -/
structure NormalizedGeneratorSupply where
  generator : CommonPrimeCompletion
    ((qVFamTensorPlaces T b) () (qVFamTensorTuple ()))
  generator_norm :
    ‖generator‖ =
      (qVFamTensorP T b : Real) ^ (-(qVFamPureCoefficient T b ()))

/-- Conditional actual pure fractional scaling data from an explicit normalized
generator supply.  Every field comes from the production constructor
arithmeticTuplePureFractionalScalingData_ofGenerator; nothing is faked. -/
noncomputable def qVFamPureFractionalScalingData_of_supply
    (S : NormalizedGeneratorSupply T b) :
    ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple (qVFamPureCoefficient T b) :=
  arithmeticTuplePureFractionalScalingData_ofGenerator
    (qVFamTensorPlaces T b) qVFamTensorTuple (qVFamPureCoefficient T b)
    (fun _ => S.generator) (fun _ => S.generator_norm)

/-- The exact missing normalized generator supply.  This is not asserted. -/
def NormalizedGeneratorSupplyMissing : Prop :=
  Nonempty (NormalizedGeneratorSupply T b)

/-- Exact norm-instance mismatch: the actual qVFamily unit lives in Completion
with the default valuation norm, while the tensor constructor needs a generator
in CommonPrimeCompletion with the normalized spectral norm.  The tree supplies
no equality of these two norm instances on the qVFamily element. -/
def QVFamNormalizedNormInstanceGap : Prop :=
  NormalizedGeneratorSupplyMissing T b

end LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual

end
