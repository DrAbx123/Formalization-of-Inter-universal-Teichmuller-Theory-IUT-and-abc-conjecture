import tmp.sheaf.xif.paper.S812LeastLambdaOFiniteLStackActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceStepVAssembly

-- S815: paper scaling data at cRoot = order/(2l).
-- Exact reduction to local generators of norm p^(-cRoot); finite-L
-- alternative data and the exact finite-L -> completion bridge.

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S815PaperScalingDataFiniteLActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.BadPlacePaperRootThetaHullActual
open LeanFormal.IUT.XiFPaper.S793PaperLeastLambdaOHullActual
open LeanFormal.IUT.XiFPaper.S799LeastLambdaOPaperTargetActual
open LeanFormal.IUT.XiFPaper.S812LeastLambdaOFiniteLStackActual
open LeanFormal.IUT.XiFPaper.S782FiniteRootStackExtensionActual
open MeasureTheory

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

theorem paperScalingData_nonempty_iff_localGenerator :
    Nonempty (ArithmeticTuplePureFractionalScalingData
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b)) ↔
      ∃ g : (i : qVFamTensorV) →
          CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i)),
        ∀ i, ‖g i‖ = (qVFamTensorP T b : Real) ^
          (-(paperRootCoefficientFamily T b i)) := by
  constructor
  · rintro ⟨data⟩
    exact ⟨data.localGenerator, data.localGenerator_norm⟩
  · rintro ⟨g, hg⟩
    exact ⟨arithmeticTuplePureFractionalScalingData_ofGenerator
      (qVFamTensorPlaces T b) qVFamTensorTuple
      (paperRootCoefficientFamily T b) g hg⟩

/-- Finite-L alternative local scaling data: generators in L(mu_2l). -/
structure FiniteLScalingGenerator where
  generator : qVFamTensorV → rootStackExtension T b
  generator_ne_zero : ∀ i, generator i ≠ 0
  generator_norm : ∀ i, ‖generator i‖ = (qVFamTensorP T b : Real) ^
    (-(paperRootCoefficientFamily T b i))

/-- Exact bridge from finite-L generators to completion generators. -/
structure FiniteLToPaperScalingBridge where
  finite : FiniteLScalingGenerator (l := l) T b
  comparison : (i : qVFamTensorV) → rootStackExtension T b →
    CommonPrimeCompletion (qVFamTensorPlaces T b i (qVFamTensorTuple i))
  comparison_norm : ∀ i (x : rootStackExtension T b),
    ‖comparison i x‖ = ‖x‖
  comparison_generator_norm : ∀ i,
    ‖comparison i (finite.generator i)‖ = (qVFamTensorP T b : Real) ^
      (-(paperRootCoefficientFamily T b i))

def FiniteLToPaperScalingBridgeRequired : Prop :=
  Nonempty (FiniteLToPaperScalingBridge (l := l) T b)

/-- S782 stackRootSection divisor is exactly the cRoot coefficient. -/
theorem stackRootSection_divisor_eq_paperCoefficient :
    stackDivisorSection (l := l) T b (stackRootSection (l := l) T b) =
      Multiplicative.ofAdd (paperRootCoefficientFamily T b ()) :=
  rfl

#check paperScalingData_nonempty_iff_localGenerator
#check FiniteLScalingGenerator
#check FiniteLToPaperScalingBridgeRequired
#check stackRootSection_divisor_eq_paperCoefficient

end LeanFormal.IUT.XiFPaper.S815PaperScalingDataFiniteLActual

end