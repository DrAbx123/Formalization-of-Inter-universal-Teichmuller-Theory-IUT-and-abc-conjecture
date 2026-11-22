import tmp.sheaf.xif.paper.QVFamNormalizedGeneratorSupplyActual
import tmp.sheaf.xif.paper.QVFamRootFactorCorrectionActual
noncomputable section
set_option maxHeartbeats 1000000
namespace LeanFormal.IUT.XiFPaper.S2154NormalizedSupplyActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QVFamPureFractionalScalingDataGapActual
open LeanFormal.IUT.XiFPaper.QVFamNormalizedGeneratorSupplyActual
open LeanFormal.IUT.XiFPaper.QVFamRootFactorCorrectionActual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Exact norm-coefficient gap of the qVFamily normalized completion. -/
abbrev s2154CoefficientGap : Prop :=
  QVFamNormalizedCoefficientGap T b
/-- Actual conditional supply at the default-norm qVFamily coefficient. -/
noncomputable def s2154NormalizedGeneratorSupply_of_coefficientGap
    (h : s2154CoefficientGap T b) : NormalizedGeneratorSupply T b :=
  qVFamNormalizedGeneratorSupply_of_coefficient_eq T b h
/-- A generator at an arbitrary coefficient c in the actual normalized
completion.  This is the exact supply shape needed by the paper root
coefficient. -/
structure s2154GeneratorAt (c : Real) where
  generator : CommonPrimeCompletion ((qVFamTensorPlaces T b) () ())
  generator_norm : ‖generator‖ = (qVFamTensorP T b : Real) ^ (-(c))
/-- The actual qVFamily normalized generator gives a supply at
qVFamNormalizedCoefficient, not at the paper root coefficient. -/
noncomputable def s2154GeneratorAtNormalized :
    s2154GeneratorAt T b (qVFamNormalizedCoefficient T b) where
  generator := qVFamNormalizedGenerator T b
  generator_norm := qVFamNormalizedGenerator_norm T b
/-- Exact first missing for the paper root coefficient: a normalized-completion
generator of norm p^(-(qVFamPaperRootCoefficient)). -/
def s2154RootCoefficientSupplyMissing : Prop :=
  Nonempty (s2154GeneratorAt T b (qVFamPaperRootCoefficient T b))
/-- The coefficient gap supplies NormalizedGeneratorSupply at the default-norm
coefficient. -/
theorem s2154_normalizedGeneratorSupply_of_gap
    (h : s2154CoefficientGap T b) : Nonempty (NormalizedGeneratorSupply T b) :=
  ⟨s2154NormalizedGeneratorSupply_of_coefficientGap T b h⟩
#print axioms s2154NormalizedGeneratorSupply_of_coefficientGap
#print axioms s2154_normalizedGeneratorSupply_of_gap
end LeanFormal.IUT.XiFPaper.S2154NormalizedSupplyActual
end
