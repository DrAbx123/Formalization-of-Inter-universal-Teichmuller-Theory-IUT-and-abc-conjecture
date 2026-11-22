import tmp.sheaf.xif.paper.S1097BasePowActual
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
/-! # S1101: rational residue base from the absNorm/natGenerator identity
residueNormBase of the rational comap place is Ideal.absNorm of its maximal ideal;
completionRationalPrime is Rat.HeightOneSpectrum.primesEquiv of the same ideal,
whose value is natGenerator.  The exact arithmetic minimum is the general
identity absNorm v.asIdeal = (primesEquiv v).val for v : HeightOneSpectrum Z. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000
namespace LeanFormal.IUT.XiFPaper.S1101RationalBaseActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1097BasePowActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable (b : Bad (nativePlaceSelection T))
/-- Exact general arithmetic input: rational ideal absNorm = prime generator. -/
def S1101AbsNormNatGenerator : Prop :=
  ∀ v : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ),
    Ideal.absNorm v.asIdeal = (Rat.HeightOneSpectrum.primesEquiv v).val
theorem s1097RationalBase_of_absNorm
    (h : S1101AbsNormNatGenerator) :
    S1097RationalBase (l := l) T b := by
  unfold S1097RationalBase residueNormBase qVFamTensorP completionRationalPrime
  change (Ideal.absNorm
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.asIdeal) : Real) =
    ((Rat.HeightOneSpectrum.primesEquiv
      (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal).val : Real)
  exact_mod_cast h ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal)
end LeanFormal.IUT.XiFPaper.S1101RationalBaseActual
