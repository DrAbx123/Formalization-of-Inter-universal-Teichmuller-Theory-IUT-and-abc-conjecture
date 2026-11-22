import tmp.sheaf.xif.paper.S1547ResidueNormBaseActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1563ResidueNormBaseProofActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1547ResidueNormBaseActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- Exact first missing number-theory identity: the absolute norm of the
rational prime ideal is its natural generator. -/
def S1563AbsNormEqNatGenerator : Prop :=
  residueNormBase (comap (k := ℚ) (qVFamTensorPlace T b)) =
    (Rat.HeightOneSpectrum.natGenerator
      ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal) : Real)

/-- The rational prime of the actual F-place is the natural generator of the
contracted rational height-one prime. -/
theorem s1563Prime_eq_natGenerator :
    (qVFamTensorP T b : Real) =
      (Rat.HeightOneSpectrum.natGenerator
        ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal) : Real) := by
  unfold qVFamTensorP
  rfl

/-- The abs-norm/nat-generator identity implies S1547's residue-norm-base
equality. -/
theorem s1563ResidueNormBaseEqPrime_of_absNorm
    (h : S1563AbsNormEqNatGenerator (l := l) T b) :
    S1547ResidueNormBaseEqPrime (l := l) T b := by
  unfold S1547ResidueNormBaseEqPrime S1563AbsNormEqNatGenerator at *
  rw [h, s1563Prime_eq_natGenerator]

end LeanFormal.IUT.XiFPaper.S1563ResidueNormBaseProofActual

end
