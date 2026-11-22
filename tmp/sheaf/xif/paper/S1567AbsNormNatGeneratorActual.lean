import tmp.sheaf.xif.paper.S1563ResidueNormBaseProofActual
import Mathlib.RingTheory.Ideal.Operations
import Mathlib.NumberTheory.Padics.HeightOneSpectrum

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1567AbsNormNatGeneratorActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotBaseChange
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.S1547ResidueNormBaseActual
open LeanFormal.IUT.XiFPaper.S1563ResidueNormBaseProofActual
open LeanFormal.IUT.XiFPaper.S1526S1087CoeffLeActual
open LeanFormal.IUT.XiFPaper.S1087Q1UContainmentActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]
variable [∀ b : Bad (nativePlaceSelection T), MeasurableSpace (qVFamTensorBlock T b)]
variable [∀ b : Bad (nativePlaceSelection T), BorelSpace (qVFamTensorBlock T b)]
variable (b : Bad (nativePlaceSelection T))

/-- The contracted rational height-one prime of the actual F-place. -/
noncomputable abbrev contractedRationalPrime :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal

/-- The contracted rational prime ideal. -/
noncomputable abbrev contractedRationalIdeal :
    Ideal (NumberField.RingOfIntegers ℚ) :=
  (contractedRationalPrime (l := l) T b).asIdeal

/-- Actual quotient-ring equivalence from Ruben's intEquiv. -/
noncomputable def contractedQuotientEquiv :
    (NumberField.RingOfIntegers ℚ) ⧸ contractedRationalIdeal (l := l) T b ≃+*
      ℤ ⧸ Ideal.span
        {(Rat.HeightOneSpectrum.natGenerator
          (contractedRationalPrime (l := l) T b) : ℤ)} :=
  Ideal.quotientEquiv
    (contractedRationalIdeal (l := l) T b)
    (Ideal.span
      {(Rat.HeightOneSpectrum.natGenerator
        (contractedRationalPrime (l := l) T b) : ℤ)})
    (Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ))
    (Rat.HeightOneSpectrum.span_natGenerator
      (contractedRationalPrime (l := l) T b))

/-- Actual residue norm of the contracted rational prime is its natural
generator. -/
theorem s1567AbsNorm_eq_natGenerator :
    Ideal.absNorm (contractedRationalIdeal (l := l) T b) =
      Rat.HeightOneSpectrum.natGenerator
        (contractedRationalPrime (l := l) T b) := by
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcard := Nat.card_congr (contractedQuotientEquiv (l := l) T b).toEquiv
  rw [hcard]
  simpa using Int.card_ideal_quot
    (Rat.HeightOneSpectrum.natGenerator (contractedRationalPrime (l := l) T b))

/-- The actual S1563AbsNormEqNatGenerator. -/
theorem s1567AbsNormEqNatGenerator_actual :
    S1563AbsNormEqNatGenerator (l := l) T b := by
  unfold S1563AbsNormEqNatGenerator residueNormBase
  change (Ideal.absNorm (contractedRationalIdeal (l := l) T b) : Real) =
    (Rat.HeightOneSpectrum.natGenerator
      (contractedRationalPrime (l := l) T b) : Real)
  exact_mod_cast s1567AbsNorm_eq_natGenerator (l := l) T b

/-- Hence S1547 residue-norm-base equality. -/
theorem s1567ResidueNormBaseEqPrime_actual :
    S1547ResidueNormBaseEqPrime (l := l) T b :=
  s1563ResidueNormBaseEqPrime_of_absNorm (l := l) T b
    (s1567AbsNormEqNatGenerator_actual (l := l) T b)

/-- Actual S1526 residue log-ratio bound. -/
theorem s1567ResidueLogRatio_actual :
    S1526ResidueLogRatioGeOne (l := l) T b :=
  s1547ResidueLogRatio_of_residueNormBase (l := l) T b
    (s1567ResidueNormBaseEqPrime_actual (l := l) T b)

/-- Actual S1087 coefficient comparison. -/
theorem s1567CoeffLe_actual :
    S1087CoeffLe (l := l) T b :=
  s1547CoeffLe_of_residueNormBase (l := l) T b
    (s1567ResidueNormBaseEqPrime_actual (l := l) T b)

end LeanFormal.IUT.XiFPaper.S1567AbsNormNatGeneratorActual

end
