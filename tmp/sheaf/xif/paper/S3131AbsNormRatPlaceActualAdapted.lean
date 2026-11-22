import Mathlib
import tmp.sheaf.xif.paper.S3131SameCSourceInputActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual

namespace LeanFormal.IUT.XiFPaper.S3131AbsNormRatPlaceActualAdapted

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem S3131AbsNorm_ratPlace_eq_natGenerator :
    Ideal.absNorm (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal.asIdeal
      = Rat.HeightOneSpectrum.natGenerator
          ((comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal) := by
  let P := (comap (k := ℚ) (qVFamTensorPlace T b)).maximalIdeal
  let e : NumberField.RingOfIntegers ℚ ≃+* ℤ := Rat.ringOfIntegersEquiv
  have hfun : (e : NumberField.RingOfIntegers ℚ →+* ℤ) =
      Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ) := by
    ext x
    exact (Rat.IsIntegralClosure.intEquiv_apply_eq_ringOfIntegersEquiv x).symm
  have hmap : P.asIdeal.map (e : NumberField.RingOfIntegers ℚ →+* ℤ)
      = Ideal.span {(Rat.HeightOneSpectrum.natGenerator P : ℤ)} := by
    rw [hfun]
    exact (Rat.HeightOneSpectrum.span_natGenerator P).symm
  rw [Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have hcard : Nat.card (NumberField.RingOfIntegers ℚ ⧸ P.asIdeal) =
      Nat.card (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator P : ℤ)}) :=
    Nat.card_congr (Ideal.quotientEquiv P.asIdeal
      (Ideal.span {(Rat.HeightOneSpectrum.natGenerator P : ℤ)}) e hmap.symm).toEquiv
  rw [hcard]
  have h2 : Nat.card (ℤ ⧸ Ideal.span {(Rat.HeightOneSpectrum.natGenerator P : ℤ)}) = Ideal.absNorm (Ideal.span {(Rat.HeightOneSpectrum.natGenerator P : ℤ)}) := (Ideal.absNorm_apply _).symm
  rw [Ideal.absNorm_span_singleton (Rat.HeightOneSpectrum.natGenerator P : ℤ)]
  simp

#check S3131AbsNorm_ratPlace_eq_natGenerator

end LeanFormal.IUT.XiFPaper.S3131AbsNormRatPlaceActualAdapted
end