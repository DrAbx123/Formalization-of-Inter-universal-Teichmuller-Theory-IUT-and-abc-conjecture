import tmp.sheaf.xif.paper.NormalizedCompletionPadicBridgeActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.Ideal.Norm.AbsNorm
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotBaseChange

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.NormalizedCompletionPadicBridgeActual
open LeanFormal.IUT.ArithmeticQPilotBaseChange

namespace LeanFormal.IUT.XiFPaper.Node09AbsNormRatActual

/-- For a rational finite place, the ideal absolute norm is the rational
prime, via the rational integral-closure ring equivalence. -/
theorem absNorm_rat_eq (place : NumberField.FinitePlace ℚ) :
    Ideal.absNorm place.maximalIdeal.asIdeal = (completionRationalPrime place).val := by
  let v := place.maximalIdeal
  let ee : NumberField.RingOfIntegers ℚ ≃+* ℤ :=
    Rat.IsIntegralClosure.intEquiv (NumberField.RingOfIntegers ℚ)
  have hspan : Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)} =
      v.asIdeal.map ee :=
    Rat.HeightOneSpectrum.span_natGenerator v
  have hcard : Ideal.absNorm place.maximalIdeal.asIdeal =
      Ideal.absNorm (Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)}) := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply]
    exact Nat.card_congr (Ideal.quotientEquiv v.asIdeal
      (Ideal.span {(Rat.HeightOneSpectrum.natGenerator v : ℤ)}) ee hspan).toEquiv
  have hgen : Rat.HeightOneSpectrum.natGenerator v = (completionRationalPrime place).val := by
    have hcp : (completionRationalPrime place).val =
        Rat.HeightOneSpectrum.natGenerator
          ((comap (k := ℚ) place).maximalIdeal) := rfl
    rw [hcp, comap_self_rat place]
  rw [hcard, hgen]
  rw [Ideal.absNorm_span_natCast]
  simp

/-- The rational base residue norm is the rational prime (actual form). -/
theorem residueNormBase_rat_eq (place : NumberField.FinitePlace ℚ) :
    residueNormBase place = ((completionRationalPrime place).val : ℝ) := by
  unfold residueNormBase
  rw [absNorm_rat_eq place]

/-- hlogp for rational places, given the place-prime compatibility. -/
theorem hlogp_rat_of_place_prime_eq
    {p : Nat} {place : NumberField.FinitePlace ℚ}
    (i : FinitePlaceAtPrime ℚ p)
    (hprime : (completionRationalPrime place).val =
      (completionRationalPrime (i.val)).val) :
    Real.log (((completionRationalPrime (i.val)).val : ℕ) : ℝ) =
      Real.log (residueNormBase place) := by
  rw [residueNormBase_rat_eq place]
  congr 1
  exact_mod_cast hprime.symm

end LeanFormal.IUT.XiFPaper.Node09AbsNormRatActual
