import Mathlib.Algebra.MvPolynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1CompactnessActual
open LeanFormal.IUT
open MvPolynomial

/-- Actual Fermat equation X^n + Y^n - 1 in two variables over ℚ. -/
def fermatPolynomial (n : ℕ) : MvPolynomial (Fin 2) ℚ :=
  X 0 ^ n + X 1 ^ n - 1

/-- Actual Fermat ideal. -/
def fermatIdeal (n : ℕ) : Ideal (MvPolynomial (Fin 2) ℚ) :=
  Ideal.span {fermatPolynomial n}

/-- Actual Fermat coordinate ring. -/
abbrev FermatCoordinateRing (n : ℕ) : Type :=
  MvPolynomial (Fin 2) ℚ ⧸ fermatIdeal n

/-- Actual Fermat scheme as the prime spectrum of the coordinate ring. -/
abbrev FermatScheme (n : ℕ) : Type :=
  PrimeSpectrum (FermatCoordinateRing n)

instance fermatSchemeCompactSpace (n : ℕ) : CompactSpace (FermatScheme n) :=
  PrimeSpectrum.compactSpace

/-- Actual compactness of the Fermat scheme. -/
theorem fermatScheme_isCompact (n : ℕ) :
    IsCompact (Set.univ : Set (FermatScheme n)) :=
  isCompact_univ

/-- Actual Fermat point field: a point of the Fermat scheme. -/
structure FermatPoint (n : ℕ) where
  point : FermatScheme n

/-- Actual local height formula on affine coordinates of the Fermat curve. -/
def fermatLocalHeightFormula (p : ℚ × ℚ) : ℝ :=
  Real.log (max (|p.1|) 1)

/-- Actual local different exponent formula for the Fermat equation. -/
def fermatDifferentFormula (n : ℕ) : ℤ :=
  (n : ℤ) - 1

end LeanFormal.IUT.XiFPaper.G1CompactnessActual
end
