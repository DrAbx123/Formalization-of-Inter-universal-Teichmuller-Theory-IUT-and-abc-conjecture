import tmp.sheaf.xif.paper.Mzk1G1QHeightActual
import Mathlib.NumberTheory.Height.MvPolynomial
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.G1JHeightBezoutActual
open LeanFormal.IUT
open MvPolynomial

/-!
# Bezout relations for the Legendre j-map (L-H, route section 6.3)

Integer coefficient forms of the two homogeneous Bezout relations for the two
coordinates A = 256 (U^2 - UV + V^2)^3 and B = U^2 V^2 (V - U)^2 of the degree
6 j-map.  These give the lower height bound h(j(lam)) >= 6 h(lam) - C.
-/

/-- Integer model of the numerator coordinate of the j-map. -/
def jNumZ : MvPolynomial (Fin 2) ℤ :=
  (256 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 - MvPolynomial.X 0 * MvPolynomial.X 1
    + MvPolynomial.X 1 ^ 2) ^ 3

/-- Integer model of the denominator coordinate of the j-map. -/
def jDenZ : MvPolynomial (Fin 2) ℤ :=
  MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2 * (MvPolynomial.X 1 - MvPolynomial.X 0) ^ 2

/-- Scaled Bezout coefficient 256 * q(0,0). -/
def jQ00Z : MvPolynomial (Fin 2) ℤ :=
  (-3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1)
    + (1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0)

/-- Scaled Bezout coefficient 256 * q(0,1). -/
def jQ01Z : MvPolynomial (Fin 2) ℤ :=
  (256 : MvPolynomial (Fin 2) ℤ) * ((3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (-6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (-8 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
    + (6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))

/-- Scaled Bezout coefficient 256 * q(1,0). -/
def jQ10Z : MvPolynomial (Fin 2) ℤ :=
  (1 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (-3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)

/-- Scaled Bezout coefficient 256 * q(1,1). -/
def jQ11Z : MvPolynomial (Fin 2) ℤ :=
  (256 : MvPolynomial (Fin 2) ℤ) * ((6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 0 * MvPolynomial.X 1 ^ 4)
    + (-8 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 1 * MvPolynomial.X 1 ^ 3)
    + (11 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 2 * MvPolynomial.X 1 ^ 2)
    + (-6 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 3 * MvPolynomial.X 1 ^ 1)
    + (3 : MvPolynomial (Fin 2) ℤ) * (MvPolynomial.X 0 ^ 4 * MvPolynomial.X 1 ^ 0))

/-- Kernel-checked integer Bezout identity for X0. -/
theorem jBezUZ :
    jQ00Z * jNumZ + jQ01Z * jDenZ = (256 : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X 0 ^ 10 := by
  unfold jQ00Z jQ01Z jNumZ jDenZ
  ring

/-- Kernel-checked integer Bezout identity for X1. -/
theorem jBezVZ :
    jQ10Z * jNumZ + jQ11Z * jDenZ = (256 : MvPolynomial (Fin 2) ℤ) * MvPolynomial.X 1 ^ 10 := by
  unfold jQ10Z jQ11Z jNumZ jDenZ
  ring

#print axioms jBezUZ
#print axioms jBezVZ

end LeanFormal.IUT.XiFPaper.G1JHeightBezoutActual
end
