import LeanFormal.IUT.IUTI.InitialTheta.SourceDefinition31Boundary
import LeanFormal.IUT.Foundations.AlgebraicGeometry.AffinePunctureIdealInvertible

/-!
# The actual source puncture ideal is an invertible module

This is the ideal on the usual affine Weierstrass chart. For an affine puncture
it is its actual point ideal. For the point at infinity its restriction is the
unit ideal. The latter does not describe a trivial divisor on the projective
curve, and this file does not construct a theta structure.
-/

noncomputable section

namespace ABCBridge.SourceQlThetaPunctureIdeal

open LeanFormal.IUT LeanFormal.IUT.Theorem311Source LeanFormal.IUT.AffinePunctureIdeal

universe u

variable {l : PrimeGeFive} (S : SourceDefinition31Data.{u} l)

abbrev sourcePunctureAffineModel : WeierstrassCurve.Affine S.arithmetic.F :=
  S.arithmetic.curve.curve.toAffine

abbrev sourcePunctureCoordinateRing : Type u :=
  (sourcePunctureAffineModel S).CoordinateRing

def sourcePunctureAffinePoint : (sourcePunctureAffineModel S).Point :=
  S.arithmetic.curve.puncture.toAffineLift

def sourcePunctureVanishingIdeal : Ideal (sourcePunctureCoordinateRing S) :=
  pointVanishingIdeal (sourcePunctureAffineModel S) (sourcePunctureAffinePoint S)

abbrev sourcePunctureIdealModule : Type u := ↥(sourcePunctureVanishingIdeal S)

theorem sourcePunctureVanishingIdeal_of_zero
    (h : sourcePunctureAffinePoint S = .zero) :
    sourcePunctureVanishingIdeal S = ⊤ := by
  simp only [sourcePunctureVanishingIdeal, h, pointVanishingIdeal]

theorem sourcePunctureVanishingIdeal_of_some
    {x y : S.arithmetic.F} {h : (sourcePunctureAffineModel S).Nonsingular x y}
    (hpt : sourcePunctureAffinePoint S = .some x y h) :
    sourcePunctureVanishingIdeal S =
      WeierstrassCurve.Affine.CoordinateRing.XYIdeal
        (sourcePunctureAffineModel S) x (Polynomial.C y) := by
  simp only [sourcePunctureVanishingIdeal, hpt, pointVanishingIdeal]

theorem sourcePunctureIdeal_invertible :
    Module.Invertible (sourcePunctureCoordinateRing S) (sourcePunctureIdealModule S) :=
  pointVanishingIdeal_invertible (sourcePunctureAffineModel S) (sourcePunctureAffinePoint S)

theorem sourcePunctureIdeal_projective :
    Module.Projective (sourcePunctureCoordinateRing S) (sourcePunctureIdealModule S) :=
  pointVanishingIdeal_projective (sourcePunctureAffineModel S) (sourcePunctureAffinePoint S)

theorem sourcePunctureIdeal_finite :
    Module.Finite (sourcePunctureCoordinateRing S) (sourcePunctureIdealModule S) :=
  pointVanishingIdeal_finite (sourcePunctureAffineModel S) (sourcePunctureAffinePoint S)

theorem sourcePunctureIdeal_finrank_eq_one :
    Module.finrank (sourcePunctureCoordinateRing S) (sourcePunctureIdealModule S) = 1 :=
  pointVanishingIdeal_finrank_eq_one (sourcePunctureAffineModel S) (sourcePunctureAffinePoint S)

theorem sourcePunctureIdeal_projective_rankOne :
    Module.Projective (sourcePunctureCoordinateRing S) (sourcePunctureIdealModule S) ∧
      Module.finrank (sourcePunctureCoordinateRing S) (sourcePunctureIdealModule S) = 1 :=
  ⟨sourcePunctureIdeal_projective S, sourcePunctureIdeal_finrank_eq_one S⟩

end ABCBridge.SourceQlThetaPunctureIdeal
