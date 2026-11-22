import Mathlib.AlgebraicGeometry.EllipticCurve.Affine.Point
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed

/-!
# Route 3 C-Divisor: affine coordinate-ring order infrastructure

This file records the part of the Dedekind/order infrastructure that is
actually derivable from Mathlib for an elliptic Weierstrass coordinate ring:

* Module.Finite K[X] W.CoordinateRing (the polynomial in Y is monic);
* Algebra.IsIntegral K[X] W.CoordinateRing;
* Ring.DimensionLEOne W.CoordinateRing, by integrality over K[X] and the PID
  dimension-one instance for K[X];
* IsNoetherianRing W.CoordinateRing.

The missing step is integral closedness of W.CoordinateRing in its fraction
field. Mathlib has no theorem that a smooth plane cubic coordinate ring is
integrally closed, and no IsDedekindDomain instance for W.CoordinateRing is
available. Consequently orderAtAffine via HeightOneSpectrum.valuation is NOT
constructed here; this is the exact remaining gap. No fake order function or
extra assumption is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1AffineOrderActual

open Polynomial

variable {K : Type*} [Field K]
variable (W : WeierstrassCurve.Affine K) [W.IsElliptic]

/-- The coordinate ring is a finite module over K[X] because the Weierstrass
polynomial is monic in Y. -/
theorem coordinateRing_moduleFinite :
    Module.Finite K[X] W.CoordinateRing := by
  exact W.monic_polynomial.finite_adjoinRoot

/-- Hence the coordinate ring is integral over K[X]. -/
theorem coordinateRing_isIntegral :
    Algebra.IsIntegral K[X] W.CoordinateRing := by
  haveI : Module.Finite K[X] W.CoordinateRing := coordinateRing_moduleFinite W
  infer_instance

/-- The coordinate ring has Krull dimension at most one, by integrality over
K[X] and the PID case. -/
theorem coordinateRing_dimensionLEOne :
    Ring.DimensionLEOne W.CoordinateRing := by
  haveI : Algebra.IsIntegral K[X] W.CoordinateRing := coordinateRing_isIntegral W
  exact Ring.DimensionLEOne.of_isIntegral (R := K[X]) (B := W.CoordinateRing)

/-- Coordinate ring is Noetherian (AdjoinRoot of a monic polynomial over K[X]). -/
theorem coordinateRing_noetherian :
    IsNoetherianRing W.CoordinateRing := by
  infer_instance

/-- The exact missing Dedekind hypotheses: IsIntegrallyClosed is the only
condition not available from the above. -/
def IsIntegrallyClosedGap : Prop :=
  IsIntegrallyClosed W.CoordinateRing

#print axioms coordinateRing_moduleFinite
#print axioms coordinateRing_isIntegral
#print axioms coordinateRing_dimensionLEOne
#print axioms coordinateRing_noetherian

end LeanFormal.IUT.XiFPaper.Mzk1AffineOrderActual
