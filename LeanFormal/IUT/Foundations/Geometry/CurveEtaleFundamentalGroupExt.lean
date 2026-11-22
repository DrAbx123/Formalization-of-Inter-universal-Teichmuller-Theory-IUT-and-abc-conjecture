import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup

set_option linter.unusedSectionVars false
noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.Foundations.Geometry

universe u

/-! ## Extension: arithmetic data and an actual geometric point -/

variable (K : Type u) [Field K]

/-- The Weierstrass model y^2 = x^3 - x of the once-punctured curve. -/
def puncturedEllipticWeierstrassCurve (K : Type u) [Field K] : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

/-- The discriminant of the Weierstrass model y^2 = x^3 - x is 64. -/
theorem puncturedEllipticWeierstrassCurve_Δ (K : Type u) [Field K] :
    (puncturedEllipticWeierstrassCurve K).Δ = 64 := by
  simp [puncturedEllipticWeierstrassCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈]
  norm_num

/-- In characteristic not 2, the Weierstrass model y^2 = x^3 - x is elliptic:
its discriminant 64 = 2^6 is a unit. -/
theorem puncturedEllipticWeierstrassCurve_isElliptic (K : Type u) [Field K]
    (h2 : (2 : K) ≠ 0) : (puncturedEllipticWeierstrassCurve K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, puncturedEllipticWeierstrassCurve_Δ]
  exact isUnit_iff_ne_zero.mpr (by
    rw [show (64 : K) = 2 ^ 6 by norm_num]
    exact pow_ne_zero 6 h2)

variable (Omega : Type u) [Field Omega] [Algebra K Omega]

/-- Evaluation at the origin (x,y) = (0,0) of the affine curve y^2 = x^3 - x. -/
def puncturedEllipticOriginEval : MvPolynomial (Fin 2) K →+* Omega :=
  MvPolynomial.eval₂Hom (algebraMap K Omega) (fun _ => 0)

/-- The defining equation vanishes at the origin. -/
theorem puncturedEllipticOriginEval_equation :
    puncturedEllipticOriginEval K Omega (puncturedEllipticEquation K) = 0 := by
  simp [puncturedEllipticOriginEval, puncturedEllipticEquation]

/-- The origin defines a ring homomorphism from the coordinate ring of the
punctured curve to Omega. -/
def puncturedEllipticOriginRingHom :
    puncturedEllipticCoordinateRing K →+* Omega :=
  Ideal.Quotient.lift _
    (puncturedEllipticOriginEval K Omega)
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul, puncturedEllipticOriginEval_equation, zero_mul])

/-- The actual geometric point of the punctured elliptic curve at the origin,
with values in any K-algebra Omega. -/
def puncturedEllipticOriginPoint :
    Spec (CommRingCat.of Omega) ⟶ puncturedEllipticCurveScheme K :=
  Spec.map (CommRingCat.ofHom (puncturedEllipticOriginRingHom K Omega))

/-- The geometric fiber functor of the actual punctured elliptic curve at the
origin: finite etale covers are sent to their geometric fibers. -/
abbrev puncturedEllipticOriginFiberFunctor :=
  geometricFiberFunctor (X := puncturedEllipticCurveScheme K) Omega
    (puncturedEllipticOriginPoint K Omega)

/-- The actual geometric etale fundamental group of the once-punctured elliptic
curve at the origin, as the automorphism group of its geometric fiber functor. -/
abbrev puncturedEllipticOriginFundamentalGroup : Type (u + 1) :=
  curveEtaleFundamentalGroup (X := puncturedEllipticCurveScheme K) Omega
    (puncturedEllipticOriginPoint K Omega)

instance : Group (puncturedEllipticOriginFundamentalGroup K Omega) :=
  inferInstance

end LeanFormal.IUT.Foundations.Geometry
