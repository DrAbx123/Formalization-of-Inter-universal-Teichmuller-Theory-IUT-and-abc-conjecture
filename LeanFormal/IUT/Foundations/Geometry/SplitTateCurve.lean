import LeanFormal.IUT.Foundations.Geometry.CurveEtaleFundamentalGroup

set_option linter.unusedSectionVars false
noncomputable section

open CategoryTheory AlgebraicGeometry

namespace LeanFormal.IUT.Foundations.Geometry

universe u

/-!
# Extension for task-133: the split Tate model y^2 + x*y = x^3 + 5

The model y^2 = x^3 - x is kept only as an explicitly named generic test curve
(it is a genuine elliptic curve with discriminant 64 and j = 1728, but it is NOT
the concrete source/test model of the project).  The concrete split model is

  splitTateWeierstrassCurve : y^2 + x*y = x^3 + 5
  (a1, a2, a3, a4, a6) = (1, 0, 0, 0, 5),

with discriminant -10805, j = -1/10805, and bad reduction at 5 (5 | Delta,
25 does not divide Delta, so v_5(Delta) = 1).  We construct its affine scheme,
a genuine geometric point (x,y) = (0, y0) with y0^2 = 5 over a K-algebra Omega,
the geometric fiber functor at that point and the actual fiber-functor
automorphism group.  No source Pi_v claim is made; the profinite Pi_v/Galois
interface remains the data record of the production file.
-/

variable (K : Type u) [Field K]

/-! ## 1. Generic test curve y^2 = x^3 - x (not the source model) -/

/-- Generic test Weierstrass curve y^2 = x^3 - x.  This is a genuine elliptic
curve (Delta = 64, j = 1728) used only as a named test curve; it is not the
concrete split source/test model. -/
def genericTestCurveY2EqX3SubX (K : Type u) [Field K] : WeierstrassCurve K :=
  { a₁ := 0, a₂ := 0, a₃ := 0, a₄ := -1, a₆ := 0 }

theorem genericTestCurveY2EqX3SubX_Δ (K : Type u) [Field K] :
    (genericTestCurveY2EqX3SubX K).Δ = 64 := by
  simp [genericTestCurveY2EqX3SubX, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-! ## 2. The concrete split Tate model y^2 + x*y = x^3 + 5 -/

/-- The split Tate Weierstrass model y^2 + x*y = x^3 + 5 over a field K,
i.e. (a1,a2,a3,a4,a6) = (1,0,0,0,5). -/
def splitTateWeierstrassCurve (K : Type u) [Field K] : WeierstrassCurve K :=
  { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 5 }

theorem splitTateWeierstrassCurve_Δ (K : Type u) [Field K] :
    (splitTateWeierstrassCurve K).Δ = -10805 := by
  simp [splitTateWeierstrassCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
  norm_num

/-- The split Tate curve is elliptic over K when -10805 is nonzero. -/
theorem splitTateWeierstrassCurve_isElliptic (K : Type u) [Field K]
    (h : (-10805 : K) ≠ 0) : (splitTateWeierstrassCurve K).IsElliptic := by
  rw [WeierstrassCurve.isElliptic_iff, splitTateWeierstrassCurve_Δ]
  exact isUnit_iff_ne_zero.mpr h

/-- The j-invariant of the split Tate model is -1/10805. -/
theorem splitTateWeierstrassCurve_j (K : Type u) [Field K] [CharZero K] :
    haveI : (splitTateWeierstrassCurve K).IsElliptic :=
      splitTateWeierstrassCurve_isElliptic K (by norm_num)
    (splitTateWeierstrassCurve K).j = (10805 : K)⁻¹ * (-1) := by
  haveI : (splitTateWeierstrassCurve K).IsElliptic :=
    splitTateWeierstrassCurve_isElliptic K (by norm_num)
  simp [WeierstrassCurve.j, splitTateWeierstrassCurve, WeierstrassCurve.Δ,
    WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆,
    WeierstrassCurve.b₈, WeierstrassCurve.c₄]
  norm_num

/-- Over Q the split Tate j-invariant is exactly -1/10805. -/
theorem splitTateWeierstrassCurveQ_j :
    haveI : (splitTateWeierstrassCurve ℚ).IsElliptic :=
      splitTateWeierstrassCurve_isElliptic ℚ (by norm_num)
    (splitTateWeierstrassCurve ℚ).j = (-1 : ℚ) / 10805 := by
  haveI : (splitTateWeierstrassCurve ℚ).IsElliptic :=
    splitTateWeierstrassCurve_isElliptic ℚ (by norm_num)
  rw [splitTateWeierstrassCurve_j ℚ]
  norm_num


/-! ## 3. Integral model and bad reduction at 5 -/

/-- The split Tate model over Z. -/
def splitTateWeierstrassCurveZ : WeierstrassCurve ℤ :=
  { a₁ := 1, a₂ := 0, a₃ := 0, a₄ := 0, a₆ := 5 }

theorem splitTateWeierstrassCurveZ_Δ : splitTateWeierstrassCurveZ.Δ = -10805 := by
  simp [splitTateWeierstrassCurveZ, WeierstrassCurve.Δ, WeierstrassCurve.b₂,
    WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]

/-- Bad reduction at 5: the discriminant is divisible by 5. -/
theorem splitTateWeierstrassCurveZ_badReductionAtFive :
    (5 : ℤ) ∣ splitTateWeierstrassCurveZ.Δ := by
  rw [splitTateWeierstrassCurveZ_Δ]
  norm_num

/-- The valuation v_5(Delta) is exactly 1: 25 does not divide Delta. -/
theorem splitTateWeierstrassCurveZ_v5_eq_one :
    ¬ (25 : ℤ) ∣ splitTateWeierstrassCurveZ.Δ := by
  rw [splitTateWeierstrassCurveZ_Δ]
  norm_num

/-! ## 4. The affine scheme of the split model and a genuine geometric point

The affine equation is y^2 + x*y = x^3 + 5.  A genuine point is (x,y) = (0,y0)
with y0^2 = 5; over a K-algebra Omega such y0 is a parameter. -/

/-- The affine equation y^2 + x*y - x^3 - 5 of the split model. -/
def splitTateEquation (K : Type u) [Field K] : MvPolynomial (Fin 2) K :=
  (MvPolynomial.X 1) ^ 2 + (MvPolynomial.X 0) * (MvPolynomial.X 1) -
    (MvPolynomial.X 0) ^ 3 - MvPolynomial.C 5

/-- The coordinate ring of the affine split model. -/
abbrev splitTateCoordinateRing (K : Type u) [Field K] : Type u :=
  MvPolynomial (Fin 2) K ⧸
    Ideal.span ({splitTateEquation K} : Set (MvPolynomial (Fin 2) K))

/-- The affine scheme of the split Tate model y^2 + x*y = x^3 + 5. -/
abbrev splitTateCurveScheme (K : Type u) [Field K] : Scheme.{u} :=
  Spec (CommRingCat.of (splitTateCoordinateRing K))

variable (Omega : Type u) [Field Omega] [Algebra K Omega]

/-- Evaluation at (x,y) = (0,y0) for y0^2 = 5 (the image of 5 in Omega). -/
def splitTatePointEval (y0 : Omega) : MvPolynomial (Fin 2) K →+* Omega :=
  MvPolynomial.eval₂Hom (algebraMap K Omega)
    (fun i : Fin 2 => if i = 0 then 0 else y0)

/-- The defining equation vanishes at (0,y0) when y0^2 = 5. -/
theorem splitTatePointEval_equation (y0 : Omega)
    (hy0 : y0 ^ 2 = algebraMap K Omega 5) :
    splitTatePointEval K Omega y0 (splitTateEquation K) = 0 := by
  simp [splitTatePointEval, splitTateEquation, hy0]

/-- The ring homomorphism from the split coordinate ring to Omega induced by
the point (0,y0), y0^2 = 5. -/
def splitTatePointRingHom (y0 : Omega)
    (hy0 : y0 ^ 2 = algebraMap K Omega 5) :
    splitTateCoordinateRing K →+* Omega :=
  Ideal.Quotient.lift _
    (splitTatePointEval K Omega y0)
    (by
      intro a ha
      rw [Ideal.mem_span_singleton] at ha
      obtain ⟨c, rfl⟩ := ha
      rw [map_mul, splitTatePointEval_equation K Omega y0 hy0, zero_mul])

/-- The genuine geometric point of the split Tate curve at (0,y0), y0^2 = 5. -/
def splitTatePoint (y0 : Omega) (hy0 : y0 ^ 2 = algebraMap K Omega 5) :
    Spec (CommRingCat.of Omega) ⟶ splitTateCurveScheme K :=
  Spec.map (CommRingCat.ofHom (splitTatePointRingHom K Omega y0 hy0))

/-- The geometric fiber functor of the split Tate curve at the point (0,y0). -/
abbrev splitTateFiberFunctor (y0 : Omega) (hy0 : y0 ^ 2 = algebraMap K Omega 5) :=
  geometricFiberFunctor (X := splitTateCurveScheme K) Omega
    (splitTatePoint K Omega y0 hy0)

/-- The actual geometric etale fundamental group of the split Tate curve at the
point (0,y0), as the automorphism group of its geometric fiber functor. -/
abbrev splitTateFundamentalGroup (y0 : Omega)
    (hy0 : y0 ^ 2 = algebraMap K Omega 5) : Type (u + 1) :=
  curveEtaleFundamentalGroup (X := splitTateCurveScheme K) Omega
    (splitTatePoint K Omega y0 hy0)

instance splitTateFundamentalGroupGroup (y0 : Omega)
    (hy0 : y0 ^ 2 = algebraMap K Omega 5) :
    Group (splitTateFundamentalGroup K Omega y0 hy0) :=
  inferInstance

end LeanFormal.IUT.Foundations.Geometry
