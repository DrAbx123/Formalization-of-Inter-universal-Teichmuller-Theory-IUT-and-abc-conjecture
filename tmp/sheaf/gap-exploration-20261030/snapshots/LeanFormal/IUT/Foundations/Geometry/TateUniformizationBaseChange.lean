/-
  Base change of the Tate parametrization data along continuous field homomorphisms.

  The series-side naturality already exists (`coordinateSeries_map`,
  `yCoordinateSeries_map`); this file supplies the missing coefficient-level and
  curve-level layer:

  * `lambertSeries_map`, `a4_map`, `a6_map` -- the canonical `q`-coefficients are natural
    in continuous field homomorphisms;
  * `weierstrassCurve_map` -- the canonical `q`-series curve base changes;
  * `tateWeierstrassX_map` / `tateWeierstrassY_map` -- the coordinates of the candidate
    point are natural;
  * `coordinateParameterDomain_map_iff` -- the pole-excluded domain is transported
    backwards along the injective homomorphism;
  * `tateWeierstrassEquation_map` / `tateWeierstrassNonsingular_map` -- the named
    equation hypothesis and the nonsingularity data transport to the base-changed
    parameter.

  Scope: the coefficient, curve, coordinate, domain, equation and nonsingularity lemmas
  are coordinate-level statements; the final two sections additionally construct the
  induced map of orbit quotients and prove that the base-changed quotient point map
  sends the class of `u` to the point with base-changed coordinates.  The `q`-series
  equation identity (`tateWeierstrassEquation`) itself remains a named hypothesis, and
  no specialization to number-field completions or absolute Galois groups is claimed
  here.
-/

import LeanFormal.IUT.Foundations.Geometry.TateUniformizationPointMapReduction

namespace LeanFormal.IUT.TateCurve

noncomputable section

open WeierstrassCurve

/-! ## Injectivity of field homomorphisms -/

/-- A ring homomorphism from a field to a nontrivial ring is injective.  Stated here
to keep the transport lemmas below self-contained. -/
theorem fieldHom_injective
    {E : Type*} {F : Type*} [Field E] [Ring F] [Nontrivial F]
    (fieldHom : E →+* F) : Function.Injective fieldHom := by
  intro a b hab
  have hsub : fieldHom (a - b) = 0 := by rw [map_sub, hab, sub_self]
  by_contra hne
  have hprod : fieldHom (a - b) * fieldHom ((a - b)⁻¹) = 1 := by
    rw [← map_mul, mul_inv_cancel₀ (sub_ne_zero.mpr hne), map_one]
  rw [hsub, zero_mul] at hprod
  exact zero_ne_one hprod

/-! ## The Lambert series and the canonical coefficients -/

/-- The Lambert-series value is natural in continuous ring homomorphisms between
complete normed fields. -/
theorem lambertSeries_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    (weight : Nat) {q : E} (parameterNorm : ‖q‖ < 1) :
    fieldHom (lambertSeries E weight q) = lambertSeries F weight (fieldHom q) := by
  have sourceHasSum :
      HasSum (fun n : Nat => (n : E) ^ weight * q ^ n / (1 - q ^ n))
        (lambertSeries E weight q) :=
    (lambertSeries_summable E weight parameterNorm).hasSum
  have transportedHasSum := sourceHasSum.map fieldHom homContinuous
  have hfun :
      Function.comp (fieldHom : E → F)
          (fun n : Nat => (n : E) ^ weight * q ^ n / (1 - q ^ n)) =
        fun n : Nat => (n : F) ^ weight * (fieldHom q) ^ n / (1 - (fieldHom q) ^ n) := by
    funext n
    simp only [Function.comp_apply, map_mul, map_pow, map_natCast, map_div₀, map_sub, map_one]
  rw [hfun] at transportedHasSum
  exact transportedHasSum.tsum_eq.symm

/-- The `a4` coefficient of the canonical Tate equation is natural in continuous
field homomorphisms. -/
theorem a4_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) :
    fieldHom (a4 E q) = a4 F (fieldHom q) := by
  simp only [a4, map_mul, map_neg, map_ofNat,
    lambertSeries_map fieldHom homContinuous 3 parameterNorm]

/-- The `a6` coefficient of the canonical Tate equation is natural in continuous
field homomorphisms. -/
theorem a6_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    [CharZero E] [CharZero F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) :
    fieldHom (a6 E q) = a6 F (fieldHom q) := by
  simp only [a6, map_div₀, map_neg, map_add, map_mul, map_ofNat,
    lambertSeries_map fieldHom homContinuous 3 parameterNorm,
    lambertSeries_map fieldHom homContinuous 5 parameterNorm]

/-- The canonical `q`-series Weierstrass curve base changes along continuous field
homomorphisms. -/
theorem weierstrassCurve_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    [CharZero E] [CharZero F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) :
    (weierstrassCurve E q).map fieldHom = weierstrassCurve F (fieldHom q) := by
  simp only [weierstrassCurve, WeierstrassCurve.map, map_one, map_zero,
    a4_map fieldHom homContinuous parameterNorm,
    a6_map fieldHom homContinuous parameterNorm]

/-! ## The coordinates of the candidate point -/

/-- The `X`-coordinate of the candidate Tate point is natural in continuous field
homomorphisms. -/
theorem tateWeierstrassX_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) (u : E) :
    fieldHom (tateWeierstrassX q u) = tateWeierstrassX (fieldHom q) (fieldHom u) :=
  coordinateSeries_map fieldHom homContinuous parameterNorm u

/-- The `Y`-coordinate of the candidate Tate point is natural in continuous field
homomorphisms. -/
theorem tateWeierstrassY_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) (u : E) :
    fieldHom (tateWeierstrassY q u) = tateWeierstrassY (fieldHom q) (fieldHom u) :=
  yCoordinateSeries_map fieldHom homContinuous parameterNorm u

/-! ## The pole-excluded domain -/

/-- The pole-excluded parameter domain is transported backwards along a field
homomorphism: `fieldHom u` is a legal parameter for `fieldHom q` exactly when `u` is a
legal parameter for `q`.  Injectivity of the homomorphism is what makes this an
equivalence. -/
theorem coordinateParameterDomain_map_iff
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (q u : E) :
    fieldHom u ∈ coordinateParameterDomain (fieldHom q) ↔
      u ∈ coordinateParameterDomain q := by
  have hinjective : Function.Injective fieldHom := fieldHom_injective fieldHom
  simp only [coordinateParameterDomain, coordinatePoleExclusion, Set.mem_setOf_eq]
  constructor
  · rintro ⟨hne, hpole⟩
    refine ⟨fun hzero => hne (by rw [hzero, map_zero]), fun n hv => hpole n ?_⟩
    rw [← map_zpow₀, ← map_mul, hv, map_one]
  · rintro ⟨hne, hpole⟩
    refine ⟨fun hzero => hne (hinjective (by rw [hzero, map_zero])), fun n hv => hpole n ?_⟩
    exact hinjective (by rw [map_mul, map_zpow₀, hv, map_one])

/-! ## Equation and nonsingularity transport -/

/-- The named equation hypothesis transports along continuous field homomorphisms. -/
theorem tateWeierstrassEquation_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    [CharZero E] [CharZero F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q u : E} (parameterNorm : ‖q‖ < 1) (h : tateWeierstrassEquation q u) :
    tateWeierstrassEquation (fieldHom q) (fieldHom u) := by
  unfold tateWeierstrassEquation at h ⊢
  rw [← weierstrassCurve_map fieldHom homContinuous parameterNorm,
    ← tateWeierstrassX_map fieldHom homContinuous parameterNorm,
    ← tateWeierstrassY_map fieldHom homContinuous parameterNorm]
  exact WeierstrassCurve.Affine.Equation.map fieldHom h

/-- The nonsingularity data of the candidate point transports, parameter by parameter,
along continuous field homomorphisms.  This is the point-data input restricted to the
image of the homomorphism; the data at parameters outside the image is not claimed. -/
theorem tateWeierstrassNonsingular_map
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    [CharZero E] [CharZero F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1)
    (pointData : TateWeierstrassPointData (K := E) q)
    (u : ↥(coordinateParameterDomain q)) :
    (weierstrassCurve F (fieldHom q)).toAffine.Nonsingular
      (tateWeierstrassX (fieldHom q) (fieldHom (u : E)))
      (tateWeierstrassY (fieldHom q) (fieldHom (u : E))) := by
  rw [← weierstrassCurve_map fieldHom homContinuous parameterNorm,
    ← tateWeierstrassX_map fieldHom homContinuous parameterNorm,
    ← tateWeierstrassY_map fieldHom homContinuous parameterNorm]
  exact (WeierstrassCurve.Affine.map_nonsingular (weierstrassCurve E q)
      (fieldHom_injective fieldHom) (tateWeierstrassX q (u : E))
      (tateWeierstrassY q (u : E))).mpr (pointData u)

/-! ## Functoriality of the parameter quotient along field homomorphisms -/

/-- The image of a nonzero parameter under a field homomorphism is nonzero. -/
theorem fieldHom_ne_zero
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) {q : E} (qNeZero : q ≠ 0) :
    fieldHom q ≠ 0 :=
  fun hzero => qNeZero (fieldHom_injective fieldHom (by rw [hzero, map_zero]))

/-- The pole-excluded domain mapped forward along a field homomorphism: the image of a
legal parameter is a legal parameter for the base-changed coefficient. -/
def coordinateParameterDomainMap
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (q : E) (u : ↥(coordinateParameterDomain q)) :
    ↥(coordinateParameterDomain (fieldHom q)) :=
  ⟨fieldHom (u : E), (coordinateParameterDomain_map_iff fieldHom q (u : E)).mpr u.2⟩

/-- Orbit membership is preserved by a field homomorphism. -/
theorem tateParameterOrbitRel_map
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (q : E) {u v : ↥(coordinateParameterDomain q)}
    (orbitRel : tateParameterOrbitRel q u v) :
    tateParameterOrbitRel (fieldHom q) (coordinateParameterDomainMap fieldHom q u)
      (coordinateParameterDomainMap fieldHom q v) := by
  obtain ⟨m, hm⟩ := orbitRel
  refine ⟨m, ?_⟩
  change fieldHom q ^ m * fieldHom (u : E) = fieldHom (v : E)
  rw [← map_zpow₀, ← map_mul, hm]

/-- The induced map of parameter quotients. -/
noncomputable def tateParameterQuotientMap
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (q : E) (qNeZero : q ≠ 0) :
    TateParameterQuotient q qNeZero →
      TateParameterQuotient (fieldHom q) (fieldHom_ne_zero fieldHom qNeZero) :=
  Quotient.map (coordinateParameterDomainMap fieldHom q)
    (fun _ _ orbitRel => tateParameterOrbitRel_map fieldHom q orbitRel)

/-- Value of the induced quotient map on a class. -/
theorem tateParameterQuotientMap_mk
    {E : Type*} {F : Type*} [Field E] [Field F]
    (fieldHom : E →+* F) (q : E) (qNeZero : q ≠ 0)
    (u : ↥(coordinateParameterDomain q)) :
    tateParameterQuotientMap fieldHom q qNeZero (Quotient.mk _ u) =
      Quotient.mk _ (coordinateParameterDomainMap fieldHom q u) :=
  rfl

/-! ## Coordinate equivariance of the quotient point map -/

/-- The base-changed quotient point map sends the class of `u` to the point with the
base-changed coordinates: the coordinate-level form of equivariance of the Tate
uniformization under field homomorphisms.  The image point data is an explicit
hypothesis; the transported nonsingularity proof is supplied by
`tateWeierstrassNonsingular_map`. -/
theorem tateQuotientPoint_map_mk
    {E : Type*} {F : Type*} [NontriviallyNormedField E] [CompleteSpace E] [NormedField F]
    [CharZero E] [CharZero F]
    (fieldHom : E →+* F) (homContinuous : Continuous fieldHom)
    {q : E} (parameterNorm : ‖q‖ < 1) (qNeZero : q ≠ 0)
    (pointData : TateWeierstrassPointData (K := E) q)
    (imagePointData : TateWeierstrassPointData (K := F) (fieldHom q))
    (u : ↥(coordinateParameterDomain q)) :
    tateQuotientPoint (fieldHom q) (fieldHom_ne_zero fieldHom qNeZero) imagePointData
        (tateParameterQuotientMap fieldHom q qNeZero (Quotient.mk _ u)) =
      WeierstrassCurve.Affine.Point.some (tateWeierstrassX (fieldHom q) (fieldHom (u : E)))
        (tateWeierstrassY (fieldHom q) (fieldHom (u : E)))
        (tateWeierstrassNonsingular_map fieldHom homContinuous parameterNorm pointData u) := by
  rw [tateParameterQuotientMap_mk]
  rw [tateQuotientPoint_mk]
  change WeierstrassCurve.Affine.Point.some (tateWeierstrassX (fieldHom q)
        (fieldHom (u : E)))
      (tateWeierstrassY (fieldHom q) (fieldHom (u : E)))
      (imagePointData (coordinateParameterDomainMap fieldHom q u)) =
    WeierstrassCurve.Affine.Point.some (tateWeierstrassX (fieldHom q) (fieldHom (u : E)))
      (tateWeierstrassY (fieldHom q) (fieldHom (u : E)))
      (tateWeierstrassNonsingular_map fieldHom homContinuous parameterNorm pointData u)
  rw [WeierstrassCurve.Affine.Point.some.injEq]
  exact ⟨rfl, rfl⟩

end

end LeanFormal.IUT.TateCurve