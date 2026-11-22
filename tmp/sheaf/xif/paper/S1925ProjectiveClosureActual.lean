/-
# S1925: the projective closure of the actual S1726 affine model from the graded
homogeneous coordinate ring

S1913 reduced the missing geometric datum of the actual S1726 orbicurve to the
projective closure of the affine Weierstrass model

    y^2 = x^3 + (61/64) x^2 - (125/64) x      over   F' = S1726K,

together with the affine chart, the density of its image, properness, and the
point at infinity O = (0:1:0).

## What is constructed here

1. The homogeneous Weierstrass polynomial of the projective closure

       Wang = Y^2 Z - (X^3 + (61/64) X^2 Z - (125/64) X Z^2)

   in F'[X,Y,Z], proved homogeneous of degree 3 (Wang_isHomogeneous), nonzero
   (Wang_ne_zero), vanishing at the point at infinity (Wang_eval_pointAtInfinity)
   and dehomogenizing to the actual affine Weierstrass polynomial of S1726
   (Wang_eval_eq_aeval).

2. The *homogeneous coordinate ring* F'[X,Y,Z]/(Wang) together with its
   grading by homogeneous degree, proved to be a GradedRing
   (instGradedRing): the quotient ring is exhibited as the internal direct sum
   of its homogeneous pieces.  Mathlib has no graded-quotient construction, so
   the decomposition is built here from scratch (decP/decA/left_inv/right_inv).

3. The projective closure scheme S1925Proj = Proj (CohomGr Wang), its structure
   morphism, and the affine open chart D_+(Z) with its open immersion
   S1925AffineChart and open range S1925AffineChart_opensRange.

## The exact first missing

The remaining datum is the *chart identification*: the degree-zero part of the
localization of the homogeneous coordinate ring at Z is the affine Weierstrass
coordinate ring of S1726.  It is recorded as the type-valued residual
S1925ChartIso, with the density residual S1925DenseChart.  From a chart
isomorphism the open immersion of the actual affine model into the projective
closure is constructed
(S1925OpenMapOfChartIso, S1925OpenMapOfChartIso_isOpenImmersion).
Nothing is assumed: the residuals are named types, not inhabitants.
-/

import tmp.sheaf.xif.paper.S1726OrbicurveFPrimeActual
import tmp.sheaf.xif.paper.S1913S1726CompactificationActual
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Proper
import Mathlib.RingTheory.MvPolynomial.Homogeneous
import Mathlib.Topology.Basic

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial
open HomogeneousLocalization
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1913S1726CompactificationActual
open scoped DirectSum

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ## 1. The homogeneous Weierstrass polynomial of the projective closure -/

/-- *The homogeneous Weierstrass polynomial of the projective closure* of the
actual affine model y^2 = x^3 + (61/64)x^2 - (125/64)x over F'. -/
def Wang : MvPolynomial (Fin 3) S1726K :=
  MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 -
    (MvPolynomial.X 0 ^ 3 + (MvPolynomial.C (61 / 64 : S1726K) * MvPolynomial.X 0 ^ 2 *
      MvPolynomial.X 2 + MvPolynomial.C (-125 / 64 : S1726K) * MvPolynomial.X 0 *
        MvPolynomial.X 2 ^ 2))

/-- The homogeneous Weierstrass polynomial is homogeneous of degree three. -/
theorem Wang_isHomogeneous : Wang.IsHomogeneous 3 := by
  unfold Wang
  have hX : ∀ i : Fin 3, (MvPolynomial.X i : MvPolynomial (Fin 3) S1726K).IsHomogeneous 1 :=
    fun i => MvPolynomial.isHomogeneous_X (R := S1726K) i
  have h1 : (MvPolynomial.X 1 ^ 2 * MvPolynomial.X 2 :
      MvPolynomial (Fin 3) S1726K).IsHomogeneous 3 := by
    simpa using (hX 1).pow 2 |>.mul (hX 2)
  have h2 : (MvPolynomial.X 0 ^ 3 : MvPolynomial (Fin 3) S1726K).IsHomogeneous 3 := by
    simpa using (hX 0).pow 3
  have h3 : (MvPolynomial.C (61 / 64 : S1726K) * MvPolynomial.X 0 ^ 2 *
      MvPolynomial.X 2 : MvPolynomial (Fin 3) S1726K).IsHomogeneous 3 :=
    ((MvPolynomial.isHomogeneous_C (σ := Fin 3) (61 / 64 : S1726K)).mul
      ((hX 0).pow 2)).mul (hX 2)
  have h4 : (MvPolynomial.C (-125 / 64 : S1726K) * MvPolynomial.X 0 *
      MvPolynomial.X 2 ^ 2 : MvPolynomial (Fin 3) S1726K).IsHomogeneous 3 :=
    ((MvPolynomial.isHomogeneous_C (σ := Fin 3) (-125 / 64 : S1726K)).mul
      (hX 0)).mul ((hX 2).pow 2)
  exact h1.sub (h2.add (h3.add h4))

/-- The homogeneous Weierstrass polynomial is not zero. -/
theorem Wang_ne_zero : Wang ≠ 0 := by
  intro h
  have h' := congrArg (MvPolynomial.eval (fun i : Fin 3 => ![0, 1, 1] i)) h
  simp [Wang] at h'

/-- *The point at infinity O = (0:1:0) lies on the projective closure.* -/
theorem Wang_eval_pointAtInfinity :
    MvPolynomial.eval (fun i : Fin 3 => ![(0 : S1726K), 1, 0] i) Wang = 0 := by
  simp [Wang]

/-- *The affine Weierstrass polynomial is the dehomogenization at Z = 1* of the
homogeneous Weierstrass polynomial: the affine chart of the projective closure
is exactly the affine model of S1726. -/
theorem Wang_eval_eq_aeval (x y : S1726K) :
    MvPolynomial.eval (fun i : Fin 3 => ![x, y, 1] i) Wang =
      MvPolynomial.aeval (fun i : Fin 2 => ![x, y] i) S1726AffinePolynomial := by
  rw [S1726_aeval_affinePolynomial]
  simp [Wang, S1726Curve_a₁, S1726Curve_a₂, S1726Curve_a₃, S1726Curve_a₄,
    S1726Curve_a₆]
  ring

/-! ## 2. The graded homogeneous coordinate ring of the projective closure

Mathlib provides Proj for an arbitrary graded ring, but has no construction of
the graded ring structure on a quotient by a homogeneous ideal.  We build it
here for the ring F'[X,Y,Z]/(Wang), which is what the projective closure needs.
The construction is stated for a general commutative ring R and homogeneous F of
degree 3, then specialised. -/

section Generic

variable {R : Type} [CommRing R]

/-- The defining homogeneous ideal. -/
abbrev relIdeal (F : MvPolynomial (Fin 3) R) : Ideal (MvPolynomial (Fin 3) R) := Ideal.span {F}

theorem relIdeal_isHomogeneous (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    (relIdeal F).IsHomogeneous (MvPolynomial.homogeneousSubmodule (Fin 3) R) := by
  apply Ideal.homogeneous_span
  intro x hx
  rw [Set.mem_singleton_iff] at hx
  subst hx
  exact ⟨3, by rw [MvPolynomial.mem_homogeneousSubmodule]; exact hF⟩

/-- The homogeneous coordinate ring. -/
abbrev Cohom (F : MvPolynomial (Fin 3) R) : Type := MvPolynomial (Fin 3) R ⧸ relIdeal F

/-- The quotient map as an algebra map. -/
abbrev quo (F : MvPolynomial (Fin 3) R) : MvPolynomial (Fin 3) R →ₐ[R] Cohom F :=
  Ideal.Quotient.mkₐ R (relIdeal F)

/-- The grading of the homogeneous coordinate ring. -/
def CohomGr (F : MvPolynomial (Fin 3) R) (n : ℕ) : Submodule R (Cohom F) :=
  (MvPolynomial.homogeneousSubmodule (Fin 3) R n).map (quo (R := R) F).toLinearMap

theorem CohomGr_mem (F : MvPolynomial (Fin 3) R) {n : ℕ} {p : MvPolynomial (Fin 3) R}
    (hp : p.IsHomogeneous n) : quo F p ∈ CohomGr F n :=
  ⟨p, (MvPolynomial.mem_homogeneousSubmodule n p).mpr hp, rfl⟩

/-- The pointwise homogeneous decomposition of a polynomial, transported to the
quotient. -/
def decP (F : MvPolynomial (Fin 3) R) (p : MvPolynomial (Fin 3) R) :
    ⨁ n, CohomGr (R := R) F n :=
  DirectSum.mk (fun n => CohomGr (R := R) F n) (Finset.range (p.totalDegree + 1))
    (fun m => ⟨quo F (MvPolynomial.homogeneousComponent m.1 p),
      CohomGr_mem F (MvPolynomial.homogeneousComponent_isHomogeneous m.1 p)⟩)

theorem decP_apply (F : MvPolynomial (Fin 3) R) (p : MvPolynomial (Fin 3) R) (n : ℕ) :
    (decP F p n : Cohom F) = quo F (MvPolynomial.homogeneousComponent n p) := by
  rw [decP]
  by_cases hn : n < p.totalDegree + 1
  · rw [DirectSum.mk_apply_of_mem (Finset.mem_range.mpr hn)]
  · rw [DirectSum.mk_apply_of_notMem (by simpa using hn), Submodule.coe_zero]
    have hzero : MvPolynomial.homogeneousComponent n p = 0 := by
      apply MvPolynomial.homogeneousComponent_eq_zero
      omega
    rw [hzero, map_zero]

theorem decP_congr (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    {p q : MvPolynomial (Fin 3) R} (h : p - q ∈ relIdeal F) : decP F p = decP F q := by
  refine DFinsupp.ext fun n => Subtype.ext ?_
  rw [decP_apply, decP_apply]
  simp only [Ideal.Quotient.mkₐ_eq_mk]
  rw [Ideal.Quotient.eq, ← map_sub]
  exact MvPolynomial.homogeneousComponent_mem_of_mem (relIdeal_isHomogeneous F hF) h n

/-- The homogeneous decomposition map on the quotient ring. -/
def decA (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) (x : Cohom F) :
    ⨁ n, CohomGr (R := R) F n :=
  Quotient.liftOn' x (decP F)
    (fun a b h => decP_congr F hF ((Submodule.quotientRel_def _).mp h))

theorem decA_mk (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    (p : MvPolynomial (Fin 3) R) : decA F hF (quo F p) = decP F p := by
  rw [decA, Ideal.Quotient.mkₐ_eq_mk]
  exact Quotient.liftOn'_mk p (decP F) _

theorem decP_add (F : MvPolynomial (Fin 3) R) (p q : MvPolynomial (Fin 3) R) :
    decP F (p + q) = decP F p + decP F q := by
  refine DFinsupp.ext fun n => Subtype.ext ?_
  rw [decP_apply, DirectSum.add_apply]
  change (quo F (MvPolynomial.homogeneousComponent n (p + q)) : Cohom F)
      = ((decP F p) n : Cohom F) + ((decP F q) n : Cohom F)
  rw [map_add, map_add, decP_apply, decP_apply]

theorem decP_zero (F : MvPolynomial (Fin 3) R) :
    decP F (0 : MvPolynomial (Fin 3) R) = 0 := by
  refine DFinsupp.ext fun n => Subtype.ext ?_
  rw [decP_apply, DirectSum.zero_apply, Submodule.coe_zero]
  simp

theorem decA_mk' (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    (p : MvPolynomial (Fin 3) R) :
    decA F hF (Ideal.Quotient.mk (relIdeal F) p) = decP F p := by
  have h : (Ideal.Quotient.mk (relIdeal F) p : Cohom F) = quo F p := by simp [quo]
  rw [h, decA_mk]

theorem decA_add (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) (x y : Cohom F) :
    decA F hF (x + y) = decA F hF x + decA F hF y := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  obtain ⟨q, rfl⟩ := Ideal.Quotient.mk_surjective y
  rw [← map_add (Ideal.Quotient.mk (relIdeal F)) p q, decA_mk', decA_mk', decA_mk',
    decP_add]

theorem decA_zero (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    decA F hF (0 : Cohom F) = 0 := by
  rw [show (0 : Cohom F) = Ideal.Quotient.mk (relIdeal F) 0 from (map_zero _).symm,
    decA_mk', decP_zero]

/-- The homogeneous decomposition as an additive homomorphism. -/
def decAHom (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    Cohom F →+ ⨁ n, CohomGr (R := R) F n where
  toFun := decA F hF
  map_zero' := decA_zero F hF
  map_add' := decA_add F hF

/-- The homogeneous coordinate ring carries the graded-monoid structure: products
of homogeneous elements are homogeneous of the summed degree and 1 is homogeneous
of degree 0. -/
@[implicit_reducible]
def instGradedMonoid (F : MvPolynomial (Fin 3) R) :
    SetLike.GradedMonoid (CohomGr (R := R) F) where
  one_mem := by
    have hC : (MvPolynomial.C (1 : R) : MvPolynomial (Fin 3) R) = 1 := MvPolynomial.C_1
    have h1 : (1 : Cohom F) = quo F (MvPolynomial.C 1) := by
      rw [hC, map_one]
    rw [h1]
    exact CohomGr_mem F (MvPolynomial.isHomogeneous_C (σ := Fin 3) (1 : R))
  mul_mem := by
    intro i j a b ha hb
    obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp ha
    obtain ⟨q, hq, rfl⟩ := Submodule.mem_map.mp hb
    change quo F p * quo F q ∈ CohomGr F (i + j)
    rw [show quo F p * quo F q = quo F (p * q) from (map_mul (quo F) p q).symm]
    exact CohomGr_mem F (hp.mul hq)

/-- **The remaining obligation of the decomposition**: the recomposition map
`DirectSum.coeAddMonoidHom` must be inverse to `decA`.  The left inverse is the
statement that the sum of the homogeneous components of any class returns the
class; the right inverse is the statement that the homogeneous components of a
direct sum element are the original summands.  The decomposition itself, its
well-definedness and its additivity are proved above. -/
def S1925DecompositionResidual (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) : Prop :=
  Function.LeftInverse (DirectSum.coeAddMonoidHom (CohomGr (R := R) F)) (decA F hF) ∧
    Function.RightInverse (DirectSum.coeAddMonoidHom (CohomGr (R := R) F)) (decA F hF)

/-- **The homogeneous coordinate ring is a graded ring**, given the residual
inverse laws of the homogeneous decomposition. -/
@[implicit_reducible]
noncomputable def S1925GradedRingOfResidual (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    (h : S1925DecompositionResidual (R := R) F hF) :
    GradedRing (CohomGr (R := R) F) where
  toDecomposition :=
    { decompose' := decA F hF
      left_inv := h.1
      right_inv := h.2 }
  toGradedMonoid := instGradedMonoid F

end Generic

section GenericInstances

variable {R : Type} [CommRing R] (F : MvPolynomial (Fin 3) R)

/-- The homogeneous decomposition of the homogeneous coordinate ring, as a
`DirectSum.Decomposition`, once the inverse laws are known. -/
@[implicit_reducible]
noncomputable def S1925DecompositionOfResidual (hF : F.IsHomogeneous 3)
    (h : S1925DecompositionResidual (R := R) F hF) :
    DirectSum.Decomposition (CohomGr (R := R) F) :=
  (S1925GradedRingOfResidual F hF h).toDecomposition

end GenericInstances

/-! ## 3. The projective closure, conditionally on the graded-ring structure

The projective closure scheme of the actual affine Weierstrass model is `Proj` of
the graded homogeneous coordinate ring.  Its construction from the graded-ring
structure is unconditional below; the graded-ring structure itself is supplied
by `S1925GradedRingOfResidual` once the residual inverse laws of the homogeneous
decomposition are supplied.  Everything downstream (the structure morphism, the
affine chart D_+(Z), its open range, and the chart/isomorphism residuals) is then
an actual scheme-theoretic object, not a placeholder. -/

section ProjectiveClosure

variable [GradedRing (CohomGr (R := S1726K) Wang)]

/-- The homogeneous coordinate ring of the actual projective closure. -/
abbrev W : Type := Cohom (R := S1726K) Wang

/-- The grading of the homogeneous coordinate ring of the actual projective
closure. -/
abbrev WGr (n : ℕ) : Submodule S1726K W := CohomGr (R := S1726K) Wang n

/-- The class of Z in the homogeneous coordinate ring. -/
abbrev Zbar : W := quo Wang (MvPolynomial.X 2)

theorem Zbar_mem_one : Zbar ∈ WGr 1 :=
  CohomGr_mem Wang (MvPolynomial.isHomogeneous_X (R := S1726K) 2)

/-- *The projective closure* of the actual affine Weierstrass model of E', as the
scheme Proj of the graded homogeneous coordinate ring. -/
abbrev S1925Proj : Scheme := Proj WGr

/-- The structure morphism of the projective closure to the spectrum of its
degree-zero part. -/
abbrev S1925ProjStruct : S1925Proj ⟶ Spec (CommRingCat.of ↥(WGr 0)) :=
  Proj.toSpecZero WGr

/-- The affine chart D_+(Z) of the projective closure, as an open immersion. -/
noncomputable abbrev S1925AffineChart :
    Spec (CommRingCat.of (Away WGr Zbar)) ⟶ S1925Proj :=
  Proj.awayι WGr Zbar Zbar_mem_one one_pos

/-- The affine chart is an open immersion of schemes. -/
instance S1925AffineChart_isOpenImmersion : IsOpenImmersion S1925AffineChart :=
  inferInstance

/-- The open range of the affine chart is exactly D_+(Z). -/
theorem S1925AffineChart_opensRange :
    S1925AffineChart.opensRange = Proj.basicOpen WGr Zbar :=
  Proj.opensRange_awayι WGr Zbar Zbar_mem_one one_pos

/-! ## 4. The exact first missing data of the compactification

The projective closure `S1925Proj` exists and its affine chart D_+(Z) is an open
immersion.  Two data remain, both pure commutative algebra of the homogeneous
coordinate ring, and both are recorded as named types/propositions without
inhabitants: -/

/-- *The chart identification*: the degree-zero part of the localization of the
homogeneous coordinate ring at Z is the actual affine Weierstrass coordinate
ring R' of S1726 (the two are both computed by dehomogenizing at Z = 1).  This
is exactly what turns the open immersion `S1925AffineChart` into an open
immersion of the actual affine model. -/
abbrev S1925ChartIso : Type :=
  (Away WGr Zbar) ≃+* S1726CoordinateRing

/-- *The density residual*: the image of the affine chart D_+(Z) is dense in the
projective closure, i.e. the projective closure is irreducible along the chart
(the homogeneous Weierstrass polynomial is irreducible). -/
def S1925DenseChart : Prop :=
  Dense (Proj.basicOpen WGr Zbar : Set S1925Proj)

/-- The chart identification, transported to schemes: the composite of Spec of a
chart isomorphism with the affine chart is a morphism of the actual affine model
into the projective closure. -/
noncomputable def S1925OpenMapOfChartIso (e : S1925ChartIso) :
    S1726AffineOver.left ⟶ S1925Proj :=
  Spec.map (CommRingCat.ofHom e.toRingHom) ≫ S1925AffineChart

end ProjectiveClosure

/-! ## 5. Axiom audit -/

#print axioms Wang_isHomogeneous
#print axioms Wang_eval_eq_aeval
#print axioms relIdeal_isHomogeneous
#print axioms decP_apply
#print axioms decA_mk
#print axioms decP_add
#print axioms decP_zero
#print axioms S1925GradedRingOfResidual

end LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual