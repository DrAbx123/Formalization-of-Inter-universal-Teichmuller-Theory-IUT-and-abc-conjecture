/-
# S1936: the homogeneous decomposition of the actual projective closure is a
graded-ring decomposition

S1925 constructed the homogeneous coordinate ring

    W = F'[X,Y,Z]/(Wang),    Wang = Y^2 Z - (X^3 + (61/64) X^2 Z - (125/64) X Z^2),

of the projective closure of the actual S1726 affine Weierstrass model, together
with its grading `CohomGr` by homogeneous degree, the pointwise decomposition
`decP` of a polynomial into homogeneous components, the induced additive map
`decA` on the quotient, and the graded-monoid structure `instGradedMonoid` on
the homogeneous pieces.  It isolated the remaining algebraic obligation as

    S1925DecompositionResidual F hF :
      LeftInverse (DirectSum.coeAddMonoidHom (CohomGr F)) (decA F hF) ∧
      RightInverse (DirectSum.coeAddMonoidHom (CohomGr F)) (decA F hF),

and constructed `S1925GradedRingOfResidual F hF h : GradedRing (CohomGr F)`
from a proof `h` of that residual.  Mathlib has no graded-quotient construction,
so the two inverse laws are genuinely needed.

## What is proved here

1. **Left inverse** (`decA_leftInverse`).  For a class `x = quo p`, the
   recomposition of `decP p` is the finite sum of the homogeneous components of
   `p`.  By `DFinsupp.sum` and `DirectSum.coeAddMonoidHom_eq_dfinsuppSum` this
   is computed as the sum of `quo (homogeneousComponent i p)` over the support of
   `decP p`; extending it to `range (p.totalDegree + 1)` and applying
   `MvPolynomial.sum_homogeneousComponent` gives back `quo p`.

2. **Right inverse** (`decA_rightInverse`).  A homogeneous class of degree `n`
   is a single direct summand: for `p` homogeneous of degree `n`,

       decP p = DFinsupp.single n ⟨quo p, _⟩

   (`decP_eq_dfinsupp_single`), because all other homogeneous components vanish.
   Hence `decA` sends the image of `DirectSum.of` back to the same summand.
   Extensionality of additive maps out of a direct sum
   (`DirectSum.addHom_ext`) then gives the right inverse.

3. **The residual is closed** (`S1925DecompositionResidual_holds`), and therefore

       S1936GradedRing F hF : GradedRing (CohomGr F)

   is unconditional: it is exactly `S1925GradedRingOfResidual F hF` applied to
   the closed residual.  Consequently `DirectSum.IsInternal (CohomGr F)` holds
   as well (`S1936IsInternal`).

4. **The projective closure of the actual model**.  Specialising to the actual
   homogeneous Weierstrass polynomial `Wang` over `F' = S1726K` gives the
   global instance `GradedRing (CohomGr Wang)`, and hence unconditional
   `Proj (CohomGr Wang)`, the affine chart `D_+(Z)`, its open-immersion
   property and its open range.  The downstream S1925 objects
   `S1925Proj`, `S1925AffineChart`, `S1925AffineChart_isOpenImmersion` and
   `S1925AffineChart_opensRange` now elaborate with this instance.

Nothing is assumed and no axiom is added: the only axioms are the standard
`propext`, `Classical.choice`, `Quot.sound`.

## What remains after S1936

The graded-ring structure of the homogeneous coordinate ring is now complete.
The remaining named geometric residuals of S1925 are unchanged: the chart
identification `S1925ChartIso : (Away WGr Zbar) ≃+* S1726CoordinateRing` and the
density `S1925DenseChart`.  They are not addressed in this file.
-/
import tmp.sheaf.xif.paper.S1925ProjectiveClosureActual

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

open CategoryTheory
open AlgebraicGeometry
open MvPolynomial
open HomogeneousLocalization
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1925ProjectiveClosureActual
open scoped DirectSum

namespace LeanFormal.IUT.XiFPaper.S1936GradedResidualActual

variable {R : Type} [CommRing R]

/-! ## 1. The left inverse: recomposition of the homogeneous components -/

/-- **The left inverse of `decP`**, pointwise on polynomials: recomposing the
homogeneous decomposition of a polynomial `p` in the ambient quotient ring
returns the class of `p`.

The proof computes `DirectSum.coeAddMonoidHom (decP p)` as the `DFinsupp.sum`
over the support of `decP p` (Mathlib's
`DirectSum.coeAddMonoidHom_eq_dfinsuppSum`), rewrites each summand by
`decP_apply`, extends the sum from the support to `range (p.totalDegree + 1)`
(the terms outside the support are zero), and finally uses
`MvPolynomial.sum_homogeneousComponent`. -/
theorem decP_coeAddMonoidHom (F : MvPolynomial (Fin 3) R) (p : MvPolynomial (Fin 3) R) :
    DirectSum.coeAddMonoidHom (CohomGr (R := R) F) (decP F p) = quo F p := by
  classical
  rw [DirectSum.coeAddMonoidHom_eq_dfinsuppSum]
  change (∑ i ∈ (decP F p).support,
    ((decP F p i : CohomGr (R := R) F i) : Cohom F)) = quo F p
  have hsupp : (decP F p).support ⊆ Finset.range (p.totalDegree + 1) := by
    intro i hi
    by_contra hri
    have hlt : p.totalDegree < i := by
      simp only [Finset.mem_range, not_lt] at hri
      omega
    have hcomp : MvPolynomial.homogeneousComponent i p = 0 :=
      MvPolynomial.homogeneousComponent_eq_zero i p hlt
    have hzero : decP F p i = 0 := by
      apply Subtype.ext
      rw [decP_apply, hcomp, map_zero]
      rfl
    exact (DFinsupp.mem_support_toFun (decP F p) i).mp hi hzero
  calc
    (∑ i ∈ (decP F p).support,
        ((decP F p i : CohomGr (R := R) F i) : Cohom F))
        = ∑ i ∈ (decP F p).support,
            quo F (MvPolynomial.homogeneousComponent i p) := by
          exact Finset.sum_congr rfl (fun i _ => decP_apply F p i)
    _ = ∑ i ∈ Finset.range (p.totalDegree + 1),
            quo F (MvPolynomial.homogeneousComponent i p) := by
          refine Finset.sum_subset hsupp ?_
          intro i _ hi_not_support
          rw [← decP_apply F p i]
          have hzero : decP F p i = 0 := by
            by_contra hne
            exact hi_not_support ((DFinsupp.mem_support_toFun (decP F p) i).mpr hne)
          simpa using congrArg (fun a : CohomGr (R := R) F i => (a : Cohom F)) hzero
    _ = quo F p := by
          rw [← map_sum (quo F)
            (fun i => MvPolynomial.homogeneousComponent i p)
            (Finset.range (p.totalDegree + 1))]
          rw [MvPolynomial.sum_homogeneousComponent]

/-- **The left inverse of `decA`**: every class in the homogeneous coordinate
ring is the sum of its homogeneous components. -/
theorem decA_leftInverse (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    Function.LeftInverse (DirectSum.coeAddMonoidHom (CohomGr (R := R) F))
      (decA F hF) := by
  intro x
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [decA_mk']
  rw [decP_coeAddMonoidHom F p]
  simp [quo]

/-! ## 2. The right inverse: homogeneous classes are single summands -/

/-- **A homogeneous polynomial is a single direct summand** of the decomposition:
if `p` is homogeneous of degree `n`, then `decP p = DFinsupp.single n ⟨quo p, _⟩`.
This is the `DFinsupp.single` form of the pointwise decomposition; it is the
key input for the right inverse. -/
theorem decP_eq_dfinsupp_single (F : MvPolynomial (Fin 3) R)
    {n : ℕ} {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    decP F p = DFinsupp.single n (⟨quo F p, CohomGr_mem F hp⟩ : CohomGr (R := R) F n) := by
  apply DFinsupp.ext
  intro m
  apply Subtype.ext
  rw [decP_apply]
  by_cases hmn : m = n
  · subst hmn
    rw [MvPolynomial.homogeneousComponent_eq_self hp]
    rw [DFinsupp.single_eq_same]
  · have hcomp : MvPolynomial.homogeneousComponent m p = 0 := by
      rw [MvPolynomial.homogeneousComponent_of_mem (m := m) (n := n) (p := p) hp,
        if_neg hmn]
    rw [hcomp, map_zero]
    rw [DFinsupp.single_eq_of_ne (i := n) (i' := m) hmn]
    rfl

/-- On a class represented by a homogeneous polynomial of degree `n`, `decA`
is the corresponding single summand `DirectSum.of`. -/
theorem decA_of_homogeneous (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    {n : ℕ} {p : MvPolynomial (Fin 3) R} (hp : p.IsHomogeneous n) :
    decA F hF (quo F p) =
      DirectSum.of (fun n => CohomGr (R := R) F n) n
        ⟨quo F p, CohomGr_mem F hp⟩ := by
  rw [decA_mk, decP_eq_dfinsupp_single F hp]
  rfl

/-- On any homogeneous class of degree `n`, `decA` is the corresponding
single summand `DirectSum.of`. -/
theorem decA_of_mem (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3)
    {n : ℕ} (x : Cohom F) (hx : x ∈ CohomGr (R := R) F n) :
    decA F hF x =
      DirectSum.of (fun n => CohomGr (R := R) F n) n ⟨x, hx⟩ := by
  obtain ⟨p, hp, rfl⟩ := Submodule.mem_map.mp hx
  exact decA_of_homogeneous F hF hp

/-- **The right inverse of `decA`**: decomposing a direct sum element after
recomposing it returns the original direct sum element.  Both sides are additive
maps out of the direct sum, so by `DirectSum.addHom_ext` it suffices to check
the equality on a single summand, where it is `decA_of_mem`. -/
theorem decA_rightInverse (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    Function.RightInverse (DirectSum.coeAddMonoidHom (CohomGr (R := R) F))
      (decA F hF) := by
  classical
  have h : (decAHom F hF).comp
      (DirectSum.coeAddMonoidHom (CohomGr (R := R) F)) =
      AddMonoidHom.id (⨁ n, CohomGr (R := R) F n) := by
    apply DirectSum.addHom_ext
    intro i x
    rw [AddMonoidHom.comp_apply, AddMonoidHom.id_apply, DirectSum.coeAddMonoidHom_of]
    exact decA_of_mem F hF x x.2
  intro y
  exact DFunLike.congr_fun h y

/-! ## 3. The residual of S1925 is closed -/

/-- **The decomposition residual of S1925 is a theorem**: `decA` and the
recomposition map `DirectSum.coeAddMonoidHom` are mutually inverse. -/
theorem S1925DecompositionResidual_holds (F : MvPolynomial (Fin 3) R)
    (hF : F.IsHomogeneous 3) : S1925DecompositionResidual (R := R) F hF :=
  ⟨decA_leftInverse F hF, decA_rightInverse F hF⟩

/-- **The homogeneous coordinate ring is a graded ring**, unconditionally.  This
is `S1925GradedRingOfResidual` applied to the now-proved residual. -/
@[implicit_reducible]
noncomputable def S1936GradedRing (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    GradedRing (CohomGr (R := R) F) :=
  S1925GradedRingOfResidual F hF (S1925DecompositionResidual_holds F hF)

/-- The constructive `DirectSum.Decomposition` underlying the graded-ring
structure: its decomposition map is `decA` and its two inverse fields are the
left and right inverse proved above. -/
@[implicit_reducible]
noncomputable def S1936Decomposition (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    DirectSum.Decomposition (CohomGr (R := R) F) :=
  (S1936GradedRing F hF).toDecomposition

/-- The family `CohomGr F` is an internal direct sum decomposition of the
homogeneous coordinate ring. -/
theorem S1936IsInternal (F : MvPolynomial (Fin 3) R) (hF : F.IsHomogeneous 3) :
    DirectSum.IsInternal (CohomGr (R := R) F) := by
  haveI := S1936Decomposition F hF
  exact DirectSum.Decomposition.isInternal _

/-! ## 4. The actual projective closure, unconditionally

The actual homogeneous Weierstrass polynomial `Wang` is homogeneous of degree
three (`Wang_isHomogeneous`, S1925), so the graded-ring structure is available
for the actual homogeneous coordinate ring over `F' = S1726K`.  Everything in
S1925 section 3 (the scheme `Proj`, the chart `D_+(Z)`, its open range) now
elaborates without the section hypothesis `[GradedRing (CohomGr Wang)]`. -/

section Wang

/-- The homogeneous coordinate ring of the actual projective closure is graded. -/
noncomputable instance S1936GradedRingWang :
    GradedRing (CohomGr (R := S1726K) Wang) :=
  S1936GradedRing Wang Wang_isHomogeneous

/-- **The projective closure** of the actual affine Weierstrass model of S1726,
as `Proj` of the graded homogeneous coordinate ring `F'[X,Y,Z]/(Wang)`. -/
noncomputable abbrev S1936Proj : Scheme := Proj (CohomGr (R := S1726K) Wang)

/-- **The affine chart `D_+(Z)`** of the projective closure, as an open
immersion. -/
noncomputable abbrev S1936AffineChart :
    Spec (CommRingCat.of (Away (CohomGr (R := S1726K) Wang) Zbar)) ⟶ S1936Proj :=
  Proj.awayι (CohomGr (R := S1726K) Wang) Zbar Zbar_mem_one one_pos

/-- The affine chart is an open immersion of schemes. -/
instance S1936AffineChart_isOpenImmersion : IsOpenImmersion S1936AffineChart :=
  inferInstance

/-- The open range of the affine chart is exactly `D_+(Z)`. -/
theorem S1936AffineChart_opensRange :
    S1936AffineChart.opensRange = Proj.basicOpen (CohomGr (R := S1726K) Wang) Zbar :=
  Proj.opensRange_awayι (CohomGr (R := S1726K) Wang) Zbar Zbar_mem_one one_pos

/-- The S1925 projective closure is definitionally the unconditional one. -/
example : S1925Proj = S1936Proj := rfl

/-- The S1925 affine chart is an open immersion once the graded-ring instance is
supplied by `S1936GradedRingWang`. -/
example : IsOpenImmersion S1925AffineChart := inferInstance

/-- The S1925 open-range computation also applies unconditionally. -/
example : S1925AffineChart.opensRange =
    Proj.basicOpen (CohomGr (R := S1726K) Wang) Zbar :=
  S1925AffineChart_opensRange

end Wang

/-! ## 5. Axiom audit -/

#print axioms decP_coeAddMonoidHom
#print axioms decA_leftInverse
#print axioms decP_eq_dfinsupp_single
#print axioms decA_of_homogeneous
#print axioms decA_of_mem
#print axioms decA_rightInverse
#print axioms S1925DecompositionResidual_holds
#print axioms S1936GradedRing
#print axioms S1936Decomposition
#print axioms S1936IsInternal
#print axioms S1936GradedRingWang

end LeanFormal.IUT.XiFPaper.S1936GradedResidualActual
