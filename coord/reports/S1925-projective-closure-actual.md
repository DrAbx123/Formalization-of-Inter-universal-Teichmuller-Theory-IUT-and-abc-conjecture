# S1925: the projective closure from the graded homogeneous coordinate ring

Status: **file compiled** (EXIT=0, no error; one linter warning about `def` vs
`theorem` on a class-valued definition; axioms trio only, no `sorryAx`).
Result type: **partial construction + exact first missing** (the graded-ring
instance is reduced to one named residual; everything above it is conditional,
not fabricated).

## Deliverable

| item | value |
|---|---|
| file | tmp/sheaf/xif/paper/S1925ProjectiveClosureActual.lean |
| lines | 315 |
| source bytes | 17224 |
| source SHA256 | 4662D820D95648782A21E4C7C3FB96A895AA2DD3242ADF141CAE894550EA4CFE |
| compile | `lake env lean -j1 -R D:\lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1925ProjectiveClosureActual.olean tmp/sheaf/xif/paper/S1925ProjectiveClosureActual.lean` |
| EXIT | 0 |
| olean | .lake/build/lib/lean/tmp/sheaf/xif/paper/S1925ProjectiveClosureActual.olean (553128 bytes, 2026-11-01T15:25:26) |
| olean SHA256 | 87F256EF1DD0D28BBCA92704C4E6D863EFA1BA614A6FFA9E09E49579EEFF4D2E |
| axioms | propext, Classical.choice, Quot.sound only (8 `#print axioms` checks) |
| sorry/admit/new axiom | none (grep; the words occur only in this report) |

## What is constructed (unconditional)

1. **The homogeneous Weierstrass polynomial** of the projective closure

       Wang = Y^2 Z - (X^3 + (61/64) X^2 Z + (-125/64) X Z^2)  in F'[X,Y,Z],

   with proofs: `Wang_isHomogeneous` (degree 3), `Wang_ne_zero`,
   `Wang_eval_pointAtInfinity` (O = (0:1:0) lies on it), and
   `Wang_eval_eq_aeval`: its dehomogenization at Z = 1 is literally the affine
   Weierstrass polynomial `S1726AffinePolynomial` of the S1726 model, evaluated
   at (x,y).  This ties the projective closure to the actual curve
   y^2 = x^3 + (61/64)x^2 - (125/64)x (coefficients from `S1726Curve_aᵢ`).

2. **The homogeneous coordinate ring** `Cohom = F'[X,Y,Z]/(Wang)` with its
   grading `CohomGr n = image of the degree-n homogeneous part`, and the
   pointwise homogeneous decomposition:
   - `decP` (DirectSum.mk over `range (totalDegree+1)`),
   - `decP_apply` (component formula),
   - `decP_congr` (well-definedness on the quotient, using homogeneity of the ideal),
   - `decA` (the decomposition on the quotient, via `Quotient.liftOn'`),
   - `decA_mk` (`decA (quo p) = decP p`),
   - `decP_add`, `decP_zero` (additivity of the pointwise decomposition),
   - `instGradedMonoid` (**the graded-monoid structure**: products of
     homogeneous elements are homogeneous of summed degree, 1 is homogeneous of
     degree 0).

   Mathlib has no graded-quotient construction at all (verified by search: no
   `GradedRing`/`Decomposition` instance on any quotient); the above is the
   concrete replacement for it on this ring.

## The exact first missing

    S1925DecompositionResidual F hF : Prop
      := Function.LeftInverse (DirectSum.coeAddMonoidHom (CohomGr F)) (decA F hF)
       ∧ Function.RightInverse (DirectSum.coeAddMonoidHom (CohomGr F)) (decA F hF)

i.e. the two inverse laws of the homogeneous decomposition (the "recomposition"
is inverse to `decA`).  From it,

    S1925GradedRingOfResidual F hF (h : S1925DecompositionResidual F hF) :
      GradedRing (CohomGr F)

is **constructed** (graded ring = decomposition + graded monoid, and the graded
monoid is unconditional), and then, in the section
`variable [GradedRing (CohomGr (R := S1726K) Wang)]`:

* `S1925Proj : Scheme = Proj WGr` — the projective closure,
* `S1925ProjStruct : S1925Proj ⟶ Spec (WGr 0)` — its structure morphism,
* `Zbar`, `Zbar_mem_one` — the homogeneous coordinate Z,
* `S1925AffineChart : Spec (Away WGr Zbar) ⟶ S1925Proj` = `Proj.awayι`, the
  affine chart D_+(Z),
* `S1925AffineChart_isOpenImmersion` (**proved**: it is an open immersion),
* `S1925AffineChart_opensRange` (**proved**: its open range is exactly
  D_+(Z) = `Proj.basicOpen WGr Zbar`),
* `S1925ChartIso : Type := (Away WGr Zbar) ≃+* S1726CoordinateRing` — the
  *chart identification* residual (named type, no inhabitant),
* `S1925DenseChart : Prop := Dense (Proj.basicOpen WGr Zbar : Set S1925Proj)` —
  the density residual (named proposition, no inhabitant),
* `S1925OpenMapOfChartIso (e : S1925ChartIso) : S1726AffineOver.left ⟶ S1925Proj`
  — the induced morphism of the actual affine model into the projective closure.

## Honest boundary

* The projective closure scheme is constructed **conditionally** on the graded
  ring instance; the instance is itself constructed from
  `S1925DecompositionResidual`.  The residual is not assumed anywhere: it is a
  named `Prop` and `S1925GradedRingOfResidual` takes it as an explicit
  hypothesis.
* What is *not* proved: (a) the decomposition residual, (b) the chart
  isomorphism `Away WGr Zbar ≃+* R'`, (c) density of D_+(Z), (d) properness of
  the structure morphism (needs `Algebra.FiniteType (WGr 0) W`, which needs a
  local `Algebra (WGr 0) W` instance; Mathlib has no such instance for graded
  rings, and it is not constructed here), (e) the point at infinity as a scheme
  morphism `Spec F' ⟶ S1925Proj` (natural construction:
  `Proj.fromOfGlobalSections` with X↦0, Y↦1, Z↦0; the separation from the chart
  then follows from `fromOfGlobalSections_preimage_basicOpen`, but this is not
  carried out here).
* Nothing is replaced by `PUnit`, `True`, a `sorry` or a new axiom.

## Technical notes for the next worker (obstacles hit)

1. `MvPolynomial.isHomogeneous_X` has `R` explicit: use
   `isHomogeneous_X (R := K) i`.  `MvPolynomial.isHomogeneous_C` has `σ`
   explicit: use `isHomogeneous_C (σ := Fin 3) (r : K)`.  Plain
   `isHomogeneous_X 1` mis-elaborates the numeral as a *type*.
2. In this file's context the function coercion of `DirectSum` (`⨁ i, β i`) and
   `Π₀` do not unify at default transparency inside `rw`/pattern matching:
   `DirectSum.of_eq_of_ne`/`of_apply` and `DirectSum.add_apply`-based
   componentwise rewriting fail with "the argument ... has type ⨁ ... but is
   expected to have type Π₀ ...".  This is what blocked the two residual inverse
   laws.  Workarounds to try: state component lemmas with `DFinsupp.single`
   directly, or use `DirectSum.IsInternal` +
   `DirectSum.IsInternal.chooseDecomposition` (needs `iSupIndep` and
   `iSup = ⊤`, both provable from `decP_apply`/`decP_congr` by the same
   polynomial-component argument), or
   `DirectSum.coeAddMonoidHom_eq_dfinsuppSum` + `DFinsupp.sum` lemmas.
3. `DirectSum.sum_support_of` needs the dependent `Decidable` instance; plain
   `classical` in the proof was not enough inside `conv`/`have` in one attempt.
4. Mathlib's `Proj` properness instance needs `Algebra.FiniteType (𝒜 0) A`;
   `Algebra (𝒜 0) A` is *not* an instance for `GradedRing` (confirmed: no such
   instance in Mathlib), so a local instance must be written, and then
   `Algebra.FiniteType` proved from `Algebra.adjoin (𝒜 0) {quo X, quo Y, quo Z} = ⊤`.

## Consequence for S1913

The first missing datum of S1913 is now split into four independent algebra
statements about the *concrete* ring `F'[X,Y,Z]/(Wang)`:
the decomposition residual, the chart identification, the density of D_+(Z),
and the finite-type instance for properness.  The scheme-level objects
(`Proj`, D_+(Z), the open immersion) are no longer part of the gap.
