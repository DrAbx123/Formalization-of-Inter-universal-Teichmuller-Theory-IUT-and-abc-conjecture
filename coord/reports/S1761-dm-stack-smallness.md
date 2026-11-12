# S1761: finite-type DM-stack smallness and the orbicurve cover category

Date: 2026-11-01
Task: S1761, follow-up to S1738.
File: `tmp/sheaf/xif/paper/S1761DMStackSmallnessActual.lean`
Namespace: `LeanFormal.IUT.XiFPaper.S1761DMStackSmallnessActual`

## Verdict

The general theorem

> finite-type DM etale stacks over a field form an essentially small category,
> and the finite-etale cover category of a finite-type stacky orbicurve is
> essentially small at the base universe,

is **not proved**.  Mathlib v4.32.2 has no algebraic stacks, no
Deligne-Mumford stacks, no representability of the diagonal, no etale atlases,
no stack quotient/stackification of Cat-valued presheaves, and no smallness
theorem for finite-type DM stacks.  The file therefore reports `missing` for
the general theorem and isolates the exact geometric inputs.

The file does compile (`EXIT=0`) with no `sorry`, no `axiom`, no
`Shrink`, no `ULift`, and only the standard axiom trio.  It proves the
scheme-level bounds, the strict 2-Yoneda theorem left open by S1738, smallness
of representable-stack homs, and smallness of the raw finite-etale descent
category.  It also proves that two named missing geometric statements imply
the target cardinality bound for the actual cover category.

## What Mathlib actually supplies

* `AlgebraicGeometry.essentiallySmall_costructuredArrow_Spec`
  (`Mathlib/AlgebraicGeometry/Morphisms/FiniteType.lean`): affine schemes
  locally of finite type over a fixed scheme are essentially small.
* `MorphismProperty.CostructuredArrow` and the affine finite-etale slice are
  essentially small by the same theorem; this is the small model used below.
* `Pseudofunctor.IsStack` and descent for category-valued pseudofunctors on a
  site (`Mathlib/CategoryTheory/Sites/Descent/IsStack.lean`).
* `CategoryTheory.EssentiallySmall`, `Skeleton`, `fromSkeleton`, and the
  standard transfer lemmas.

Mathlib has no declaration of `AlgebraicStack`, `DMStack`,
`DeligneMumford`, an etale atlas, a representable diagonal, or a quotient
stack.  The project's `Iut.EtaleStackOverField` is a category-valued etale
stack with no algebraicity, finiteness, or diagonal data.

## Proved unconditionally in the file

1. `S1761_affineFiniteType_essentiallySmall` and
   `S1761_affineField_essentiallySmall`: the S1738 affine finite-type bound,
   restated for the field base.
2. `S1761AffineFiniteEtaleSlice_essentiallySmall (S : Scheme.{u})`:
   the affine finite-etale slice
   `S1761FiniteEtale.CostructuredArrow ⊤ Scheme.Spec S` is essentially small
   for every scheme `S`.  Its skeleton is the small index used for descent.
   `S1761FieldFiniteEtale_essentiallySmall` is the concrete field case
   `S = Spec F`: finite-etale covers of a point are essentially small.
3. `S1761TwoYonedaStrong (S T)`: **strict** 2-Yoneda for representable
   etale stacks.  Every strong transformation
   `S1738R S ⟶ S1738R T` is strictly determined by its value at the identity.
   This closes S1738's `S1738TwoYonedaStrong`, which S1738 recorded as its
   second missing input.
4. `S1761TwoYonedaRequired`: the S1738 packaged form, now proved for an
   arbitrary field `F : Type u`.
5. `S1761StrongTrans_small (S T)`:
   `Small.{u} (StrongTrans (S1738R S) (S1738R T))` for the **raw** strong
   transformation type, not only for 2-isomorphism classes.
6. `S1761RepresentableIsStack (U)` and `S1761RepresentableStack U`:
   every scheme over the field represents an actual etale stack, using the
   project's constructed discrete-sheaf-to-stack bridge (S1419), not an
   assumed instance.
7. `S1761RawDescent (s t)`: the category of raw finite-etale descent data
   along arbitrary `s t : R ⟶ U`.  Objects are an affine finite-etale scheme
   `V` over `U` (taken from the small skeleton of the affine finite-etale
   slice) together with an isomorphism between its two pullbacks to `R`.
   No cocycle condition is imposed.
   - `S1761RawDescentHom`: morphisms are morphisms over `U` compatible with
     the two descent isomorphisms; their type is `Type u`.
   - `S1761RawDescent_essentiallySmall`: the raw descent category is
     `EssentiallySmall.{u}`.
   - `S1761RawDescentSubcategory_essentiallySmall`: every full subcategory,
     in particular the actual cocycle subcategory, is essentially small.
   - `S1761RawDescentId`: non-vacuity in the diagonal case `s = t`.
8. `S1761AtlasSurjective`: a faithful local-surjectivity predicate for a
   stack map at scheme-valued points (etale-local lifts).
9. `S1761FiniteTypeDMAtlas X`: the precise atlas interface used by the
   cardinality argument: an affine finite-type etale atlas whose
   self-fiber-product is again affine of finite type.  The DM
   unramified-diagonal condition is not used by the size argument and is not
   formalized here (Mathlib has no DM-stack definition).
10. `S1761Cover_essentiallySmall_of_atlasDescent`: if the actual cover
    category is equivalent to a full subcategory of the raw descent category
    (with the actual `S1728CoverCategory11` on the cover side), then
    `EssentiallySmall.{u} (OrbicurveFiniteEtaleCover X)`.
11. `S1761FiniteTypeDMCoverSmallness_of_inputs`: the target follows from the
    two named missing inputs below.

## Exact missing theorem list

### M1. Algebraic/DM stack and atlas definition

Mathlib is missing:

* an `AlgebraicStack`/`DMStack` structure over a base scheme;
* representability of the diagonal (for a stack morphism);
* the unramified condition on the diagonal;
* quasi-compact/quasi-separated and finite-type conditions on stacks and on
  the diagonal.

In the file, `S1761FiniteTypeDMAtlas X` records the finite-type affine etale
atlas and the affine finite-type self-fiber-product, but not the unramified
diagonal.  A Mathlib-level definition is needed before the phrase "finite-type
DM stack" can be formalized without a surrogate.

### M2. Atlas existence

`S1761FiniteTypeDMAtlasExistence X : Prop`
`:= Nonempty (S1761FiniteTypeDMAtlas X)`.

For a finite-type separated DM stack over a field, this is the standard
existence of an affine finite-type etale atlas with affine finite-type
self-fiber-product (for a proper DM stack the diagonal is finite, hence
affine).  The file does **not** assert this for arbitrary stacks; it is the
precise input missing for the actual stacky orbicurve.  For the S1726
orbicurve the stack is representable by the affine Weierstrass model
`S1726AffineOver`, so the intended atlas is the identity; constructing that
atlas in Lean is a separate concrete task.

### M3. Descent along an atlas

`S1761FiniteTypeDMCoverDescent X : Prop`
`:= ∀ A : S1761FiniteTypeDMAtlas X.stack, S1761AtlasDescentEquiv A`.

`S1761AtlasDescentEquiv A` says that the actual finite-etale cover category
`OrbicurveFiniteEtaleCover X` (with the S1728 2-isomorphism-quotient
category `S1728CoverCategory11`) is equivalent to the full subcategory of
`S1761RawDescent s t` cut out by the cocycle condition.  This is the stack
descent theorem for a morphism of stacks `U ⟶ X`; Mathlib's
`Pseudofunctor.IsStack` is descent for a cover in the site of schemes, not
for an atlas morphism.  The cocycle predicate is left as a parameter in the
statement because the groupoid multiplication/composition has not been
formalized; the file does not assert a particular `C`.

### M4. DM diagonal

The unramified diagonal of the DM stack (equivalently, the relative diagonal
of the atlas being formally unramified) is not formalized.  It is not needed
for the object/hom cardinality bound once the affine self-fiber-product
descent model is available, but it is part of the exact definition of DM.

### M5. Stack quotient / groupoid presentation

To pass from an atlas `U ⟶ X` and its self-fiber-product `R ⇉ U` to the
cocycle subcategory used in M3, one needs the stack quotient of the groupoid
and its universal property (or equivalent descent for the small etale site of
`X`).  Mathlib has no stackification of Cat-valued presheaves and no
quotient-stack construction.  This is the main missing theory behind M3.

### M6. Smallness of arbitrary finite-type schemes

The present proof avoids this by using affine finite-etale slices over `U`
and `R`.  An alternative route would need Mathlib smallness for all
finite-type `F`-schemes (not only affine ones); Mathlib does not currently
have that.

### M7. Smallness of the category of finite-type DM stacks

The file proves smallness of the raw descent data, not of the category of
all finite-type DM stacks.  The latter would follow from M1--M3 plus
full/faithfulness of the quotient comparison.  No such comparison is
constructed here.

## Consequences for the S1738 route

* S1738's `S1738TwoYonedaRequired` is **proved** here
  (`S1761TwoYonedaRequired`).
* S1738's `S1738StrongTrans_small_of_twoYoneda` now applies unconditionally
  (`S1761StrongTrans_small`).
* The remaining gap in the general finite-type route is exactly M1--M3:
  DM-stack/atlas definitions, atlas existence, and atlas descent.
* The scheme-level smallness theorem is not the obstruction; the obstruction
  is the stack quotient/descent theory, as S1738 anticipated.

## Evidence

* Lean source: `tmp/sheaf/xif/paper/S1761DMStackSmallnessActual.lean`
  - lines: 489
  - bytes: 22650
  - SHA256: `34EAC146B1125457C0BDB832F44315477C483DDF9CE5A6702F550D647C8506F5`
* Build command:
  `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1761DMStackSmallnessActual.olean tmp/sheaf/xif/paper/S1761DMStackSmallnessActual.lean`
* `EXIT=0`, no warnings.
* Olean: `.lake/build/lib/lean/tmp/sheaf/xif/paper/S1761DMStackSmallnessActual.olean`
  - bytes: 818400
  - SHA256: `4F5B8BC88D5797B1BD24D876FED0B19E787690F90175FC3B448080A9B1619740`
* Axiom audit: every `#print axioms` in the file reports only
  `propext`, `Classical.choice`, `Quot.sound`.  No `sorryAx`.
* Dependency versions: S1738 olean built 2026-11-01 00:36:51; S1419 and S1728
  oleans present.  S1728 is imported for the actual cover category
  `S1728CoverCategory11`; S1419 for the discrete-sheaf-to-stack bridge.

## Consumer

S1738 (`S1738TwoYonedaRequired` now closed), S1733/S1743/S1755 (small cover
category / model comparison), and the D6 `OrbicurveFundamentalGroupData`
field of S1728/S1732, which needs the small Galois cover category.

## Next executable step

Either:

1. **Concrete representable case.**  For the S1726 orbicurve, construct
   `S1761FiniteTypeDMAtlas S1726Orbicurve.stack` with `U = S1726AffineOver`
   and the identity atlas, prove the self-fiber-product is `U`, and prove the
   descent equivalence for the identity groupoid (this should reduce to the
   affine finite-etale slice and S1742/S1743); or
2. **General DM theory.**  Add the missing `DMStack`/atlas/representable-
   diagonal definitions and the stack quotient/descent theorem; then M2/M3
   become provable and `S1761FiniteTypeDMCoverSmallness_of_inputs` closes the
   cardinality bound for arbitrary finite-type DM orbicurves.

## Honest boundary

The main theorem "finite-type DM etale stacks over a field are essentially
small" is **not proved**.  The file proves the cardinality bound for raw
descent data and reduces the actual cover-category bound to two precise
missing geometric statements.  No `Shrink`, `ULift`, `PLift`, `PUnit`,
`sorry`, axiom, or fake category is used.  `Skeleton` is Mathlib's genuine
categorical skeleton, not a substitute for a smallness proof.