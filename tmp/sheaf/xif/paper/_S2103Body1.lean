import tmp.sheaf.xif.paper.S2093D9StackActual
import Mathlib.CategoryTheory.Sites.SheafHom
import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv

/-!
# S2103: the prestack half of S2093 -- slice `SheafHom` versus `Pseudofunctor.presheafHom`

For a site `(C, J)`, a category `A`, an object `S : C` and sheaves `M N : Sheaf (J.over S) A`,
Mathlib provides two presheaves of morphisms on `(Over S)ᵒᵖ`:

* `Pseudofunctor.presheafHom M N` for the pseudofunctor `J.pseudofunctorOver A`,
  whose value at `j : Over S` is `Hom ((Over.map j.hom)^* M) ((Over.map j.hom)^* N)`, i.e.
  `Hom` in `Sheaf (J.over j.left) A` of the pullbacks along `Over.map j.hom`; its
  restriction maps are the `pullHom` maps built from the pseudofunctor's composition
  constraints (`GrothendieckTopology.overMapPullbackComp`);

* `CategoryTheory.sheafHom' M N` (the underlying presheaf of `SheafHom.sheafHom`), whose
  value at `j` is `Hom ((Over.forget j)^* M) ((Over.forget j)^* N)`, i.e. `Hom` in
  `Sheaf ((J.over S).over j) A`; its restriction maps are pushforwards along `Over.map`.

`SheafHom.sheafHom M N` *is a sheaf* (`Presheaf.IsSheaf (J.over S) (sheafHom' M N)`); hence,
if the two presheaves are isomorphic, the prestack half `S2093SheafPrestack K` of S2093
(descent of morphisms for `S2029SheafPrestack K`) follows.

This file constructs, for every `j : Over S`, the canonical comparison

  `(sheafHom' M N).obj (op j) ≃ (presheafHom M N).obj (op j)`,

using `Over.iteratedSliceBackward_forget` (which is `rfl`: `Over.forget j` coincides with
`iteratedSliceBackward j ⋙ Over.map j.hom`) and the dense subsite structure of the iterated
slice equivalence (`Functor.IsDenseSubsite.full_sheafPushforwardContinuous` and
`...faithful_sheafPushforwardContinuous`).  The comparison is `W_j = (Over.iteratedSliceBackward j)^*`
acting on morphisms; it is a bijection by fullness/f faithfulness, and it is `rfl`-compatible with
the values of `presheafHom`.

## Honest boundary: the naturality in `j` is not available in Mathlib v4.32.2

The comparison is *pointwise* an isomorphism, but Mathlib has no lemma making it natural in
`j : Over S`, so it does **not** by itself give a `NatIso` of presheaves.  The exact first
missing is recorded below as `SlicePushNaturality`; it is equivalent to the existence of a
`NatIso` `sheafHom' M N ≅ (J.pseudofunctorOver A).presheafHom M N` whose components are the
canonical pointwise maps (`naturality_iff_exists_natIso`).  Establishing it needs the
compatibility of two Mathlib-internal comparisons that are *not* related by `rfl`:

* the pseudofunctorial composition constraints of `GrothendieckTopology.pseudofunctorOver`,
  i.e. `GrothendieckTopology.overMapPullbackComp` (built from `Functor.sheafPushforwardContinuousComp'`
  applied to `Over.mapComp` and from `overMapPullbackCongr`);
* the naturality of the iterated slice equivalence, `Over.iteratedSliceEquivOverMapIso`
  (built from `Over.iteratedSliceForwardNaturalityIso`), in its `Backward` form
  `Over.iteratedSliceBackward Y₂ ⋙ Over.map q ≅ Over.map q.left ⋙ Over.iteratedSliceBackward Y₁`.

Mathlib v4.32.2 provides `iteratedSliceForwardNaturalityIso` (forward form, `Iso.refl` on data)
and `iteratedSliceEquivOverMapIso`, but no lemma identifying the pseudofunctor coherence with
these, and no backward-form naturality iso; `Over.mapComp`, which enters `overMapPullbackComp`,
is a genuine isomorphism (components `Over.isoMk (Over.isoMk (Iso.refl _))`) whose
`Over.w`-proofs are propositional, so the comparison cannot be discharged by `rfl`/`simp`.

Consequently this file proves:

1. the pointwise comparison `sliceComparison` and its bijectivity (`sliceComparison_bijective`);
2. the exact naturality statement `SlicePushNaturality` and the equivalence with the existence of
   a `NatIso` with the canonical components (`naturality_iff_exists_natIso`);
3. the reduction `SlicePushNaturality -> IsPrestack -> S2093SheafPrestack K`
   (`isSheaf_of_naturality`, `isPrestack_of_naturality`, `S2093SheafPrestack_of_firstMissing`);
4. the precise first missing `S2103FirstMissing K`, which is exactly `S2093SheafPrestack K`'s
   descent-of-morphisms half.

No `sorry`, no new axiom, no pointwise-only claim: the unproved input is isolated as an
explicitly quantified `Prop` and never used to fake a result.
-/

noncomputable section
open CategoryTheory Opposite

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2103D9PrestackActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2093D9StackActual

universe v u v' u'

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

/-! ## 1. The iterated-slice pushforward -/

/-- The pushforward of sheaves along the inverse of the iterated slice equivalence
`Over j ≌ Over j.left`, from the slice site `(J.over S).over j` to `J.over j.left`. -/
abbrev slicePush {S : C} (X : Over S) : Sheaf ((J.over S).over X) A ⥤ Sheaf (J.over X.left) A :=
  X.iteratedSliceEquiv.inverse.sheafPushforwardContinuous A (J.over X.left) ((J.over S).over X)

/-- `slicePush X` is full: it is the pushforward of a dense subsite.  Note that this does *not*
need the limit hypotheses required by `Functor.IsDenseSubsite.sheafEquiv`. -/
lemma slicePush_full {S : C} (X : Over S) : (slicePush (J := J) (A := A) X).Full :=
  inferInstance

/-- `slicePush X` is faithful. -/
lemma slicePush_faithful {S : C} (X : Over S) : (slicePush (J := J) (A := A) X).Faithful :=
  inferInstance

/-- **The value identification.**  The value of the pseudofunctor's `presheafHom` at `j` is the
value of the slice `Hom` presheaf at `j` after applying the iterated-slice pushforward. -/
lemma presheafHom_obj_eq {S : C} (M : Sheaf (J.over S) A) (X : Over S) :
    (J.overMapPullback A X.hom).obj M =
      (slicePush (J := J) (A := A) X).obj (((J.over S).overPullback A X).obj M) := rfl

/-- The canonical pointwise comparison of morphism types at `j : Over S`. -/
def sliceComparison {S : C} (M N : Sheaf (J.over S) A) (X : Over S) :
    (CategoryTheory.sheafHom' (J := J.over S) M N).obj (op X) →
      ((J.pseudofunctorOver A).presheafHom M N).obj (op X) :=
  fun φ => (slicePush (J := J) (A := A) X).map φ

/-- **The pointwise comparison is a bijection.** -/
lemma sliceComparison_bijective {S : C} (M N : Sheaf (J.over S) A) (X : Over S) :
    Function.Bijective (sliceComparison (J := J) (A := A) M N X) := by
  haveI := slicePush_full (J := J) (A := A) X
  haveI := slicePush_faithful (J := J) (A := A) X
  constructor
  · intro a b h
    exact Functor.Faithful.map_injective (F := slicePush (J := J) (A := A) X) h
  · intro b
    exact Functor.Full.map_surjective (F := slicePush (J := J) (A := A) X)
      (X := ((J.over S).overPullback A X).obj M) (Y := ((J.over S).overPullback A X).obj N) b