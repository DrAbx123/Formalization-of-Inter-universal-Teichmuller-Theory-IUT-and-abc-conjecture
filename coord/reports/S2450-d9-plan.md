# S2450: D9 non-compiling proof plan (S2427SignProjection + S2444OverMapCompatIso)

Date: 2026-11-02. BUILD HOLD: no lake command was run for this plan. No declaration is claimed actual.

## 0. Gate assumptions for post-build

- Restore Mathlib artifacts via build coordinator; then run one serialized compile per file, no concurrent lake builds.
- Allowed final axioms: propext, Classical.choice, Quot.sound.
- No sorry/axiom/True/PUnit/fake carriers.

## 1. S2427SignProjection

Objects:
- Q = S2152Q; M N : Q.obj (op S).
- S2427Comp T := eqToIso (S2271QHomObj_eq_subtype S M N T) : Q.presheafHom.obj T ≅ S2332Obj T.
- S2332Psub.map p keeps the subtype value: (S2332Psub.map p h).1 = h.1 (definitional).
- Goal: forall T1 T2 p x, (S2427Comp T2).hom (Q.presheafHom.map p x) = S2332Psub.map p ((S2427Comp T1).hom x).

### 1.1 S2425 helper path

1. Build `S2450CompEquiv T : Q.presheafHom.obj T ≃ S2332Obj T` from `(S2427Comp T).hom` and `.inv`.
2. Use `S2425NatIsoCastHelpersActual.presheafNatIsoOfPointwiseEquiv` (or natIsoOfPointwiseEquiv) with pointwise input exactly S2427SignProjection; this only repackages, does not prove it.
3. For the pointwise input do `apply Subtype.ext`; reduce to equality of SignGroup values.
4. Use S2425:`eqToIso_hom_apply`, `eqToIso_inv_apply`, `subtype_eqToIso_apply`, `subtype_funext`, `eqToIso_trans`, `eqToIso_symm`.
5. Need the label lemma below.

### 1.2 Minimal label subgoals

`S2450QMapLabel` (core):
  forall T1 T2 p x,
    (((S2427Comp T2).hom (Q.presheafHom.map p x) : S2332Obj T2).1)
      = (((S2427Comp T1).hom x : S2332Obj T1).1).

`S2450MapCompLabel`: the coherence `mapComp'` of S2152Q acts as label 1:
  forall (f g h) (M), ((S2152Q.mapComp' f g h ...).hom.toNatTrans.app M).1 = 1.
  Note: this is an action-category label, not a Cat-level functor; the statement must be given at the action-category hom type, not via a wrong `.val` on the Cat-level app. Diagnose with #check.

`S2450PullHomLabel`: after unfolding `Pseudofunctor.presheafHom_map` and `pullHom`:
  S1971PrecompFunctor_map_val gives the middle precomposition label = x.1;
  S2450MapCompLabel gives both coherence labels = 1;
  ActionCategory.id_val/ActionCategory.comp_val close the label computation.

### 1.3 Lemma list

- S2271QHomObj_eq_subtype
- S1971PointwiseQuotient_hom, ActionCategory.hom_as_subtype
- Pseudofunctor.presheafHom_map
- Pseudofunctor.LocallyDiscreteOpToCat.pullHom
- pullHom_id, pullHom_pullHom
- S2259QMapPrecomp
- S1971PrecompFunctor_map_val
- ActionCategory.id_val, ActionCategory.comp_val
- S2425: eqToIso_hom_apply, eqToIso_inv_apply, subtype_eqToIso_apply, subtype_funext, eqToIso_trans, eqToIso_symm
- FunctorToTypes.naturality / ConcreteCategory.hom ext

### 1.4 Risk

`S2450MapCompLabel` is the hard point: S2152Q = S2152PFunctor.toPseudofunctor' with mapComp = Iso.refl, but the app is a natural-transformation component at the Cat level. Need an explicit type ascription to the action-category hom subtype and prove the component is the identity (or label 1) by unfolding `Functor.toPseudofunctor'`, `pseudofunctorOfIsLocallyDiscrete`, `Cat.Hom.toNatTrans`. If this fails, report the exact #check type of the app and the goal.

## 2. S2444OverMapCompatIso

Target type:
  (slicePush g) ⋙ (J.overMapPullback A p.left)
    ≅ ((J.over X).overMapPullback A p) ⋙ (slicePush f).

### 2.1 Unit/counit cancellation lemmas

1. `S2450PushforwardComp` from `Functor.sheafPushforwardContinuousComp`:
   pushforward of a composite is the reverse composite of pushforwards.
2. `S2450SlicePushBackward` : slicePush X = pushforward of X.iteratedSliceBackward (definitional; use `rfl`/dsimp).
3. `S2450SlicePushUnit` : pushforward of `iteratedSliceForward f` is inverse to pushforward of `iteratedSliceBackward f` up to `f.iteratedSliceEquiv.unitIso`/`counitIso`.
   Lemma list: Over.iteratedSliceEquiv, .unitIso, .counitIso, Over.isoMk, Iso.refl, Functor.sheafPushforwardContinuousIso, Functor.sheafPushforwardContinuousComp.
4. `S2450IteratedSliceMapIso`: apply `Functor.sheafPushforwardContinuousIso` to `Over.iteratedSliceEquivOverMapIso p`.
5. Assemble: pushforward of `forward f ⋙ Over.map p.left ⋙ backward g` is iso to pushforward of `Over.map p`; then insert unit/counit to replace `forward f` pushforward by the inverse of `slicePush f`.

### 2.2 Associativity/unit lemma list

- Category.assoc
- Iso.trans_assoc
- Iso.trans_symm_self / Iso.symm_trans_self
- Iso.inv_hom_id, Iso.hom_inv_id
- Functor.associator_hom, Functor.associator_inv
- Functor.leftUnitor, Functor.rightUnitor
- Functor.sheafPushforwardContinuousId, Functor.sheafPushforwardContinuousComp
- Over.iteratedSliceEquivOverMapIso, hom_app_left_left
- GrothendieckTopology.overMapPullbackComp
- overMapPullback_assoc, overMapPullback_comp_id, overMapPullback_id_comp (Sites/Over.lean)

### 2.3 Component-level alternative

If functor-level assembly is too large:
- NatIso.ofComponents with component at a sheaf object S0 being exactly the S2436 equality;
- prove component naturality by ext and the S2436 pullHom coherence;
- this still reduces to the same coherence, so the preferred path is the functor-level unit/counit cancellation above.

## 3. Execution order after BUILD HOLD

1. Serialized gate: restore Mathlib, then compile S2450 skeleton (no import of unbuilt files beyond accepted oleans).
2. S2425 helpers first; then S2427SignProjection label lemma; then S2444 unit/counit lemmas.
3. One lake process at a time; no subagent lake builds in parallel while shared .lake is being repaired.
4. Report EXIT/olean/SHA/axioms for each accepted file; no IsStack claim unless actual.

No compilation performed for this plan.