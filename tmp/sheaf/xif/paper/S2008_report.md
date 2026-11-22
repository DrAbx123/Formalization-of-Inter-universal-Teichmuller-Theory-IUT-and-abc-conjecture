# S2008 report: descent of morphisms for the l-tors root prestack

Date: 2026-11-01.  File: `tmp/sheaf/xif/paper/S2008RootPrestackActual.lean`.

## Verdict

The target `(S1997RootPrestack K l).IsPrestack (etaleTopology K)` is **not**
closed.  The file removes the whole *pseudofunctor-coherence* obstruction to it
(which was the real Lean-level gap) and reduces the target to a single concrete
sheaf-theoretic statement, `S2008RootHomSheaf`.  That statement is exactly
Mathlib's `IsPrestack` unfolded; its remaining mathematical content is isolated
below.

EXIT=0.  No `sorry`, `admit`, new axiom, or instance is used; all `#print axioms`
give only `propext`, `Classical.choice`, `Quot.sound`.

## What is proved (unconditional, kernel-checked)

1. `S2008zeta_eqToHom`, `S2008zeta_id`, `S2008zeta_comp`, `S2008RootMap_zeta`,
   `S2008zeta_inv_of_hom`: bookkeeping for the unit component `zeta` of root
   morphisms.

2. `S2008cat_eqToIso_hom_toNatTrans_app`, `..._inv_...`, `..._trans_...`,
   `..._trans_inv_...`: the components of `eqToIso` of an equality of
   `Cat`-morphisms are `eqToHom`s on objects, and `≪≫` splits into composition.

3. `S2008mapComp_zeta_hom`, `S2008mapComp_zeta_inv`, `S2008mapComp'_zeta_hom`,
   `S2008mapComp'_zeta_inv`: **the `mapComp` / `mapComp'` coherence isomorphisms
   of the strict root pseudofunctor have trivial unit component** (`zeta = 1`).
   This is the technical core: these components are `eqToIso`-transports of
   equalities of functors whose underlying object maps are only propositionally
   equal, so `cases` on the equality is not available (dependent elimination
   fails).  The proof uses `Functor.toPseudofunctor'_mapComp`,
   `PrelaxFunctor.map₂Iso_eqToIso`, `generalize_proofs`, and transport of the
   proven `eqToHom` formula along the (proof-irrelevant) equality.

4. `S2008pullHom_zeta` (**pullback formula**, the main result of the file):
   for `g : Y ⟶ X` in `Over S` and `x` a root morphism over `X`,

     `(presheafHom M N).map g.op x |>.zeta = Units.map (appTop g.left.left) x.zeta`.

   This says the `zeta`-projection of the root hom presheaf is *natural*:
   descent of morphisms can now be tested on units of the structure sheaf and on
   the defining equation, with no coherence interference.

5. `S2008presheafHom_obj`, `S2008RootMap_obj_b`: the pointwise description
   (definitional) of the root hom presheaf and of the `b`-component.

6. `S2008RootPrestackIsPrestack` (the target), `S2008RootHomSheaf` (the same
   statement written concretely), `S2008isPrestack_iff` (they are equivalent, by
   definition), `S2008isStack_iff` (from S2002:
   `IsStack ↔ IsPrestack ∧ S1997RootEffectiveDescent`), and
   `S2008isStack_iff_effDescent` (given descent of morphisms, `IsStack` is
   *equivalent* to effective descent).

7. `S2008PF_defeq` : the elaboration-only abbreviation `S2008PF` is
   definitionally `S1997RootPrestack`.

## The exact first missing

After `S2008pullHom_zeta` the only remaining gap is

    S2008RootHomSheaf :
      forall (S : SchemeOverField K) (M N : root fiber over S),
        Presheaf.IsSheaf (J.over S) ((S1997RootPrestack K l).presheafHom M N),

i.e. exactly `IsPrestack` denuded of coherence.  Concretely, an element of
`presheafHom M N` over `T = (p : X → S)` is a pair
`(zeta : Gamma(X, O)^x, h : zeta^l = 1 and p^*(N.b) = zeta * p^*(M.b))`,
and by 4 the restriction map acts by `zeta |-> appTop g (zeta)`.  The sheaf
condition therefore reduces to two *sections-of-the-structure-sheaf* facts on
the etale over-site:

* (M1) `T |-> Gamma(T.left.left, O)` is a sheaf for `J.over S`,
* (M2) hence so is the sheaf of units `T |-> Gamma(T.left.left, O)^x`,
  together with locality of the equation `N.b = zeta * M.b` (separation of (M1)).

Neither is in Mathlib.  A route that should work with existing Mathlib
infrastructure (not carried out here, no time):

* `Scheme.etaleTopology.Subcanonical` follows from
  `Scheme.etaleTopology <= proetaleTopology <= fpqcTopology` and the fpqc
  subcanonical instance (`AlgebraicGeometry/Sites/{Fpqc,Proetale}.lean`), cf.
  `tmp/sheaf/n8/closure/RepresentableStackIsStackConstructed.lean`;
* the adjunction `Scheme.Gamma ⊣ Scheme.Spec` (`AlgebraicGeometry/
  GammaSpecAdjunction.lean`) gives, for `B = Z[t]`, the natural bijection
  `Hom(B, Gamma(X, O)) ~ Hom(X, Spec B)`, hence `Gamma(-, O) ~ Hom(-, Spec Z[t])`,
  which is a sheaf by subcanonicity;
* `Over.forget S` is continuous for the over-topologies
  (`GrothendieckTopology.over`, `Functor.IsContinuous`,
  `Functor.op_comp_isSheaf_of_isSheaf`), which transports (M1) to `J.over S`.

The missing work is the natural isomorphism `Gamma(-, O) ~ Hom(-, Spec Z[t])`
and the general lemma "sub-presheaf of a sheaf cut out by a local equation is a
sheaf" (used twice: sections -> units -> root homs).

## Note on the other half

`S1997RootEffectiveDescent` is *expected to fail* for Kummer covers (S2002,
section "The exact first missing"), so `IsPrestack` is the half that should
actually hold; it is the "descent of morphisms" half of `IsStack`.

## Evidence

- Build: `lake env lean -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S2008RootPrestackActual.olean tmp/sheaf/xif/paper/S2008RootPrestackActual.lean`
- EXIT=0, no warnings other than none; no `sorry`/`admit`/new axiom.
- Source: 15124 bytes, SHA256 `30DED4CA5BD61074FC892955B6AF98245CF8608403D43426874021EC48C5246E`.
- Olean: 442208 bytes, SHA256 `663AB578E9BE369656544A58BAADF1C53BF664293EA646D126BBF1B0D769CFEA`.
- `#print axioms` for the five main declarations: only `propext`, `Classical.choice`, `Quot.sound`.
- Lean 4.32.2; repo HEAD as of this session.

## Next executable step

Prove (M1) as above (subcanonicity + `Gamma ⊣ Spec` + continuity of `Over.forget`),
then the two `sub-presheaf-of-sheaf` lemmas, then assemble `IsPrestack` from
`S2008pullHom_zeta`; finally combine with `S2008isStack_iff` so that `IsStack`
is equivalent to `S1997RootEffectiveDescent` alone.
