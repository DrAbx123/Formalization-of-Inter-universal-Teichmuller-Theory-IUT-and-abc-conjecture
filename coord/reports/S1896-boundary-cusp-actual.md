# S1896: the cusp's compactification / representable open immersion

Status: **proof file compiled** (EXIT=0, no error, no warning, axioms trio only,
no `sorryAx`).  Two things are delivered:

1. the **first inhabitant in the tree of the representable-open-immersion
   property**: the identity morphism of an arbitrary etale stack is representably an
   open immersion, with a *full* `TwoPullbackWitness` for every scheme-valued
   point (`S1896IdentityOpenImmersion`);
2. the **exact first missing datum of the D9 cusp** as a decomposition plus two
   non-substitution theorems: the cusp is exactly (compactification stack,
   representable open immersion, boundary point), and the identity open immersion
   can never be the cusp's open map, for any candidate compactification equal to
   the orbicurve itself and any candidate boundary point.

Consumer: S1887 `S1887D9CuspFirstMissing` / `S1887D9CuspPairOfCusp` /
`S1887S1732SourceData`, and the whole S1743/S1756/S1784/S1804/S1831
representability line.  The package removes the statement "no inhabitant of
`EtaleStackRepresentableMorphismProperty` exists in the tree" (S1887 report, §3)
and replaces it with a construction of the property type plus a proof that the
constructed instance is *not* the cusp.

## Deliverable

| item | value |
|---|---|
| file | tmp/sheaf/xif/paper/S1896BoundaryCuspActual.lean |
| lines | 520 |
| source bytes | 24752 |
| source SHA256 | B69D9E5F1585B5140788970E8D6D79AFF60DCD3E398D9BFAE0AB2BAE38446BE2 |
| compile | `lake env lean -j1 -o .lake/build/lib/lean/tmp/sheaf/xif/paper/S1896BoundaryCuspActual.olean tmp/sheaf/xif/paper/S1896BoundaryCuspActual.lean` |
| EXIT | 0 (no error, no warning) |
| olean | .lake/build/lib/lean/tmp/sheaf/xif/paper/S1896BoundaryCuspActual.olean (437560 bytes, 2026-11-01T13:09:15) |
| olean SHA256 | 6999EEF2D94AA7954EB22955F5113B7DBFA02E1154411AF366570D3A1D4C9AD1 |
| import probe | tmp/sheaf/xif/paper/_S1896ImportProbe.lean, EXIT=0, 27 declarations `#check`ed + the target-type example |
| probe SHA256 | 819DA950F51BF45499A68BAE647952306E025775B66129EA3E7DFAF7563EBF93 |
| axioms | propext, Classical.choice, Quot.sound only (25 `#print axioms` checks, all public declarations) |
| sorry/admit/axiom in code | none (grep; the words appear only in the doc comment) |

## 1. The representable open immersion of the identity (construction)

For every field `F` and every etale stack `Y : Iut.EtaleStackOverField F`:

    S1896IdentityOpenImmersion (Y) : Iut.EtaleStackOpenImmersion (𝟙 Y.fiber).

The proof is a construction: for every test scheme `T : Over (Spec F)` and every
scheme-valued point `point : h_T ⟶ Y.fiber`,

    S1896IdentityBaseChange Y T point :
      EtaleStackBaseChangePresentation (𝟙 Y.fiber) T point

with `pullbackScheme = T`, `projection = 𝟙 T`, `projectionMap =
S1896IdentityProjectionMap T` (the 2-Yoneda 1-cell of `𝟙 T` with its `app`
pinned by `rfl`), `toSource = point`, and a **full** 2-pullback
`S1896IdentityPullback`.  This is S1804's "apex = the scheme" model: the actual
2-pullback of the cospan `(𝟙, point)` is the test scheme itself, so no schematic
fiber product beyond `T` is needed.  The witness is

* `lift` = the test-scheme leg `cone.toY` of the cone;
* `liftToX` = the cone's own 2-commuting square followed by the right unitor;
* `liftToY` = left whiskering of the unit comparison
  `S1896YonedaOneIso T : S1742StrongTransOfHom (𝟙 T) ≅ 𝟙 (h_T)` followed by the
  right unitor;
* `liftTwoCell` = the test-scheme leg of the cone morphism;
* `liftTwoCell_toX` = the cone-morphism compatibility plus the right-whiskering
  unit law `S1896WhiskerRightId`;
* `liftTwoCell_toY` and `twoCell_ext` = automatic, because every 2-cell between
  strong transformations into a *represented* stack has discrete components
  (`S1896Modification_subsingleton`).

Auxiliary bricks, all proved (no assumptions):

* `S1896App_one_eq_id`, `S1896YonedaOneIso`: the 2-Yoneda 1-cell of `𝟙 T` is
  2-isomorphic to the identity transformation (from `Category.comp_id` on the
  discrete category of sections);
* `S1896IdentityProjectionMap`: the `SchemeRepresentableMap` of `𝟙 T`;
* `S1896WhiskerLeftIso`, `S1896WhiskerRightIso`, `S1896LeftUnitorIso`,
  `S1896RightUnitorIso`, `S1896WhiskerRightId`, `S1896WhiskerExchange`,
  `S1896WhiskerRightIff`: the bicategorical unit/exchange calculus in the
  explicitly instantiated form at `EtaleStackPseudofunctor F` (see the engineering
  note below);
* `hasProperty`: the base-change projection is `𝟙 T`, whose underlying scheme map
  is `𝟙 T.left`, an open immersion.

## 2. The exact first missing datum of the D9 cusp

`S1896CuspOpenData X = Sigma Z, Sigma (m : X.stack.Hom Z), EtaleStackOpenImmersion m`
and `S1896CuspPointData D` (residue scheme, point of the compactification fiber,
boundary separation), with

    S1896CuspEquivOpenData (X) : OrbicurveBoundaryCusp X ≃ Sigma D, S1896CuspPointData D

and hence

    S1896FirstMissing_structure (l) (S : S1881D9OrbicurveSlot l) :
      Nonempty (S1887D9CuspFirstMissing l S) ↔
        ∃ D : S1896CuspOpenData S.cK, Nonempty (S1896CuspPointData D).

So the S1887 first missing datum is exactly: a compactification stack `Z` of the
K-core orbicurve, a representable open immersion `S.cK.stack ⟶ Z`, and a point of
`Z` outside the image.

## 3. Why the identity does *not* fill the cusp (non-substitution)

* `S1896Id_app_essSurj`: the identity's open map is essentially surjective at every
  scheme.
* `S1896Id_not_boundary`: for any candidate compactification equal to `X.stack`
  and *any* candidate boundary point, the boundary separation condition fails (the
  boundary point is carried to itself).  Hence the identity open map is not the open
  map of a boundary cusp.
* `S1896Cusp_openMap_app_not_essSurj`: conversely, every boundary cusp's open map
  fails to be essentially surjective at its own boundary residue scheme — the cusp
  genuinely gains a point.
* `S1896D9Cusp_identity_not_openImmersion`: the D9 specialisation of
  `S1896Id_not_boundary`.

Therefore the constructed `S1896IdentityOpenImmersion` is *not* offered as the D9
cusp: the remaining datum is the geometric compactification of `S.cK` (a stack
strictly extending it) with an open immersion that is not levelwise essentially
surjective at the boundary point.  No such stack is constructed here, and none can
be derived from the identity.

## 4. Engineering note (reusable)

Two `Category` instances coexist on `Pseudofunctor.StrongTrans X Y`:
`EtaleStackPseudofunctor.homCategory` (global, Iut/Foundations/Orbicurve.lean) and
mathlib's scoped `Pseudofunctor.StrongTrans.homCategory`.  The two are defeq but
not syntactically equal, so mathlib's `Bicategory.whisker_exchange` /
`whiskerRight_id` / `whiskerRight_iff` / `whiskerLeftIso` / `rightUnitor` fail to
elaborate directly at `EtaleStackPseudofunctor F` (metavariables for the hom type
stay unsolved).  The working recipe is the S1756 one, generalised here: pass through
a `let Bicat := EtaleStackPseudofunctor F; letI : Bicategory Bicat := inferInstance`
wrapper and `exact @Bicategory.<lemma> Bicat _ ...`.  A second trap: after
`simp only [Category.assoc]` a mixed-instance 2-cell equation may remain; `rfl`
closes it (the residual is definitional).  Both facts cost several compile cycles
here and should be stated in future representability packages.

## 5. Honest boundary (not claimed)

* No compactification stack of `S.cK`, no cusp, and no non-identity open immersion
  is constructed.  `S1881D9OrbicurveMissing` (hence `S1886PaperCF`) is untouched.
* The schematic fiber products `T ×_Z X` required by a *proper* compactification
  are not constructed; mathlib's scheme pullbacks are not used, because the identity
  case needs none.
* The paper's bad-place local generator (IUT I, Definition 3.1(f) second half)
  remains the parked card `IUT-I.definition-3.1-D9-cusp-local-generator`.
* No `True`, `PUnit`, arbitrary proposition, `sorry`, `admit` or new axiom.

## 6. One executable next step

Given a compactification candidate `Z` of `S.cK` (i.e. `S1881D9OrbicurveMissing`
plus a chosen `Z` with a scheme-level open immersion model), fill
`EtaleStackBaseChangePresentation` at each point with the schematic fiber product
`T ×_Z S.cK` and reuse `S1896IdentityPullback`'s two-cell strategy
(`S1896Modification_subsingleton` for the represented leg, `S1896WhiskerExchange`
for the open leg); then `S1896CuspOpenData` supplies the cusp as soon as the
boundary point exists.  `S1896FirstMissing_structure` is the exact interface.
