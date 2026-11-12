# S2042: D6 effectivity consumed; geometric half of S1864(c)

Date: 2026-11-02 (Asia/Shanghai).  Scope: read-only audit + one Lean reduction file.

## Layer / domain / direction / consumer

- Layer: D6 (finite-etale cover stack geometry).
- Source object: the iso-comma site pseudofunctor of two actual finite-etale
  cover maps f : A -> C, g : B -> C of S1726/S1728 covers.
- Domain: every cospan (A,B,C,f,g) of actual covers.
- Direction: actual construction / exact missing; no reverse or conditional
  wrapper is counted as the target.
- Consumer: S1864FirstMissingPseudopullbackStack -> S1836/S1832 pullback ->
  S1762 finite limits -> S1736 PreGalois category.

## What is closed

- S2026 proves `S2026IsoCommaEffectivity`, `S2026IsoCommaStack`,
  `S2026EffectivityAll`; `#print axioms` shows only
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- S2028 closes `S2018SourceSchemeAll`, `S2015IdentityRepairAll`,
  `S2018FirstMissing`, `S2001UniqFirstMissing` (not touched here).
- S1985 constructs the site-level `toA`, `toB`, `liftSite`, `liftToA`,
  `liftToB` and reduces S1864 to `S1985ApexData`.

## Exact remaining geometric half

`S1985ApexData` has fields:
1. `isStack` -- now supplied unconditionally by S2026 (removed);
2. `finiteEtale : EtaleStackFiniteEtaleMorphism (structureMap f g)`;
3. `structureMap_eq' : Iso (toB ≫ B.map) (structureMap f g)`;
4. `liftCommutes` (lift compatibility with the structure map);
5. `uniq` (lift uniqueness up to 2-isomorphism).

Items 2 and 3 are the S1864(c) fields explicitly named by the task; items 4-5
are the remaining pseudo-cone universal-property fields.  They are NOT faked:
the Lean file only removes the `isStack` field using S2026 and records the
remaining fields as an exact structure obligation.

## Geometric reason for item 2/3

`structureMap f g = toA f g ≫ A.map` by definition in S1985, and
`A.finiteEtale : EtaleStackFiniteEtaleMorphism A.map`.

- `structureMap_eq'` should follow from the two cover-map 2-commutations
  `f.commutes : f.map ≫ C.map ≅ A.map`, `g.commutes : g.map ≫ C.map ≅ B.map`
  and the iso-comma square `commutes f g`.  This is a 2-categorical
  cancellation, not a new geometric input; it is not yet written in the tree.
- `finiteEtale` of `toA ≫ A.map` needs representable finite-etale stability
  under the iso-comma projection, or the base-change identification
  `toA ≫ f.map ≅ toB ≫ g.map` plus finite-etale descent.  The tree has the
  finite-etale cover maps and the iso-comma comparison, but no closure lemma
  for `EtaleStackFiniteEtaleMorphism` under this composite.

## Lean file

`tmp/sheaf/xif/paper/S2042D6GeometricHalfActual.lean`

Contents:
- `S2042IsoCommaStack`: actual `IsStack` from `S2026IsoCommaStack`;
- `S2042ApexRemaining`: the four remaining fields (stack removed);
- `S2042ApexDataOfRemaining`: fills S1985 apex data using the actual stack field;
- `S2042FirstMissingGeometricHalf_sufficient`: remaining geometric half implies
  S1864FirstMissingPseudopullbackStack.

Build: EXIT=0.  olean: 158088 bytes at
`.lake/build/lib/lean/tmp/sheaf/xif/paper/S2042D6GeometricHalfActual.olean`.
SHA256: `D3A56111C11CA6D72132474A87B98DE7E9638D7F8580AC4282FB76D3B4D366B0`.
Axiom audit:
- `S2042IsoCommaStack`: [propext, Classical.choice, Quot.sound];
- `S2042ApexDataOfRemaining`: [propext, Classical.choice, Quot.sound];
- `S2042FirstMissingGeometricHalf_sufficient`: same, no `sorryAx`.
No source change was made to S2026/S1985/S1864.

## What is NOT claimed

- No `IsStack` is faked; `S2042IsoCommaStack` is S2026's theorem.
- No weak `TwoPullbackWitness` is used as a full pullback.
- No `finiteEtale`/`structureMap_eq'` inhabitant is fabricated.
- S1864(c), S1836/S1832 geometric half and D6 remain open until items 2-5 are
  constructed.

## S2043 update (2026-11-02)

`tmp/sheaf/xif/paper/S2043D6StructureMapEqActual.lean`

- EXIT=0; olean 37072 bytes;
  SHA256 `811C54F5A909EECE8A1F2EEA9E8BD7A7988E4B7D180E570A5FD32261F09ABF1D`.
- Axioms of `S2043_structureMap_eq'`:
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Constructs `S2043_structureMap_eq' : Iso (vcomp (toB f g) B.map) (structureMap f g)`
  by the explicit bicategorical cancellation
  `(toB ≫ B.map) <- (toB ≫ (g.map ≫ C.map)) <- ((toB ≫ g.map) ≫ C.map)
   <- ((toA ≫ f.map) ≫ C.map) -> (toA ≫ (f.map ≫ C.map)) -> (toA ≫ A.map)`
  using `g.commutes`, `commutes f g`, `f.commutes` and the
  associator/whiskering isomorphisms.
- Remaining exact D6(c) field: `S2043FirstMissingFiniteEtale` =
  `EtaleStackFiniteEtaleMorphism (source := S2042IsoCommaStackObj f g)
  (target := S1726Orbicurve.stack) (structureMap f g)`.  No representable
  finite-etale closure/stability lemma for the iso-comma projection `toA`
  exists in the tree; no fake certificate is provided.


## S2044 update: finiteEtale reduced to two named closure fields

`tmp/sheaf/xif/paper/S2044D6FiniteEtaleClosureActual.lean`

- EXIT=0; olean 20640 bytes;
  SHA256 `25E86FF8568F6CD75DCD46B4AC4496E3131C885DB58F8AB5C28B4EC7C43F0EFC`.
- Axioms of `S2044FiniteEtaleOfClosure`: `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`.
- The remaining D6(c) finite-etale certificate is reduced to exactly:
  1. `S2044ToAFiniteEtaleField`: the iso-comma first projection `toA f g` is
     representably finite etale;
  2. `S2044CompositionClosure`: representable finite etaleness is closed under
     composition of stack morphisms (pasting of base-change squares).
- `S2044FiniteEtaleOfClosure` derives `S2043FirstMissingFiniteEtale` from
  these two fields and `A.finiteEtale`.
- Neither closure field is in the tree: `EtaleStackRepresentableMorphismProperty`
  has no composition/iso-invariance API, and no `toA` finite-etale certificate
  exists.  No fake certificate is provided.


## S2046 update: finite-etale API gap (exact lemma list)

`tmp/sheaf/xif/paper/S2046FiniteEtaleAPIGapActual.lean`

- EXIT=0; olean 22088 bytes;
  SHA256 `12EC1065A5B85B0F7DAA2E798C021F7236089D999FD6AF0DFF478D6C6F62ED05`.
- Axioms of `S2046FiniteEtaleOfAPI`: `[propext, Classical.choice, Quot.sound]`,
  no `sorryAx`.
- The three missing API statements are Type-valued (no Prop/Nonempty gate):
  1. `S2046IsoInvarianceStatement`:
     `Iso f g → EtaleStackFiniteEtaleMorphism f → EtaleStackFiniteEtaleMorphism g`;
  2. `S2046CompositionStatement`:
     `EtaleStackFiniteEtaleMorphism f → EtaleStackFiniteEtaleMorphism g →
       EtaleStackFiniteEtaleMorphism (vcomp f g)`;
  3. `S2046ToAStatement`: the iso-comma first projection `toA f g` is
     representably finite etale.

### Needed lemmas to add to `Iut/Foundations/Orbicurve.lean`

1. `EtaleStackBaseChangePresentation.comp`: given a presentation of
   `f : W ⟶ Y` at a point `q : S ⟶ Z` and a presentation of `g : Y ⟶ Z`
   at the induced point `S' ⟶ Y`, construct the presentation of `vcomp f g`
   at `q`.  Apex: `pullbackScheme_g`; projection: composite
   `S'' → S' → S`; `toSource`: first `toSource` then second; commutes:
   associator/whisker composite of the two comparisons.
2. `EtalePseudofunctorSquare.TwoPullbackWitness.paste`: paste the two
   `TwoPullbackWitness` universal properties of the presentations; cone-level
   lift is the two-step lift, and the two coherence fields use
   `whiskerRight_comp`, `comp_whiskerRight`, `whisker_exchange`.
3. Scheme-level closure: Mathlib already has `Etale.comp`; add the
   `IsFinite.comp` instance if missing, then
   `isFinite_and_etale_comp` for the projection of the pasted presentation.
4. `EtaleStackFiniteEtaleMorphism.ofIso`: 2-isomorphism invariance, by
   transporting each presentation along `Iso` of morphisms.
5. `toA_finiteEtale`: the geometric certificate for the first projection.
   Geometrically it is the base change of the finite-etale cover map `B.map`
   along `A.map`; formally it needs the iso-comma realization (a) and the
   universal property (d) of S1864 to identify the base change of `toA` with
   that of `B.map`.

No witness/certificate is fabricated.  S1892 records the same pasting and
first-missing analysis; S2046 states the API at Type level without
`Nonempty`.


## S2048 update: scheme-level finite-etale composition implemented

`tmp/sheaf/xif/paper/S2048FiniteEtaleCompSchemeActual.lean`

- EXIT=0; olean 14432 bytes;
  SHA256 `96D49D6E679742981755D718D251948656C15979952080D4518E7BA0A1257130`.
- Axioms: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Proves:
  `S2048_isFinite_and_etale_comp : [IsFinite f] [Etale f] [IsFinite g] [Etale g]
   -> IsFinite (f ≫ g) ∧ Etale (f ≫ g)`,
  and the finite-only form `S2048_isFinite_and_etale_comp_apply`.
  This is API step (3) from the S2046 list.

### Remaining API steps (not faked)

1. `EtaleStackBaseChangePresentation.comp`: requires pasting two base-change
   squares; object/2-cell data is an associator/whisker composite, but the
   `TwoPullbackWitness` of the pasted square needs `TwoPullbackWitness.paste`.
2. `EtalePseudofunctorSquare.TwoPullbackWitness.paste`: two-step cone lift;
   coherence fields via `whiskerRight_comp`, `comp_whiskerRight`,
   `whisker_exchange`; not in `Iut/Foundations/Orbicurve.lean`.
3. `EtaleStackFiniteEtaleMorphism.ofIso`: needs transport of a presentation
   (including `TwoPullbackWitness` along an iso of map/commutes), not just
   object-level transport.
4. `toA_finiteEtale`: geometric certificate; base change of `B.map` along
   `A.map`, using iso-comma realization (a) and universal property (d).


## S2050: TwoPullbackWitness.paste exact statement (not implemented)

`tmp/sheaf/xif/paper/S2050TwoPullbackPasteGapActual.lean`

- EXIT=0; olean 199608 bytes;
  SHA256 `3E26029B4C07DA47D2EEE689890A468FE398D3F2EA1942DEB885421E4D48BDD3`.
- No witness is constructed and no axiom/sorry is used (no theorem asserted).
- Defines:
  - `S2050PasteProblem`: two composable 2-commutative squares `sq1`, `sq2`,
    their `TwoPullbackWitness`s, and the candidate composite square;
  - `S2050PasteStatement`: the exact missing pasting theorem, at Type level.
- Coherence list recorded in `S2050PasteCoherenceList`: two-step cone lift,
  associator/whisker comparisons for liftToX/Y, induced cone morphisms for
  liftTwoCell, and `whiskerRight_comp` / `comp_whiskerRight` /
  `whisker_exchange` for the two coherence fields plus two-step
  `twoCell_ext`.
## S2058 update: iso-invariance proved; composition reduced to one pasting computation

`tmp/sheaf/xif/paper/S2058D6FiniteEtaleActual.lean`

- EXIT=0; olean 774552 bytes;
  SHA256 `9A4288B46EE98C8FCB285AFE2F3121EFCC8F2744AC0C182E0B19D68DD28AB1B8`.
- All printed theorems: `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- **Proved** (new API): 2-isomorphism invariance of
  `EtaleStackRepresentableMorphismProperty` (generic over the field,
  `S2058IsoInvarianceProperty`) and of representable finite etaleness
  (`S2058IsoInvarianceFiniteEtale`).  The presentation is kept literally; the
  witness transport uses only `Bicategory.whisker_exchange`.  This closes
  `S1892TransportHolds` = `S2046IsoInvarianceStatement` (items 3/4 of the lists above).
- **Proved**: composition of representable scheme maps
  (`S2058SchemeRepresentableMapComp`), the full composite base-change
  presentation (`S2058BaseChangeComp`), composition closure of a representable
  morphism property from one bicategorical input (`S2058CompositionClosureOfPasting`),
  `S2044CompositionClosure` from that input
  (`S2058S2044CompositionClosure_of_pasting`), and D6(c) from the two S2044
  fields (`S2058D6FiniteEtaleCertificate`).
- **Exact first missing** (uninhabited Type obligations, nothing faked):
  1. `S2058PastingStatement` (the S2050 paste statement).  Beyond S2050, the cone
     conversions and the pasted lift are now constructed
     (`S2058Pasting.pastCone2/pastCone1/pastLift/pastLiftToX/pastLiftToY` plus the
     projection lemmas `pastCone2_toX/_toY/_commutes`).  Still to construct:
     `pastCone2Hom`, `pastCone1Hom`, `pastWitness`, and inside it the
     `liftTwoCell_toY` distribution computation (pure bicategorical coherence).
  2. `S2058IsoCommaTwoPullback` -- the general 2-universal property of the
     iso-comma square for *arbitrary* cones (S1864 (d) general form; the tree has
     only the bicone case `liftSite` and S1893's fibre-level statement).  With it
     plus a second pasting (`T x_A (A x_C B) = T x_C B`) one gets
     `S2044ToAFiniteEtaleField`.
- **Not claimed**: `S2044ToAFiniteEtaleField` remains open; D6(c) is reduced to
  (1)+(2), not closed.


## S2066: explicit hom/inv components of S2058 pastLiftToY

`tmp/sheaf/xif/paper/S2066PastLiftToYComponentsActual.lean`

- EXIT=0; olean 51288 bytes;
  SHA256 `EBBBFE3EBC846009836945FE8C9CD9AAE9CFA0D893574599BF417A263B5C42BD`.
- Axioms: both component lemmas depend only on
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Proves, with rw only on `Iso.trans_hom`/`Iso.trans_inv`/`Iso.symm_hom`/
  `Iso.symm_inv` (no simp expansion of nested `Iso.trans`):
  - `S2066_pastLiftToY_hom`:
    `(pastLiftToY ...).hom = assoc.inv ≫ (w1.liftToY ▷ D.toY2).hom ≫ (w2.liftToY).hom`;
  - `S2066_pastLiftToY_inv`:
    `(pastLiftToY ...).inv = (w2.liftToY).inv ≫ (w1.liftToY ▷ D.toY2).inv ≫ assoc.hom`.
- Also needed `set_option backward.isDefEq.respectTransparency false` because
  `pastCone1.toY` is not unfolded at `instances` transparency.

Next: `liftTwoCell_toY` distribution using these explicit components, then
`pastCone2Hom`/`pastCone1Hom`/`pastWitness`, then S2058IsoCommaTwoPullback.


## S2067 attempt: pastCone2Hom blocked on dependent type cast

Attempted `S2067pastCone2Hom` (upper-square cone morphism) with
`toX := whiskerRight m.toX D.x1`, `toY := m.toY`, and compatibility by
`associator_naturality_left` + `m.compatibility`.

Exact blocker: the expected field type uses
`(D.pastCone2 c).toX`, while the 2-cell `whiskerRight m.toX D.x1` has source
`c.toX ≫ D.x1`.  These are propositionally (and by the rfl theorem
`S2058Pasting.pastCone2_toX`) equal but not definitionally equal at the
transparency used by the structure-field checker.  `rw` fails because the
motive is not type-correct (the whisker term's source type depends on the
rewritten `toX`).

Concrete fix (next step):
1. build `pastCone2Hom.toX` as
   `eqToHom (pastCone2_toX).symm ≫ whiskerRight m.toX D.x1 ≫ eqToHom pastCone2_toX`
   (2-cell casts in the hom category), or
2. make `S2058Pasting.pastCone2` an `abbrev`/add reducible projection lemmas,
   so `(pastCone2 c).toX` reduces to `c.toX ≫ D.x1`.
Then the compatibility proof reduces to `associator_naturality_left`,
`Category.assoc`, and `m.compatibility`.

No file was accepted this step; S2066 remains the last EXIT=0 artifact.


## S2069: composition closure completed unconditionally

`tmp/sheaf/xif/paper/S2069D6CompositionClosureActual.lean`

- EXIT=0; olean 34072 bytes;
  SHA256 `4AE0AF184D6D4266A5BA39B11BA2D079849D736F052A2ABC1DBFC021D2358B24`.
- Axioms: `S2069CompositionStatement`, `S2069CompositionClosure`,
  `S2069D6FiniteEtaleOfToA` all depend only on
  `[propext, Classical.choice, Quot.sound]`, no `sorryAx`.
- Uses S2062's unconditional `Iut.EtaleStackBaseChangePresentation.comp` and
  `Iut.SchemeRepresentableMap.comp` plus S2048's scheme-level
  `S2048_isFinite_and_etale_comp`.
- Proves:
  - `S2069CompositionStatement : S2046CompositionStatement` (unconditional);
  - `S2069CompositionClosure : S2044CompositionClosure` (unconditional);
  - `S2069D6FiniteEtaleOfToA (htoA : S2044ToAFiniteEtaleField) :
     S2043FirstMissingFiniteEtale` for every cospan.

So the only remaining D6(c) finite-etale input is the geometric
`S2044ToAFiniteEtaleField` (equivalently `S2058IsoCommaTwoPullback`).


## S2074: iso-comma 2-universal property exact missing

`tmp/sheaf/xif/paper/S2074IsoCommaTwoPullbackActual.lean`

- EXIT=0; olean 121504 bytes;
  SHA256 `310BF127DFC5E8406684A160DCC49B0F3B5E6CEA72CB25C88186EBF71CDFF5D6`.
- Introduces the general pseudo-cone `S2074GeneralCone` (arbitrary
  pseudofunctor W, arbitrary `toA/toB` strong transformations and a commuting
  2-cell iso) and the exact statement
  `S2074IsoCommaTwoPullbackStatement` (the full `TwoPullbackWitness` of the
  iso-comma square for every cospan).
- No witness is fabricated.  The tree has only:
  - `S1893Lift`: fibre-level lift for a cone of functors at one test object;
  - `S1985.liftSite`: site-level lift only for bicones `S1832Bicone`.
- Exact missing site-level content:
  1. `generalLiftNat`: natural iso across a site morphism, built from
     `c.toA.naturality`, `c.toB.naturality`, `c.commutes` and S1893's
     `S1893ComparisonFunctor`;
  2. `naturality_naturality`, `naturality_id`, `naturality_comp` coherence
     (analogues of S1985 `liftNatConeA/B`/`liftNatIso`, only bicone);
  3. `liftToA`/`liftToB` site-level naturality;
  4. `liftTwoCell`/`_toA`/`_toB`;
  5. `twoCell_ext` (available from `S1836IsoComma_hom_ext`).


## S2076: fixed site API gap beyond S1832Bicone

`tmp/sheaf/xif/paper/S2076GeneralLiftAPIGapActual.lean`

- EXIT=0; olean 31936 bytes;
  SHA256 `BC17FC0838E45A7CA88EFFB5B24599CB706E3E83EA1112A959DFEE9AC037EEE6`.
- Records the four Type-valued API statements needed to generalize S1985 from
  bicones to arbitrary `S2074GeneralCone`s:
  1. `S2076ComponentIsoStatement`: the component of `c.commutes` at U as an
     iso `(c.toA.vcomp f.map).app U ≅ (c.toB.vcomp g.map).app U`;
  2. `S2076ConeAtStatement`: the transported `S1893Cone`;
  3. `S2076LiftAppStatement`: the fibre-level `S1893Lift` functor;
  4. `S2076SiteLiftStatement`: the site-level strong transformation
     `W -> sitePseudofunctor f g`.
- Exact first missing: no instance `IsIso (c.commutes.hom.as.app U)`.
  Mathlib gives only `Cat.Hom.toNatIso` / `Cat.Hom.isoMk`, and S1985 avoids
  this by using `S1832Bicone` fields directly.  A component-iso extraction from
  `c.commutes : Iso (vcomp ...) (vcomp ...)` (plus the two
  `Pseudofunctor.StrongTrans.comp_app` transports) is required first; then
  `generalLiftNat`/coherence mirror S1985 `liftNatConeA/B`, `liftCone_compat`,
  `liftConeIso`, `liftNatIso`, `liftSite`.


## S2077/S2078: component iso and fibre-level lift implemented

### S2077
`tmp/sheaf/xif/paper/S2077ComponentIsoActual.lean`
- EXIT=0; olean 56616 bytes;
  SHA256 `B0D05B9DD85C20499D3F7CF7E76827A6C680E44445BA008CC3D4C719C4E07D07`.
- `S2077ComponentIso (c) (U) :
   Iso ((c.toA.vcomp f.map).app U) ((c.toB.vcomp g.map).app U)`.
- Proof extracts the component of `c.commutes.hom_inv_id` and
  `c.commutes.inv_hom_id` via the modification-component formulas; no
  `IsIso` instance is fabricated.
- Axioms: `[propext, Classical.choice, Quot.sound]`.

### S2078
`tmp/sheaf/xif/paper/S2078ConeAtLiftAppActual.lean`
- EXIT=0; olean 54184 bytes;
  SHA256 `4FD5C74CDFF36B2810745B499489231F2F933439E27F2786015D2D7926AF04FD`.
- `S2078ConeAt (c) (U) : S1893Cone ...`, with the comparison transported along
  `Pseudofunctor.StrongTrans.comp_app`;
- `S2078LiftApp (c) (U) : ↑(c.W.obj U) ⥤ S1836IsoComma ...` via `S1893Lift`.
- Axioms clean.

### S2079 (in progress, not accepted)
`generalLiftNatConeA/B` typecheck, but `S2079cone1_commutes_app` still needs
the app lemma for `S2078ConeAt.commutes`: rewrite `S2077ComponentIso` through
`Cat.Hom.toNatIso` and the two `comp_app` `eqToIso` transports.  Exact
missing: a lemma
`((eqToIso e).trans (Cat.Hom.toNatIso e')...).app x` reducing to
`e'.hom.toNatTrans.app x`; the required names/API are
`Cat.Hom.toNatIso_hom` plus `Iso.trans_hom`/`NatIso.trans_hom_app`
(`Iso.trans_app` does not exist).


## S2077/S2078/S2079: component iso, lifted cone, first naturality maps

- S2077 `S2077ComponentIso`: EXIT=0, SHA
  `B0D05B9DD85C20499D3F7CF7E76827A6C680E44445BA008CC3D4C719C4E07D07`,
  olean 56616; axioms trio.
- S2078 `S2078ConeAt`/`S2078LiftApp`: EXIT=0, SHA
  `4FD5C74CDFF36B2810745B499489231F2F933439E27F2786015D2D7926AF04FD`,
  olean 54184; axioms trio.
- S2079 `S2079LiftNatConeA/B`: EXIT=0, SHA
  `46452DE5BD1360C68BE3A3C9D7784102D2EF6469ECBFD3BCA42DF2CA32808527`,
  olean 39504; `S2079LiftNatConeA` axioms trio (ConeB same construction).
- Still missing: `cone1_commutes_app`, i.e.
  `((S2078ConeAt ...).commutes.app x).hom = (c.commutes.hom.as.app V).toNatTrans.app x`.
  Explicit rewrite status: `NatIso.trans_app` applies, reducing to a
  composition of the two `eqToIso` app isos and the component iso.  The
  remaining app-level lemma is
  `(eqToIso h).app x = eqToHom (congrArg (fun F => F.obj x) h)` together with
  `Iso.trans_hom`/associativity; `Iso.trans_hom` does not match the current
  goal directly, so the next step is a dedicated
  `S2079ConeAt_commutes_app` lemma with an explicit `change` to the
  `eqToHom ≫ ... ≫ eqToHom` form.


## S2080: app-level eqToIso lemma

`tmp/sheaf/xif/paper/S2080ConeAtCommutesActual.lean`
- EXIT=0; olean 20664 bytes;
  SHA256 `1EE8C23A70453B279F6EEFD5DF26A6B4F8303A35174A672F710EF2B46DBD46E0`.
- Proves `S2080_eqToIso_app :
  (eqToIso h).app x = eqToIso (congrArg (fun F => F.obj x) h)`, axioms trio.
- The dedicated `S2080ConeAt_commutes_app` still needs the hom-level form
  `((eqToIso h).app x).hom = eqToHom (congrArg (fun F => F.obj x) h)`
  (stating it with RHS `𝟙 (F.obj x)` is ill-typed before `cases h`), then
  `Iso.trans_hom` for the composition of the two `eqToIso` app isos and the
  `S2077ComponentIso` component.


## S2080/S2081: app-level eqToIso and cone1 commutativity

- S2080 EXIT=0; SHA
  `3C0CFA16FA0AEAFDD3F48C47228B34AFA7FD772BAA8814960EF6C397797BA795`;
  olean 90568; axioms trio.
  - `S2080_eqToIso_app`;
  - `S2080_eqToIso_app_hom` (hom-level helper);
  - `S2080ConeAt_commutes_app`:
    `((S2078ConeAt ...).commutes.app y).hom = (c.commutes.hom.as.app V).toNatTrans.app y`.
- S2081 EXIT=0; SHA
  `E47054FBB749D20CB7EB096AE17AD0161190468C149CDA2C447161A2A075E771`;
  olean 72648; axioms trio.
  - `S2081cone1_commutes_app` for general cones.
- S2082 (cone2) attempted but not accepted: after `S1893Lift_structure`, the
  term `(S2078ConeAt).commutes.app x` has type with source
  `(ConeAt.toA ⋙ f).obj x`, while rewriting the lift projections to
  `(c.toA.app U).toFunctor.obj x` makes the motive ill-typed.  Next fix:
  prove app-level projection lemmas
  `((S1893Lift ...).obj x).obj.left = (c.toA.app U).toFunctor.obj x` and
  right version, then rewrite `S2080ConeAt_commutes_app` **before** the
  projection rewrites (or use `congrArg` on the whole comparison).


## S2082-S2084: general cone2, liftCone_compat, liftNatIso

- S2082 `cone2_commutes_app` plus `S2082At_commutes_app'` (at U, needed by cone2):
  EXIT=0; SHA `03145C5ECCCFC93609144E22C3C84935AF40FB7E2FB24FDECF9F893B6F8F8E2D`;
  olean 141696; axioms trio.
- S2083 `liftCone_compat` (with general `vcomp_toA/B_naturality_apply`):
  EXIT=0; SHA `DA5E907BD4567F6569D1722B153CF3AD77C903E416442E98A6A427647A592D4D`;
  olean 214912; axioms trio.
- S2084 `liftConeHomForward`, `liftConeIso`, `liftNatIso`:
  EXIT=0; SHA `38F1BDBCF689A790602763546D470418E027A3139A267DAF2CB02001385BD599`;
  olean 121832; axioms trio.
- Remaining: `liftNatIso_hom_fst/snd`, `liftSite` (naturality_naturality/id/comp,
  long S1985 copy adapted to `c.W`), then `liftToA/liftToB` and the full witness.


## S2086: ToA assembly from the iso-comma witness

`tmp/sheaf/xif/paper/S2086ToAAssemblyActual.lean`
- EXIT=0; olean 163120 bytes;
  SHA256 `3B8FB1BA82D8C7C4788E69E988EF9C37A8E5FC5524C3A1845167CD951A4AFD7D`.
- Axioms of `S2086ToAOfWitnessBaseChange`: `[propext, Classical.choice, Quot.sound]`.
- Uses S2076's complete `S2058IsoCommaTwoPullback` and the B-side finite-etale
  presentation; derives `S2044ToAFiniteEtaleField` from the exact missing
  geometric input `S2086WitnessBaseChangeStatement`:
  for every point `ptA` of A and every B-presentation at
  `(ptA ≫ f.map) ≫ C.map`, produce an `EtaleStackBaseChangePresentation` of
  `toA f g` at `ptA` whose projection is finite etale.
- This is exactly the base-change stability/cone construction step: construct
  the cone over the iso-comma square from `ptA` and the B base change, apply
  `S2076Witness.lift/liftToA`, and identify the C-side comparison with the
  C.source point.  No presentation or finite-etale certificate is fabricated.
- `S2071PastingStatement` is not used in this assembly (it is a pasting
  theorem, not a base-change restriction of the witness).


## S2087: exact obstruction for S2086WitnessBaseChangeStatement

`tmp/sheaf/xif/paper/S2087ToAObstructionActual.lean`
- EXIT=0; olean 9864 bytes;
  SHA256 `8C1384A940B531D05EE5A0D1FBCC93BB79E3EB4907135F2D9E2DAB634392C33A`.
- To construct the cone over the iso-comma square from `ptA`, one needs a
  point of `B.source.fiber` over the **C.source** point `ptA ≫ f.map`.
  The only finite-etale presentation in the tree is
  `B.finiteEtale : EtaleStackFiniteEtaleMorphism B.map`, whose target is the
  orbicurve stack, not `C.source.fiber`.
- Exact additional input:
  `S2087GMapFiniteEtaleField` (every cover map `g : B -> C` is representably
  finite etale), equivalently a direct finite-etale proof for
  `structureMap = toA ≫ A.map`.
- No such certificate is fabricated; if `g.map` is not finite etale, the
  ToA factorization `structureMap = toA ≫ A.map` is insufficient.


## S2088: scheme cancellation and stack cancellation reduction

`tmp/sheaf/xif/paper/S2088GMapCancellationActual.lean`
- EXIT=0; olean 25976 bytes;
  SHA256 `0FAB3E9DD477789FBE8AD55A200AAB5573921A2CBCF6430009CE80331E5EB2E7`.
- Axioms of both theorems: `[propext, Classical.choice, Quot.sound]`.
- Proves scheme-level cancellation
  `S2088_scheme_finiteEtale_cancel`:
  `[Etale (f ≫ g)] [LocallyOfFiniteType g] [FormallyUnramified g]
   [IsFinite (f ≫ g)] [IsSeparated g] -> Etale f ∧ IsFinite f`
  using Mathlib `Etale.of_comp` and `IsFinite.of_comp`.
- Reduces `S2087GMapFiniteEtaleField` to
  `S2088StackCancellation`:
  `finiteEtale (f ≫ g) -> finiteEtale g -> finiteEtale f`.
  The proof uses `B.finiteEtale`, `C.finiteEtale`, and
  `S2058IsoInvarianceFiniteEtale` with `g.commutes`.
- Exact remaining input for D6(c): `S2088StackCancellation`.  Its proof needs
  the stack-level base-change presentation construction: present `f` at a
  point `ptY` of Y by using the presentation of `g` at `ptY ≫ g` and the
  presentation of `f ≫ g` at the resulting Z-point, then cancel the scheme
  morphisms with `S2088_scheme_finiteEtale_cancel`.


## S2089: stack cancellation reduced to presentation + property

`tmp/sheaf/xif/paper/S2089StackCancellationActual.lean`
- EXIT=0; olean 23976 bytes;
  SHA256 `C5E04AB9E409DF3B413B9BE7AFAB0AC875F2BB48B19232738DB8538C810E11DB`.
- Axioms of `S2089StackCancellationOfPresentation`:
  `[propext, Classical.choice, Quot.sound]`.
- `S2089StackPresentationStatement`: from `finiteEtale (f ≫ g)` and
  `finiteEtale g`, construct `EtaleStackBaseChangePresentation f T ptY`.
- `S2089StackPropertyStatement`: its projection is finite etale.
- `S2089StackCancellationOfPresentation`: these two give
  `S2088StackCancellation`.

Exact remaining D6(c) content:
1. presentation construction: base-change the triangle along `ptY` using
   `hg.baseChange T (ptY ≫ g)` and `hf.baseChange` at the resulting Z-point,
   then compare the two presentations via full faithfulness of `toA`/finite-etale
   covers; the presentation of `f` has the composite scheme projection;
2. property: apply `S2088_scheme_finiteEtale_cancel` to the two scheme
   projections.  The missing formal step is the comparison/pasting of the two
   `EtaleStackBaseChangePresentation`s, not the scheme-level cancellation.


## S2090: obstruction to stack-cancellation presentation route

`tmp/sheaf/xif/paper/S2090StackCancellationObstructionActual.lean`
- EXIT=0; olean 12632 bytes;
  SHA256 `EE941E1A65CF4E954CB067F537EBB6179CD89D406DF1C526F04538E4AF2BF9F4`.
- States the exact missing postcomposition-cancellation principle
  `S2090PostcompCancellation`:
  `Iso (a ≫ g) (b ≫ g) → Iso a b`.
- This principle is false for an arbitrary stack morphism `g` (in Cat,
  postcomposition by a constant functor loses information).  Therefore one
  cannot build the presentation of `f` at `ptY` by cancelling `g` in the
  comparison 2-isomorphism of the two presentations.
- Consequence: `S2089StackPresentationStatement` is not derivable from the
  recorded fields; the exact remaining input is representability/finite
  etaleness of the cover-map morphisms (S2087 fields), or a direct finite-etale
  proof of `structureMap = toA ≫ A.map`.


## S2091: scheme-level cancellation specialized

`tmp/sheaf/xif/paper/S2091SchemeDirectActual.lean`
- EXIT=0; olean 14616 bytes;
  SHA256 `21E06ED92492D99698840D142822620A20EC7CE1246AEB99F68E940B1C12DB58`.
- Proves `S2091_scheme_finiteEtale_cancel_special`:
  `[IsFinite (f ≫ h)] [Etale (f ≫ h)] [IsFinite h] [Etale h] ->
   IsFinite f ∧ Etale f`.
- This is the scheme-level cancellation required after base change, but it
  does **not** by itself yield `EtaleStackFiniteEtaleMorphism g.map`:
  `g.map : B.source.Hom C.source` is a morphism of stacks, and a
  base-change presentation at a point of `C.source` is exactly the
  representability data not in the tree.
- Exact remaining input: `S2087GMapFiniteEtaleField` (or a stack
  representability theorem for morphisms between finite-etale stacks), then
  S2091 closes the scheme-level property after presentations.


## S2092: exact stack-level morphism API

`tmp/sheaf/xif/paper/S2092FiniteEtaleStackMorphismActual.lean`
- EXIT=0; olean 17672 bytes;
  SHA256 `81F796480355A5DB529BD6B62425EF1E86C13826D171CEF002A498890985A5FC`.
- Axioms of `S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks`:
  `[propext, Classical.choice, Quot.sound]`.
- Exact missing API `S2092MorphismOfFiniteEtaleStacks`:
  `orall (m : X.Hom Y) (y : Y.Hom Z) (x : X.Hom Z),
    Iso (m ≫ y) x -> finiteEtale x -> finiteEtale y -> finiteEtale m`.
- `S2092GMapFiniteEtaleOfMorphismOfFiniteEtaleStacks` shows this API gives
  `S2087GMapFiniteEtaleField` (take `m = g.map`, `x = B.map`,
  `y = C.map`, `g.commutes`).
- Why C/B presentations alone do not suffice: after base change one only
  compares points of `C.source` after composing with `C.map`; comparing them
  before `C.map` is exactly the missing representability/descent step.
- This is the precise remaining D6(c) input: a stack-level theorem that a
  morphism between finite-etale stacks over a base is representably finite
  etale, or equivalently the corresponding base-change/descent construction.


## S2094: two full-2-universal inputs for S2086BaseChangePullback

`tmp/sheaf/xif/paper/S2094FullUniversalInputsActual.lean`
- EXIT=0; olean 17840 bytes;
  SHA256 `8A7BC9698328B5E390E229A925172ACC80A71331FBA75257EA805E03E4272D14`.
- Exact missing inputs, stated as Prop:
  1. `S2094BigSquareEssSurj`: the iso-comma square
     `(toA, toB, f.map, g.map)` has the full 2-universal property
     `S1827EssSurjOf` with the S2076 witness.  S2076 supplies a weak
     `TwoPullbackWitness`, not `S1827EssSurjOf`.
  2. `S2094GPresentationConeEssSurj`: every used
     `EtaleStackBaseChangePresentation g.map` has `S1852ConeEssSurj`; the
     presentation's `isPullback` field is only a weak
     `TwoPullbackWitness`.
- To prove `S2086BaseChangePullback` one must upgrade both to the full
  2-universal properties and paste them in the butterfly configuration, then
  obtain the base-change square's full witness.  No witness is fabricated.


## S2095: lift uniqueness reduced to a single statement

`tmp/sheaf/xif/paper/S2095BigLiftUniqActual.lean`
- EXIT=0; olean 24176 bytes;
  SHA256 `43B33D2ED3AE6215EE317C1BCF79A599CC95D733A338EB636B6A809EA1A699AA`.
- Axioms of `S2095BigEssSurj_of_liftUniq`:
  `[propext, Classical.choice, Quot.sound]`.
- Exact remaining lift-uniqueness statement `S2095BigLiftUniq`: for every cone
  `c` over the iso-comma square and every `h : W -> sitePseudofunctor` with
  isos of the two projections to `c`, there is an iso
  `h ≅ (S2076Witness).lift W c`.
- `S2095BigEssSurj_of_liftUniq : S2095BigLiftUniq -> S2094BigSquareEssSurj`.
- This is exactly the full 2-universal (essential-surjectivity/lift-uniqueness)
  property missing from the weak S2076 witness.  Next: prove it via
  `S1893LiftUniq`/fibre comparison + `gTwoCell_ext`, then
  `S1852ConeEssSurj Pg`.


## S2096: lift uniqueness needs site-level S1893 naturality

Proving `S2095BigLiftUniq` requires the following missing API, not present in
the tree:

1. `S1893LiftUniq`/fibre comparison gives an isomorphism of functors at each
   test object U, but its **naturality in U** for the site pseudofunctor is
   absent.  The required lemma is a natural iso between
   `h.app U` and `gLiftApp c U` compatible with
   `S1890IsoCommaMap f g φ`, built from the two projection isos `eX`, `eY`.
2. The site-level coherence of this natural iso (`naturality_naturality`,
   `naturality_id`, `naturality_comp`) must be checked after whiskering by
   `toA`/`toB` and closed by `gTwoCell_ext`; the projection equations are
   exactly `eX`/`eY`, but the coherence identities are not in the tree.
3. `S1852ConeEssSurj Pg` is the analogous full 2-universal property for the
   g-presentation square; it is also absent.

No witness is fabricated.  `S2095BigLiftUniq` remains the exact missing
site-level lemma; once it is proved, S2095/S2094 give
`S2094BigSquareEssSurj`, then S1852 gives the base-change pullback.


## S2102: g-presentation full property identified

`tmp/sheaf/xif/paper/S2102GPresentationFullActual.lean`
- EXIT=0; olean 19520 bytes;
  SHA256 `4701BB86288F89C559200DE85DB39B869FD9EEBAE8A036D72211ED10D30F401A`.
- Proves `S2102ConeEssSurj_iff :
  S1852ConeEssSurj P ↔ S1827EssSurjOf (S1852WeakSquare P) P.isPullback`.
- Defines the exact missing input `S2102GPresentationFull`: every g-presentation
  used in S2086 satisfies `S1852ConeEssSurj`.
- This is the full 2-universal property of the base-change presentation square,
  not a consequence of the weak `isPullback` field (cf. S1899).


## S2103: strong-presentation assembly (weak S2094 input refuted)

`tmp/sheaf/xif/paper/S2103StrongAssemblyActual.lean`
- EXIT=0; olean 31136 bytes;
  SHA256 `9DED2F8516BE0CAE07C0DD7F401ED970CD786C948EB83AE24CFA2283479BE926`.
- Axioms of both `S2103ToAOfStrongInputs` and
  `S2103D6FiniteEtaleOfStrongInputs`: `[propext, Classical.choice, Quot.sound]`.
- Replaces the refuted weak input `S2094GPresentationConeEssSurj` (S2100) by
  strong finite-etale structures:
  - `S2103StrongCospanGMapFiniteEtale`: every `g.map` carries a
    `StrongEtaleStackFiniteEtaleMorphism`;
  - `S2103StrongBaseChangePullback hg`: butterfly two-pullback required only
    for the strong presentations selected by `hg`;
  - `S2103ToAOfStrongInputs hg h : S2044ToAFiniteEtaleField`;
  - `S2103D6FiniteEtaleOfStrongInputs hg h`: D6(c) for every cospan.
- No false universal quantification over arbitrary weak presentations remains.


## S2103 correction

`S2087 M1` (curve affine quotient packaging,
`curvePreGaloisRemainingFields`) is **not** the strong finite-etale certificate
for `g.map`; `S2103StrongCospanGMapFiniteEtale` still requires the S2092
stack theorem or an added strong structure.  D6(c) remains:
1. `S2103StrongCospanGMapFiniteEtale`;
2. `S2103StrongBaseChangePullback` / `S2095ToBButterfly`;
3. `S2094BigSquareEssSurj`.

No new accepted artifact this step; S2103 remains the last EXIT=0 assembly.


## S2104: canonical twist in the actual butterfly configuration

`tmp/sheaf/xif/paper/S2104ButterflyTwistActual.lean`
- EXIT=0; olean 26912 bytes;
  SHA256 `F4C11F0E958CB424CBE14577E437CC0FEEC0A71B404CA636C71673BD8DC71D5A`.
- Axioms of `S2104ToBButterflyCanonicalTwist`:
  `[propext, Classical.choice, Quot.sound]`.
- Instantiates `S2099TwistAt_canonical` at the actual S2095 path-B butterfly cone:
  `c = S2095ToBCone`, `h = (S2076Witness).lift`,
  `alpha = liftToX`, `beta = liftToY`.  Thus the compatibility (twist)
  datum genuinely exists in the butterfly configuration.
- S2099SiteFirstMissing asks the twist for **arbitrary** `h`; this is not
  implied by the weak witness and is not asserted.  The actual butterfly only
  needs the canonical twist, which is proved here.
- Remaining: package this canonical twist into the full cone comparison /
  butterflies two-pullback witness; S2094BigSquareEssSurj still needs the
  arbitrary-h site statement and is not derivable.


## S2105: packaging S2095ToBButterfly status

The canonical twist (S2104) covers the compatibility of the two projection
2-cells in the actual butterfly.  However `S2095ToBButterfly` is a
`TwoPullbackWitness` of `S2095ToBSquare` and still needs:

1. a lift for an arbitrary butterfly cone `W` (a 1-cell `W -> Pf.apex`),
   not derivable from the canonical twist alone;
2. `liftToX`/`liftToY` comparisons with the two legs;
3. `liftTwoCell`/`_toX`/`_toY`;
4. `twoCell_ext` for the pasted square.

The paste is not literally an S2062/S2064 composite: the S2064 corrected
pasting has the second square's base legs tied to the first square, while the
butterfly square `T x_C A = T x_B (A x_C B)` has the Pf-presentation square
on `f.map` sharing the C-point but not the B-leg.  Hence S2062's pasting
theorem does not directly apply.

S2104 remains the last accepted artifact for this route; no witness is
fabricated.


## S2106: right-cancel status

Attempted to attack `S2097RightCancelStatement` (reverse pasting: weak+full
bottom and weak+full pasted -> weak top).  A direct construction needs a
top-square lift from a top cone; the top cone does not induce a cone over the
bottom square, and the pasted-square cone comparison only becomes available
after the top lift exists.  The full `S1827EssSurjOf` properties of bottom and
pasted squares do not themselves provide the reverse pasting: this is precisely
the non-tautological 2-categorical lemma isolated by S2097, and no construction
was completed.

Also `S2097TwoFullInputs.pastedTransport` remains unformalized
(swap/toY-leg iso via `S2097LiftToB`, blocked on whiskerRight coherence).

No new accepted artifact; last accepted remains S2104
(SHA `F4C11F0E958CB424CBE14577E437CC0FEEC0A71B404CA636C71673BD8DC71D5A`).


## S2109: strong-input butterfly (replaces false S2108 hG)

`tmp/sheaf/xif/paper/S2109StrongButterflyActual.lean`
- EXIT=0; olean 60792 bytes;
  SHA256 `D14CB121DB51300F77E96388C76733E535650A3FC36C120F9C97F6820753D9CC`.
- Axioms of `S2109StrongBaseChangePullbackOfInputs` and
  `S2109D6FiniteEtaleOfStrongInputs`: `[propext, Classical.choice, Quot.sound]`.
- Uses only strong finite-etale structures on `g.map` (S2103 input); no
  `S2094GPresentationConeEssSurj` (refuted by S2100).
- `S2109StrongPastedFull hg` = big-square full property
  (`S2094BigSquareEssSurj`) + pasted-square full data for the strong
  presentations `((hg ...).baseChange ...).toWeak`.
- `S2109StrongBaseChangePullbackOfInputs (hRC) hg h :
   S2103StrongBaseChangePullback hg` via S2097's right-cancel theorem.
- `S2109D6FiniteEtaleOfStrongInputs (hRC) hg h : D6(c)`.

Exact remaining for this route:
1. `S2109StrongCospanGMapFiniteEtale` (strong certificate for every `g.map`);
2. `S2109StrongPastedFull`: `S2094BigSquareEssSurj` + pasted transport for
   strong presentations;
3. `S2097RightCancelStatement`.


## S2110: canonical 2-cell for the actual butterfly

S2107 reduces right-cancel to `S2107CanonicalLiftTwoCell`: an action on cone
morphisms of the lower square with the two projection equations.
`S2104ToBButterflyCanonicalTwist` supplies the twist for the *canonical lift*
in the actual butterfly, but constructing the 2-cell action from it still
needs the `D.toY1`-projection equation for
`sigma0 = wP.liftTwoCell (E m)`; the pasted witness gives the equation only
after `D.toY1 ; D.toY2`.  The missing ingredient is the upper-square
2-cell fullness/compatibility isolated in S2107 §6
(`S2107ImageCone`/`S2107ConeComparisonFull`, S1801 `TwoCellSurjTo` shape).

No new accepted artifact; last accepted S2109
(SHA `D14CB121DB51300F77E96388C76733E535650A3FC36C120F9C97F6820753D9CC`).


## S2111: canonical twist vs canonical 2-cell

S2101's `S2096LiftUniq_of_projectionCompat` gives lift uniqueness **after**
supplying `S2096ProjectionCompatibility` for the given `h`.  S2104 supplies
that compatibility only for the canonical lift
(`h = gLiftSite c`, `eX = gLiftToA`, `eY = gLiftToB`); it does not supply
the compatibility for an arbitrary `h`, so it cannot be used to prove
`S2095BigLiftUniq`/global `S2099SiteFirstMissing`.

For `S2107CanonicalLiftTwoCell`, both source and target lifts are the
canonical lift, and the canonical twist is available; but the remaining
`D.toY1`-projection equation for `wP.liftTwoCell (E m)` still requires the
upper-square 2-cell fullness isolated in S2107 §6
(`S2107ImageCone`/`S2107ConeComparisonFull`, S1801 `TwoCellSurjTo` shape).
No construction of that fullness is present, so the canonical 2-cell action is
not proved.

No new accepted artifact; last accepted S2109
(SHA `D14CB121DB51300F77E96388C76733E535650A3FC36C120F9C97F6820753D9CC`).


## S2116: concrete pasted-comparison twist status

`S2115PastedComparisonTwist` is not yet proved for
`wP = S2108PastedWitness`.  The witness is the leg-change transport
`S2108IsoWitnessY` with
`e = (S2097LiftToB).symm`, `c' = (S2097Pasting ...).gamma`; its
`liftToY` is a whisker-left composite.  The required equation is the
cone-morphism compatibility of `S2107LiftToYIsoX/Y` with the upper-square
commutes cell.  A proof must unfold `S2108PastedWitness` and
`S2107LiftToYIsoX/Y` and use the explicit definitions of
`S2097Pasting.gamma` and `S2086Cone.commutes`; no lemma packaging this
equation exists in the tree.

No new accepted artifact; last accepted S2109
(SHA `D14CB121DB51300F77E96388C76733E535650A3FC36C120F9C97F6820753D9CC`).


## S2127/S2128 batch (review-corrected, no blind R1)

### S2127 acceptance
`tmp/sheaf/xif/paper/S2127ToYLegsActual.lean`
- EXIT=0 after adding `set_option backward.isDefEq.respectTransparency false`
  (the only source change; needed for the `D.toY1` vs `square1.toY`
  transparency mismatch in the leg rewrites).
- olean 195680 bytes; SHA256
  `B657A7E6EA868EE3D80AE027B78946672501D906206C671229779B8422B34235`.
- Axioms: all audited declarations depend only on
  `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- **Registration correction**: every main theorem
  (`S2127XiLeg`, `S2127ToY2Leg`, `S2127Legs`, `S2127ToYEquation`,
  `S2127RebuiltWitness`, `S2127ToAWitness`) takes
  `h : S2121ComparisonTwist f g T ptA Pg`.  The file header's
  "unconditionally" wording is inaccurate; it must be cited as conditional on
  `S2121ComparisonTwist`.

### S2128 doubled probe
`tmp/sheaf/xif/paper/S2128DoubledProbeActual.lean`
- EXIT=0; olean 16272 bytes; SHA256
  `BFF7CD86EEE5C7C0D526128E8B2763D82DC0FB741E2C2CAD2C275268DBB6E699`.
- Concrete datum: `A = B = C = S1850DoubledCover`,
  `f = g = S1641CoverMapId A`, `T = S1850T`, `ptA = S1733BasePoint`,
  `Pg = S1850Doubled T ptA`.
- `S2128Pg` and `S2128F` axioms trio.  Both
  `S2121ComparisonTwist ... S2128Pg` and `S2094BigSquareEssSurj` typecheck.
- **No counterexample derived**: the probe typechecks the instantiations but
  does not produce a contradiction, so neither statement is marked
  REFUTED-informal.  They remain unverified/conditional and are not used for
  D6.

### Exact missing
`S2121ComparisonTwist` (still open for the concrete `S2108PastedWitness`) and
`S2097RightCancelStatement`; no coherence field was added and no false `hG`
is used.


## S2151: S2096 vertex-square unpasting, exact missing

`tmp/sheaf/xif/paper/S2151UnpastingActual.lean`
- EXIT=0; olean 18592 bytes;
  SHA256 `6201331E792CD8ACF0B221A10D20C8D79457ECE5B49F37022D2DE80BDD4ABD78`.
- Defines the exact missing implication
  `S2151UnpastingOfFull`: for every m, y, T, ptY and presentations Py, Px,
  the full cone essential-surjectivity
  `S1827EssSurjOf (S1852WeakSquare Py) Py.isPullback` and
  `... Px ...` give a weak `TwoPullbackWitness` of
  `S2096VertexSquare`.
- No inhabitant is asserted; hence `S2096UnpastingStatement` remains open.
- Exact gap: full cone essential-surjectivity supplies 1-cell uniqueness, but
  the weak lift/comparisons of the vertex square still require the
  reverse-pasting/right-cancellation step (S2097/S2107) plus the square
  transport; the tree has no proof of this implication.


## S2156: S2096BaseChangeStatement exact missing API

`tmp/sheaf/xif/paper/S2156S2096BaseChangeActual.lean`
- EXIT=0; olean 14240 bytes;
  SHA256 `EE8BBCC298329FC781498FCB4AEFC1CB664AEF5A5D116BF897B20770207A2664`.
- Defines `S2156SchemeRepresentableMapBaseChange`: base change of a
  `SchemeRepresentableMap` along a scheme square with given pullback
  projections, assuming the right leg finite etale; the base-changed projection
  is again scheme-representable.
- `S2096BaseChangeStatement` typechecks but has no inhabitant.
- Exact first missing: the above scheme-map base-change API, plus base change of
  the weak `TwoPullbackWitness` of the presentation square.  No coherence
  fields were added; no presentation/witness is fabricated.


## S2161: S2156 scheme-map base-change API closed

`tmp/sheaf/xif/paper/S2161BaseChangeAPIActual.lean`
- EXIT=0; olean 21480 bytes;
  SHA256 `B477E585118894C7E2CF7CF4FFD391C01D8115FDB62D3ED157268C838A0C1B26`.
- Axioms of `S2161SchemeRepresentableMapBaseChange`:
  `[propext, Classical.choice, Quot.sound]`.
- **Unconditional**: for every scheme morphism `q : R -> T`,
  `S1742StrongTransOfHom q` is definitionally the induced functor, hence
  `SchemeRepresentableMap q`.  The square/finite-etale hypotheses are unused
  for this API.
- Thus S2156 input (1) is closed.
- S2096BaseChangeStatement remains open: the missing part is now only the
  base change of the weak `TwoPullbackWitness` of the presentation square
  (plus the scheme-side construction of the base-changed presentation data).


## S2165: scheme-side base-changed presentation data (partial (a))

`tmp/sheaf/xif/paper/S2165BaseChangeWitnessActual.lean`
- EXIT=0; olean 49544 bytes;
  SHA256 `528C33E3146D1ED8A5A459F7E6B61DDC0620501463A268D79A4468F734933AF5`.
- `S2165Square` axioms: `[propext, Classical.choice, Quot.sound]`.
- Constructed:
  - `S2165Apex`: Over-pullback of `Q.pullbackScheme` along `s`;
  - `S2165Fst` / `S2165Snd`: the two Over-projections;
  - `S2165Square`: `S2165Fst ≫ Q.projection = S2165Snd ≫ s`;
  - `S2165ProjectionMap`: `SchemeRepresentableMap (S2165Snd)` via S2161.
- Still missing for S2096BaseChangeStatement:
  1. the `toSource` and `commutes` 2-cell of the base-changed presentation
     (whiskering Q.commutes along `S2165Fst`, plus the pullback square);
  2. base change of the weak `TwoPullbackWitness` along this finite-etale
     square (2-categorical stability/right-cancel).


## S2175: base-changed presentation toSource + projection comparison

`tmp/sheaf/xif/paper/S2175BaseChangePresentationActual.lean`
- EXIT=0; olean 41600 bytes;
  SHA256 `D27A2F326AD14FB0D32BFD062610D68311A84C4A61A87D62767637848E61FD7D`.
- `S2175ProjectionIso` axioms: `[propext, Classical.choice, Quot.sound]`.
- Constructed:
  - `S2175FstT`, `S2175SndT`, `S2175sT` (Yoneda strong transformations);
  - `S2175ToSource`: `FstT ; Q.toSource`;
  - `S2175HomEq`: the two composites have the same underlying scheme map
    (via S2165Square), and `S2175ProjectionIso`:
    `(FstT ; Q.projectionMap.transformation) ≅ (SndT ; sT)`.
- **Not proved**: `S2175Commutes` (the commutes 2-cell by whisking
  `Q.commutes` and reassociating).  An explicit nested
  `Iso.trans`/associator chain exceeded the 600 s build budget; it must be
  factored into small component lemmas before retrying.
- Still missing for S2096BaseChangeStatement: commutes 2-cell + base change of
  the weak `TwoPullbackWitness`.


## S2208: factored commutes components (partial)

`tmp/sheaf/xif/paper/S2208BaseChangeCommutesActual.lean`
- EXIT=0; olean 25104 bytes;
  SHA256 `4924234FEFDC9C73979D379B18532582836DAE80CE8575DA78A97732BD2D2E8D`.
- Constructed component isomorphisms:
  - `S2208LeftAssoc`: `(FstT ; Q.toSource) ; m ≅ FstT ; (Q.toSource ; m)`;
  - `S2208WhiskerLeft`: whisker `Q.commutes` by `FstT`;
  - `S2208RightAssoc`: `FstT ; (Q.proj ; vy) ≅ (FstT ; Q.proj) ; vy`;
  - `S2208ProjectionWhisker`: whisker `S2175ProjectionIso` by `vy`.
- **Not proved**: `S2208Commutes` (the four-component composition) and the final
  associator `(SndT ; sT) ; vy ≅ SndT ; (sT ; vy)`.  The composition/final
  associator retriggered the whnf timeout; they must be stated with further
  intermediate defs (or component homs) to avoid elaboration blow-up.
- Still missing: the commutes 2-cell and (b) weak witness base change.


## S2224: final associator + commutes composition closed

`tmp/sheaf/xif/paper/S2224BaseChangeCommutesFinalActual.lean`
- EXIT=0; olean 27760 bytes;
  SHA256 `F2E26DA0F527E33886ADB656FCDD893E40983CFE07F40CF6D250C7260CA07524`.
- Axioms of `S2224FinalAssoc`, `S2224Comp1`, `S2224Comp2`,
  `S2224Commutes`: `[propext, Classical.choice, Quot.sound]`; no `sorryAx`.
- `S2224FinalAssoc`: `(SndT ; sT) ; vy ≅ SndT ; (sT ; vy)` with
  `sT = S1742StrongTransOfHom s` stated explicitly (avoids abbreviation blow-up).
- `S2224Comp1`, `S2224Comp2`: the two two-step composites of the S2208
  components.
- `S2224Commutes`: entire chain
  `(FstT ; Q.toSource) ; m ≅ SndT ; (sT ; vy)`.
- Thus the commutes 2-cell of the base-changed presentation is actual up to the
  definitional identification of `S2165ProjectionMap.transformation` with
  `SndT` and of `S2175ToSource` with `FstT ; Q.toSource`.
- Remaining for S2096BaseChangeStatement: (b) base change of the weak
  `TwoPullbackWitness` along the finite-etale square.


## S2231: witness base change -- exact missing interface

`tmp/sheaf/xif/paper/S2231WitnessBaseChangeActual.lean`
- EXIT=0; olean 5432 bytes;
  SHA256 `A624EB5065C5E791D6E57699331C334CEFED5C4C785FC9865C28DA1D701C22C0`.
- Records `S2231WitnessTransport := S2096BaseChangeStatement` as the exact
  missing witness-transport input.  No construction of the weak
  `TwoPullbackWitness` from `Q.isPullback` is available; the actual
  base-changed presentation data (apex/projections/toSource/commutes) are in
  S2165/S2175/S2224.
- No witness fabricated, no coherence fields, no false hG.


## S2237: witness transport interface

`tmp/sheaf/xif/paper/S2237WitnessTransportActual.lean`
- EXIT=0; olean 6752 bytes;
  SHA256 `69D3C951E87517ED78527F83FA2CE8CAADC6E6143C5410D71C7A505B8841B8D7`.
- Records the two conceptual missing maps only:
  `S2237ConeOverQ` (base-changed cone -> Q cone) and
  `S2237SchemePullbackLift` (compatible pair -> lift to the base-changed apex).
  In this file both are only interfaces (reducible to
  `S2096BaseChangeStatement`); **no witness is constructed**.
- Actual construction would need:
  1. cone over Q from the base-changed cone using `S2224Commutes`;
  2. `Q.isPullback.lift` plus the literal scheme-pullback universal property;
  3. liftToX/liftToY and the 2-cell coherence, which is the true 2-categorical
     stability step.
- No fake witness, no coherence fields, no false hG.


## S2241: witness construction attempt (not accepted)

Attempted step (1): transport a cone over the base-changed square to a cone
over Q's square using the S2224 commutes chain.  The file
`tmp/sheaf/xif/paper/S2241WitnessActual.lean` failed to typecheck
(`IsFinite`/`Etale` binder resolution and dependent argument inference);
no olean was produced and it is not recorded as accepted.

Steps (2) and (3) remain the exact missing 2-categorical stability:
`Q.isPullback.lift` + the literal scheme-pullback universal property, then
liftToX/liftToY and 2-cell coherence.  No fake witness.


## S2244: cone transport attempt blocked on missing square

`tmp/sheaf/xif/paper/S2244ConeTransportActual.lean` did not typecheck: the
attempted `S2231Square` reference is unavailable (the earlier S2231 file was
recorded as the minimal `S2231WitnessTransport := S2096BaseChangeStatement`
interface, so the concrete base-changed square definition is not in the tree).
No olean produced; not accepted.

Next concrete dependency: first re-declare the base-changed presentation square
`S2231Square` with explicit universe binders (the earlier attempt hit
`stuck at solving universe constraint`), then the cone transport in S2244 can
be retried.  Steps (2)/(3) remain unchanged.


## S2247: actual base-changed presentation square

`tmp/sheaf/xif/paper/S2247BaseChangeSquareActual.lean`
- EXIT=0; olean 21080 bytes;
  SHA256 `C1A6C4FD2E49164FA0BA0A1DD467E359C81FAACC6C46F4B8A3159E055872859E`.
- `S2247Square` actual:
  - apex `schemeRep (S2165Apex ...)`;
  - `toX := S2175ToSource`;
  - `toY := S2165ProjectionMap.transformation`;
  - `xToBase := m`;
  - `yToBase := S1742StrongTransOfHom s ; vy`;
  - `commutes := S2224Commutes`.
- Universe/typeclass binders explicit (`AlgebraicGeometry.IsFinite/Etale`,
  named `m,s,vy,Q,hs,hse,hq,hqe`); no invalid option.
- Next: S2244 cone transport can use `S2247Square`; then (2)/(3) remain.


## S2252: cone transport step (1) actual

`tmp/sheaf/xif/paper/S2252ConeTransportActual.lean`
- EXIT=0; olean 26688 bytes;
  SHA256 `A7CDCEB7F18BC293CD158D6B255892AD7493C6F7D9F635E715D53DD7F4B228D4`.
- `S2252ConeOverQ`: from a cone over `S2247Square` produces a cone over
  `S1852WeakSquare Q`:
  - `toX := c.toX`;
  - `toY := c.toY ; S1742StrongTransOfHom s`;
  - `commutes := c.commutes ; (associator c.toY sT vy).symm`.
- Step (1) is now actual.

### Exact first missing for step (2)
The lift cannot come from a *literal scheme pullback* universal property: a cone
over the base-changed square supplies `W -> X.fiber` and `W -> schemeRep T`
with `W` an arbitrary etale-stack pseudofunctor, not a scheme.  A lift
`W -> schemeRep (S2165Apex)` is a **2-categorical** pullback/unpasting
statement for representable presheaves, not the scheme-level universal property.
The needed input is the left-leg unpasting/right-cancel
(`S2151UnpastingOfFull` / `S2097RightCancelStatement` plus square transport),
followed by `liftToX/liftToY` and 2-cell coherence.  No witness is fabricated.


## S2254: unpasting/lift API audit

`tmp/sheaf/xif/paper/S2254UnpastingLiftActual.lean`
- EXIT=0; olean 34288 bytes;
  SHA256 `3ADE33C8C6326D6EF9D8385726D3A05736E6BC3B71F4C438F66C9050B2E5101F`.
- Audit: no inhabitant of the 2-categorical unpasting API exists in the tree.
  - `S2151UnpastingOfFull`: Type, no inhabitant;
  - `S2097RightCancelStatement`: stated, not proved;
  - `S2107CanonicalLiftTwoCell`: reduction, not proved.
- `S2254UnpastingAPI := S2151UnpastingOfFull`;
  `S2254RightCancelInputs` bundles `S2097RightCancelStatement` +
  `S2094BigSquareEssSurj`.
- No lift `W -> schemeRep (S2165Apex)` constructed; nothing faked.


## S2257: concrete right-cancel attempt

`tmp/sheaf/xif/paper/S2257RightCancelActual.lean`
- EXIT=0; olean 6424 bytes;
  SHA256 `BB426BD3E8E6EB43DA4C451A3BDD57839CBBC9B78CBE0D8F76117023550F4E5D`.
- Attempted concrete `S2097RightCancelStatement` using the strict scheme
  pullback of S2165 and S2224 commutes.  Obstruction: the strict pullback only
  controls scheme-valued points, while the required lift is for an arbitrary
  etale-stack pseudofunctor `W`; the concrete instance still needs the
  2-categorical unpasting input.
- Recorded missing types `S2257ConcreteRightCancel := S2097RightCancelStatement`
  and `S2257ConcreteUnpasting := S2151UnpastingOfFull`.  No proof fabricated.


## S2261: audit of S2094BigSquareEssSurj

`tmp/sheaf/xif/paper/S2261BigSquareEssSurjActual.lean`
- EXIT=0; olean 6288 bytes;
  SHA256 `FF42D4867A4713E7E79EDF63B3EC89DEABFCC44DAB7349B47148309642D600C8`.
- Audit:
  - `S2100NotGPresentationConeEssSurj` refutes only
    `S2094GPresentationConeEssSurj`, **not** `S2094BigSquareEssSurj`;
  - no counterexample to `S2094BigSquareEssSurj` in the tree;
  - only reduction available: `S2095BigLiftUniq` ->
    `S2094BigSquareEssSurj`; `S2095BigLiftUniq` unproved.
- Exact first missing: `S2095BigLiftUniq` (site-level lift uniqueness /
  naturality).  No proof or refutation fabricated.


## S2262: audit of S2095BigLiftUniq

`tmp/sheaf/xif/paper/S2262BigLiftUniqActual.lean`
- EXIT=0; olean 5408 bytes;
  SHA256 `661BA714FDA5DBF5A938970AB0B054AF1E48226D904F893DD823E0FD480FCBAE`.
- Audit: `S2095BigLiftUniq` needs, for arbitrary `h`, the projection
  compatibility `S2096ProjectionCompatibility` (a family, not a single Prop)
  plus site naturality of `S1893LiftIsoOfConeIso`.  S2101 proves the latter
  only *given* compatibility; S2104 supplies compatibility only in the
  canonical case.  The weak witness does not yield compatibility for arbitrary
  `h`.
- Exact first missing: arbitrary-h projection compatibility / site naturality.
  No proof or refutation fabricated.


## S2265: arbitrary-h projection compatibility audit

`tmp/sheaf/xif/paper/S2265ProjectionCompatActual.lean`
- EXIT=0; olean 4352 bytes;
  SHA256 `A3071DE150400D5135A8469D81A4F26EAEC357C4F093E051BBC7F8E879F78A54`.
- Records/checks `S2095BigLiftUniq` and `S2094BigSquareEssSurj`.
- Audit: S2101 proves lift uniqueness only **given**
  `S2096ProjectionCompatibility`; S2104 gives compatibility only for the
  canonical lift.  No construction for arbitrary `h` and no formal
  counterexample was produced.
- Exact first missing remains arbitrary-h `S2096ProjectionCompatibility` plus
  site naturality.  No fake.


## S2272: arbitrary-h compatibility audit

`tmp/sheaf/xif/paper/S2272ArbitraryHCompatActual.lean`
- EXIT=0; olean 3560 bytes;
  SHA256 `E98B9F41920304D5A954068D96FD2B2315C05B49B2A7C25AD92398F647383D8F`.
- Audit: S2104 canonical compatibility + S2101 uniqueness only covers the
  canonical lift; for arbitrary `h` and arbitrary projection isomorphisms the
  missing premise is exactly the compatibility being sought.  No proof or
  formal counterexample produced.
- Exact first missing unchanged: arbitrary-h
  `S2096ProjectionCompatibility` + site naturality.


## S2274: arbitrary-h compatibility counterexample attempt

`tmp/sheaf/xif/paper/S2274ArbitraryHCounterexampleActual.lean`
- EXIT=0; olean 3728 bytes;
  SHA256 `5BB1814CA69A1D869B3D5AB89AF2F4B61CFBB5E6419A92D31B84C0CF0F731F52`.
- No formal counterexample was obtained.  The existing noncanonical data
  (`S1850Doubled`, inl/inr, `S1827EssSurjNotFromWitness`) concern 1-cell or
  full-essential-surjectivity failures, not a failure of the 2-cell twist
  `S2096ProjectionCompatibility` for a specific `h` with projection
  isomorphisms.
- Qualitative status: **unrefuted**; exact first missing remains arbitrary-h
  projection compatibility + site naturality.


## S2276: presentation twist / strict-cone coherence, qualitative closure

`tmp/sheaf/xif/paper/S2276PresentationTwistActual.lean`
- EXIT=0; olean 10400 bytes;
  SHA256 `38378F4A3D34922A859D886A8ACAD2AD9CB89B77FA73B029794E81B55DD71B99`.
- `S2276StrongCoverConeIso (Cs) (B) : S2240ConeIsoAt B (StrongCover.cover Cs)`,
  built from the actual S2240 theorem `S2240ConeEssSurjAt_of_strongCover`
  (full 2-universal property of the strong finite-etale structure).
- `S2276UniformWeakRefuted : ¬ S2240FirstMissing`, exactly
  `S2240NotFirstMissing` (S1850Doubled refutation).
- Qualitative: the coherent lift cone morphism / strict-cone comparison exists
  for **strong target covers**; the uniform version over all recorded weak
  covers is **false** (refuted), not merely missing.
- Exact remaining for D6: use strong target covers (S1852/S2100 route); no
  uniform weak construction is possible.


## S2281: actual S2086/S2087 target cover is NOT necessarily strong

`tmp/sheaf/xif/paper/S2281ActualCoverStrongActual.lean`
- EXIT=0; olean 23368 bytes;
  SHA256 `0490CE6770095BCC6D3CBB8819CDB183F26ACEE9DE131C5C05FE9A52F212A34F`.
- Axioms of both theorems: `[propext, Classical.choice, Quot.sound]`.
- `S2281NotAllCoversStrong`:
  `¬ ∀ A : S1728Cover, ∃ M : StrongEtaleStackFiniteEtaleMorphism A.map,
  M.toWeak = A.finiteEtale`.
  Proof: apply to `S1850DoubledCover`; then `S1852Doubled_not_strong`.
- `S2281NotAllCoversCoherent`: `¬ ∃ C : CoherentCover,
  C.cover = S1850DoubledCover`; proof `S1852DoubledCover_not_coherent`.
- Therefore the actual S2086/S2087 target (all `S1728Cover`) **cannot** be
  closed by the strong-cover route as-is.  Either a strong finite-etale
  structure is added as an explicit input (S2103 route), or the target is
  restricted (not allowed).  No target change was made.


## S2284: S2086/S2087 quantifier audit

`tmp/sheaf/xif/paper/S2284S2086QuantifierActual.lean`
- EXIT=0; olean 12456 bytes;
  SHA256 `0B37AB289B4394BCF093BBBCAED228908A90F574D922F0CD00AE4DFC0FBECBCF`.
- Axioms of both theorems: `[propext, Classical.choice, Quot.sound]`.
- `S2284CospanFullQuantifier`: definitionally,
  `S2086CospanGMapFiniteEtale = forall A B C f g,
  EtaleStackFiniteEtaleMorphism g.map`.  The target is **not** restricted to
  concrete covers.
- `S2284StrongCospanToWeak`: the S2103 strong input forgets to S2086's weak
  cospan field.
- Therefore D6(c) unrestricted is conditional on
  `S2103StrongCospanGMapFiniteEtale` (strong certificate for every `g.map`),
  which is not proved.  Executable next target: prove that strong certificate
  (S2092 stack theorem / added strong structure), or keep D6(c) conditional.


## S2287: doubled cover does NOT refute S2103StrongCospanGMapFiniteEtale

`tmp/sheaf/xif/paper/S2287StrongCospanRefuteActual.lean`
- EXIT=0; olean 11000 bytes;
  SHA256 `CAB251B21945F0F39A26CEA1D345643CA3B971180A272956681302483B0EFE95`.
- `S2287G := S1641CoverMapId S1850DoubledCover`;
  `S2287StrongOnDoubled := StrongEtaleStackFiniteEtaleMorphism S2287G.map`;
  `S2287QuantifierInstance : S2103StrongCospanGMapFiniteEtale ->
  S2287StrongOnDoubled` by direct instantiation.
- **No refutation**: S2103 quantifies only over `g.map` and asks for some strong
  structure; it does **not** require `M.toWeak = g.finiteEtale`.
  `S1852Doubled_not_strong` only rules out strong structures whose weak part
  equals `S1850DoubledFiniteEtale`, so it does not apply.
- Exact obstruction to this refutation route: the missing equality
  `M.toWeak = g.finiteEtale` inside S2103.  S2103 remains **unrefuted**.


## S2290: S2103 is not trivially true

`tmp/sheaf/xif/paper/S2290StrongCospanActual.lean`
- EXIT=0; olean 13744 bytes;
  SHA256 `82003E4B13384C46E87B736168E987B60A95E028B966336C7C8CFB82D5F3BAFF`.
- `S2290WeakToStrongUpgrade`: the per-cospan upgrade
  `EtaleStackFiniteEtaleMorphism g.map -> StrongEtaleStackFiniteEtaleMorphism g.map`.
- `S2290S2103ToWeak : S2103 -> S2087CospanGMapFiniteEtaleField` (forget).
- `S2290S2103_of_weakUpgrade : upgrade -> weak field -> S2103`.
- Hence S2103 is equivalent to the weak field plus the missing per-morphism
  upgrade; it is **not** trivially true, and no strong structure is constructed.
- Exact missing: `S2290WeakToStrongUpgrade` (full cone essential surjectivity /
  S1852/S2100 strong structure for arbitrary `g.map`).


## S2293: weak-to-strong upgrade audit

`tmp/sheaf/xif/paper/S2293WeakToStrongActual.lean`
- EXIT=0; olean 5376 bytes;
  SHA256 `2327FE018B16F8391AAAA89DB9ED7E9894D100414615F0E8CACE5C9E40AE7D3A`.
- `S2293Upgrade := S2290WeakToStrongUpgrade`.
- Audit: `StrongEtaleStackFiniteEtaleMorphism` adds the full cone
  essential-surjectivity of the chosen base-change presentations
  (`StrongEtaleStackBaseChangePresentation`).  Upgrading an arbitrary weak
  structure requires producing a full presentation at every point, i.e. the
  S1852/S2100 full 2-universal property, unavailable for arbitrary `g.map`.
- No upgrade constructed; no counterexample.  Exact first missing:
  `S2290WeakToStrongUpgrade` (equivalently per-`g.map` full presentation).


## S2327: three rational 2-torsion transport -- exact missing

`tmp/sheaf/xif/paper/S2327TorsionTransportActual.lean`
- EXIT=0; olean 3912 bytes;
  SHA256 `B4C220DBF64B7117D7B0902453F023DBACD74CFF8A2597279EDA3012F3C9E0C0`.
- Audit: `T.clauseC.torsion23_rational` is only
  `PuncturedEllipticCurve.Torsion23Rational X = AllNTorsionRational X 6`
  (every closure 6-torsion point has an F-rational affine representative).  It
  does not provide three explicit distinct nonzero 2-torsion points.
- To construct `S2296ThreeRationalTwoTorsion` one still needs:
  1. three distinct nonzero 2-torsion points over the algebraic closure;
  2. their rational affine representatives from `torsion23_rational`;
  3. base change F -> Fv -> LF + `Projective.Point.toAffineAddEquiv` +
     `pointTransport_galois` (S1550) into `SideKPoint T b`;
  4. `IsGaloisFixed`, `2 • P = 0`, pairwise distinctness.
- No witness constructed; no fake.


## S2333: three rational 2-torsion -- exact missing API

`tmp/sheaf/xif/paper/S2333ThreeTwoTorsionActual.lean`
- EXIT=0; olean 4192 bytes;
  SHA256 `B6AEF0D29286EE0A84722FC3F3A889F8B2F82D474E0CB9C394819D7634657115`.
- Mathlib has `WeierstrassCurve.twoTorsionPolynomial`,
  `WeierstrassCurve.Affine.Point.mk`, `Point.baseChange`,
  `Projective.Point.toAffineAddEquiv`; S1550 has `pointTransport_galois`.
- Missing: a lemma identifying `twoTorsionPolynomial.eval x = 0` with
  `W.Equation x 0` (only described in Mathlib comments/TODO), and a
  2-torsion point constructor.  Without these, the three distinct nonzero
  2-torsion points and their rational representatives cannot be built.
- No witness fabricated.


## S2335: twoTorsionPolynomial vs Equation x 0

`tmp/sheaf/xif/paper/S2335TwoTorsionRootActual.lean`
- EXIT=0; olean 101416 bytes;
  SHA256 `EC45546407D1665D3E20A984DC3018A9A500175A4237F223B6A2EF407FB5E54A`.
- Axioms of `S2335TwoTorsionPolynomial_eval`:
  `[propext, Classical.choice, Quot.sound]`.
- Proved identity:
  `W.twoTorsionPolynomial.toPoly.eval x =
  (W.a1*x + W.a3)^2 + 4*(x^3 + a2*x^2 + a4*x + a6)`.
- Since `W.Equation x 0` is exactly
  `x^3 + a2*x^2 + a4*x + a6 = 0`, the root condition
  `twoTorsionPolynomial.eval x = 0` is **not** equivalent to
  `W.Equation x 0` when `a1*x + a3 != 0` (e.g. outside char 2).
  The correct 2-torsion point has `y = -(a1*x + a3)/2`, not `y = 0`.
- Exact first missing/route correction: either use the general
  `y = -(a1*x+a3)/2` point, or restrict to `a1 = a3 = 0` short Weierstrass
  form.  No fake equivalence.


## S2337: corrected 2-torsion y-coordinate

`tmp/sheaf/xif/paper/S2337TwoTorsionCorrectActual.lean`
- EXIT=0; olean 16520 bytes;
  SHA256 `182F170DAF9AA30C80CA6F3375A889F95A634BC593110C68654D3D6C100A554A`.
- Defined `S2337Y W x = -((a1*x + a3)/2)`.
- The attempted proof of `WeierstrassCurve.Affine.Equation W x (S2337Y W x)`
  from `twoTorsionPolynomial.eval x = 0` did not close: after `field_simp`
  the final inverse-of-4 normalisation failed, and a hypothesis `(2:R) ≠ 0`
  is needed (char 2 requires the separate short-Weierstrass branch).  The
  failing theorem was removed, so no sorryAx is present.
- Exact first missing: (i) the equation proof with `2 ≠ 0` (clean computation
  from the S2335 identity); (ii) `2 • Point.mk ... = 0`; (iii) three distinct
  roots over the splitting field.  No fake.


## S2344: corrected Equation proof still open

`tmp/sheaf/xif/paper/S2344TwoTorsionEquationActual.lean`
- EXIT=0; olean 3336 bytes;
  SHA256 `1B43DCDE0B382898959146BC021DEB5220E3A243EE7339D7DA202B57EFDED1D9`.
- No theorem: the attempted proof of
  `W.Equation x (S2337Y W x)` under `(2:R) ≠ 0` from the S2335 identity
  still failed at the final polynomial normalisation/linear-combination
  (field_simp leaves inverse-of-4 terms; nlinarith/linear_combination close
  neither directly).
- Exact missing is now purely the final algebra step: after
  `2y = -(a1x+a3)` and
  `(a1x+a3)^2 + 4*(x^3+a2x^2+a4x+a6)=0`, prove
  `y^2 + a1xy + a3y = x^3+...`.  No fake.


## S2349: calc proof of 2-torsion Equation -- still not closed

`tmp/sheaf/xif/paper/S2349TwoTorsionEqProofActual.lean`
- EXIT=0; olean 3352 bytes;
  SHA256 `66DE5BA6614313C110A8E4CEDEE6992341D28E70085827CBDCFBEDDEB095D566`.
- No theorem: the explicit calc proof still fails.  Recorded errors: the
  `h4` derivation leaves an unsolved `linarith`, the first calc step's
  `field_simp/ring` closes too early ("No goals"), and the final division
  step leaves `linarith` on a `False` goal.  The failing theorem was removed;
  no sorryAx.
- Exact remaining: a correct `h4` normalization
  (`s = a1*x+a3`, `s^2 + 4*f = 0`) and the final
  `-s^2/4 = f` step without field_simp-induced false goals.


## S2354: 2-torsion point from S2353, 2P=0 still missing

`tmp/sheaf/xif/paper/S2354TwoTorsionPointsActual.lean`
- EXIT=0; olean 18240 bytes;
  SHA256 `B6D581230CFA775C947F917B1A6F48A442B4565DD58BDE9C86242D2F74E6D38A`.
- Actual: `S2354Point W h2 x hx := Affine.Point.mk (S2353_equation W h2 x hx)`,
  the 2-torsion affine point attached to a 2-division root.
- Missing: `(2 : Nat) • S2354Point ... = 0`.  Attempts failed on
  (i) `HSMul ℕ W.toAffine.Point` instance resolution (AddCommGroup instance
  not selected through `W.toAffine`), and (ii) unfolding `Point.mk`/
  `WithZero.some.injEq` for the negation comparison.
- Exact first missing: the affine `AddCommGroup`/negation API route
  (`AddCommGroup W.toAffine.Point` instance plus `WithZero.some.injEq` /
  `neg_some`) to prove `P = -P`, then `add_eq_zero_iff_eq_neg`.
- No fake; no sorryAx.


## S2358: 2-torsion order attempt blocked on affine group instance

`tmp/sheaf/xif/paper/S2358TwoTorsionOrderActual.lean`
- EXIT=0; olean 2352 bytes;
  SHA256 `1994787CC37CAA08C6AB89ABF0EF3F01DBD20812CABEED4A859490A5EE668854`.
- No theorem: `letI : AddCommGroup W.toAffine.Point := inferInstance` fails
  ("failed to synthesize AddCommGroup W.toAffine.Point"), so `2 • S2354Point`
  cannot be elaborated; `WithZero.some.injEq` is also not the available name.
- Exact first missing: the correct `AddCommGroup W.toAffine.Point` instance
  route (Mathlib's affine group instances are under a section whose variables
  do not unify with `W.toAffine` automatically) and the proper
  `WithZero/Point.some` injectivity lemma; then `P = -P` and `2 • P = 0`.
- No fake; no sorryAx.


## S2365: three distinct 2-torsion points -- exact missing

`tmp/sheaf/xif/paper/S2365ThreeTwoTorsionActual.lean`
- EXIT=0; olean 2616 bytes;
  SHA256 `5517954A4269C7210D16349D72E771802718D166903B5627DDEB3C99A48E43EF`.
- Audit: Mathlib has `Cubic.roots`, `Cubic.splits_iff_roots_eq_three`,
  `Cubic.discr_ne_zero_iff_roots_nodup`; S2353/S2354/S2358 (lead's direct proof)
  give Equation/point/2-torsion for each root.
- Still needed: assume `(2:R)≠0`, base-change `W` to `AlgebraicClosure R`,
  extract three distinct roots from `discr ≠ 0`/nodup, apply the point
  construction at each root, then `Affine.Point.baseChange` +
  `Projective.Point.toAffineAddEquiv` + `pointTransport_galois` (S1550), and
  prove nonzeroness/distinctness/`IsGaloisFixed`.
- No witness fabricated.


## S2369: three distinct roots over algebraic closure -- exact missing

`tmp/sheaf/xif/paper/S2369ThreeTwoTorsionActual.lean`
- EXIT=0; olean 2880 bytes;
  SHA256 `01BA0CACB0C90EEC12EFAC09F029F4A95D39E795786779D6376AA9AD0088AC2F`.
- Audit: `IsAlgClosed.splits`, `Cubic.splits_iff_roots_eq_three`,
  `Cubic.discr_ne_zero_iff_roots_nodup`, `WeierstrassCurve.baseChange` are
  available.  Still needed: `(2:R)≠0`, W elliptic, base-change to
  `AlgebraicClosure R`, extract x1 x2 x3 from splits + discr ≠ 0, apply
  S2353/S2354/S2358 at each root, then `Affine.Point.baseChange` +
  `Projective.Point.toAffineAddEquiv` + `pointTransport_galois` (S1550).
- No witness constructed.


## S2376: three distinct 2-division roots over the algebraic closure (actual)

`tmp/sheaf/xif/paper/S2376ThreeRootsActual.lean`
- EXIT=0; olean 81136 bytes;
  SHA256 `F37B43B199F3ABCB622777E74F0D2C24BCEC1C0E1639E9CE3CFDF23F70EAEB96`.
- Axioms of `S2376ThreeDistinctRoots`: `[propext, Classical.choice, Quot.sound]`.
- Proved: for a field `R`, `W : WeierstrassCurve R` with `W.IsElliptic`, and
  `(2:R) ≠ 0`, there exist `x y z : AlgebraicClosure R` pairwise distinct,
  each a root of `Cubic.map (algebraMap R (AlgebraicClosure R))
  W.twoTorsionPolynomial`.
- Construction: `Cubic.splits_iff_roots_eq_three` +
  `IsAlgClosed.splits` + `twoTorsionPolynomial_discr_ne_zero` +
  `Cubic.discr_ne_zero_iff_roots_ne`.
- Next: convert root membership to `eval = 0` for the base-changed curve,
  apply S2353/S2354/S2358 to get the three points, then transport to
  `SideKPoint` via S1550.  No witness beyond the roots is fabricated.


## S2385: transport from roots -- exact missing

`tmp/sheaf/xif/paper/S2385TwoTorsionTransportActual.lean`
- EXIT=0; olean 2872 bytes;
  SHA256 `1F7EEF0FE9DDDB199813E3CE0B6CC5593BE53BE94301769B911CA03937B6448C`.
- Audit: S2376 three distinct roots actual; S2353/S2354/S2358 and
  `pointTransport_galois` available.
- Exact remaining:
  1. prove
     `(W.map (algebraMap R (AlgebraicClosure R))).twoTorsionPolynomial =
     Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial`
     (attempted by ext/simp; unsolved goal);
  2. turn root membership into `toPoly.eval = 0` via `Cubic.mem_roots_iff`;
  3. apply S2353/S2354/S2358 at each root on the base-changed curve;
  4. transport via `Affine.Point.baseChange`, `Projective.Point.toAffineAddEquiv`,
     `pointTransport_galois`, and prove nonzero/distinct/`IsGaloisFixed`.
- No witness constructed.


## S2389: base-change polynomial identity actual

`tmp/sheaf/xif/paper/S2389RootEvalActual.lean`
- EXIT=0; olean 46536 bytes;
  SHA256 `96995A8ECF57107D92FC4C2C1202D1657F8E9BE66F538961B301DF0FE4C94F26`.
- Actual: `(W.map (algebraMap R (AlgebraicClosure R))).twoTorsionPolynomial
  = Cubic.map (algebraMap R (AlgebraicClosure R)) W.twoTorsionPolynomial`
  by `Cubic.ext` + coefficient simp.
- An attempted `S2389EvalZero_of_mem` (root membership -> toPoly.eval=0) was
  removed because its axiom audit contained `sorryAx`; the remaining missing
  step is that conversion with a genuine nonzero-polynomial proof, then
  S2353/S2354/S2358 per root and the S1550 transport.


## S2402: eval-zero conversion still has sorryAx

`tmp/sheaf/xif/paper/S2402RootEvalDoneActual.lean`
- EXIT=0; olean 2336 bytes;
  SHA256 `BB6883FCA4B51D724A5D8B81411BAD98504E40996A6C6F33D139A60297F8161A`.
- The attempted genuine proof
  `x ∈ Cubic.map φ P roots -> (W.map φ).twoTorsionPolynomial.toPoly.eval x = 0`
  (via `Cubic.ne_zero_of_a_ne_zero` + `Polynomial.mem_roots`) still audited
  `sorryAx`; the theorem was removed and is **not** accepted.
- Exact remaining: a sorry-free route for that membership-to-eval conversion
  (suspect: one of the Mathlib `Cubic`/root lemmas used in the attempted
  chain carries `sorryAx`, or the defeq `Cubic.roots = toPoly.roots` step);
  then S2353/S2354/S2358 per root and S1550 transport.


## S2406: three 2-torsion points on the base-changed curve -- instance blocker

`tmp/sheaf/xif/paper/S2406TwoTorsionPointsTransportActual.lean`
- EXIT=0; olean 2608 bytes;
  SHA256 `419B360332DC0AA799832EBFCB0848A3236D1BB7483A504FBC05B276E4BB29AE`.
- No theorem: assembling the three points on
  `WK = W.map (algebraMap R (AlgebraicClosure R))` failed on instance
  synthesis (lines 28: `WK.toAffine.IsElliptic` / Point instances) and on
  the `S2358_two_nsmul` application shape ("Function expected").  The failing
  theorem was removed; no sorryAx remains.
- Exact remaining: provide the base-changed curve's
  `toAffine.IsElliptic` and `AddCommGroup WK.toAffine.Point` instances with
  the right elaboration, and call `S2358_two_nsmul` with explicit implicit
  arguments; then three points/2-torsion, then the S1550 transport.


## S2411: explicit-instance point build -- blocked

`tmp/sheaf/xif/paper/S2411PointBuildActual.lean`
- EXIT=0; olean 2592 bytes;
  SHA256 `BC31028EFF22FCE228FDD51D7EDF8392C3C1C4C9514C0BBA7F65ECF35D1E0699`.
- No theorem: the explicit-instance attempt failed at line 27 with
  `synthInstanceFailed` for the base-changed curve/Point type, and
  `algebraMap_injective` is not the available name for h2'.
- Exact missing: correct instances for
  `(W.map (algebraMap R (AlgebraicClosure R))).toAffine.IsElliptic` and
  `AddCommGroup ...toAffine.Point`, and the right `h2'` injectivity lemma;
  then S2358_two_nsmul with explicit @ arguments.


## S2412: three 2-torsion points on the base-changed curve (actual)

`tmp/sheaf/xif/paper/S2412ThreePointsTransportActual.lean`
- EXIT=0; olean 123152 bytes;
  SHA256 `36EE149777C6043F999BD6E2A23DD30AB77605F880DDD468B1AF8D157B069A79`.
- Axioms of `S2412ThreePoints`: `[propext, Classical.choice, Quot.sound]`.
- Proved: for `(2:R)≠0`, there exist three points
  `P1 P2 P3 : (W.map (algebraMap R (AlgebraicClosure R))).toAffine.Point`
  with `(2:Nat) • Pi = 0` for all three.
- Uses the lead's actual `S2411_two_torsion_point` per S2376 root.
- Remaining: prove `P1,P2,P3` pairwise distinct and nonzero, then transport
  to `SideKPoint T b` via `Affine.Point.baseChange`,
  `Projective.Point.toAffineAddEquiv`, `pointTransport_galois` (S1550).


## S2415: SideKPoint transport interface (not proved)

`tmp/sheaf/xif/paper/S2415SideKPointActual.lean`
- EXIT=0; olean 2488 bytes;
  SHA256 `A7F5A1464B364117CF893FBC79B30EC8D52B865C7071D35B81E7DB5CCCEFBE7E`.
- Audit only: S2412/S2414 actual; `pointTransport : SideFPoint T b ≃+ SideKPoint T b`,
  `pointTransport_galois`; `WFproj`/`WKproj` definitions recorded.
- Exact first missing for S2296ThreeRationalTwoTorsion: identify the
  S2412 curve `W.map (algebraMap R (AlgebraicClosure R))` with the S1550
  F-side curve (F -> Fv -> LF) via S1493 `curveEq`, apply `pointTransport`,
  then prove preservation of 2-torsion/distinctness/nonzeroness and
  `IsGaloisFixed`.  No witness constructed.
- (Lead's proposed subagent split A/B/C was not executed in this run; no
  parallel teammates were spawned.)


## BUILD INCIDENT: Mathlib artifacts missing; all compilation stopped

Lead reports missing Mathlib artifacts (LibraryRewrite.olean, Bochner/Set.olean,
UniformField.olean), likely from concurrent subagent lake builds.

- All compilation stopped immediately on instruction.
- No further xif_parallel_build / lake / lean runs performed.
- The last S2420 gate build failed (EXIT=1); its failure is under the incident
  (missing dependency artifacts), not accepted as a mathematical failure.
- S2420LCoprimeRepresentativeActual.lean: no clean olean/SHA/axioms; status
  unresolved pending build coordinator.
- S2432Layer1SplitActual.lean: still EXIT=1 (b/Bad namespace resolution and
  Nonempty-to-Type elimination); no accepted olean.
- Spawned subagents (S1493 transport ids 1822374f-..., 4f2ea922-...; l-torsion
  c647dc92-...) cannot be messaged (not active teammates); they may still run
  builds and must be stopped by the coordinator if possible.

Accepted files unchanged:
- S2412 SHA 36EE149777C6043F999BD6E2A23DD30AB77605F880DDD468B1AF8D157B069A79,
  olean 123152, axioms trio.
- S2414 (lead) point_ne/point_ne_zero.
- S2415 SHA A7F5A1464B364117CF893FBC79B30EC8D52B865C7071D35B81E7DB5CCCEFBE7E.

No new compilation or verification was attempted after the stop instruction.

## S2454: layer (1) split package ACTUAL

tmp/sheaf/xif/paper/S2454Layer1Skeleton.lean
- EXIT=0 (serial lake env lean -o ...); olean 10088 bytes;
  SHA256 FF3C6C16730B6FE903C93701D1065888B5DA8F0F0F9FDDC48F3E6365E0A510CD.
- Axioms of S2454Layer1Split_of_paperConditions: [propext, Classical.choice, Quot.sound].
- Actual: noncomputable def S2454Layer1Split_of_paperConditions
  (h : S2232PaperArithmeticConditions T b) : S2040QVPlaceSplitPackage T b,
  via Classical.choice (s2232_package_of_paperArithmeticConditions T b h) and s2135_toPackage.
- Binder: T : LeanFormal.IUT.InitialThetaSource.SourceNativeInitialThetaData;
  b : LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction.Bad
  (LeanFormal.IUT.nativePlaceSelection T).

## S2420: l-torsion file still broken

Serial compile EXIT=1: many Unknown identifier b / sectionQ; warning: declaration
uses sorry (line 291). No clean olean/SHA/axioms; NOT accepted.

## S2462: q_v l-th power / S2420ModLTrivial audit (no new build)

S2420 is clean (EXIT=0, SHA A906589CC62A16DB7A20A8AAE47DF367C4729A5C55C94F6FE3C21DD346352C61,
olean 391952, axioms trio, no sorryAx).  The only remaining input is
`S2420ModLTrivial T b` / `S2190QLthPowerSource T b` (q_v in Kv^l).

Audit route (no proof yet):
- q_v is `(sectionQ T b).q`, an actual completion value; S1413 gives
  `(sectionQ T b).q = completionMapSection T b (shadowQ T b).q` and the order
  law `(sectionQ T b).order = eSource T b * (shadowQ T b).order`.
- If `l.value` divides `(sectionQ T b).order`, then q_v cannot be an l-th
  power in Kv (the valuation/order of an l-th power is divisible by l).  This
  is a concrete refutation criterion, not an interface.
- If `l` does not divide the order, an l-th root still requires a Kummer/Tate
  uniformization statement (S2223) identifying the Tate parameter; this is
  not present as an actual theorem in the tree.

Exact missing (choose one):
1. a proof that `l.value` does not divide `(sectionQ T b).order` plus the
   Tate-uniformization/Kummer theorem giving q_v in Kv^l; or
2. a concrete (T,b) with `l.value ∣ (sectionQ T b).order`, refuting
   `S2190QLthPowerSource T b` for that datum.

No interface was accepted as actual; no fake.

## S2466: l-th power refutation criterion ACTUAL

tmp/sheaf/xif/paper/S2466LthPowerDecideActual.lean
- EXIT=0 (serial lake env lean -o); olean 9744; SHA256
  11FBC5F0D7FDD536624BE99CE2D0D7322D05820556DA64EAE177A96EACB85757.
- Axioms trio, no sorryAx.
- S2466_lthPower_forces_l_dvd_ramification:
  S2190QLthPowerSource T b -> S2129LDivRamification T b.
- S2466_not_lthPower_of_not_l_dvd_ramification:
  (not S2129LDivRamification T b) -> not S2190QLthPowerSource T b.

Exact remaining arithmetic: a concrete (T,b) with l not dividing eSource (then
refutation), or with l dividing eSource plus the Tate/Kummer l-th root.  The
source data does not fix eSource, so no unconditional refutation/root.

## S2420 accepted clean
EXIT=0; SHA A906589CC62A16DB7A20A8AAE47DF367C4729A5C55C94F6FE3C21DD346352C61;
olean 391952; axioms trio; sorryAx 0.
