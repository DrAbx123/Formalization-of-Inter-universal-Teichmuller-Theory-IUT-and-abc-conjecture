# SHEAF L1-F1 — STAGE 1 record: finite-étale / finite-continuous-G_K-set equivalence

- Node: L1-F1 (equivalence)
- Owner of this delivery: read-only stage-1 record; queue lists iplsheapt for the file. No production edit.
- Date: 2026-10-22 (Asia/Shanghai)
- Target production file: `LeanFormal/IUT/IUTII/Frobenioid/Example36GSetEtaleEquivalenceAssembly.lean`
- Consumers read: `Example36CurveGaloisCategory.lean`, `Example36GaloisCorrespondence.lean`
- Toolchain: Lean 4.32.2; Mathlib v4.32.2 (manifest rev 905b95818eb32af7874a58b427f50c1711a5e96c)
- Stage: 1 only. No production edit, no new Lean file, no Project build. Positive compile evidence
  below is either (a) a fresh build of the target file to a temp olean, or (b) a
  `#check` / `#print axioms` probe fed to `lake env lean --stdin`. Probes are not production
  artifacts and are not part of the project build.

## 0. Bottom line

The unit and the counit of the intended field Galois equivalence are **already constructed and
proved** in the current source, not parameters:

- unit `UnitNaturality.unitNatIso` (Assembly:2016),
- counit `continuousGaloisSetCounitNat` (Assembly:1711),
- assembled equivalence `finiteEtaleContinuousEquivalenceFinal` (Assembly:2038), target
  `(CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K`,
- frozen cards inhabited: `fieldGaloisCorrespondenceFinal` (2046),
  `galoisNaturalityCardFinal` (2051), `gSetToEtaleNaturalityCardFinal` (2067).

The **only unit/counit parameter that remains unproved is the strict triangle**. The Final path
does not supply it; it calls Mathlib `Equivalence.mk`, which replaces the supplied unit by
`adjointifyη unitNatIso continuousGaloisSetCounitNat`. Verified by `rfl` probes: functor,
inverse and counit of the Final equivalence are the named ones; its `unitIso` is *not*
`unitNatIso`.

The **stated consumer relation is not realized**. `Example36GaloisCorrespondence.lean` only
declares the cards; `Example36CurveGaloisCategory.lean` contains no reference to any L1-F1
declaration (its frozen remaining field is the G2 quotient field, i.e. L1-F2). No file imports
the Assembly except the thin wrapper, and the wrapper is red. The Assembly is not in
`Project.lean`'s import closure, so `lake build LeanFormal.IUT.Project` does not check it.

## 1. Exact objects

Universe `u`; `(K : Type u) [Field K]`.

| object | declaration | Assembly line | exact type (abridged) |
|---|---|---|---|
| F | `finiteEtaleToContinuousFunctor K` | 260 | `(CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ⥤ FiniteContinuousGaloisSetCategory K` |
| G | `continuousGaloisSetToFiniteEtaleFunctor K` | 866 | `FiniteContinuousGaloisSetCategory K ⥤ (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ` |
| η | `UnitNaturality.unitNatIso K` | 2016 | `𝟭 ((CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) ≅ F ⋙ G` |
| ε | `continuousGaloisSetCounitNat (K := K)` | 1711 | `G ⋙ F ≅ 𝟭 (FiniteContinuousGaloisSetCategory K)` |
| E | `finiteEtaleContinuousEquivalenceFinal` | 2038 | `(CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K` |
| FGC | `fieldGaloisCorrespondenceFinal` | 2046 | `FieldGaloisCorrespondence K` |
| GNC | `galoisNaturalityCardFinal` | 2051 | `GaloisNaturalityCard K` |
| GSENC | `gSetToEtaleNaturalityCardFinal` | 2067 | `GSetToEtaleNaturalityCard K` |

Forward construction:

- object map `finiteEtaleToContinuousGSet` (218), morphism map `finiteEtaleFiberActionHom` (223),
  functor `finiteEtaleToActionFunctor` (245), lifted to the continuous full subcategory as
  `finiteEtaleToContinuousFunctor` (260) by `ObjectProperty.lift`.
- continuity of the forward fiber action: `finiteEtaleObjectToGSet_isContinuous` (212), from
  `finiteEtaleFiberStabilizer_isOpen` (188), from the stabilizer/fixing-subgroup identity
  `mem_stabilizer_iff_fixingSubgroup` (125), from `finiteEtaleFiberAdjoinField_finiteDimensional`
  (106) and `IntermediateField.fixingSubgroup_isOpen`.
- reverse object map `gSetToFiniteEtaleObjectMap` (431), with functor laws
  `gSetToFiniteEtaleObjectMap_id` (483) and `gSetToFiniteEtaleObjectMap_comp` (837); the functor
  is `continuousGaloisSetToFiniteEtaleFunctor` (866).
- unit component `gfToIdComponent` (1967) = `(CommAlgCat.FiniteEtale.isoMk (fiberEvalAlgEquiv K A)).op`,
  with `fiberEvalAlgEquiv` (1956) built from `fiberEvalPi_bijective` (1946) and the
  evaluation map `fiberEvalPi` (1780); naturality `gfToIdComponent_naturality` (1999) /
  `fiberEvalAlgHom_naturality` (1973); `gfToIdNatIso` (2010);
  `unitNatIso := (gfToIdNatIso K).symm` (2016).
- counit component `fiberActionIsoFull` (886) = `ObjectProperty.isoMk _ (fiberActionIso ...)`;
  naturality `fiberActionIsoFull_natural` (1679); `continuousGaloisSetCounitNat` (1711)
  via `counitOfComponents` (922).

No `sorry`, `admit` or `axiom` occurs in the file (the only match for sorry|admit|axiom is
the comment "Proved (axioms propext, ...)" at line 1836).

## 2. Exact unit/counit parameter residual

### 2.1 Parameterized assemblers (exist, unused)

- `finiteEtaleContinuousEquivalence` (905–919). Parameters:
  - `unitIso : 𝟭 ((CommAlgCat.FiniteEtale.{u} K)ᵒᵖ) ≅ F ⋙ G`
  - `counitIso : G ⋙ F ≅ 𝟭 (FiniteContinuousGaloisSetCategory K)`
  - `triangle : ∀ X, F.map (unitIso.hom.app X) ≫ counitIso.hom.app (F.obj X) = 𝟙 (F.obj X)`
  The structure literal sets `unitIso := unitIso`, `counitIso := counitIso`,
  `functor_unitIso_comp := triangle`.
- `finiteEtaleContinuousEquivalenceOfComponents` (952–971). Parameters:
  `unitComponent`, `unitNat`, `counitNat`, and the `triangle` built from
  `unitOfComponents`/`counitOfComponents`. It has no caller.
- `unitOfComponents` (932) takes `component` and `naturality`; its only caller is the
  unused `OfComponents` assembler. `counitOfComponents` (922) takes `naturality` and is
  used by `continuousGaloisSetCounitNat` with the proved `fiberActionIsoFull_natural`.

So the generic assemblers remain as alternative interfaces with unit/counit **parameters**, but the
Final path does not use them.

### 2.2 What the Final path supplies and what it does not

`finiteEtaleContinuousEquivalenceFinal` is

    CategoryTheory.Equivalence.mk F G (UnitNaturality.unitNatIso K) (continuousGaloisSetCounitNat)

Mathlib `Equivalence.mk` (Mathlib `CategoryTheory/Equivalence.lean:356`) is
`⟨F, G, adjointifyη η ε, ε, adjointify_η_ε η ε⟩`. Hence:

- counit: supplied = the named `continuousGaloisSetCounitNat` (rfl-checked);
- unit: supplied `unitNatIso` is replaced by `adjointifyη unitNatIso continuousGaloisSetCounitNat`
  (`Equivalence.lean:330–338`), which is `unitNatIso` followed by unitors/associators,
  `ε.symm` and `η.symm` whiskerings. It is **not** the named unit;
- triangle: not proved explicitly; `adjointify_η_ε` (Equivalence.lean:341) proves the triangle for
  the *adjusted* unit.

rfl probe (2026-10-22, exit 0 for the first three, exit 1 for the fourth):

    (finiteEtaleContinuousEquivalenceFinal K).functor   = finiteEtaleToContinuousFunctor K        -- rfl
    (finiteEtaleContinuousEquivalenceFinal K).inverse   = continuousGaloisSetToFiniteEtaleFunctor K -- rfl
    (finiteEtaleContinuousEquivalenceFinal K).counitIso = continuousGaloisSetCounitNat K           -- rfl
    (finiteEtaleContinuousEquivalenceFinal K).unitIso   = UnitNaturality.unitNatIso K              -- FAILS

### 2.3 The residual, exactly

The only unproved unit/counit coherence in the whole file is the strict triangle:

    theorem finiteEtale_unit_counit_triangle (K : Type u) [Field K] :
        ∀ X : (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ,
          (finiteEtaleToContinuousFunctor K).map ((UnitNaturality.unitNatIso K).hom.app X) ≫
            (continuousGaloisSetCounitNat (K := K)).hom.app
              ((finiteEtaleToContinuousFunctor K).obj X) =
          𝟙 ((finiteEtaleToContinuousFunctor K).obj X)

Status: **statement_compiles = true**, proof_body_checked = false. Elaborated 2026-10-22 as a
`lake env lean --stdin` probe: exit 0 with exactly one "declaration uses sorry" warning.
If proved, `finiteEtaleContinuousEquivalence K (UnitNaturality.unitNatIso K) (continuousGaloisSetCounitNat)`
applied to the triangle is an equivalence whose `unitIso` field is literally `unitNatIso` —
the strongest unit/counit form, and the exact discharge of the triangle parameter.

Proof route (stage 3 sketch; not executed): reduce with `ObjectProperty.hom_ext` /
`Action.Hom.ext` / `FintypeCat.hom_ext`; unfold
`continuousGaloisSetCounitNat = counitOfComponents (fiberActionIsoFull_natural)`,
`fiberActionIsoFull = ObjectProperty.isoMk _ (fiberActionIso ...)`; use
`fiberActionIso_hom_apply` (1670) and the point formula
`fiberActionEquiv (x.comp (fiberEvalAlgEquiv.toAlgHom)) = x`. The latter should follow from
the donor definitions `fiberActionEquiv` (GSetToEtaleAlgebra:1223),
`fiberProductSigmaEquiv_eq_arrowCongr_trans` (donor:1190) and the `orbitDecomposition`
roundtrips. Known obstruction class: the two descriptions `orbitFixedField q` and
`openSubgroupFixedField (orbitStabilizer q)` match only at default transparency; the same
obstruction was crossed once by `fiberEvalAlgHom_naturality` (1973) and is documented in the
stale block at 1850–1862.

## 3. Actual equivalence target

Exactly:

    (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ EtaleCoverFoundations.FiniteContinuousGaloisSetCategory K

where (Example36EtaleCoverFoundations.lean:304–315)

    def IsContinuousFiniteGaloisSet (X : FiniteGaloisSetCategory K) : Prop :=
      ∀ x : ↥X.V, IsOpen (MulAction.stabilizer (Iut.AbsoluteGaloisProfinite K) x : Set _)
    abbrev FiniteContinuousGaloisSetCategory (K : Type u) [Field K] : Type (u + 1) :=
      ObjectProperty.FullSubcategory (fun X : FiniteGaloisSetCategory K => IsContinuousFiniteGaloisSet X)

with `FiniteGaloisSetCategory K := Action FintypeCat.{u} ↥(Iut.AbsoluteGaloisProfinite K)`.

It is **not**:

- `FiniteGaloisSetCategory K` / `Action FintypeCat G` (all finite actions; equating it with
  the continuous category is false — see the warning in `Example36ContinuousGaloisSets.lean:51–60`);
- `finiteContinuousGaloisSets G = ContAction FintypeCat G` (Mathlib's continuous-action model);
  reachable from the Final equivalence by composing with
  `continuousActionEquivalenceOpenStabilizers G` (ContinuousGaloisSets:177), but not the stated target;
- `FiniteEtaleCover (Spec K)` / `FiniteEtaleCover (specBase K)` — that is the separate
  F1e comparison `specCoverEquivalence` (SpecCoverEquivalenceFinal:90);
- `FiniteEtaleCover (curveScheme K)` — L1-F2/F3d.

`fieldGaloisCorrespondenceFinal` inhabits the frozen card `FieldGaloisCorrespondence K`
(EtaleCoverFoundations:330), whose second field `specEssentialSurjectivity` is filled from
`SpecEssentialSurjectivity.fieldGaloisCorrespondence_specEssentialSurjectivity`
(Example36SpecEssentialSurjectivity:181). So the card is fully inhabited, but its equivalence field is
the continuous-category equivalence above.

## 4. Consumers: what actually consumes L1-F1

### 4.1 `Example36GaloisCorrespondence.lean` (SHA 33847871…FB96, 185 lines)

Only freezes structures; it proves no equivalence and consumes none:

- `FiniteEtaleFiberContinuityCard` (119), `FiniteGSetToFiniteEtaleObjectCard` (132),
  `GaloisObjectCorrespondenceCard` (146), `GaloisNaturalityCard` (171).
- `GaloisNaturalityCard` is exactly the statement-level interface of L1-F1:
  `equivalence : (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ FiniteContinuousGaloisSetCategory K` and
  `fiber_compatibility : ∀ A, Nonempty ((equivalence.functor.obj A).obj ≅ finiteEtaleObjectToGSet K A.unop)`.
  It is inhabited by `galoisNaturalityCardFinal` (Assembly:2051); the `fiber_compatibility` component
  is `⟨Iso.refl _⟩` because `(F.obj A).obj = finiteEtaleObjectToGSet K A.unop` definitionally
  (Assembly:943–944) and `E.functor = F` definitionally.
- No theorem in the tree consumes `GaloisNaturalityCard` except the packaging defs
  `galoisNaturalityCardOfEquivalence` (GSetToEtaleAlgebra:1282) and
  `gSetToEtaleNaturalityCardOfFieldCorrespondence` (1290), which take the data as parameters.

### 4.2 `Example36CurveGaloisCategory.lean` (SHA A511236C…70AE, 783 lines)

Contains **zero** references to `FieldGaloisCorrespondence`, `GaloisNaturalityCard`,
`GSetToEtaleNaturalityCard`, `finiteEtaleContinuousEquivalence` or any L1-F1 declaration
(grep over the file). Its imports are `CurveScheme`, `CurveConnectedness`, `CurveEtaleCovers`
and Mathlib only. Its frozen remaining field is

    structure CurvePreGaloisCategoryRemainingFields (S : Scheme.{u}) where
      hasQuotientsByFiniteGroups :
        ∀ (G : Type u) [Group G] [Finite G],
          Limits.HasColimitsOfShape (SingleObj G) (FiniteEtaleCover S)     -- line 330

i.e. the L1-F2 G2 field. Therefore the LAYER1-PLAN consumer edge
"L1-F1 → Example36CurveGaloisCategory" is **not realized**: deleting L1-F1 would change no
declaration in that file.

### 4.3 The only theorem-level API that can consume it

`Example36FiberAutomorphism.fiberAutMulEquivOfFiberCorrespondence` (line 285) takes

    (E : (CommAlgCat.FiniteEtale K)ᵒᵖ ≌ finiteContinuousGaloisSets (Iut.AbsoluteGaloisProfinite K))
    (hF : fieldFiber K ≅ E.functor ⋙ finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K))
    : Aut (fieldFiber K) ≃* ↥(Iut.AbsoluteGaloisProfinite K)

The Assembly does not import this file and this file does not import the Assembly, but a stdin probe
(2026-10-22, exit 0) showed the two data are available from L1-F1 by composition (see §8, L1-F1.a).
The remaining F1g gap after that application is the G_K-equivariance `hcompat` of the fiber
identification (FiberAutomorphism:299–307 and the note at 414–419), not L1-F1.

### 4.4 Grep over the whole `LeanFormal` tree

- `finiteEtaleContinuousEquivalenceFinal`, `fieldGaloisCorrespondenceFinal`,
  `galoisNaturalityCardFinal`, `gSetToEtaleNaturalityCardFinal`: occurrences exist **only**
  inside `Example36GSetEtaleEquivalenceAssembly.lean`.
- `FieldGaloisCorrespondence`: only its definition, the two generic lemmas in
  EtaleCoverFoundations, the packaging defs in GSetToEtaleAlgebra, comments in
  FiberAutomorphism/GaloisCorrespondence, and the two Assembly/wrapper definitions.
- `Example36GSetEtaleEquivalenceAssembly`: imported only by
  `Example36GSetEtaleEquivalence.lean:1` (the broken wrapper).

### 4.5 Project closure

`Project.lean` imports 103 `Example36*` modules, including GaloisCorrespondence (513),
SpecEssentialSurjectivity (514), ContinuousGaloisSets (515), CurveGaloisCategory (523),
SpecCoverEquivalenceFinal (535), FiberAutomorphism (536) — but **not** the Assembly and **not** the
wrapper. L1-F1 is therefore outside the production build closure; a Project build neither checks nor
breaks on it. Importing it into Project would be a production decision, and Project import alone is
not progress.

## 5. Donors used (actual, with status)

| donor | SHA256 | olean (last build) | role |
|---|---|---|---|
| Example36EtaleCoverFoundations.lean | 89C3CD36…B9A86C | 2026-10-19 06:21:06 | FiniteContinuousGaloisSetCategory 313, FieldGaloisCorrespondence 330, finiteGaloisSetFiber 285 |
| Example36GaloisCorrespondence.lean | 33847871…E64FB96 | 2026-10-19 06:22:23 | forward fiber object map 64/78, finiteEtale_decomposition 93, cards 119/132/146/171 |
| Example36GSetToEtaleAlgebra.lean | 9439FEB1…771465E | 2026-10-20 00:20:52 | reverse object map, fiberActionEquiv 1223, fiberActionIso 1250, fieldGaloisCorrespondenceOfEquivalence 1300, card packaging 1282/1290 |
| Example36SpecEssentialSurjectivity.lean | C2EC85AC…C3B21 | 2026-10-19 06:22:24 | specBase 51, fieldGaloisCorrespondence_specEssentialSurjectivity 181 |
| Example36ContinuousGaloisSets.lean | 588ADB27…2CD5FC | 2026-10-19 06:22:23 | finiteContinuousGaloisSets 108, openStabilizerActions 153, continuousActionEquivalenceOpenStabilizers 177, fiber/Galois/π1 189–212 |
| Example36FiniteEtaleFiber.lean | BF30594D…9C8EAA | 2026-10-19 04:32:34 | finiteEtaleFiber 30 |
| Example36FiberAutomorphism.lean | 85EA841E…C358492 | 2026-10-20 00:21:26 | fieldFiber 73, fiberAutMulEquivOfFiberCorrespondence 285 |
| Mathlib CategoryTheory/Equivalence.lean | — | Mathlib v4.32.2 | adjointifyη 330, Equivalence.mk 356, adjointify_η_ε 341 |

No donor was modified in this package.

## 6. File SHA / status

| file | SHA256 | bytes | source mtime | status |
|---|---|---|---|---|
| Example36GSetEtaleEquivalenceAssembly.lean | 5D2CB960AF7DF5557595847F9588D6AE6276260BBF5DD276B1E261B1791FAFFF | 102900 | 2026-10-20 06:51:46 | **fresh build exit 0** 2026-10-22 (temp olean 2,495,240 B, ≈48 s); no sorry/admit/axiom; untracked (??) |
| Example36GSetEtaleEquivalence.lean | 77F83E1B0EB6A72EF9096187C942E9B7B43A3A249EECDABA20884167E8955819 | 1127 | 2026-10-20 06:48:23 | **red**: lake env lean exit 1 — object file ... Example36UnitNaturality.olean ... does not exist; untracked |
| Example36GaloisCorrespondence.lean | 33847871BFB5D36B2708EE45170E6CF37DCEBCF674A36795B3932473EE64FB96 | 9367 | 2026-10-19 06:20:05 | olean exists (2026-10-19 06:22:23); not rebuilt here |
| Example36CurveGaloisCategory.lean | A511236C3BDDC76BC346A7A735010607F1F1C884C9EE007DB1FA5F1D6BA270AE | 36704 | 2026-10-20 03:58:41 | olean exists (2026-10-20 04:02:27); not rebuilt here |
| Example36GSetToEtaleAlgebra.lean | 9439FEB1AB48100E6D15695F55A5424E212728625A61617838C5A70C6771465E | 58496 | 2026-10-20 00:19:37 | olean exists (2026-10-20 00:20:52) |
| Example36EtaleCoverFoundations.lean | 89C3CD3684839ADD1E1BB991BEF5BF728469B15DE04020679510384688B9A86C | 19575 | 2026-10-19 06:19:13 | olean exists (2026-10-19 06:21:06) |
| Example36FiberAutomorphism.lean | 85EA841E638C9DBF7FB94C95869D2F51F60F203B23F2C85B36BA5EF36C358492 | 23452 | — | olean exists (2026-10-20 00:21:26) |
| Example36SpecEssentialSurjectivity.lean | C2EC85AC4C44E528FCE7631B21FC94B01C6B7E2EFBC948217DEE73F9B04C3B21 | 11242 | 2026-10-19 04:46:31 | olean exists (2026-10-19 06:22:24) |
| Example36ContinuousGaloisSets.lean | 588ADB27C7384891774FEDF36B145BB181694A11E3CC9FC4C5C63D32312CD5FC | 11475 | 2026-10-19 04:53:07 | olean exists (2026-10-19 06:22:23) |
| Example36FiniteEtaleFiber.lean | BF30594D73DD116CBB278DD5121D1962E1214B447605C30C50C5E123FD9C8EAA | 2854 | 2026-10-19 04:31:22 | olean exists (2026-10-19 04:32:34) |
| Example36SpecCoverEquivalenceFinal.lean | B3200BB8939BF49B62F1928F1116B39C48A4A6E259CFB65CDF52BA63C13282C9 | 4174 | 2026-10-19 05:30:46 | imported by Project 535 |
| tmp/n8-20261018/gset-etale/Example36UnitNaturality.duplicate.lean | 4B8EC9B62C5553C16365C849023FD3486A9F39FF33E830B3EE5C89F234C6D4ED | 15716 | 2026-10-20 06:45:46 | 312 lines; preserved pre-merge copy of the deleted production module |

Evidence commands run in this delivery (all from `D:/lean`):

    lake env lean -o $env:TEMP/l1f1-assembly.olean LeanFormal/IUT/IUTII/Frobenioid/Example36GSetEtaleEquivalenceAssembly.lean
    --> EXIT=0, temp olean 2,495,240 bytes, 2026-10-22 07:39:38

    lake env lean -o $env:TEMP/l1f1-wrapper.olean LeanFormal/IUT/IUTII/Frobenioid/Example36GSetEtaleEquivalence.lean
    --> EXIT=1: object file '...Example36UnitNaturality.olean' ... does not exist

    $code | lake env lean --stdin      # #check / #print axioms / rfl / snippet probes
    --> exit 0 for: final types, axioms, ContAction-model composition, fiber iso,
        fiberAutMulEquivOfFiberCorrespondence application, triangle statement with sorry.

Axiom probe (#print axioms, exit 0, 2026-10-22):

    finiteEtaleContinuousEquivalenceFinal  -> [propext, Classical.choice, Quot.sound]
    fieldGaloisCorrespondenceFinal        -> [propext, Classical.choice, Quot.sound]
    UnitNaturality.unitNatIso             -> [propext, Classical.choice, Quot.sound]
    continuousGaloisSetCounitNat          -> [propext, Classical.choice, Quot.sound]

Reporting per AGENTS.md:

- statement_compiles = true (fresh build of the current source, exit 0).
- proof_body_checked = true for the Assembly's own proofs (no sorry; all declarations elaborated).
  Imports were taken from existing oleans, not rebuilt.
- kernel_closed = **not established for the whole file**; only the four named declarations have the
  transitive axiom probe above (and imports are trusted as prebuilt).
- target_accepted = false: no locked Challenge/TargetsCheck, no comparator run, no independent
  source-semantics review, no consumer acceptance.

Not run in this delivery: lake build LeanFormal.IUT.Project; recompilation of the consumer files;
independent review; comparator; a test that the Assembly's .lake olean equals the fresh oleans
(sizes differ, 2,468,480 vs 2,495,240 B; both environments expose the Final declarations).

## 7. Precise gaps

1. **Strict triangle unproved** (the only unit/counit parameter residue). The Final path bypasses it
   via Equivalence.mk/adjointifyη; consequence: the Final unitIso is not unitNatIso. No current
   consumer needs the strict form.
2. **No consumer wiring**. The Assembly is imported only by the broken wrapper; Project does not
   import it; the plan's consumer Example36CurveGaloisCategory contains no reference.
3. **Wrapper red**. Example36GSetEtaleEquivalence.lean imports the deleted module
   Example36UnitNaturality; only stale .lake artifacts (trace/hashes/setup.json, 2026-10-20 06:47:44)
   remain. Its body compiles against the Assembly (stdin probe, exit 0): the two declarations
   duplicate finiteEtaleContinuousEquivalenceFinal / fieldGaloisCorrespondenceFinal and have no
   consumer. Restoring the deleted module is **not** the fix: the preserved copy
   tmp/n8-20261018/gset-etale/Example36UnitNaturality.duplicate.lean imports the Assembly and
   re-declares UnitNaturality.unitNatIso, which would duplicate Assembly:2016.
4. **Stale in-file documentation**. Assembly:26–48 and 1833–1876 still advertise missing
   unit/counit lemmas; the items listed there are implemented at 1878–2025
   (fiberEvalPi_eq_zero 1878, fiberEvalPi_injective 1921, finrank_eval_target 1927,
   fiberEvalPi_surjective 1937, fiberEvalAlgEquiv 1956, gfToIdNatIso 2010). This is the
   documentation that keeps the queue note "unit/counit 仍须核对".
5. **Untracked status**. All Example36 files involved here are ?? (never committed); the SHAs above
   are content hashes, not git blobs.

## 8. Smallest stage-2 statement / child

### L1-F1.a — consumer-model equivalence + fiber identification (smallest next child; stage 2 -> 3 immediate)

Exact snippets, both verified to elaborate in a stdin probe (2026-10-22, exit 0):

    noncomputable def finiteEtaleContinuousGaloisSetsEquivalence (K : Type u) [Field K] :
        (CommAlgCat.FiniteEtale.{u} K)ᵒᵖ ≌ finiteContinuousGaloisSetsOfField K :=
      (finiteEtaleContinuousEquivalenceFinal (K := K)).trans
        (continuousActionEquivalenceOpenStabilizers (Iut.AbsoluteGaloisProfinite K)).symm

    noncomputable def finiteEtaleContinuousGaloisSetsFiberIso (K : Type u) [Field K] :
        fieldFiber K ≅
          (finiteEtaleContinuousGaloisSetsEquivalence K).functor ⋙
            finiteContinuousGaloisSetFiber (Iut.AbsoluteGaloisProfinite K) :=
      finiteEtaleFiberIsoContinuous (K := K)

With these two, the probe also checked (exit 0):

    noncomputable example (K : Type u) [Field K] :
        Aut (fieldFiber K) ≃* ↥(Iut.AbsoluteGaloisProfinite K) :=
      fiberAutMulEquivOfFiberCorrespondence (K := K)
        (finiteEtaleContinuousGaloisSetsEquivalence K)
        (finiteEtaleContinuousGaloisSetsFiberIso K)

This is the smallest pair of declarations that turns L1-F1 into an actual consumer reduction
(the F1g API). It is glue, not new mathematics; proposed tmp file
tmp/sheaf/l1-f1/ConsumerModel.lean (not written in this delivery) with namespace
LeanFormal.IUT.IUTII.Frobenioid.Example36.L1F1. Production wiring into
Example36FiberAutomorphism.lean (import + these two defs) is a separate edit needing the file owner.

### L1-F1.b — strict triangle (the only unproved statement; stage 2 with named sorry)

Exact statement as in §2.3; status: statement_compiles (exit 0, one sorry warning), proof not
attempted. Keep this child **only if** a consumer needs the explicit unitNatIso as the unit field,
e.g. to compare the unit formula or to prove the F1g compatibility hcompat. If no such consumer
appears, the triangle stays a recorded non-gap: the Final equivalence exists and is usable without it.

### L1-F1.c — production hygiene (no mathematics)

Repair Example36GSetEtaleEquivalence.lean: delete the stale import ...Example36UnitNaturality line
(body verified to compile against the Assembly), or delete/replace the wrapper with the Final
declarations. Owner decision; not done here. Separately decide whether the Assembly should enter
Project.lean's closure for build coverage.

## 9. Node stage assignment and one next action

- L1-F1 stage 1: **complete for the equivalence object and its unit/counit** (exact objects, target,
  donors, consumer audit above). The consumer edge claimed in LAYER1-PLAN is not realized; that is
  a separate node fact, not an L1-F1 proof gap.
- L1-F1 stage 2: **already in production** (Assembly:2038–2071); no new statement is required for
  the equivalence itself. Optional strict-unit statement = L1-F1.b.
- L1-F1 stage 3: proof bodies of the Assembly check (fresh exit 0); the four Final declarations are
  axiom-clean (propext/choice/Quot.sound); full-file kernel closure not audited; imports trusted.
- L1-F1 target acceptance: **not** claimed (no locked target, no comparator, no consumer acceptance).

One concrete next action (for the parent to choose):

1. If the goal is to convert the finished L1-F1 into a real consumer: write
   tmp/sheaf/l1-f1/ConsumerModel.lean with L1-F1.a (statement + proof, both already checked), then
   coordinate with the Example36FiberAutomorphism.lean owner for the production import.
2. If the goal is the strict unit/counit form: assign L1-F1.b (triangle) as a stage-2 named-sorry
   task in tmp, then attempt §2.3's proof route.
3. If the goal is hygiene: L1-F1.c (delete the stale wrapper import; fix the stale docstrings at
   Assembly:26–48 and 1833–1876), then re-run the wrapper build and the Assembly build.

No production file was edited; no Project build was run; no claim of target_accepted is made.
