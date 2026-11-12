# S2453: D6 composite Mono / map iso exact proof plan

Date: 2026-11-03. Layer O (D6(c) finite-etale input). **BUILD HOLD**:
this file is planning only; no lake/lean command was run.

## Inputs / kernel-checked state before hold

- `tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean` (last EXIT=0):
  - `S2429CastComp_general`
  - `S2429CastComp_holds : S2429CastComp`
  - `S2429MonoCastComp`
  - `S2429CompositeMap`
  - `S2429CompositeMap_mono`
  - `S2424CompositeOfMapIso`, `S2424CompositionRequired_of_mapIso`
- `tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.lean` (last EXIT=0):
  - `S2431CastHomMidIso`
  - `S2431StrongTransOfHomCompIso`
  - `S2431CompositeMapIsoRequired_holds`
  - `S2431S2424CompositionRequired`
- `tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.lean` (EXIT=0):
  non-identity coherent cover with `S2403RepresentableCoverMap`.

No new build is run in this plan.

## 1. Mono of the composite scheme map

### Target

```text
S2429CompositeMap H := H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)
Mono (S2429CompositeMap H)
```

### General type lemma (already actual)

```text
theorem S2429MonoCastComp
    {S1 S2 S2' S3 : SchemeOverField S1726K}
    (a : S1 ⟶ S2) (b : S2' ⟶ S3)
    [Mono a] [Mono b] (h : S2 = S2') :
    Mono (a ≫ (h ▸ b)) := by
  cases h
  exact inferInstance
```

Proof points:

1. Generalize the **scheme types** `S2` and `S2'` as variables; `h` is then
   a standalone equality, so dependent elimination is structural.
2. `cases h` makes `S2'` definitionally `S2` and `h ▸ b` definitionally
   `b`.
3. Use Mathlib's `Mono.comp` / `inferInstance` for `a ≫ b`.

### Instantiation (already actual)

```text
theorem S2429CompositeMap_mono (H) : Mono (S2429CompositeMap H) := by
  haveI : Mono H.R1.g0 := H.R1.mono
  haveI : Mono H.R2.g0 := H.R2.mono
  exact S2429MonoCastComp H.R1.g0 H.R2.g0 H.middle_eq
```

No missing input. Mono is closed.

## 2. Composite map iso

### Target

```text
S2429CompositeMapIsoRequired H
  = Nonempty (Iso
      (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq
        (S1641CoverMapComp g1 g2).map)
      (S1742StrongTransOfHom (S2429CompositeMap H)))
```

### Step 2a: transport the second map_iso along the middle equality

```text
S2431CastHomMidIso
  (h2 : B.fiber = S1742YS X2)
  (h2' : B.fiber = S1742YS X2')
  (m : X2 = X2')
  (h3 : C.fiber = S1742YS X3)
  (g : B.Hom C) (g0 : X2' ⟶ X3)
  (e : Iso (S2403CastHom h2' h3 g)
            (S1742StrongTransOfHom g0)) :
  Iso (S2403CastHom h2 h3 g)
      (S1742StrongTransOfHom (m ▸ g0))
```

Proof plan (already actual):

1. `cases m`; then `h2` and `h2'` are equalities of the same fiber type
   to the same representable type.
2. Since equality proofs of a proposition are subsingleton,
   `Subsingleton.elim h2 h2'`.
3. Rewrite the cast via `congrArg (fun e => S2403CastHom e h3 g)`, convert
   the resulting equality to `eqToIso`.
4. Compose with the given `e`.

This is the exact transport needed because `R2.map_iso` is stated for
`R2.sourceScheme`, while the composite uses `R1.targetScheme` (equal through
`H.middle_eq`).

### Step 2b: representable composition equation in iso form

```text
S2431StrongTransOfHomCompIso (a : X1 ⟶ X2) (b : X2 ⟶ X3) :
  Iso (vcomp (S1742StrongTransOfHom a) (S1742StrongTransOfHom b))
      (S1742StrongTransOfHom (a ≫ b))
```

Proof plan (already actual):

1. Apply `S1742StrongTransIsoOfHom` to
   `vcomp (S1742StrongTransOfHom a) (S1742StrongTransOfHom b)`.
2. Rewrite its underlying hom by `S2398HomOfStrongTrans_vcomp a b`:
   `S1742HomOfStrongTrans (vcomp ...) = a ≫ b`.
3. Take `.symm` to get the desired direction.

### Step 2c: assemble the composite iso

For H : `S2424ComposableRepresentable g1 g2`, with `e1 := H.R1.map_iso`,
`e2 := H.R2.map_iso`, define:

```text
Y1 := S1742YS H.R1.sourceScheme
Y2 := S1742YS H.R1.targetScheme
Y3 := S1742YS H.R2.targetScheme
A1 := S2403CastHom H.R1.source_fiber_eq H.R1.target_fiber_eq g1.map
A2' := S2403CastHom H.R1.target_fiber_eq H.R2.target_fiber_eq g2.map
B1 := S1742StrongTransOfHom H.R1.g0
B2 := S1742StrongTransOfHom (H.middle_eq ▸ H.R2.g0)
```

Then compose:

1. **cast-composition**:
   ```text
   hcast : S2403CastHom h1 h3 (vcomp g1.map g2.map) = vcomp A1 A2'
   ```
   from `S2429CastComp_holds`.
   `step1 := eqToIso hcast`.
2. **first map_iso, whiskered right**:
   ```text
   step2 : Iso (vcomp A1 A2') (vcomp B1 A2')
   := whiskerRightIso e1 A2'
   ```
3. **second map_iso transported + whiskered left**:
   ```text
   e2' : Iso A2' B2
     := S2431CastHomMidIso ... e2
   step3 : Iso (vcomp B1 A2') (vcomp B1 B2)
     := whiskerLeftIso B1 e2'
   ```
4. **representable composition equation**:
   ```text
   step4 : Iso (vcomp B1 B2) (S1742StrongTransOfHom (S2429CompositeMap H))
     := S2431StrongTransOfHomCompIso H.R1.g0 (H.middle_eq ▸ H.R2.g0)
   ```
5. `exact ((step1.trans step2).trans step3).trans step4`.

This is the actual construction of `S2431CompositeMapIsoRequired_holds`.

### Step 2d: S2424 integration

```text
S2424CompositeOfMapIso H (S2431CompositeMapIsoRequired_holds H)
  : S2424CompositeRepresentable H

S2424CompositionRequired_of_mapIso H (S2431CompositeMapIsoRequired_holds H)
  : S2424CompositionRequired H
```

The last theorem `S2431S2424CompositionRequired` is already in S2431 (last
EXIT=0 before the build hold). Thus `S2424CompositionRequired` is actual for
composable representable cover maps.

## 3. Remaining non-composite gaps

These are NOT closed by S2424 composition:

```text
S2086StackCancellation
S2089StackPresentationStatement
```

S2424 composition handles pairs of representable maps. It does not construct
an arbitrary f-presentation from g/f;g presentations. The exact boundary remains:

```text
S2089StackPresentationStatement
  = forall f g,
      EtaleStackFiniteEtaleMorphism (f ; g) ->
      EtaleStackFiniteEtaleMorphism g ->
      forall T ptY, EtaleStackBaseChangePresentation f T ptY
```

plus the finite-etale property field. The corrected geometric apex S2367 gives
strong per-cover presentations; arbitrary weak covers still require stack
cancellation or a corrected-apex supply.

## 4. Verification plan after build coordinator clears the hold

Do NOT run now. When cleared, run exactly:

```text
cd D:/lean
lake env lean -j1 -R 'D:/lean' -o '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.olean' 'tmp/sheaf/xif/paper/S2429CompositeAssemblyActual.lean'
lake env lean -j1 -R 'D:/lean' -o '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.olean' 'tmp/sheaf/xif/paper/S2431CompositeMapIsoActual.lean'
lake env lean -j1 -R 'D:/lean' -o '.lake/build/lib/lean/tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.olean' 'tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.lean'
```

Then axiom probes:

```text
#print axioms S2429CastComp_general
#print axioms S2429CastComp_holds
#print axioms S2429CompositeMap_mono
#print axioms S2431CompositeMapIsoRequired_holds
#print axioms S2431S2424CompositionRequired
```

Expected axioms: `propext, Classical.choice, Quot.sound`.

## 5. Honest status

- Mono: actual, no missing.
- Composite map: actual.
- Composite map iso: actual (S2431), last EXIT=0 before hold; independent
  axiom probe pending after hold.
- S2424CompositionRequired: actual for representable composable pairs.
- S2086StackCancellation / S2089PresentationStatement: still exact missing.
- No false S2130/S2185/S2269 and no conditional/fake substitution used.
