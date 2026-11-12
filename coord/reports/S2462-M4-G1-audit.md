# S2462: M4 PsiCns Kummer normalization / G1 muHatZ action audit

Date: 2026-11-03. Layer O (S2046 M4/G1; S2039/S2017 cyclotome).
No target change, no fake.

## Files read

- `tmp/sheaf/xif/paper/S2036ActualPsiCnsM234Actual.lean`
  (`PsiCnsKummerNormalization`, `M2FirstMissing`, `M3`,
  `S2036PsiCnsM234FirstMissing`)
- `tmp/sheaf/xif/paper/S2039ActualPsiCns.lean`
  (`PsiCnsNormalization`, `NormalizationMissing`, actual Kummer map/limit)
- `tmp/sheaf/xif/paper/S2039ActualPsiCnsInterface.lean`
- `tmp/sheaf/xif/paper/S2136M4KummerNormalizationActual.lean`
  (`S2136M4NormalizationData`, `S2136M4_of_data`,
  `S2136M4CupProductNormalizationRequired`)
- `tmp/sheaf/xif/paper/S2046G1CyclotomeActual.lean`
  (`S2046G1TopologicalModuleData`, `S2046G1PsiCnsAction`,
  `S2046G1ModuleEquivOfComparison`)
- `tmp/sheaf/xif/paper/S2017VerlagerungActual.lean`
  (`muHatZ`, `muHatComparison`)
- reports `S2046-m4-conditional.md`, `S2046-g1-cyclotome.md`,
  `S2046-m3m4-s2091-port.md`, `S2039-actual-psicns.md`

## Source object / domain / direction

- M4: the [AbsTopIII] Cor 1.10(b) normalization
  `nu : H^1(G_v, mu_hat^Z) ->> Z-hat` and its Kummer-image/kernel
  properties, on the actual S2000 cohomological limit.
- G1: the topological action of `G_v` on `muHatZ p` and its equivariant
  comparison with the actual `PsiCnsCyclotome` action.
- Domain: original O-layer; no reduced/fake model.

## M4 evidence / status

### Actual

- S2039 / S2000 / S2006: actual cohomological limit
  `PsiCnsCohomology p`, actual Kummer map `PsiCnsKummer p`, injectivity,
  actual Kummer image `PsiCnsBaseImage`, and the nonnegative cone
  `zhatNatMonoid`.
- S2039 `PsiCnsNormalization`: `norm : PsiCnsCohomology p →* Multiplicative
  Zhat`, `surjective`; but no inhabitant.
- S2136 actual H2/Br ports:
  `S2136H2ZHatEquiv : H^2(Q_p, Zhat(1)) ≃* Multiplicative Zhat`;
  `S2136BrEquivQZ : Br(Q_p) ≃* Multiplicative Q/Z`.
- S2136 `S2136M4_of_data (D : S2136M4NormalizationData p) :
  PsiCnsKummerNormalization p`, actual conditional.

### Exact M4 first missing

```text
S2136M4NormalizationData p
  = norm : PsiCnsCohomology p →* Multiplicative Zhat
    surjective : Function.Surjective norm
    kummer_image :
      MonoidHom.mrange (PsiCnsKummer p) =
        Submonoid.comap norm zhatNatMonoid
    kernel_units :
      ∀ a : Otri p,
        norm (PsiCnsKummer p a) = 1 ↔
          ∃ u : (Otri p)ˣ, (u : Otri p) = a
```

Equivalent proposition (exact, no inhabitant):

```text
PsiCnsKummerNormalization p
```

`S2136M4CupProductNormalizationRequired p := S2136M4NormalizationData p`.

The missing construction is the normalization map `nu` from the H^2 class /
cup product, not a restatement. The H2/Br comparison modules are actual; the
map itself and its Kummer-image/kernel identification are not.

### Consumers

- `S2046M4ConditionalActual` (M4 local units reduction);
- `S2046PsiCnsActionActual`, `S2046PsiCnsActualComponents`;
- `S2068PsiCnsActorReduction` (`S2068M4NormalizationRequired`);
- `S2046M3M4S2091Port` / `S2091H2ZhatActual`.

## G1 evidence / status

### Actual

- `S2046G1PsiCnsAction p : Gv p →* MulAut (PsiCnsCyclotome p)`, actual.
- `S2046G1ModuleEquivOfComparison (h : muHatComparison p) :
  muHatZ p ≃* PsiCnsCyclotome p`, actual conditional.
- `S2046G1TorsionEquiv : PsiCnsCyclotome p ≃* PsiCnsTorsionCyclotome p`,
  actual.
- `S2017 muHatZ p = KummerCyclotome (Multiplicative (muQZ p))`,
  actual transfer/colimit construction.

### Exact G1 first missing

```text
S2046G1TopologicalModuleData p
  = muHatAction : Gv p →* MulAut (muHatZ p)
    equiv : muHatZ p ≃* PsiCnsCyclotome p
    equivariant :
      ∀ g x, equiv (muHatAction g x) =
        S2046G1PsiCnsAction p g (equiv x)
```

No inhabitant. Additionally, the current structure has **no topology or
continuity field**:

```text
TopologicalSpace (muHatZ p)
Continuous (fun p : Gv p × muHatZ p => muHatAction p.1 p.2)
continuous equiv / homeomorphism compatibility
```

These are not encoded in `S2046G1TopologicalModuleData`; the existing
"topological" name refers to the cyclotome module comparison, not a proven
continuous action. Exact first missing for the paper G1 statement is therefore:

1. `muHatComparison p` (S2017) for the module equivalence;
2. `muHatAction` and its equivariance with the actual PsiCns action;
3. a topology on `muHatZ p` and continuity of the action, plus continuity of
   the comparison.

`S2046G1MuHatComparisonRequired p := muHatComparison p` is itself exact
missing (S2017); no inhabitant.

### Consumers

- S2046 M3/M4 reduction (`S2046M3M4S2091Port`);
- S2091 H2=Zhat port;
- S2036 PsiCns H2 normalization.

## Evidence / hashes

```text
S2036ActualPsiCnsM234Actual.lean
  lines=472
  source SHA256=E29536ED3249C72C97EC7BC9644A9349976C2D9379BBD19FB1E99288918445DC
  olean=YES

S2039ActualPsiCns.lean
  lines=710
  source SHA256=34A38CD7F40EF6B71591F0F6A988F4E6E19B89C163248CEBAB409D19CEEBDCF2
  olean=YES

S2136M4KummerNormalizationActual.lean
  lines=76
  source SHA256=33D76985B4081548B5B8384703386CBFC4D52764B81698C40207E62080F1DE7A
  olean=YES
  S2136.out axioms: S2136H2ZHatEquiv, S2136BrEquivQZ, S2136M4_of_data
    -> propext, Classical.choice, Quot.sound

S2046G1CyclotomeActual.lean
  lines=64
  source SHA256=C664AC7D205A621B4CAE924F373F4448CAFB048F5BCA662EE569379195F2A8CA
  olean=YES
  S2046G1.out axioms: S2046G1ModuleEquivOfComparison,
    S2046G1TorsionEquiv -> trio

S2017VerlagerungActual.lean
  lines=377
  source SHA256=28D57C256A7170B1CE9B8F592ADAB09C684B2A58FEDDAE6A30ADD09B3D5F6BA8
  olean=YES
```

No new compile was run for this audit; the above are existing build artifacts.

## Honest boundary

- M4 actual H2/Br modules and conditional reduction exist; the normalization
  map/Kummer image is exact missing.
- G1 actual PsiCns action and conditional module equivalence exist; the
  `muHatAction`/equivariance and topology/continuity are exact missing.
- No fake normalization, no trivial action, no terminal/point substitution.
