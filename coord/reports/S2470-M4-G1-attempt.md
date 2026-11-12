# S2470: M4/G1 actual construction attempt — exact missing

Date: 2026-11-03. Layer O (S2046 M4/G1). No new compilation was run for this
attempt; evidence hashes are from existing oleans and S2136.out/S2046G1.out.

## M4: S2136M4NormalizationData

### Goal

```text
norm : PsiCnsCohomology p →* Multiplicative Zhat
surjective : Function.Surjective norm
kummer_image :
  MonoidHom.mrange (PsiCnsKummer p) = Submonoid.comap norm zhatNatMonoid
kernel_units :
  ∀ a : Otri p, norm (PsiCnsKummer p a) = 1 ↔
    ∃ u : (Otri p)ˣ, (u : Otri p) = a
```

### What is available

- S2000/S2006/S2039: actual `PsiCnsCohomology p`, actual Kummer map
  `PsiCnsKummer p` and injectivity, actual Kummer image and nonnegative cone.
- S2136: actual H2/Br equivalences
  `H^2(Q_p, Zhat(1)) ≃* Multiplicative Zhat`,
  `Br(Q_p) ≃* Multiplicative Q/Z`;
  actual conditional `S2136M4_of_data`.

### Why the norm cannot be assembled

The H2/Br equivalences are **module comparisons**, not a map
`H^1(G_v, mu_hat^Z) → Zhat`. The paper's `nu` is produced by the
H^2 class/cup-product construction (AbsTopIII Cor 1.10(b)); the tree has:

- no cup-product pairing into the normalization;
- no comparison from the H^1 limit to the H^2 class;
- no map `PsiCnsCohomology p →* Multiplicative Zhat`.

Therefore the first missing is literally the `norm` field and its three
properties, not a consequence of the H2/Br equivalences.

### Exact first missing

```text
S2136M4NormalizationData p
```

which is equivalent to `PsiCnsKummerNormalization p`.
No inhabitant exists in the tree.

### Required API

1. the H^2 class / cup-product normalization map;
2. proof that its inverse image of `zhatNatMonoid` is exactly
   `mrange (PsiCnsKummer p)`;
3. proof that its kernel on the Kummer image is the unit subgroup;
4. surjectivity.

No fake normalization/trivial map is used.

## G1: S2046G1TopologicalModuleData

### Goal

```text
S2046G1TopologicalModuleData p
  muHatAction : Gv p →* MulAut (muHatZ p)
  equiv : muHatZ p ≃* PsiCnsCyclotome p
  equivariant :
    ∀ g x, equiv (muHatAction g x) = S2046G1PsiCnsAction p g (equiv x)
```

plus topology/continuity:

```text
TopologicalSpace (muHatZ p)
Continuous (fun q : Gv p × muHatZ p => muHatAction q.1 q.2)
continuous comparison/homeomorphism after adding topology to PsiCnsCyclotome
```

### What is available

- `S2046G1PsiCnsAction p : Gv p →* MulAut (PsiCnsCyclotome p)`, actual.
- `S2046G1TorsionEquiv`, actual.
- `S2046G1ModuleEquivOfComparison (h : muHatComparison p)`, actual
  conditional.

### Why the action cannot be assembled

- `muHatZ p = KummerCyclotome (Multiplicative (muQZ p))` is an actual
  colimit-type object, but the tree contains no `G_v` action on `muQZ p` or
  on its `KummerCyclotome`. S2017 explicitly records (M5) that no topology is
  put on this action.
- `S2046G1PsiCnsAction` acts on the *other* cyclotome
  `PsiCnsCyclotome p`; there is no action on `muHatZ p` to compare with.
- `muHatComparison p` (S2017) is itself an exact missing comparison, so even
  the module equivalence is conditional.
- No `TopologicalSpace (muHatZ p)` and no continuity statement exist in the
  tree.

### Exact first missing

```text
S2046G1TopologicalModuleData p
```

plus the topology/continuity structure. The least-coupled subgoal is
`muHatComparison p`; the hard missing piece is the actual `G_v`-action on
`muHatZ p` and its equivariance.

## Evidence hashes (existing, no new build)

```text
S2036ActualPsiCnsM234Actual.lean   source SHA=E29536ED…8445DC
S2039ActualPsiCns.lean             source SHA=34A38CD7…BDCF2
S2136M4KummerNormalizationActual   source SHA=33D76985…1DE7A
S2046G1CyclotomeActual.lean        source SHA=C664AC7D…2A8CA
S2017VerlagerungActual.lean        source SHA=28D57C25…5F6BA8
axioms (existing probes): propext, Classical.choice, Quot.sound
```

## Consumer

- M4: S2046M4ConditionalActual, S2046PsiCnsComponents, S2068 actor reduction,
  S2046M3M4S2091Port.
- G1: S2046 M3/M4, S2091 H2 port.

## Conclusion

Neither M4 nor G1 is constructed. Exact first missing is
`S2136M4NormalizationData p` and
`S2046G1TopologicalModuleData p` (plus topology/continuity). No fake
normalization, no trivial action, no terminal/point substitution.
