# S2433: non-identity strong/coherent cover representable example

Date: 2026-11-03. Layer: **O** (D6(c) finite-etale input).
No target change, no fake.

## Deliverable

`tmp/sheaf/xif/paper/S2433NonidentityStrongRepresentable.lean`

```text
EXIT=0
olean=YES
lines=431
source SHA256=890178D59040C3B0CE9FA34B18D557148937FD7B5958B57FFBFA89B80E442852
olean SHA256=9E7EED2EB452EC72EE88B46D59785374030E24D39477265F096BD7C858148FC8
olean bytes=130512
axioms: propext, Classical.choice, Quot.sound
```

## BUILT / actual

1. `S2433FoldCover : S1816Target`: finite etale cover of Spec R' with
   carrier Spec R' x Spec R' and structure morphism the fold S1850Fold.
2. `S2433FoldStrong : StrongCover S1726Orbicurve` and
   `S2433FoldCoherent : CoherentCover`: strong finite-etale structure from
   S1943Strong, coherence derived via CoherentCover.ofStrong.
3. `S2433Map : S1728CoverMap S1852TerminalCoherent.cover
   S2433FoldCoherent.cover`, represented by the first coproduct inclusion
   `S2433G0 : S2433T ⟶ S1897CoverScheme S2433FoldCover`.
4. `S2433Representable : S2403RepresentableCoverMap S2433Map` with
   `sourceScheme = S2433T`, `targetScheme = S1897CoverScheme...`,
   `g0 = S2433G0`, and `Mono S2433G0` from the actual retraction
   `S2433G0_comp : S2433G0 ≫ S1897CoverOver ... = 𝟙 S2433T`.
5. Non-identity certificates:
   - `S2433G0_comp`: split mono;
   - `S2433FoldInl_ne_id`, `S2433Retraction_not_section`;
   - `S2433G0_not_iso : ¬ IsIso S2433G0`.
6. `S2433FoldConeEssSurjAt`, `S2433FoldPerCoverCoherence`,
   `S2433FoldPresentation`, `S2433FoldPresentation_finiteEtale`:
   S2240/S2357 per-cover strong presentation and finite-etale projection for
   the fold coherent cover.
7. `S2433TerminalSelfMapForcedIdentity`: at the terminal cover, every
   represented self cover map is represented by the identity, explaining why
   S2403/S2409 had only identity examples.

This is a genuine non-identity coherent/strong cover map with actual
representable monic scheme data, not a terminal/point/metadata substitution.

## Consumer

`S2433Representable` can feed the representable-cover composition/cancellation
route (S2398/S2429/S2424) at a non-identity coherent cover. It does not prove
`S2086StackCancellation` for arbitrary covers.

No false S2130/S2185/S2269 target, no global cancellation is assumed.
