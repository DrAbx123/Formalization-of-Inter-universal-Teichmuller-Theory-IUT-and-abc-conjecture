# M2c deep inputs: finite generation and Nikolov-Segal width

## Result
Neither `PadicAbsoluteGaloisTopologicallyFinitelyGenerated` nor `NikolovSegalCommutatorWidth` is constructed or refuted. Both remain `Prop` with no inhabitant in the tree. No fake axiom/instance was introduced.

## (1) Finite topological generation of G_Qp
Exact target (S2117 line 291):
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated : Prop :=
    exists s : Finset (LocalAbsoluteGalois p),
      (Subgroup.closure (s : Set (LocalAbsoluteGalois p))).topologicalClosure = top.
What Mathlib v4.32.2 actually has:
- Krasner's lemma `IsKrasner` and `IsKrasner.krasner` (Mathlib.Analysis.Normed.Field.Krasner).
- No theorem that the absolute Galois group of a p-adic field is topologically finitely generated.
- No Demushkin/class-field-theory classification of G_Qp in Mathlib.
S2117 records the weaker finiteness-of-extensions statements
  FinitelyManyExtensionsOfDegree n
  FinitelyManyExtensionsOfLocalFieldOfDegree L n
  FinitelyManyOpenSubgroupsOfIndex n
and explicitly notes they are necessary but NOT sufficient for finite generation (line 333-339). The actual proof needs the Demushkin structure / finiteness of extensions plus the classification of finitely generated pro-p groups, neither available.
Exact first missing: a proof of `PadicAbsoluteGaloisTopologicallyFinitelyGenerated` from Krasner plus Demushkin/local CFT APIs (not present), or an imported theorem. No proof or counterexample was obtained.

## (2) Nikolov-Segal commutator width
Exact target (S2116 line 359):
  NikolovSegalCommutatorWidth : Prop :=
    forall (G) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
      [CompactSpace G] [T2Space G] [TotallyDisconnectedSpace G],
      (exists s : Finset G, closure(s).topologicalClosure = top) ->
      exists N, (commutator G : Set G) subset range (commutatorWord G N).
Mathlib search found no Nikolov-Segal/verbal-width theorem (only unrelated 'Segal' names in algebraic topology). S2116 records the exact statement and uses it only as an implication; no inhabitant is asserted.
Exact first missing: the Nikolov-Segal uniform commutator-width theorem for topologically finitely generated profinite groups, or a pro-p version sufficient for local Galois groups. Not available in Mathlib/tree.

## Actual conditional chain already in tree
- S2116 `commutatorWidthBounded_of_nikolovSegal (hNS) (hfg)`.
- S2116 `m2cFirstMissing_of_nikolovSegal (hNS) (hfg) : M2cFirstMissing`.
- S2117 `topologicallyFinitelyGenerated_of_padicAbsoluteGalois (hQp)`.
- S2117 `m2cFirstMissing_of_padicTopFG_and_nikolovSegal (hNS) (hQp) : M2cFirstMissing`.
- S2109 `canonicalTorsionComparison_of_commutatorClosed`; S2113 `canonicalEquiv`.
These are genuine implications, not actual inputs.

## (3) Downstream remains exact missing
M2cFirstMissing -> canonicalTorsionComparison -> S2048 LocalArtinTorsionMap.
Then `TransferBridge` (S2113) is still needed for `ArtinTransferCompat`; then S2159/S2131 action-equivariance `heq` is needed for `S2432EndComm` and literal S2189.
None is actual; no conditional data is labeled actual.

## Artifacts
Baseline actual S2442MuQZFinalActual.lean unchanged: EXIT=0, source SHA256 D290C70F48BBA29CE068982CC345BF2A4FEC572A2F564B2AB847A489A93BDA6E, olean SHA256 6FC270E7C19947E6943EEAFDB72CF8528E41A3386CAC116DB6F205089A20CB95, axioms propext/Classical.choice/Quot.sound.
No new Lean file compiled; no build/cache command run.