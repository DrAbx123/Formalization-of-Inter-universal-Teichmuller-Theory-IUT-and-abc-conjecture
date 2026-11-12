# S2455: coproduct-slice equivalence — precise missing

Date: 2026-11-02. Serialized lake env lean -j1.

Goal: construct Over (X coprod Y) ~ Over X x Over Y, then lift to J.pseudofunctorOver Type, then glue arbitrary descent data on the S2448 cover.

Attempted actual direction: S2455OverCoprodPullback (X Y) : Over (X coprod Y) -> Over X x Over Y by pullback along coprod.inl/inr using Over.map.
Compile failed at the codomain product category elaboration (invalid {..} notation / TypeCat.Hom private); no olean. This is a Lean formalization issue plus the deeper issue below.

EXACT MISSING: Mathlib v4.32.2 has no equivalence
  Over (X coprod Y) ~ Over X x Over Y
and no theorem that coproduct slices decompose. Search found Over.coprod (product in Over A), not this. Such an equivalence requires the coproduct to be universal/disjoint (extensive category); for Scheme this is mathematically true but the Over-level equivalence/counit is not in Mathlib.

Consequence: cannot decompose an arbitrary descent datum on the S2448 two-coproduct cover into two slice sheaves and glue; arbitrary S2448ConcreteAmalgam remains missing.

ACTUAL retained: S2448 concrete non-split cover (EXIT=0, olean 171072, SHA 2EE1F709...), S2453 canonical datum Amalgam (EXIT=0, olean 21280, SHA 53ea0cdc...), S2449 two-copy identity cover (EXIT=0, olean 24800).

No IsStack claim, no fake.