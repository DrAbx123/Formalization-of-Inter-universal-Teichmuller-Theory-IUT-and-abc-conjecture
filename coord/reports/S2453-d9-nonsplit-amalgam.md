# S2453: actual canonical amalgam on a concrete non-split etale cover

Date: 2026-11-02. Serialized lake env lean -j1.

Building on S2448GeneralCoverActual (subagent, EXIT=0):
- K=Q; point=Spec Q; baseScheme = Spec Q coprod Spec Q over Spec Q via codiagonal.
- coverObj i = terminal slice over point; coverArrow i = coproduct inclusions.
- coverPresieve = Presieve.ofArrows coverObj coverArrow.
- coverPresieve_mem : coverPresieve in (S2093EtalePrecoverage Q).coverings baseScheme (actual).
- genuinely non-split: generated sieve proper, neither arrow split epi, not identity cover (S2448).

S2453 actual:
- S2453CanonicalDatum M = (S2029SheafPrestack K).toDescentData f |>.obj M.
- S2453CanonicalAmalgam M : Amalgam (S2029SheafPrestack K) f (S2453CanonicalDatum M), with M and Iso.refl.
- S2453CanonicalNonempty M.

EXIT=0, olean 21280, SHA256 53ea0cdcb66913ed42e27fafa95d035b711eabf8a2ee83a413552f811b454cf0, axioms propext/Classical.choice/Quot.sound.

Limits: only the canonical descent datum (of an object M) is amalgamated. The FULL S2448ConcreteAmalgam / S2445AmalgamationRequirement for arbitrary descent data is missing. Exact first missing: Cech descent / stack-of-slice-sheaves theorem for J.pseudofunctorOver (Type u); Mathlib has no IsStack/IsStackFor instance and no coproduct-slice equivalence Over(X coprod Y) ~ Over X x Over Y. No arithmetic obstruction at this cover.

No S2152QIsStack claim, no fake.