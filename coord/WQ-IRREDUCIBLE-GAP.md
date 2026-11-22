# WQ irreducible transport gap (2026-11-15)

Clean green file: `tmp/sheaf/xif/paper/Mzk1WQMembershipTransferActual.lean` contains:
- `normedInteger_mem_valuativeInteger`;
- `valuativeInteger_mem_normedInteger`;
- `normedIntegerEquivValuative : (NormedField.valuation).integer ≃+* (ValuativeRel.valuation).integer`;
- `padicIntegersEquivZp : (NormedField.valuation (K:=Q5)).integer ≃+* Z5`.

Exact missing: transport
```lean
Irreducible (5 : Z5) -> Irreducible (5 : (NormedField.valuation (K:=Q5)).integer)
```
The failed theorem `irreducible_five_integers` was removed; current error was in the factor/unit transfer
after `IsUnit.map padicIntegersEquivZp.symm.toRingHom`, needing `RingEquiv.symm_apply_apply` and nat-cast
normalization. No fake inhabitant is kept.

Later route for §7.4: once this transport is proved, use
`unitLog_range_eq_prime_smul_integers_of_odd_unramified` with `hp2 : 5 != 2` and this `Irreducible`,
then build the range → Multiplicative Z5 Φ/Ψ maps (5^{-1} scalar and 5 scalar).