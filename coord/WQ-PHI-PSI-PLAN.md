# WQuotient 7.4 Phi/Psi construction audit (2026-11-15)

## Green inputs

- unitLogTorsionQuotientEquivRange (IntegralUnitLogarithmKernel.lean:83):
  WQuotient =* range unitLogHom
  where WQuotient = (Integers Q5)^x / torsion.
- unitLog_range_eq_prime_smul_integers_of_odd_unramified (IntegralLogShellSharpBounds.lean:1518):
  Set.range unitLog = (5 : Q5) • (Integers Q5 : Set Q5)
  requiring hp2 : 5 != 2 and hpi : Irreducible (5 : Integers Q5).
- padicIntegersEquivZp (WQMembershipTransferActual):
  (NormedField.valuation (K:=Q5)).integer =+* Z5

## Exact deferred input

Irreducible (5 : (NormedField.valuation (K:=Q5)).integer).
Documented in coord/WQ-IRREDUCIBLE-GAP.md; no inhabitant supplied.

## Remaining construction steps

1. Transport Irreducible (deferred).
2. Build the subgroup equality from the set equality:
   range unitLogHom = Subgroup.map (5 scalar action) top on Multiplicative Q5;
   requires choices/Subgroup.ext and injectivity of x -> 5*x on Q5.
3. Define Phi on range unitLogHom:
   choose a : Integers Q5 with x = 5 • a (from step 2),
   send x to Multiplicative.ofAdd a.
   Well-defined by 5 injective on Q5.
4. Define Psi (ofAdd a) = 5 • a as an element of range;
   membership from step 2.
5. Prove Psi (Phi x) = x and Phi (Psi y) = y by Multiplicative.toAdd/ofAdd and
   5-scalar cancellation.
6. Compose:
   WQuotient =* range unitLogHom =* Multiplicative (Integers Q5)
     =* Multiplicative Z5
   using padicIntegersEquivZp.map/Units.mapEquiv.

## Exact missing lemmas

- Irreducible (5 : Integers Q5) (deferred).
- Subgroup/Set.range bridge for the 5 • Integers equality (no existing donor found).
- choice of integral preimage and its well-definedness.
- injectivity of the 5-scalar map on Q5.
- conversion between Multiplicative Q5 scalar action and additive Q5.

No fake inhabitant is kept; WQ clean file only contains membership/RingEquiv/trans.
## Next donor candidates (2026-11-15)

1. `tmp/local-cft-port/PadicField/Uniformizer.lean:183` gives
   `PadicField.irreducible_ϖ : Irreducible (ϖ p K)`, and `ϖ p K` is the chosen uniformizer in `𝒪 p K`.
   For `K = Q5`, the uniformizer is 5 (`v_ϖ`/`uniformizer_spec`), so this is a concrete candidate
   for `Irreducible (5 : PadicField.Integers p Q5)`.
2. Missing bridge: `PadicField.Integers p Q5 ≃+* (NormedField.valuation (K:=Q5)).integer`
   (or a direct irreducibility transport).  No such ring equiv was found.
3. Alternative: prove `IsDiscreteValuationRing ((NormedField.valuation (K:=Q5)).integer)`
   and use `IsDiscreteValuationRing.irreducible_iff_uniformizer` with uniformizer 5.

Once `Irreducible (5)` is available, the remaining range/subgroup and Phi/Psi steps are as above.
