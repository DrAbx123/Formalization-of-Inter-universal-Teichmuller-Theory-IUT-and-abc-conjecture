# D2 Kummer layer exact missing (2026-11-15)

## Green
- `Mzk1D2KummerLayerActual` general-K interface: `D2KummerLayer` keeps `rootsFixed : RootsOfUnityFixed` as explicit input data, not a theorem.
  `kummerMap`/`kummerMap_eq` are the actual `AbsoluteKummerQuotient.absoluteKummerMapQuotient`; `injective` is the donor theorem; `bijective` remains an explicit paper-level field.
- `q5WvalModN : (Q5)^x ->* Multiplicative (ZMod n)` is a concrete Q5 helper using `PadicField.wval` mod n.

## Exact missing
1. `RootsOfUnityFixed` at Q5 only for n | 4 (Q5 contains μ4, not μ3); general n is false.
2. Kummer map surjectivity/bijectivity: donor only gives injectivity; no cardinality equality donor
   `card (K^x/(K^x)^n) = card H^1(G, μ_n)`.
3. Unit kernel quotient: `q5WvalModN.ker = {u | wval u = 0 mod n}` is NOT `nthPowerSubgroup`.
   Correct relation: kernel of valuation class on K^x/(K^x)^n is U_F/(U_F ∩ (K^x)^n), not a direct equality.

No fake inhabitant/equality is kept.
## Next action: cardinality route (not yet formalized)

The current `D2KummerLayer.kummerMap` codomain is the full hom group
`(AlgebraicClosure K =~[K] AlgebraicClosure K) ->* rootsOfUnity n`,
whose Galois group is infinite, so `Fintype`/cardinality is not available.

Route: replace it by a finite quotient model
`Gal(L/K) ->* rootsOfUnity n (AlgebraicClosure K)` for a finite Galois
extension `L/K` containing the n-th roots, then
1. `Fintype (Gal(L/K))` and `Fintype (Gal(L/K) ->* mu_n)`;
2. `Fintype.bijective_iff_injective_and_card`;
3. supply the explicit cardinality equality
   `card (K^x/(K^x)^n) = card (Gal(L/K) ->* mu_n)` as donor/field.

The finite quotient model and cardinality equality are the next exact inputs;
no fake bijectivity is asserted in the general-K file.