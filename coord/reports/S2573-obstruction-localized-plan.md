# S2573 monic f obstruction -> localized correction

## Exact obstruction
S2573ResidueDataObligations asks for `f : (O_F')[X]` with:
- `f.Monic`;
- `f.map (O_F' -> F') = C c * S2057Psi5F`, c != 0.

Actual integer model: `S2132Psi5Z` has
- leading coefficient `Lc = 2^36 * 5 = 343597383680`;
- constant coefficient `5^18 = 3814697265625`.

Thus the monic normalization over F' is `f = (1/Lc) * S2132Psi5Z` and its
constant coefficient is `5^17 / 2^36`, not in O_F'. Coefficient comparison
gives `2^36 * f.coeff 0 = 5^17`, which forces `2` to be a unit of O_F';
`¬ IsUnit (2 : O_F')` is kernel-proved by the norm argument (2^d != ±1).
Therefore S2573/S2470 monic residue datum is uninhabitable. GAP-TABLE
already records the same obstruction as 5^17/2^36.

## Localized correction (actual first segment)
`tmp/sheaf/xif/paper/S2574LocalizedModelActual.lean`:
- R = O_F'[1/Lc], Lc = 343597383680;
- f = C(invSelf Lc) * S2132Psi5Z.map (Z -> R);
- proves f_coeff_12 = 1, f_natDegree = 12, f_monic.
EXIT=0; olean 191712 B; src SHA AB3DF812F966F2EF3B922B01CF05C41C50D824B98BC11162501BB1A26D3B1F87;
olean SHA 6573B5A353FDE1829E794DBC093E238112AEF0709F496AEEA56F47D4E5398C49.

## Updated plan
1. Use localized monic f over R (or S=O_F'[1/Cden] in S2574LocalizedP12Actual).
2. Construct localized prime p over 613 and P over p in the localized five-division algebra.
3. Keep F613/S2572 fbar irreducibility degree 12 and root-set cardinality as separate fields.
4. Prove Dedekind-Frobenius 12-cycle over localized rings only; do not assert over O_F'.
5. Mark S2573ResidueDataObligations / S2470ActualResidueData over O_F' BLOCKED.

S2574LocalizedP12Actual.lean source SHA 8E5F8E9578BCAAE14DC5EF2782B474922A8DB631E2D39A2CA01F288918463FC5;
olean not confirmed at ledger time, so plan input not ACTUAL claim.

No fake monic model over O_F'.