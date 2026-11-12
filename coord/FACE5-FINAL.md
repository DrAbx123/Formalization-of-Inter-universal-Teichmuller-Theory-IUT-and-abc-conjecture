# Face 5 final status (A912)

## Three candidate sections — all failed

1. **Gaussian avgDeg** (`Iut/ThetaLink/Gauss.lean:228`): gives `sF*A`; route = equivalent
   rewriting, missing `hullLogVol >= sF*A` which would already imply SSIneq.  FAILS as new.
2. **Difference-bundle section** (`H = det(hull) (x) L_q^{-(sF-1)}`): correct shape; the
   nonzero integral section with arch bound is not constructed.  OPEN.
3. **l-division polynomial discriminant** `disc(Psi_l) = ±l^a Δ^b`: principal divisor of a
   rational number, total degree 0 (product formula) — gives an identity, not a positive
   lower bound; dictionary to `V-(sF-1)A` is not sign-definite.  FAILS.

## All-tame obstruction (hull/abc A911)

Per-place normalized target (paper, no allocation freedom):
`T_v = (sF-1)*weight_v*ord_v(q_v)*log p_v/(2l) = (sF-1)*A_v`, `H_v = (1/nC)*sum_i hullPacket_i(v)`,
`T_v <= H_v` for every finite bad place, with `H_inf >= 0`.  At tame/unramified places
`hullPacket_tame = sum_c w_c sum_j (1-1/e_{cj}) log p`; the comparison `T_v <= H_v` is a
pure, place-local numeric inequality; no allocation freedom remains.  The obstruction is
that the theta-hull packet terms `sum_j rho_{cj} log p` can be negative at ramified places,
so all-tame positivity does not propagate.

## Main theorem skeleton (green)

`tmp/sheaf/xif/paper/Mzk1Face5ProofActual.lean` (EXIT=0, olean, trio):
- `face5_inequality_from_perplace`: `V-(sF-1)A = sumMu+archTerm`, `sumMu>=0`, `archTerm>=0`
  => `(sF-1)A <= V`;
- `face5_inequality_of_section`: difference-bundle data + product formula + `sumNorms>=0`
  => `(sF-1)A <= V`;
- `Face5ConstructionObligation := Nonempty Face5SectionData` (the one open construction).

## Remaining pure numeric proposition

`sum_{v finite} T_v <= sum_{v finite} H_v + H_inf`, place-by-place form
`(sF-1)*weight_v*ord_v(q_v)*log p_v/(2l) <= (1/nC)*sum_i hullPacket_i(v)`,
with the arch term `H_inf >= 0`.  This is the ONLY remaining numeric content of face 5.
