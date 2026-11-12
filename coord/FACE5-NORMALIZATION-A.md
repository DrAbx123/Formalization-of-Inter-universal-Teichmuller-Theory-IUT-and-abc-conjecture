# Face 5 path 2: intrinsic per-place allocation of A (A911)

## Paper statement (no allocation freedom)

IUT III Cor 3.12 in variant form:
  `-|log q| <= -|log Theta|`  (equivalently `(sF-1)*A <= V`, `A = |log q|`).
The paper's `|log q|` is NOT an abstract quantity to be allocated: it is
`A = logQ/(2l)` with
  `logQ = sum_{w in V(F)^bad} weight_w * ord_w(q_w) * log p_w`,
`weight_w = f_w/[F:Q]` (lana `Iut/Cor312/LeftHandSide.lean:81-88`, the same
`QPilotData.logQ`/`absLogQ` definitions).
So the per-place contributions of `A` are FIXED by the divisor of `q`:
  `A_v := weight_v * ord_v(q_v) * log p_v / (2l)`,  `A = sum_v A_v`,
and `ord_v(q_v) = 0` for good finite places (so only bad places contribute).

Theta side: lana `logVol_hull_vcI_eq` (`Iut/WallEquiv/VcI.lean:740`):
  `V = (1/nC) * sum_{i : Fin nC} sum^fin_{vQ : RationalPlace} hullPacket i vQ`,
with finite-place exact forms (VcI.lean:806/844):
  `hullPacket_finite = sum_c w_c * sum_j rho_{c j} * log p`,
  `hullPacket_tame   = sum_c w_c * sum_j (1 - 1/e_{c j}) * log p`,
and the archimedean place gives the `archDefect`-type term `H_inf` (VcI:700).

## Unambiguous per-place target (independent of allocation choices)

Define, for every finite place v of F:
  `T_v := (sF - 1) * weight_v * ord_v(q_v) * log p_v / (2l) = (sF - 1) * A_v`,
  `H_v := (1/nC) * sum_i hullPacket_i(v)`,
  `H_inf := (1/nC) * sum_i hullPacket_i(inf)` (archimedean, one global term).
Then the global target is exactly
  `sum_{v finite} T_v <= sum_{v finite} H_v + H_inf`.
The natural intrinsic assignment is the per-place comparison
  `T_v <= H_v`  for every finite bad place v,
with the arch term on the right only (q has finite support, so no `T_inf`); under the
paper normalization `H_inf >= 0` (archConstant = log(sqrt 2 pi) > 0), so ignoring it is
a strengthening, not a weakening.

## What is and is not allocation-dependent

- `T_v` is fixed by the q-divisor: there is NO freedom to move parts of `A` to the arch
  place or to rescale per place (that was the modelling choice A910 worried about);
- splitting LHS into `T_v` and RHS into `H_v` is canonical because both sides decompose by
  the SAME `RationalPlace` index (q divisor vs hullPacket);
- the only choice left is whether to prove `T_v <= H_v` place-by-place (sufficient) or only
  the sum (weaker); the per-place form is the intrinsic paper comparison.

## Consequence for face 5

The per-place target `T_v <= H_v` is exactly the statement that the hull packet at v
dominates `(sF-1)` times the q-pilot contribution at v.  For unramified bad v with
`ord_v(q_v)=1`, `weight_v = 1`, `p = p_v`:
  `T_v = (sF-1)*log p/(2l)`,  `H_v = sum_i hullPacket_i(v)`
whose tame expansion is `sum_c w_c sum_j (1 - 1/e_{cj}) log p >= 0` (positive).
The remaining quantitative comparison is exactly between these two explicit numbers;
no allocation freedom remains.
