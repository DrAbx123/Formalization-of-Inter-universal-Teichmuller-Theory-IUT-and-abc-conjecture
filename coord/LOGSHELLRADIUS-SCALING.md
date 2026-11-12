# LOGSHELLRADIUS-SCALING — scaling law and hull volume (A1023)

Status: read-only derivation from lana root tree; no compiled file.

## 1. Definitions

- `Iut.logShell k p = {(2p)^{-1} log u | ||u-1|| < 1}`
  (`Iut/Concrete/LocalConstruct/LocalLogShell.lean:41`);
  our ported copy: `Mzk1PortedLocalVolumeActual.lean`.
- `logShellRadius w p = sSup ((-ordp K w) '' {z | z ∈ logShell (completionAt K w) p ∧ z ≠ 0})`
  (`Iut/WallEquiv/VcI.lean:464`).
- `componentVol_leastHull_tensorLogShell_eq` (`VcI:603`):
  `μ^log(leastHull(⊗_j 𝓘_{c j})) = ∑_j logShellRadius(finPart(c j)) p * log p`.
- `componentVol_tensorLogShell_eq` (`VcI:165`):
  `μ^log(⊗_j 𝓘_{c j}) = shellExcess p c + orderVol p c`.
- qroot: `InitialThetaData.qroot` is the `2ℓ`-th root of the Tate q parameter
  (`Iut/Concrete/ThetaRegion.lean:16`); `scaleEltAt` uses `qroot ^ (j+1)^2`
  (`:126-132`), and `ordp_pow_nonneg` (`:151-154`) gives `ord_p(qroot^m) ≥ 0`.

## 2. Radius of the unscaled shell

- At an unramified odd prime (e = 1):
  `logShell k p = integer ring` (`LocalLogShell.lean:101`, `logShell_eq_integer`),
  hence every `z ∈ logShell` has `ord_p z ≥ 0` and units have ord 0, so
  `logShellRadius w p = 0`.
  This matches the tame hull formula `Σ_j (1 - 1/e_j) log p = 0` at e_j = 1
  (`VcI:435`).
- At a ramified/wild place e = 2ℓ (or e > p-2): the tame closed form
  `1 - 1/e` is NOT available; `logShellRadius` remains the exact `sSup`
  definition.  Only the general exact hull formula (`VcI:603`) applies.

## 3. Scaling law for the radius

Let `a` be a nonzero field element with `ord_p(a) = k`, and let `a • S` be the
scalar multiple of a set `S ⊆ completion`.  Then
  `logShellRadius(a • logShell) = logShellRadius(logShell) - k`.

Derivation: for `z = a y`,
  `ord_p z = ord_p a + ord_p y = k + ord_p y`  (`ordp_mul` additivity),
so
  `-ord_p z = -k - ord_p y`,
and the `sSup` over `y ∈ logShell` shifts by `-k`; the nonzero condition is
preserved because `a ≠ 0`.

Sign: `k = j²·ord_p(qroot) = j²·ord_p(q)/(2ℓ) ≥ 0` for the theta scaling
`qroot^{j²}`; therefore the radius DECREASES by `j²·ord_p(q)/(2ℓ)`.
Equivalently, with `A_{v} = ord_p(q_v) log p/(2ℓ)`, the radius term
`ρ·log p` decreases by `j² A_v`.

Caveat: this is a derivation from the `sSup` definition; the lana source does
not state a named `logShellRadius_units_smul` lemma, so a Lean proof would need
`ordp_mul`/`exists_isGreatest_logShellRadius` and `sSup` translation lemmas.

## 4. Hull volume under scaling

By `componentVol_leastHull_tensorLogShell_eq` (`VcI:603`), for the scaled
tensor hull with factors `a_j • 𝓘_j` (`a_j = qroot_{v_j}^{j²}`,
`k_j = j²·ord_p(q_{v_j})/(2ℓ)`):

  `V(leastHull(a • shell))
     = ∑_j logShellRadius(a_j • 𝓘_j) · log p
     = ∑_j (ρ_j - k_j) · log p
     = ∑_j ρ_j log p - ∑_j k_j log p
     = V(leastHull(shell)) - ∑_j j²·A_{v_j}`,

where `A_{v_j} = ord_p(q_{v_j}) log p/(2ℓ)`.

Sign: the scaling term is NEGATIVE (q is contracting: `ord_p(q) > 0`), and the
linear coefficient in `m = j²` is `-A_{v_j}` per factor.

At an unramified place `ρ_j = 0`, so
  `V(leastHull(a • shell)) = -∑_j j² A_{v_j}`.
At a wild place the same formula holds with the exact `ρ_j` from `sSup`; no
`1 - 1/e` shortcut is claimed.

## 5. Relation to `componentVol_tensorLogShell_eq`

`componentVol_tensorLogShell_eq` gives the unscaled shell decomposition
  `μ^log(⊗𝓘) = shellExcess + orderVol`.
Scaling by a unit `a` changes both terms via the Haar character:
`μ^log(a • X) = μ^log(a • O) + μ^log(X)` (`componentVol_units_smul`,
`IdentifiedCopies:67`), and `μ^log(a • O)` is the scaled `orderVol`
(`componentVol_scalAProd`/`scalBProd`, `VcI:199-258`).
The exact hull formula (`VcI:603`) is the simpler route; it avoids the
`orderVol`/`shellExcess` split and directly exhibits the `-k_j log p` term.

## 6. Status

- Unramified e=1: radius 0 (green source `logShell_eq_integer`; ported).
- e=2ℓ/wild: exact value is `sSup`; no closed form in tame theorem.
- Scaling law: derived, not yet formalized (needs `ordp_mul` + `sSup` translation).
- Hull volume coefficient: `-j² A_v` per factor; sign negative.
