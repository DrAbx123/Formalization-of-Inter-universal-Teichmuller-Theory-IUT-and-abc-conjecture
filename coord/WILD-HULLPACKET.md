# WILD-HULLPACKET — wild-place hull packet formula (A912)

Source: lana `Iut/WallEquiv/VcI.lean` (root tree) at the referenced lines.
Notation: `p : Nat.Primes` (residue characteristic), `c` a tuple/lab of places,
`w_c` tuple weights, `j` runs over the factors of the tensor packet, `e_{c j}` local
ramification index, `ρ_{c j} = logShellRadius`.

## 1. General (`wild`) hull packet — exact

`VcI.lean:806 hullPacket_finite`:

    hullPacket D i (finite p)
      = ∑_c w_c · ∑_j logShellRadius (finPart D.Kt (tuple D.placeSect i c j)) p · log p.

Definition of the radius (`VcI.lean:464`):

    logShellRadius w p = sSup { -ord_p z | z ∈ Iut.logShell (completionAt K w) p, z ≠ 0 },

so `𝓘_w ⊆ p^{-ρ_w}·𝓞_w` is the least such fractional ideal
(`exists_isGreatest_logShellRadius`, :469).

As a decomposition: for each capsule and factor,

    ρ_{c j}(p) = (1 − 1/e_{c j}) + δ_{c j}(p),
    H_v = ∑_c w_c · [ ∑_j (1 − 1/e_{c j})·log p + ∑_j δ_{c j}(p)·log p ],

where `δ_{c j}(p) = ρ_{c j}(p) − (1 − 1/e_{c j})` is the **wild shell correction**
(zero in the tame case, see below).  This is the requested explicit `e ≥ 2` expression;
`logShellRadius` is the exact replacement for `1 − 1/e` in the wild case.

## 2. Tame specialization — green formula in lana

`VcI.lean:844 hullPacket_tame` (for `IsTamePrime D p`: `p` odd and every `e_{c j} ≤ p − 2`):

    hullPacket D i (finite p) = ∑_c w_c · ∑_j (1 − 1/e_{c j})·log p.

Equivalent exact-hull statement `componentVol_leastHull_tensorLogShell_eq_tame` (:435):

    componentVol (leastHull (tensorLogShell)) = ∑_j (1 − 1/e_j)·log p.

and `componentVol_leastHull_tensorLogShell_eq` (:603) in general:

    componentVol (leastHull (tensorLogShell)) = ∑_j logShellRadius(...)·log p.

Hence `ρ_{c j} = 1 − 1/e_{c j}` in the tame case, and the wild correction is exactly
the difference between the two displayed formulas.

## 3. `VC(I)` packet and the `orderVol` term

`VcI.lean:794 vcIPacket_finite` (exact, every prime):

    vcIPacket D i (finite p)
      = ∑_c w_c · (shellExcess p c + orderVol p c),

where (`VcI.lean:93` and `:158`)

    orderVol p c = μ^log(R_I) = componentVol (order p c),
    shellExcess p c = log(μ(⊗𝓘)/μ(R_I))/[T : ℚ_p],
    componentVol_tensorLogShell_eq: μ^log(⊗𝓘) = shellExcess + orderVol.

For the wild place the **hull** packet is not `vcIPacket`; the defect is

    shellDefect p c := componentVol(leastHull) − componentVol(tensorLogShell)
                  = ∑_j ρ_{c j}·log p − (shellExcess + orderVol).

Bound (`Gap.lean:438` and `VcI.lean` doc :62):

    |shellDefect + orderVol| ≤ ∑_{j ∈ I*} (3 + log e_j),

which is the only non-explicit part of the wild hull packet (the `(3+log e)` correction).

Tame simplification `shellDefect_eq_neg_orderVol_tame` (:448):

    shellDefect = −orderVol   (tame),
so `hullPacket_tame` has no `orderVol` term; for `e ≥ 2` (wild) the `orderVol` term
remains in `vcIPacket`, while `hullPacket` is the `ρ`-sum above.

## 4. The remaining named (paper) identifications

* `ShellExcessAdditive p c` (:631): `shellExcess = ∑_j factorShellVol(...)`, where
  `factorShellVol` (:621) is the normalized log-volume of a factor log-shell;
* `PacketIndexFormulaGalois p w hw m` (:640): for `K_w/ℚ_p` Galois,
  `orderVol (K_w^{⊗m}) = −((m−1)/2)·d_w·log p`;
* general packet index is `−½·(d_I − d_T)·log p` (comment :638).

## 5. What is proved vs needed

* green in lana source (pending olean): `hullPacket_finite`, `hullPacket_tame`,
  `componentVol_leastHull_tensorLogShell_eq`(+`_tame`), `vcIPacket_finite`,
  `componentVol_tensorLogShell_eq`, `shellDefect_eq_neg_orderVol_tame`;
* named/open: `ShellExcessAdditive`, `PacketIndexFormulaGalois`;
* the wild correction `∑ (ρ − (1−1/e))log p` is bounded by `∑(3+log e)` but no exact
  closed form is proved in the source (paper computation in `VcI.md`).
