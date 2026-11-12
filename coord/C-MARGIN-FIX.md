# C-MARGIN-FIX — paper margin vs C1 calculator (A970)

Status: MODEL/analysis; **C3/C3b conclusions marked INVALID for the paper target** (they use route-B proxy M0).

## 1. Exact definitions (lana root tree)

- `A := |log q| = D.qPilot.absLogQ = Q.logQ / (2ℓ)`
  (`Iut/Cor312/LeftHandSide.lean:88`);
- `R := -rhs`, where `rhs = (concreteVariantData D).rhsData.rhs = vol.processionVol thetaHull`
  (`Iut/Cor312/RightHandSide.lean:107`); this is `-|log Θ|`;
- `V := logVol D (hullOf D (vcI D))`
  `= (1/nC) Σ_i Σ_v hullPacket D i v` (`Iut/WallEquiv/VcI.lean:741`);
- `gap D := rhs + sF(nC)·A - V` (`Iut/WallEquiv/Gap.lean:523`), with
  `gap = (1/nC) Σ_i Σ_v gapHullAt D i v` (`Gap.lean:895` local formula),
  `gapHullAt = Σ_c w_c · ind2Term` at finite p, `0` at ∞;
- `SSIneq D ↔ (sF(nC)-1)·A ≤ V` (`VcI.lean:889-891`);
- framework target: `(sF-1)·A ≤ V + gap`.

## 2. Paper margin

With `M := V + gap - (sF-1)A`:
  `V + gap = rhs + sF·A`,
  `M = rhs + sF·A - (sF-1)A = A + rhs = A - R`.
So the paper margin is **A - R**, independent of V and gap individually.
The `SSIneq` margin (no gap) is `V - (sF-1)A = A - R - gap`.

### Per-term expansion

`M = (1/nC) Σ_i [ Σ_{v finite} Σ_c w_c hullPacket_{i,v,c}
       + Σ_{v finite} Σ_c w_c ind2Term_{i,v,c}
       + arch_i ] - (sF-1)A`,
where the inner `Σ_c w_c` and outer `1/nC` are at the packet level;
`A = Σ_p ord_p(q) log p/(2ℓ)` (finite bad p).

## 3. C1 calculator (Mzk1 c1_calculator.py) discrepancies

Calculator uses `M = Σ_p H_p + Σ_p Ind2_p - Σ_p T_p` with
`H_p = (1-1/e)log p`, `T_p = (sF-1) ord_p(q) logp/(2l)`, nC=2, l=5.

1. **Capsule aggregation**: paper `V` has `(1/nC)Σ_i`; calculator has ONE capsule
   term (implicitly identical capsules), no explicit `1/nC`.  For nC=2, if H/Ind2
   are per-capsule values this is correct; if they are sums over capsules it is
   missing a factor `1/2`.
2. **Label/packet weights**: paper has `Σ_c w_c` (`tupleWeight`), normalized;
   calculator assumes one label tuple with total weight 1.  Missing for nontrivial
   packets.
3. **Ind2 level**: paper gap is `(1/nC)Σ_iΣ_vΣ_c w_c ind2Term`; calculator's
   `Sum_j frac(j² ord_q/(2l)) log p` is a MODEL formula (C0 open), not proved
   equal to lana `ind2Term`; no `Σ_c w_c` / `1/nC` and no componentVol definition.
4. **T coefficient**: `T_p = (sF-1) A_p` with `A_p = ord_p(q)logp/(2ℓ)` is
   correct (ℓ=5, l=5).  sF uses nC=(ℓ-1)/2; no error there.

Correct paper margin formula under uniform one-capsule model:
  `M = H + Ind2 - T` (same as calculator), but with H/Ind2 interpreted as
  per-capsule values and arch included; for general data use explicit sums and
  divide by nC.  The corrected CSV includes both `M_paper_formula = H+Ind2-T`
  and `M_corrected_avg_nC2 = (H+Ind2)/2 - T` as the average-per-capsule variant.

## 4. C3/C3b invalidation

- `M0 = log(deg φ) - 0.15 log N` is a **route-B proxy**, not the paper margin
  `A - R = |log q| - |log Θ|`.
- Any C3/C3b conclusion based on `M0` is **INVALID for the paper target**;
  it does not bound `A - R`, does not use `V`/`gap`, and cannot be used as
  evidence for SSIneq/Cor312.
- C3 must be restated using `M = A - R` (or `V+gap-(sF-1)A`) and the lana
  local terms; the old M0 regressions are stopped.

## 5. Corrected 20-curve table

`coord/c1_margin_corrected.csv` columns:
`base,k,H,T,Ind2,M_old,M_paper_formula,M_corrected_avg_nC2,note`.
`M_old` from `c1_sample.csv`; `M_paper_formula = H+Ind2-T`;
`M_corrected_avg_nC2 = (H+Ind2)/2 - T` (average variant; only if H/Ind2 are
per-packet sums).  Both are MODEL values, not evidence.

## 6. Next step

1. Replace calculator's Ind2 with a faithful `ind2Term` evaluation (needs C0
   exact formula/local data); add `(1/nC)Σ_i` and `Σ_c w_c` explicitly.
2. Recompute margin M=A-R from actual q/Θ readings, not M0.
3. Retire C3/C3b M0 conclusions; owner stepxi/hull; decision point: new margin
   table with no M0 rows.
