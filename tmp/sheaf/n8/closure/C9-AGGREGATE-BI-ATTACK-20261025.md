# C9 attack: aggregate conditional B=I surplus to global closure

Task ID: task-175 / C9-AGGREGATE-BI-ATTACK-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact-arithmetic research only; no Lean/Project edits; no target changes; no arbitrary bad set or b values; only this file written.

## 0. Inputs and binding corrections

- C9-FULLC-WEIGHTS-ATTACK-20261025.md (task-169), SHA256 142b63c7e22da681efb6cfc2e3c45e0a58c0bb5135f4e995fc35b1e488cc249c.
- C9-MODP-BRANCH-PROOF-20261025.md (task-154), SHA256 af543bbbc50e8ec8cf9909cd5675d830018254760abc66410c81501a7227eade.
- C9-MODP-CERTIFICATE-20261025.md (task-155), SHA256 e5056d524da94683e5b6ba765ea0aeaf8b23c03d96814f02b49cb47496cc9e95.
- C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md (task-162), SHA256 8e7ef66a737bbfe73ed13ea568875a4d1305f48d814de4b3773bebb3db2f3548.
- C9-RADIUS-CORRECTION-20261025.md (task-167), SHA256 d563226d8fcde7e01f06bcddd5195f19530182f828c3b419997f78ab3188405d.
- C9-ARCH-GLOBAL-20261025.md (task-156), SHA256 524e078ad85c72067627f006d165a724436e1ba508e86475c5f991860586e489.
- C9-ERROR-LEDGER-20261025.md (task-164), SHA256 06f8e743c35d2212f81db34bcd8f17483054b1aa82297772b55cae65fcd313b6.

Binding corrections: corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)), rho not a homomorphism, mapping-class source, basis alignment inferred, trace target Tr_{K/K^{d=1}}; TAME (11)-(14) are not a target proof; full Ind1 is the procession automorphism group; TC-A..TC-H and TC-S are required. B=I is conditional: under the natural trace alignment B=O_K and B=I is not actual; if the basis alignment fails, the exact coordinate v/full barGamma is not computed.

## 1. Quantities and sign conventions

Fix F_mod=Q, a single bad p=12301, e=41, and the B=O_K aligned conditional baseline. In natural log units:

    archimedean upper bound: A := ((ell+5)/4) log pi = (46/4)log pi = 13.164394...   (1.1)
    b=3 finite residual: D3 := (408/41) log 12301 = 93.71497127459669...            (1.2)
    b=273 finite residual: D273 := (38883/41) log 12301 = 8931.17457860329...      (1.3)

The B=O_K residual is positive; h_inf can reduce it by at most A. Therefore the residual after the maximal paper-level archimedean contribution is

    D3 - A = 80.55057727459669... natural,                                  (1.4)
    D273 - A = 8918.01018460329... natural.                                (1.5)

The conditional B=I b=3 local surplus at a bad prime p is

    S(p) := (12/41) log p.                                                (1.6)

This is positive only under the conditional B=I branch; it is not actual under the natural trace alignment. At p=12301:

    S(12301) = (12/41) log 12301 = 2.7563226845469613... natural.          (1.7)

All B=I b=3 places are independent only if they are distinct bad primes; a single complete C cannot use the same p twice. The actual bad set is finite but not enumerated; no upper bound on its primes is available from the current source data.

## 2. Minimal configurations at fixed p=12301

Assume for this section that every aggregate B=I place is at p=12301. This is an abstract arithmetic configuration, not a realized complete C (distinctness is discussed in §3).

### 2.1 To overcome the archimedean upper bound A

Need N * S(12301) > A:

    N > 13.164394 / 2.7563226845 = 4.7760714...
    N_min = 5.                                                          (2.1)

Five conditional B=I b=3 places at p=12301 give 13.7816134... > 13.164394. Four give 11.0252907... < 13.164394. Thus the minimal fixed-p arch-bound configuration is N=5.

### 2.2 To overcome the b=3 residual D3

Gross, without archimedean help:

    N > 93.7149712746 / 2.7563226845 = 34 exactly,                       (2.2)
    N_min = 34; 34*S = 93.7149712746 = D3.

At N=34 the surplus equals D3 exactly; to have strict compensation one needs N>=35 unless the archimedean contribution is positive. With the maximal archimedean upper bound A included:

    N > (D3-A)/S = 80.5505772746 / 2.7563226845 = 29.2239285...,          (2.3)
    N_min = 30.

Thus the minimal fixed-p configuration is 34 places gross, or 30 places if the actual h_inf attains the paper-level upper bound A (which is not proved; A is only an upper bound).

### 2.3 To overcome the b=273 residual

B=O_K b=273 residual D273=8931.1745786:

    N > D273/S = 3240.25,  N_min = 3241 gross;                          (2.4)
    with A: N > (D273-A)/S = 3235.4739..., N_min = 3236.                  (2.5)

If the b=273 p itself is B=I, its local deficit is 38463/41 log p = 8834.7032846 natural:

    N > 8834.7032846/2.7563226845 = 3205.25, N_min = 3206 gross;        (2.6)
    with A: N > 3200.4739..., N_min = 3201.                                (2.7)

These are fixed-p counts; they require respectively 3206 or 3201 additional B=I b=3 places at p=12301, impossible for a single C if p=12301 can occur only once. Section 3 treats distinct primes.

## 3. Distinct primes and unbounded prime choice

For a bad prime p, the conditional B=I b=3 surplus is S(p)=(12/41)log p. If p is not fixed, a single sufficiently large prime can exceed any fixed post-archimedean residual:

    S(p) > A       iff p > exp(41A/12) = exp(44.978346...) approx 3.4186e19;   (3.1)
    S(p) > D3      iff p > exp(41D3/12) = exp(320.192818...) approx 1.1428e139; (3.2)
    S(p) > D273    iff p > exp(41D273/12), log10 approximately 13252.4.        (3.3)

Therefore, over an arbitrary unbounded set of bad primes, the abstract minimal number of B=I b=3 places is N=1 for each of the thresholds A, D3, D273: choose one bad prime above the corresponding threshold. This is not a claim that such a prime is in any actual bad set, nor that the local type/B=I condition holds there.

For N distinct primes the exact criterion is

    sum_{i=1}^N (12/41) log p_i > T,   i.e.  prod_i p_i > exp(41T/12).    (3.4)

The minimal N is one if an allowed prime above the threshold exists; otherwise it depends on the actual bad set. No source theorem bounds the primes or the size of S_bad(C).

Thus 'minimal number' has two precise meanings:

- fixed p=12301: N=5 for A, N=34 gross / 30 with A for D3, N=3241 gross / 3236 with A for D273, or 3206 / 3201 for a B=I b=273 p;
- arbitrary bad primes: N=1 abstractly for any fixed threshold, but no actual C/bad-set realization is constructed.

## 4. Other positive branches

No other actual positive finite branch is available in the current corrected corpus:

- B=O_K bad places have positive residual for all b>0; they cannot compensate.
- B=I b>3 is not positive: b=273 B=I still has deficit 38463/41; for b>=4 branch B cannot reach Q_p.
- good finite places, Kummer zero/unit small domain, tensor order, pure permutations: zero or negative normalized contribution.
- other bad local types (e!=ell, wild, e>=p-1): no volume formula; unknown, not a positive branch.
- Ind1/Ind2/Ind3 and +infinity: no actual positive normalized volume without TC conditions.

So the aggregate B=I b=3 construction is the only candidate, and it is conditional.

## 5. Actual source realization: what would be needed

To realize N aggregate B=I b=3 places in one complete C with F_mod=Q, one would need:

1. An actual complete C whose bad set S_bad(C) contains N distinct rational primes p_i, each with the tame totally ramified local type e=41 and p_i>42. The source only guarantees S_bad(C) finite and nonempty; it does not enumerate or bound the primes.
2. For each p_i, actual local q-parameter data with b_i=3 and the corrected local field K_i=Q_{p_i}(pi), pi^41=p_i u_i.
3. B=I at each p_i: in the trace-adapted basis, the actual source generator matrices must have a nonzero W-coordinate in the first column (condition (3.5) of task-154), or the basis-change coordinate v_i must be nonzero. Under the natural trace alignment B=O_K and this fails for every p_i; if the alignment fails, v_i/full barGamma is not computed.
4. If the same p_i is used in several tensor factors/rows, the B=I surplus is not simply multiplied by the number of factors: the local volume formula is per bad place/tensor packet, and one bad prime can occur in several tuples only through the source's allowed tuple structure. The counts above assume distinct bad places with independent local surpluses; this is an abstract maximum, not a proved multiplicity.
5. TC-A..TC-H and TC-S for target containment; local B=I alone does not imply F(Hull(...)) subset H_C or h_C>=Q_C.

Under the natural trace alignment: B=O_K for all bad p, so no B=I surplus exists; aggregate compensation is impossible (though local B=O_K residuals are conditionally known). Under basis-alignment failure: B=I is possible but the actual v/full barGamma is unknown; no actual C with the required set is constructed. In neither case is an actual compensating configuration proved.

General F_mod: alpha_p may differ from 1 and the bad set/prime distribution is similarly unconstructed. The same B=I condition applies; no actual realization is available.

## 6. Verdict: actual, conditional, impossible

ACTUAL (source/arithmetic):

- S_bad(C) is finite and nonempty; F_mod=Q weights alpha_p=1; archimedean upper bound A=13.164394 natural (paper-level).
- B=O_K finite residuals D3=93.714971 and D273=8931.174579; every B=O_K bad place adds positive residual.
- Exact B=I b=3 surplus formula S(p)=(12/41) log p; arithmetic thresholds/counts in §2/§3.

CONDITIONAL:

- B=I b=3 at any bad prime; aggregate configurations N=5 (arch), N=34/30 (D3), N=3241/3236 (D273 B=O_K), N=3206/3201 (D273 B=I); arbitrary-prime N=1 abstractly.
- Their realization requires distinct bad primes, per-p local data, v_i nonzero/full barGamma, and TC-A..TC-H/TC-S. None is proved.

IMPOSSIBLE / WITHDRAWN:

- Actual aggregate B=I compensation under the natural trace alignment: impossible, since B=O_K there.
- Actual finite compensation from B=O_K, good places, Kummer zero, tensor order, permutations, Ind1/Ind2/Ind3: impossible with the stated formulas.
- Any unconditional global closure or global counterexample from aggregate B=I: not available; B=I is not actual and target conditions are missing.

## 7. Conclusion

The minimal abstract configurations are:

| target | fixed p=12301, gross | fixed p=12301, with arch A | arbitrary distinct primes, abstract |
|---|---:|---:|---:|
| arch bound A=13.164394 | 5 | - | 1 if p>3.4186e19 |
| b=3 D3=93.714971 | 34 | 30 | 1 if p>1.1428e139 |
| b=273 B=O_K D=8931.174579 | 3241 | 3236 | 1 if p>10^13252.4 |
| b=273 B=I D=8834.703285 | 3206 | 3201 | 1 if p>10^13109.3 |

These counts are conditional and abstract. No actual source C is constructed with the required distinct bad primes and B=I coordinates; under the natural trace alignment B=I is unavailable and the aggregate route is impossible. The full-C target therefore remains open, with the exact missing objects: actual S_bad(C), per-p local types/b_p, v/full barGamma, and TC-A..TC-H/TC-S.

## 8. Next executable steps

1. Fix an actual C and enumerate S_bad(C) (finite) with p, e_p, b_p and local type; this decides whether the required primes/distinctness are available.
2. For each candidate p compute the actual first-column matrices in the trace basis and decide v/B (task-154); do not assume B=I.
3. If B=I occurs, check the p=12301 surrogate counts against actual distinct primes; a single huge prime can replace many p=12301 places in the abstract, so the actual cardinality depends on S_bad(C).
4. Complete TC-A..TC-H/TC-S before any target-containment/global closure use.
5. If no B=I occurs, aggregate compensation is impossible under the natural alignment and the b=3/b=273 residual stays positive after the arch upper bound.

Status: stage1 natural-language/exact arithmetic only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6/ABC not proved.
