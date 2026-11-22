# C9 audit: aggregate B=I arithmetic and realizability

Task: task-181 (Audit aggregate B=I arithmetic and realizability).
Owner: volumedet. Date: 2026-10-25. Stage1 verification only; no new attack;
no Lean/Project/target edits. Only this file written. `target_accepted=false`.

Inputs:

- `C9-AGGREGATE-BI-ATTACK-20261025.md` (task-175), 171 lines, SHA256
  `62156bd5d334bd417bf9d0161eee00b53897380c56fb565fc572b9bbb6c6f515`;
- `C9-FULLC-WEIGHTS-ATTACK-20261025.md` (task-169), 180 lines, SHA256
  `142b63c7e22da681efb6cfc2e3c45e0a58c0bb5135f4e995fc35b1e488cc249c`.

Binding errata used: corrected donor H=Phi^{-1}(Sp), B=I conditional on the
inferred trace/symplectic basis alignment, TAME (11)-(14) not a target proof,
TC-A..TC-H/TC-S required. The arch normalization correction (task-171) leaves
the paper-level container upper bound A=(l+5)/4 log pi valid as an upper
bound, but does not make it an actual archimedean readout.

## 0. Verdict

The arithmetic of the aggregate B=I counts and thresholds is recomputed and
is correct up to small rounding in the attack file. The classification is
mostly right but needs two precision fixes:

1. The gross b=3 count N=34 is an equality, not a strict compensating
   configuration; strict closure needs N>=35 unless h_inf>0.
2. 'Impossible under natural trace alignment' is conditional on the inferred
   basis alignment, not a paper-level impossibility. If the alignment fails,
   B=I is possible but uncomputed; no actual source C realizes the aggregate
   configuration in the current corpus either way.

Answer to the realizability question: **no actual source C constructed in the
current corpus realizes the aggregate B=I configuration**. Under the natural
trace alignment it is excluded (B=O_K); if the alignment fails, it is an open
conditional possibility with no constructed S_bad, B=I coordinates, or target
container conditions. The counts are abstract arithmetic, not C-realization.

## 1. Exact recomputation of fixed-p constants

Use p=12301, e=41, l=41, m=20, in natural log units:

    log p = 9.417435838868785...,
    log pi = 1.144729885849400...,
    A = (l+5)/4 log pi = 46/4 log pi = 13.164393687268102...,
    S = S(12301) = (12/41) log p = 2.7563226845469613...,
    D3 = (408/41) log p = 93.71497127459669...,
    D273 = (38883/41) log p = 8931.174578603292...,
    DB = (38463/41) log p = 8834.703284644149... .

Ratios:

| quantity | exact ratio | value | ceiling |
|---|---:|---:|---:|
| A/S | 13.164393687268102/2.7563226845469613 | 4.776071307279412 | 5 |
| D3/S | (408/41)/(12/41) | 34 exactly | 34 (equality) |
| (D3-A)/S | 80.55057758732859/2.7563226845469613 | 29.22392869272059 | 30 |
| D273/S | (38883/41)/(12/41) | 3240.25 | 3241 |
| (D273-A)/S | 8918.010184916024/2.7563226845469613 | 3235.4739286927206 | 3236 |
| DB/S | (38463/41)/(12/41) | 3205.25 | 3206 |
| (DB-A)/S | 8821.538890956881/2.7563226845469613 | 3200.473928692721 | 3201 |

The attack file quotes D3-A as 80.55057727459669 and D273-A as
8918.01018460329; those are obtained from the rounded value 13.164394 rather
than the exact 13.164393687268102. The difference is ~3.1e-7 natural and
does not change any ceiling. Exact recomputation gives 80.55057758732859 and
8918.010184916024.

Strictness checks:

- N=5: 5S=13.7816134227 > A=13.1643936873; arch-bound threshold is met.
- N=34: 34S=D3 exactly; this is *not* a strict compensation. It needs
  h_inf>0, or N>=35, to make D3-NS-h_inf<0.
- N=30: 30S=82.6896805364; D3-30S=11.0252907382; this can close only if the
  actual h_inf is at least 11.0253 (A is an upper bound 13.1644, not an
  attained value).
- N=3241: 3241S>D273 gross; N=3236 leaves D273-3236S = (4.25)S =
  11.7143714; needs actual h_inf>=11.7144 (A upper bound).
- N=3206: 3206S>DB gross; N=3201 leaves DB-3201S=(4.25)S=11.7143714;
  needs actual h_inf>=11.7144.

So the count list 5/34/3241/3206 and arch-adjusted 30/3236/3201 is correct
as ceilings/necessary counts; 34 is not a strict closure count.

## 2. Threshold estimates and log10

With S(p)=(12/41)log p, for a single distinct prime:

| target T | condition p> | value | log10 |
|---|---:|---:|---:|
| A | exp(41A/12) | 3.418590498831952e19 | 19.5338470813 |
| D3 | exp(41D3/12) | 1.1428105183703104e139 | 139.0579742290 |
| D273 | exp(41D273/12) | -- | 13252.4294410402 |
| DB | exp(41DB/12) | -- | 13109.2815263927 |

The attack file's `3.4186e19`, `1.1428e139`, `13252.4`, `13109.3` are
correct.

For N distinct primes the exact criterion is

    sum_i (12/41) log p_i > T  iff  prod_i p_i > exp(41T/12).

This uses distinct bad places; a single C cannot use the same rational prime
twice. The N=1 arbitrary-prime statement is abstract: existence of a prime
above the threshold in the required tame e=41/B=I local type is not a
constructed source bad place, and no source theorem fixes S_bad(C).

## 3. Classification audit: actual vs conditional vs impossible

### 3.1 Actual / arithmetic

- The constants A, D3, D273, DB, S(12301) and the ratios/ceilings are exact
  arithmetic. This part is actual arithmetic, not a source-C construction.
- S_bad(C) finite and nonempty is a standard bad-reduction fact; the source
  does not enumerate it. F_mod=Q gives alpha_p=1 in the template.
- B=O_K local residual values used in the attack are conditional finite
  formulas (corrected donor/basis), not actual target h_C values.

### 3.2 Conditional

- Every B=I statement: B=I b=3 surplus 12/41 log p, the local value 9/41,
  and all aggregate counts. B=I is not actual under the natural trace
  alignment; if the alignment fails, the coordinate v/full barGamma is
  uncomputed.
- Distinct-prime configurations, arbitrary-prime N=1, and per-p b_i=3,
  e_i=41 local data: abstract/conditional, not constructed for a C.
- Arch-adjusted counts use A as an upper bound; actual h_inf is unknown
  (and under the B_I-zero normalization the shell only gives h_inf<=log pi,
  not a lower bound). The N=30/3236/3201 counts require an actual h_inf at
  least 11.0253 or 11.7144, which is not proved to be attained.
- TC-A..TC-H and TC-S are missing for any target use.

### 3.3 Impossible / withdrawn

- Under the inferred natural trace alignment, B=O_K, so B=I aggregate
  compensation is impossible *conditionally on that inference*. This is not
  an unconditional impossibility; a failed alignment could allow B=I.
- Fixed-p counts N=3241 etc. at p=12301 cannot all be realized in one C
  because the same rational prime cannot occur as multiple bad places.
  The arbitrary-prime N=1 escape is abstract, not an actual C.
- Actual compensation from B=O_K, good places, Kummer zero, tensor order,
  permutations, Ind1/Ind2/Ind3 under the stated formulas: no positive
  contribution is available; this is conditional on the formula interfaces.

## 4. Can any actual source C realize the configuration?

No construction in the current corpus. The required data are exactly:

1. an actual complete C with enumerated S_bad(C) containing N distinct
   primes of the tame e=41, b=3 local type;
2. B=I at every one of those places, i.e. nonzero v_i in the trace-adapted
   mod-p basis (or the actual full barGamma moving O_K/J);
3. actual per-p local q-parameters/b_i and tensor-row multiplicities;
4. actual archimedean h_inf at least the residual left after the finite
   surplus;
5. TC-A..TC-H/TC-S for target containment.

None of 1-5 is constructed. Under the natural trace alignment, 2 fails for
all p (B=O_K), so no B=I aggregate exists. If the alignment fails, 2 is open
but still uncomputed; the count thresholds are then abstract arithmetic.
Thus the aggregate attack is a conditional upper-bound exploration, not a
realized complete-C configuration and not a global counterexample.

## 5. What survives / what is withdrawn

Survivors:
- exact S(p), D3, D273, DB, A, ratios and ceilings above;
- 5/34/3241/3206 and arch ceilings 30/3236/3201 (with the N=34 strictness
  caveat and the actual-h_inf condition);
- threshold values/log10; distinct-prime product criterion;
- the qualitative fact that fixed-p counts are impossible for one C and
  that arbitrary-prime counts are abstract;
- the conclusion that no actual aggregate B=I C is constructed.

Withdrawn/corrected:
- treating N=34 as strict closure (needs N>=35 or h_inf>0);
- treating 'B=I impossible' as unconditional rather than conditional on the
  inferred trace alignment;
- treating arbitrary-prime N=1 as an actual realized bad set;
- treating A as an attained archimedean value rather than an upper bound;
- any use of B=I counts as target-containment or global closure without
  TC-A..TC-H/TC-S.

## 6. Status

Stage1 verification only. No new attack, no Lean/Project edits. Lean/Project/
kernel/comparator/independent review not run. Complete C9/P6 not proved;
target_accepted=false.
