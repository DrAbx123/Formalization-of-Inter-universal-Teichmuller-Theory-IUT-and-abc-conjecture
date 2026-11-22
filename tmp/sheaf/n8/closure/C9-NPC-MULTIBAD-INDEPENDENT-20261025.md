# C9 independent multi-bad NPC extension including M-prime III*

Task: task-337 (Independent multi-bad NPC extension). Owner: volumedet.
Date: 2026-10-25. Short theorem/exact obstruction; uniform scope only; no
mixed/E3, no arbitrary data, no Lean/Project edits. Only this file written.
`target_accepted=false`.

## 0. Verdict

For the actual E_{546} multi-bad target, after the source semistabilization
F_sem the bad finite set is

    V_bad={p=12301} (split multiplicative I_546),
    M-primes: Kodaira III*, local degree4, become good on F_sem;
    2,3: additive, become good on F_sem;
    good finite places: normalized volume0.                       (0.1)

Thus the multi-bad finite target has no additional positive-volume finite
component: M-prime III* and 2/3 are good after F_sem (local reference O_E,
volume0), good places are zero, and the only nonzero finite bad component is
the p-row R_B. Under the single-bad row NPC hypothesis, the multi-bad target
satisfies volume-level NPC/U:

    H_C subset R_B+arch  (volume-wise),   h_C <= H_B+h_inf.       (0.2)

Consequently, conditionally on single-bad NPC/U and the semistabilization
zero-volume facts, b=273 gives

    F=Q_C-h_C >= (38463/41)logp-A = 8821.538890956...>0.          (0.3)

No explicit positive-volume uniform possible image outside R_B+arch was
constructed. The exact obstruction is the missing single-bad NPC/target-
exhaustion theorem plus the F_sem degree/semistabilization input. Pre-
semistabilization III* components cannot be inserted as positive target
volume without changing the target/normalization.

## 1. Multi-bad local data

E_{546}: y^2=x^3+(3/M)x+(2/M), M=1728p^{546}-1, j=1/p^{546}, v_p(Delta)=546.
The bad finite primes are the p=12301 place and the primes of M (plus 2,3);
the local data from the completed E_{546} skeleton:

| place | type | F_sem behavior | normalized finite contribution |
|---|---|---|---|
| p=12301 | I_546 split multiplicative | remains I_546 | B-row H_B |
| q|M | III* additive, local degree4 | becomes good | 0 (reference O_E) |
| 2 (good I0), 3 (additive I0*) | 2 good; 3 quadratic semistabilization | becomes good on F_sem | 0 (reference O_E) |
| other good | good | good | 0 |
| arch | h_inf | separate | h_inf<=A |

The M-prime III* claim is the exact local computation:
`(v(c4),v(c6),v(Delta))=(3,5,9)`, local semistabilization degree4. After the
quartic ramified extension the model has good reduction, so in the target
over F_sem its local normalized volume is zero relative to O_E. For E_{546}, 2 already has minimal good I0 and 3 has additive I0* with a
quadratic semistabilization to good. Their exact local types are recorded in
the E_{546} skeleton; only the good-reduction/zero-volume result is used here.

## 2. Why M-prime III* does not create a positive complement

Before F_sem, a III* fiber has extra components. But the target of the fixed
C is taken after the source semistabilization F_sem: M-prime and 2,3 are good
there. The normalized finite contribution of a good place is the reference
O_E, i.e. 0. The old additive components are not part of the target
normalized volume; inserting their Haar mass would be a different
normalization/target (not the C9 h_C), not allowed by no-arbitrary-data.

Thus the multi-bad places contribute zero to h_C beyond the p-row. They do
not enlarge R_B. This is the exact reason the multi-bad extension does not
produce a positive-volume NPC counterexample in the actual E_{546} target.

## 3. Other local types / wild places

If an additional bad place is not semistabilized (wild/e!=ell/other local
type), the current corpus has no positive absolute output volume:

- the restricted-shell absolute volume is
  `((n_exp-e)f/e)logp<=0`, equality only boundary;
- `Delta_shell=((n_exp-1)f/e)logp>=0` is a normalization shift, not an
  actual output-hull term; no source theorem inserts it into h_C;
- the tame B=O_K/B=I row formulas do not transfer to wild/e!=ell.

Such a place could at most add a nonpositive shell volume or an unproved
normalization shift; it is not a positive-volume possible image. Hence it
does not construct an NPC counterexample. It is an unknown branch, not a
counterexample.

## 4. Multi-bad NPC theorem

Theorem 4.1 (conditional multi-bad U/NPC). Assume:

(M1) the actual target is formed after F_sem and the M-prime III*/2,3 places
     have good reduction there (2 already good; 3 and M-primes semistabilized),
     hence local normalized volume0;
(M2) at the unique remaining bad place p the single-bad row saturation/NPC
     holds (all p-row possible images lie in R_B, volume-wise);
(M3) good finite places have volume0 and the archimedean component is h_inf;
(M4) the target hull is the hull of the full possible-image family with
     normalized-volume monotonicity (TC-B/TC-C).

Then every finite possible image has volume inside R_B; hence

    H_C subset R_B+arch  (volume-wise),   h_C <= H_B+h_inf.       (4.1)

For b=273, H_B=-8897.409625717..., A=13.164393687..., so

    h_C <= -8884.245232030...,   Q_p=-62.706341073...,
    F=Q_p-h_C >= 8821.538890956...>0.                            (4.2)

Proof. By (M1) the multi-bad places contribute0; by (M3) good places0 and
arch h_inf; by (M2) the only positive finite row lies in R_B; by (M4) the
hull volume is monotone, so h_C<=H_B+h_inf. The b=273 arithmetic is direct.
QED.

Status: conditional on M1-M4. M2 is the single-bad NPC and M1 the F_sem
good-reduction statement; neither is an unconditional source theorem in the
current corpus.

## 5. Positive-volume counterexample search

A counterexample would need a source-valid uniform possible image with
positive normalized volume outside R_B+arch. Checked candidates:

- M-prime III*: after F_sem good, volume0; before F_sem not a target volume
  in the C9 normalization (different object/normalization).
- 2 good, 3 additive I0* semistabilized: after F_sem good, volume0.
- good places: volume0.
- arch: h_inf, already in R_B+arch.
- other wild/e!=ell: shell volume<=0, Delta_shell not actual; no positive
  output formula.
- additional multiplicative B rows: not present in E_{546} (only p); for a
  different multi-bad C they would be new rows requiring their own NPC, not
  a constructed counterexample.
- mixed profiles: excluded E3; not uniform.

No positive-volume uniform counterexample is constructed. If one existed, it
would have to violate M1/M2: either an uncounted positive M-prime III*
component (excluded by the semistabilized good target) or a p-row image
outside R_B (single-bad NPC failure).

## 6. Exact obstruction

The multi-bad NPC/U is not unconditional. The exact missing inputs are:

1. M1: actual F_sem, semistabilization of M-prime III*/2,3 and normalized
   zero at those good places (the local type is computed; the global F_sem
   degree/actual model remains conditional);
2. M2: the single-bad p-row NPC/target-exhaustion theorem (the decisive
   missing upper side);
3. M4: actual target hull/TC-B/TC-C and normalized-volume monotonicity;
4. complete C/actual arch h_inf.

Without M2, a p-row possible image outside R_B would be a positive-volume
counterexample; none is constructed. Without M1, an M-prime III* component
could in principle be a positive-volume complement; after F_sem it is good
zero, so no such complement in the actual target.

## 7. Classification

PROVED/CONDITIONAL:

- E_{546} multi-bad local list: p I_546; M-prime III* degree4; 2,3 additive;
  after F_sem only p bad, others good volume0.
- Multi-bad theorem (M1-M4) => U/NPC and b=273 F>=8821.538890956.
- No positive-volume uniform counterexample constructed.

CONDITIONAL:

- M1 F_sem/semistabilization, M2 single-bad NPC, M4 target/TC/volume;
- actual complete C/arch.

IMPOSSIBLE/WITHDRAWN:

- claiming M-prime III*/2,3 add positive target volume after F_sem;
- using pre-semistabilization additive components as target volume without
  a normalization change;
- deriving unconditional NPC/U or unconditional b=273 counterexample from
  multi-bad data.

OPEN/MISSING:

- single-bad NPC/M2, F_sem degree, actual target/arch; global P6.

## 8. Conclusion

The multi-bad extension does not produce a positive-volume complement:
after F_sem the M-prime III* and 2,3 places are good with normalized volume0,
good places are zero, and the only finite bad row is p. Conditional on
single-bad NPC and the semistabilization facts, multi-bad U/NPC holds and
b=273 gives F>=8821.538890956. The exact obstruction is M2 (single-bad NPC)
plus M1/M4; no explicit positive-volume uniform counterexample exists in the
current corpus. No mixed/E3, no arbitrary region.

## 9. Status

Short theorem/obstruction only. No Lean/Project edits. Only this file written.
`target_accepted=false`; P6 conditional on NPC/U, otherwise open.
