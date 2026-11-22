# C9 uniform arch correction: b=3 B=O_K stays open

Task: task-323 (Correct uniform arch conclusion: no b=3 counterexample).
Owner: volumedet. Date: 2026-10-25. Short correction theorem/proof only. No
arbitrary data, no Lean/Project/target edits. Only this file written.
`target_accepted=false`.

## 0. Correction

`C9-UNIFORM-ARCH-20261025.md` stated that, because the archimedean lower
bound `h_inf>=D_3` is impossible under the IV container, the uniform b=3
B=O_K profile is a 'conditional counterexample with margin 80.55'. That
inference is WRONG. The corrected statement is:

    C1 gives an UPPER bound on F=Q_C-h_C, not a lower bound;
    h_inf<=A<D_3 makes that upper bound positive, not F positive;
    no counterexample follows, and b=3 B=O_K remains OPEN.

The 80.55 is the gap between the C1 lower bound on `h_C` and `Q_C`; it is
not a counterexample margin.

## 1. C1 and the direction of the inequality

Let

    F(C)=Q_C-h_C,   D_3=Q_C-H_A=408/41 log p=93.71497127459669...,
    A=11.5 log pi=13.164393687268102... .

C1 is the conditional lower bound

    h_C >= H_A+h_inf(C),                                      (1.1)

not an equality and not an upper bound. Subtracting from `Q_C`:

    F = Q_C-h_C <= Q_C-H_A-h_inf = D_3-h_inf.                 (1.2)

Thus C1 gives an **upper bound** on F. The archimedean container gives

    h_inf <= A.                                               (1.3)

Hence

    D_3-h_inf >= D_3-A = 80.55057758732859... >0.              (1.4)

But an upper bound whose value is positive does not imply `F>0`. It only
says `F<=U` with `U>=80.55`; F may be negative, zero, or positive.

Similarly, the C1 lower bound on h_C gives

    h_C >= H_A+h_inf,

which is **below** Q_C when `h_inf<D_3`; in particular `h_inf<=A<D_3` makes
the C1 lower bound insufficient to conclude `h_C>=Q_C`. That is exactly
what the arch impossibility says: C1 cannot prove P6 in this profile. It
does not say P6 fails.

## 2. Correct truth table

| branch | C1 lower bound h_C >= | P6 from C1 iff | counterexample from C1? |
|---|---|---|---|
| b=3 B=O_K | H_A+h_inf | h_inf>=D_3 | no (C1 is lower on h, upper on F) |
| b=3 B=I | h_B+h_inf | h_inf>=-S_3 | no |
| b=273 B=O_K | H_A+h_inf | h_inf>=38883/41 logp | no |
| b=273 B=I | H_B+h_inf | h_inf>=38463/41 logp | no |

with

    D_3=408/41 logp=93.714971...
    -S_3=-12/41 logp=-2.756322... .                           (2.1)

Consequences:

- b=3 B=O_K: `h_inf<=A<D_3`, so C1's lower bound is below Q; C1 cannot
  prove P6. There is no upper bound on h_C, so no counterexample either.
  The profile is OPEN.
- b=3 B=I: C1 proves P6 if `h_inf>=-S_3`; this arch lower bound is not
  proved. No counterexample follows. B=I is also conditional/type-gapped.
- b=273 B=O_K/B=I: required arch lower bounds are far above A; C1 cannot
  prove P6 in either branch. No counterexample follows. OPEN.

## 3. What the IV arch obstruction actually proves

Theorem 3.1. Under C1 and the IV container `h_inf<=A`:

(i) for b=3 B=O_K and both b=273 branches, the C1 lower bound is strictly
    below Q_C for every allowed h_inf<=A; hence C1 does not prove P6;
(ii) no counterexample follows from C1, because C1 bounds h_C from below
     and F from above, not the other way;
(iii) for b=3 B=I, C1 would prove P6 under the additional lower bound
      `h_inf>=-S_3`, which is not available;
(iv) all four branches remain logically OPEN (P6 neither proved nor
     refuted).

Proof. `F<=D_3-h_inf`; if h_inf<=A<D_3 then D_3-h_inf>=D_3-A>0, but this is
an upper bound on F. To prove P6 one needs F<=0, i.e. a stronger lower bound
h_C>=Q_C; C1 gives h_C>=H_A+h_inf<Q_C when h_inf<D_3. To prove a
counterexample one needs F>0, i.e. an upper bound h_C<Q_C or a lower bound
F>0; C1 supplies neither. For b=3 B=I the same computation with H_B gives
F<=-S_3-h_inf, which is <=0 when h_inf>=-S_3; that is a conditional P6 proof,
not a counterexample. QED.

## 4. Corrections to downstream files

- `C9-UNIFORM-ARCH-20261025.md`: the sentence 'b=3 B=O_K remains a
  conditional counterexample with F>=D_3-A=80.55' is WITHDRAWN. Correct:
  b=3 B=O_K is OPEN; 80.55 is the C1-vs-Q gap, not a counterexample margin.
- `C9-P6-SIGN-AUDIT-20261025.md` (task-254): the sign convention
  `P6 <=> F<=0` is correct, and 'positive F is a counterexample' is a true
  conditional implication. But the claim that b=3 B=O_K has `F>=80.55`
  (and hence is a conditional counterexample) is NOT proved: C1 gives
  `F<=D_3-h_inf`, an upper bound. The 'counterexample' label must be
  replaced by 'C1 cannot prove P6; status open'.
- `C9-NEW-ARAKELOV-POSITIVE-20261025.md` (task-252): its statement that the
  current `L_diff` has degree 'at most -80.55' also used C1 in the wrong
  direction. C1 gives a **lower** bound on h_C and hence a lower bound on
  deg L_diff, not an upper bound. The negative-degree/counterexample
  conclusion is withdrawn; the line-bundle orientation `deg=h_C-Q_C`
  remains correct. Status: open.
- `C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md` (task-245): both its
  'B=O_K positivity' and 'B=I counterexample' labels are sign-confused; the
  correct reading is: C1 alone cannot prove P6 in B=O_K; it proves P6 in
  B=I only under `h_inf>=-S_3`. No genuine counterexample is produced.

## 5. What would decide the branches

To prove P6 for b=3 B=O_K one needs either:

- a stronger lower bound `h_C>=H_A+h_inf+E` with `E>=D_3-h_inf` (in
  particular a positive finite/global term beyond C1), or
- a direct lower bound `h_inf>=D_3` (impossible under the IV container), or
- a target/other argument giving `h_C>=Q_C` independently.

To prove a counterexample one needs an **upper** bound `h_C<=Q_C-epsilon`
(or `F>=epsilon>0`), which C1 does not supply. The current corpus has
neither; hence OPEN.

## 6. Classification

PROVED:

- C1 direction: `h_C>=H_A+h_inf`; `F<=D_3-h_inf`.
- `h_inf<=A<D_3` makes the C1 lower bound below Q, so C1 cannot prove P6 for
  b=3 B=O_K (nor b=273).
- No counterexample follows; branch statuses OPEN.
- b=3 B=I: C1 gives P6 if `h_inf>=-S_3`; that lower bound is unproved.

CONDITIONAL:

- C1 assembly, B branch actuality, target/TC, actual h_inf.

WITHDRAWN:

- 'b=3 B=O_K F>=80.55 conditional counterexample'.
- 'b=273 F>0 counterexample' from C1.
- task-252's 'current L_diff degree at most -80.55'.

OPEN: all four uniform branches; P6 itself.

## 7. Conclusion

The corrected statement is: C1 gives `F=Q_C-h_C <= D_3-h_inf` (an upper
bound). Since `h_inf<=A<D_3`, this upper bound is positive (at least 80.55),
but F itself is not bounded below; no counterexample follows. Equivalently,
C1's lower bound on h_C is below Q, so C1 cannot prove P6 for b=3 B=O_K.
The b=3 B=O_K profile stays OPEN. The same applies to b=273. The b=3 B=I
branch would close under `h_inf>=-S_3`, which is not proved. No arbitrary
data and no mixed profile are used.

## 8. Status

Correction theorem/proof only. No Lean/Project edits. Only this file written.
`target_accepted=false`; P6 open.
