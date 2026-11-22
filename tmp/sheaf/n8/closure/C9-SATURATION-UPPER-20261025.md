# C9 saturation upper bound h_C<=max(H_A,H_B)+h_inf: exact obstruction

Task: task-290. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits, no arbitrary enlargement.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-TARGET-EXTRA-NEW-20261025.md (task-285), 130 lines,
  SHA256 a5356db164e2cbf62f8382dd5a9574ed587a73aff1bdc90efa15974ed8668dfd.
- C9-TAME-LOG-DOMAIN-20261025.md (TAME), 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- C9-B273-EXCLUSION-CORR2-20261025.md (task-281), 104 lines,
  SHA256 cb97f6cff3acf9f31cdba954074920daa7ba731363b35fc5e887eb11af014d93.
- C9-ARCH-HULL-20261025.md (task-240), 134 lines,
  SHA256 e2a12e952811c21959fb61e9308a40ae7b1b5d6c5916d6aed4abc1920dd45ce7.

Convention: P6 is h_C>=Q_C, F=Q_C-h_C<=0. B_I-zero arch bound
h_inf<=A_proc=11.5log pi=13.164393687.

## 1. What the saturation hypothesis would give

Desired saturation upper bound:

    (SAT) h_C <= max(H_A,H_B)+h_inf.                               (1.1)

For b=273:

    H_A=-(39156/41)log p,
    H_B=-(38736/41)log p,  H_B>H_A,
    max=H_B,  D_B=Q_p-H_B=(38463/41)log p=8834.703284644....       (1.2)

If (SAT) holds, then

    F=Q_C-h_C >= Q_p-H_B-h_inf = D_B-h_inf.                       (1.3)

Using h_inf<=A_proc:

    F >= D_B-A_proc = 8821.538890... >0.                           (1.4)

Thus (SAT) plus the arch bound would be a genuine b=273 P6 counterexample.
This is the correct **upper-side** condition; it is exactly what the earlier
lower-bound arguments lacked.

## 2. What the source actually proves

TAME §6 gives a classification of the actual subfamily obtained from the
Gaussian integral region, the full per-factor Gamma action, and factor
permutations, for a fixed all-bad r-tuple:

    B=O_K: L_A=Σ_i p^s pi_i D_r;
    B=I:   L_B=p^{s-r+1}J^{tensor r};                              (2.1)

with normalized row heights

    nu_A/log p=-s-1/e,   nu_B/log p=-s+(r-1)-r/e.                 (2.2)

The classification says there is no third lattice **inside this listed
subfamily**; repeated same-type automorphisms do not produce a new lattice.
Task-285 correctly adds that mixtures of rows are convex, so the maximal
mixture in the subfamily is all-B=I, with extra

    Delta_B=H_B-H_A=(420/41)log p=96.471293959... .                (2.3)

But TAME §6 also states explicitly that this exact classification is only for
the listed actual subfamily and is **not an upper bound for the entire C output
family** (log/Theta/infinity outputs). The row heights (2.2) are source-row
hull values used for **lower** bounds h_C>=nu+h_inf, not upper bounds.

Therefore the source proves at most

    h_C >= H_A+h_inf,  h_C >= H_B+h_inf,  h_C >= max(H_A,H_B)+h_inf, (2.4)

which is a **lower** bound. It does not prove (1.1).

## 3. Exact obstruction

The implication (SAT) requires an upper-side statement not present in the
source. The missing statements are:

(S1) **R_A subset R_B** (or the B=I row hull contains the B=O_K row hull) for
     the actual source regions. The lattices L_A and L_B in (2.1) are not shown
     nested. Their normalized heights differ by Delta_B>0, but a volume
     difference does not imply inclusion; no source theorem gives L_A⊂L_B.

(S2) **Target possible-image hull generated exactly by the B=I rows.** The
     target H_C may contain other local types, good places, archimedean
     regions, aggregate B=I contributions, or other source q/BPS classes.
     TAME §6 explicitly disclaims being an upper bound for the whole C output
     family. Without this, the target hull can be larger than the B=I row hull,
     and (SAT) fails.

(S3) **No other positive finite compensation.** The master file already lists
     other-local Delta_shell, aggregate B=I, good weights, and unknown local
     types as unconstructed/conditional. None is bounded above by (SAT).

(S4) **TC equality/volume preservation.** The target container gives only the
     arch upper bound h_inf<=A_proc and lower containment TC-B for source
     regions. It does not give h_C<=max row hull+h_inf; TC equality is not
     proved.

Because S1-S4 are missing, (SAT) is not a source theorem. It is a
**conditional sufficient condition** for a b=273 counterexample, not an
established upper bound.

## 4. Could the row lattices be nested?

The TAME lattices are

    L_A=Σ_i p^s pi_i D_r,   L_B=p^{s-r+1}J^{tensor r}.             (4.1)

The B=I height is larger by Delta_B=(r-1)(1-1/e)log p. Larger normalized
height does not imply L_A⊂L_B. Even if a particular tensor model had
L_A⊂L_B, the target hull could contain both source branches plus other
regions; inclusion of two row lattices would only show their union hull has
volume max(nu_A,nu_B), not that all of H_C is bounded by it.

No source theorem states R_A⊂R_B, and the exact obstruction is precisely this
missing inclusion/target-saturation statement.

## 5. Conditional theorem (correct direction)

Theorem 5.1. If (SAT) holds for an admissible complete C with the b=273
profile and h_inf<=A_proc, then

    F>=D_B-A_proc=8821.538890...>0,                               (5.1)

so P6 is false for that C.

Proof. h_C<=H_B+h_inf gives F>=D_B-h_inf; h_inf<=A gives
D_B-h_inf>=D_B-A; evaluate. QED.

Theorem 5.1 is conditional on (SAT), which is exactly the missing upper bound.
It is not a source theorem.

## 6. What would repair the b=273 upper side

A proof of (SAT) would need one of:

(A) a source inclusion R_A⊂R_B and a proof that target H_C is the hull of the
    B=I source region alone;
(B) an independent upper bound on every other source region/local type/good
    contribution, showing none exceeds max(H_A,H_B)+h_inf;
(C) a target-saturation/TC equality theorem giving h_C=max(H_A,H_B)+h_inf;
(D) a direct upper bound h_C<=H_B+h_inf from the actual target construction.

None is in the frozen corpus. Without one, b=273 has no upper side and no
P6 counterexample; the lower bounds only give F<=D-h_inf (task-281).

## 7. Classification

| item | status |
|---|---|
| (SAT) h_C<=max(H_A,H_B)+h_inf | NOT PROVED |
| (SAT)+arch => b=273 P6 false F>=8821 | PROVED conditional |
| TAME §6 classification of subfamily | CONDITIONAL/INFERRED |
| TAME §6 is upper bound for whole C | FALSE; explicitly disclaimed |
| R_A⊂R_B | NOT PROVED |
| target generated by B=I rows | NOT PROVED |
| other local/good/aggregate bounded | NOT PROVED |
| b=273 upper-side counterexample | NOT OBTAINED |
| b=273 lower bound F<=D-h_inf | PROVED (task-281) |

## 8. Conclusion

The saturation upper bound (SAT) would be decisive: with the arch bound it
would give a b=273 P6 counterexample with margin 8821. But it is not a source
theorem. TAME §6 classifies only the actual all-bad subfamily and explicitly
does not bound the entire C output family; it gives lower row heights, not an
upper target hull. R_A⊂R_B is not proved; the target hull may contain other
local/good/arch/aggregate regions; TC equality is missing. Therefore the
b=273 upper side remains open: (SAT) is a conditional sufficient condition,
not an established bound. The correct unconditional inequality remains
F<=D-h_inf (task-281), with no P6 counterexample.

No arbitrary enlargement; no Lean/kernel closure; target_accepted=false;
P6 open.

## 9. Status

- Short natural-language theorem/obstruction only; no Lean/Project edits.
- Saturation upper bound conditional theorem and exact obstruction recorded;
  no b=273 counterexample.
- target_accepted=false.
