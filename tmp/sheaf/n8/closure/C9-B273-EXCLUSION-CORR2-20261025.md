# C9 b=273 exclusion correction 2: F<=D-h_inf, no no-go

Task: task-281. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits, no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Corrected file

This corrects C9-B273-EXCLUSION-20261025.md (task-279), 74 lines,
SHA256 e792e271b440ca0f65908e7de943ce109f47c90ac0c1dd399e52a42a93bbce9f.

Task-279 parts (a) and (b) are correct: the b=273 E_{546} skeleton is
admissible at source-skeleton level, E1 is not proved, and a complete C is not
constructed. Its part (c), the "conditional no-go" with margin >8800, repeats
the sign error corrected in task-264/E48 and is **retracted**.

## 1. Correct theorem

Let p=12301, e=41, and let C be a hypothetical admissible complete C with the
b=273 uniform profile. The C1 finite input is a **lower** bound:

    h_C >= sum_p alpha_p H_p + h_inf.                              (1.1)

Therefore

    F = Q_C-h_C <= sum_p alpha_p(Q_p-H_p) - h_inf = D-h_inf.       (1.2)

This is an **upper** bound on F, not a lower bound. For the b=273 branches:

    B=O_K: H_A=-(39156/41)log p, Q_p=-(273/41)log p,
           D_A=(38883/41)log p=8931.174578603...,
           F <= 8931.174578603 - h_inf;                           (1.3)
    B=I:   H_B=-(38736/41)log p,
           D_B=(38463/41)log p=8834.703284644...,
           F <= 8834.703284644 - h_inf.                           (1.4)

The arch bound h_inf<=A_proc=11.5log pi=13.164393687... gives

    D_A-h_inf >= D_A-A_proc = 8918.010184... >0,
    D_B-h_inf >= D_B-A_proc = 8821.538890... >0.                  (1.5)

But these are lower bounds on the **upper bound** of F. They do not imply
F>=8918 or F>=8821, and do not imply F>0. F may be negative if h_C is larger
than the lower bound (1.1).

Thus task-279's (1.4)-(1.5) and “P6 false with margin >8800” are **invalid**.
The correct statement is only (1.2): F<=D-h_inf, with no sign conclusion.

## 2. Retraction

Theorem 2.1. The following are false as derivations and are retracted:

- “if complete C with b=273 and CFTH/TC/arch exists, then P6 is false with
  margin >8800”;
- “F_A-h_inf >= 8918” and “F_B-h_inf >= 8821”;
- “b=273 is a conditional P6 counterexample in both B branches”.

The valid conclusions are:

(a) E1 (no admissible b=273 C) is **not proved**; the E_{546} source skeleton
    passes Def3.1(a)-(c), q-order, 41-coprimality, and the exact mod41 check.
(b) A complete C with b=273 is **not constructed**; explicit C_F/C_K/V/epsilon,
    BPS/Theta/gluing/target, CFTH, arch h_inf, and TC remain missing.
(c) No P6 counterexample follows from the b=273 finite lower bound.

## 3. What would actually be needed

- For a **counterexample**, one needs an **upper** bound on h_C:
      h_C <= Q_C - epsilon
  (or TC equality giving h_C=H+h_inf on the nose). The current data give only
  lower bounds on h_C.
- For a **P6 proof**, one needs h_C>=Q_C. A sufficient condition is
      h_inf >= D_p = Q_p-H_p,
  the huge positive number (D_A=8931.17 or D_B=8834.70 for b=273). Under the
  IV arch bound h_inf<=A_proc=13.16, this is impossible (task-240). Thus the
  current finite lower-bound route neither proves nor refutes P6 for b=273.

## 4. b=3 comparison

The same correction applies:

    b=3 B=O_K: F <= 93.714971 - h_inf;   no counterexample;
    b=3 B=I:   F <= -S3 - h_inf, S3=2.756322...;
               h_inf>=-S3 is sufficient for P6, not iff.
                                                                    (4.1)

Task-254/256's b=3 "F>=80.55" is retracted for the same reason.

## 5. Exact decision

- b=273 source skeleton: **admissible**; E1 not proved.
- b=273 complete C: **not constructed**.
- b=273 P6 counterexample: **not proved**; task-279 part (c) retracted.
- b=273 P6 theorem: **not proved**.
- Only escape from a hypothetical no-go is irrelevant: there is no no-go;
  E2 remains the missing-input status, not a rescue from a false inequality.
- P6: open; no proof, no counterexample from current finite data.

## 6. Status

- Short correction theorem/proof; no Lean/Project edits.
- Corrects task-279/E48 sign: F<=D-h_inf; no b=273 margin/no-go; no arbitrary
  data; target_accepted=false.
