# C9 logic correction: finite lower bound gives F<=, not F>=

Task: task-264. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits; no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. The error

Task-256 and task-254 derive P6 counterexamples from a **lower** bound

    h_C >= sum_p alpha_p H_p + h_inf                          (0.1)

and the identity F=Q_C-h_C. This is a sign inversion. From (0.1),

    F = Q_C-h_C <= sum_p alpha_p(Q_p-H_p) - h_inf = D - h_inf.   (0.2)

The inequality goes **downward**: a lower bound on h_C gives an upper bound on
F, not a lower bound. A positive upper bound for F does not prove F>0; F can be
negative if h_C is larger than the lower bound.

The correct direction is:

    h_C lower bound  =>  F upper bound;                          (0.3)
    h_C upper bound  =>  F lower bound (counterexample direction). (0.4)

No upper bound on h_C below Q_C is available. Therefore task-256 and task-254
do not prove P6 counterexamples.

## 1. Correct b=3 and b=273 formulas

Let p=12301, e=41, uniform one-bad profile. For the two recorded rows
(values used in task-254/256):

    b=3:
      Q_p=-(3/41)log p,
      H_A=-(411/41)log p,   D_A=Q-H_A=(408/41)log p=93.714971...,
      H_B=(9/41)log p,      D_B=Q-H_B=-(12/41)log p=-S3,
      S3=(12/41)log p=2.756322...
    b=273:
      Q_p=-(273/41)log p,
      H_A=-(39156/41)log p, D_A=(38883/41)log p=8931.174579...,
      H_B=-(38736/41)log p, D_B=(38463/41)log p=8834.703285...  (1.2)

Under (0.1):

    b=3 B=O_K:  F <= (408/41)log p - h_inf = 93.714971 - h_inf;
    b=3 B=I:    F <= -(12/41)log p - h_inf = -S3 - h_inf;
    b=273 B=O_K: F <= (38883/41)log p - h_inf = 8931.174579 - h_inf;
    b=273 B=I:  F <= (38463/41)log p - h_inf = 8834.703285 - h_inf. (1.3)

These are all **upper** bounds. The arch bound

    h_inf <= A_proc=11.5log pi=13.164393...                     (1.4)

gives, for example,

    b=273 B=O_K: F <= 8931.174579 - h_inf, and since
        h_inf<=A, the right side is >= 8918.010185 >0.           (1.5)

But the right side being at least 8918 does **not** imply F>=8918. It only
says F is at most a number which is at least 8918; F may be negative. No
counterexample follows.

## 2. Retraction theorem

Theorem 2.1 (retraction of task-256). The statement

    "b=273 B=O_K/B=I implies F>=8918/8821>0"

is FALSE as a derivation and is not proved by the stated inputs. The correct
statement is only

    F <= D_branch - h_inf,                                      (2.1)

which does not determine the sign of F.

Likewise task-254's b=3 claim

    "B=O_K b=3 implies F>=80.55>0"

is FALSE. The correct statement is

    F <= 93.714971 - h_inf,                                     (2.2)

whose right side is positive but does not prove F>0.

Task-254 correctly wrote P6 <=> F<=0, but then derived F>= from the lower
bound on h_C; that is the same inversion it was supposed to audit. The sign
audit itself is retracted.

## 3. What is actually true for the branches

### B=O_K b=3

Lower bound: h_C>=H_A+h_inf. Thus F<=93.714971-h_inf. Since h_inf<=A, the
upper bound is at least 80.55; no contradiction, no counterexample. If one had
the **upper** bound h_C<=H_A+h_inf, then F>=93.71-h_inf>=80.55, a conditional
counterexample; that upper bound is exactly what is missing.

### B=I b=3

Lower bound: h_C>=H_B+h_inf, so F<=-S3-h_inf. If h_inf>=-S3, then
F<= -S3-h_inf<=0, so P6 holds in this corridor. This is a **sufficient**
condition, not an iff. If h_inf<-S3, the upper bound is positive and F could
still be <=0; no counterexample follows. Task-256's claimed "counterexample
for h_inf<-S3" is invalid.

### B=O_K/B=I b=273

F<=D_branch-h_inf with D_branch=8931.17/8834.70. With h_inf<=A, the upper
bound is at least 8918/8821; positive but not a lower bound. No P6
counterexample. If h_inf>=D_branch, F<=0 and P6 holds; but D_branch>>A, so
the arch upper bound excludes this sufficient condition. P6 remains open.

## 4. Correct implication table

| branch | correct inequality | sign of F |
|---|---|---|
| b=3 B=O_K | F<=93.714971-h_inf | not determined |
| b=3 B=I | F<=-S3-h_inf | <=0 if h_inf>=-S3; else not determined |
| b=273 B=O_K | F<=8931.174579-h_inf | not determined |
| b=273 B=I | F<=8834.703285-h_inf | not determined |

P6 is F<=0. A lower bound on h_C cannot prove P6 (it gives F<=something,
which is compatible with F<=0 but not a proof) and cannot refute P6 (F may be
negative). A counterexample needs an **upper** bound h_C<=Q_C-epsilon.

## 5. Kappa correction

Task-250's kappa dichotomy remains a valid **branch** theorem:

    kappa<=0          => B=O_K;
    1<=kappa<=40      => B=I (with A=-I nonintegral);
    kappa>=41         => branch not well-posed inside I.

But it does **not** imply P6 false/true:

- kappa<=0 gives B=O_K, hence only the lower bound H_A and F<=D_A-h_inf;
  no P6 counterexample.
- 1<=kappa<=40 gives B=I, hence the lower bound H_B, not on the other side;
  for b=3 it gives F<=-S3-h_inf, so P6 holds if h_inf>=-S3; otherwise
  undetermined.
- kappa>=41 gives no branch.

Thus E47's labels "kappa<=0 => b=3 P6 false" and "1..40 => P6 holds if
h_inf>=-S3" must be corrected: the first is false; the second is a sufficient
condition, not automatic in the branch.

## 6. Consequence for E2/task-260

E2 (failure of CFTH/TC/arch) was introduced only to escape an alleged b=273
counterexample. Since the b=273 counterexample derivation is retracted, E2 is
no longer a P6-relevant escape. Task-260's conclusion that E2 is b-independent
may remain as a structural observation, but it has no counterexample to save.

Current P6 status:

- no P6 proof;
- no P6 counterexample from the finite lower bounds;
- no unconditional branch conclusion;
- P6 open.

## 7. What would actually decide P6

- **P6 proof:** h_C>=Q_C. Sufficient: h_inf>=D_branch (D_3=93.71,
  D_273=8931.17). But h_inf<=A=13.16 under IV, so this route is impossible
  for these b (task-240). Another source of upper/lower compensation or a
  different profile is needed.
- **P6 counterexample:** an **upper** bound h_C<=Q_C-epsilon. The current
  lower bounds and arch upper bound give no such upper bound on h_C.
- The missing object is still an actual complete C with actual h_C/h_inf, not
  a sign manipulation.

## 8. Status

- Short natural-language logic correction; no Lean/Project edits.
- Task-256 theorem retracted; task-254 sign audit retracted; E47 kappa-P6
  labels corrected.
- P6 remains open; no arbitrary data; target_accepted=false.
