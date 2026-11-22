# C9 P6 sign audit: +80.55 is a counterexample, not positivity

Task: task-254 (Critical sign audit: check whether B=O_K b=3 F=+80.55
is a P6 counterexample rather than positivity; audit task-245/252 sign
conventions and state truth dichotomy). Owner: volumedet. Date: 2026-10-25.
Stage1 natural-language/exact-arithmetic audit only. No arbitrary data, no
Lean/Project/target edits. Only this file written. `target_accepted=false`.

Inputs:

- `C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md` (task-245);
- `C9-NEW-ARAKELOV-POSITIVE-20261025.md` (task-252);
- `C9-NEGATIVE-GLOBAL-20261025.md` (task-239, sign-adjacent);
- C9-GLOBAL-ASSEMBLY-CORRECTED2, C9-ARCH-NORMALIZATION-CORRECTION,
  C9-UNIFORM-HULL, C9-AGGREGATE-BI, C9-ARCH-SHELL-ATTACK.

## 0. Verdict

With the correct convention

    F(C) := Q_C - h_C,

the P6 target `h_C >= Q_C` is equivalent to

    F(C) <= 0,   not F(C) >= 0.                         (0.1)

Therefore the b=3 B=O_K value

    D_3 = Q_p-h_A = (408/41) log 12301 = 93.7149712746...,
    F >= D_3 - A = 80.5505775873... > 0                 (0.2)

is a **conditional P6 counterexample**, not positivity and not a proof of
P6. Task-245 labels this positive F a 'conditional positivity theorem' and
concludes 'P6 holds'; that is a sign inversion. The correct reading is:

    if the B=O_K b=3 profile and target hypotheses are actual,
    then h_C < Q_C (by at least 80.55), so P6 is FALSE for that C.

Task-252 has the correct line-bundle orientation (`deg L_diff=h_C-Q_C`,
negative at b=3 B=O_K); its conclusion 'no positive term on current
L_diff' is consistent. But the downstream interpretation must be stated
explicitly: the negative degree is a counterexample direction, not a
positivity gap to be filled by an Arakelov section.

## 1. Correct sign convention

Fix the source normalization and the target container. Define

    Q_C = native q-pilot global normalized log-volume,
    h_C = normalized log-volume of the final target holomorphic hull,
    F(C) = Q_C-h_C.                                     (1.1)

Then:

- `F(C)>0` means `Q_C>h_C`, i.e. the target inequality `h_C>=Q_C` FAILS:
  C is a counterexample.
- `F(C)=0` is the boundary; `F(C)<0` means `h_C>Q_C`: P6 holds for C.

The finite/arch decomposition in the uniform profile is

    F(C)=sum_p alpha_p (Q_p-h_p) - h_inf(C) + good/other terms,

with F=Q-h at the global level. There is no sign change in passing from
local to global: `Q_C-h_C` is the same sign.

## 2. Task-245: corrected sign table

Task-245 uses F=Q_C-h_C but then asserts 'P6 asserts F>=0' and treats
positive F as positivity. That is inverted. Corrected classifications:

| case | F value | correct meaning | task-245 label |
|---|---|---|---|
| B=O_K, b=3 | F>=D_3-A=80.55>0 | conditional P6 counterexample | 'positivity; P6 holds' (WRONG) |
| B=I, b=3, h_inf>-S_3 | F=-S_3-h_inf<0 | P6 holds locally | 'genuine counterexample' (WRONG) |
| B=I, b=3, h_inf<-S_3 | F>0 | counterexample | 'positivity/no counterexample' (WRONG) |
| B=I, b=3, h_inf=-S_3 | F=0 | boundary | not a counterexample |
| B=I, b=273 | F=(38463/41)logp-h_inf>0 for h_inf<=A | conditional counterexample | 'positivity holds' (WRONG) |
| B=O_K, b=273 | F=(38883/41)logp-h_inf>0 | conditional counterexample | 'even more positive' (sign misread) |

with

    S_3=(12/41)log12301=2.7563226845...
    A=11.5 log pi=13.1643936873...

### 2.1 B=O_K b=3

    Q_p=-3/41 log p, h_A=-411/41 log p,
    F=Q_p-h_A=408/41 log p=93.7149712746...,
    F-h_inf >= 93.7149712746-13.1643936873=80.5505775873>0.

Thus the aligned B=O_K b=3 profile is the **strongest known conditional
counterexample**, with margin at least 80.55 natural. It is not a positive
height theorem. Task-252's `L_diff` degree is `h-Q=-93.7` (with arch at most
`-80.55`), exactly the same counterexample sign.

### 2.2 B=I b=3

    Q_p=-3/41 log p, h_B=9/41 log p,
    F=-12/41 log p - h_inf = -S_3-h_inf.

- If `h_inf>-S_3`, then F<0: `h_C>Q_C`; P6 holds in this corridor.
- If `h_inf<-S_3`, then F>0: counterexample.
- At `h_inf=A`, F=-15.920716...<0: P6 holds, not a counterexample.

Task-245 reverses this corridor. Its B=I b=3 'counterexample' is actually
the P6-positive corridor when h_inf>-S_3; the 'no counterexample' case
h_inf<-S_3 is the counterexample case.

### 2.3 b=273

    B=O_K: F=38883/41 log p - h_inf >= 8918.01>0;
    B=I:   F=38463/41 log p - h_inf >= 8821.54>0.

Both are conditional counterexamples for any actual `h_inf<=A`; neither is
'positivity'.

## 3. Task-252 audit

Task-252 correctly sets

    L_diff=L_Theta tensor L_Q^{-1}, deg_Ar(L_diff)=h_C-Q_C.

At b=3 B=O_K,

    h_A-Q_p=-408/41 log p=-93.714971...,
    with arch h_inf<=A: degree <= -93.714971+13.164394=-80.550578<0.

Thus `L_diff` is negative; no effective/nef section exists; a positive
Arakelov cycle/Green term of degree 80.55 is not a term of the current
`L_diff`, and adding one proves `Q_C<=h_C+80.55`, not `Q_C<=h_C`.

This is correct orientation. The audit correction is terminological: the
negative degree is not merely 'P6 open' or a missing positivity gap; it is
the exact conditional counterexample direction. If the current conditional
inputs were actual, `L_diff` would have negative degree and P6 would fail.

## 4. Truth dichotomy

For the b=3 B=O_K aligned profile there are exactly two logical
possibilities:

(A) **Conditional counterexample branch.** A complete admissible C
    realizes the B=O_K aligned finite formula, the IV archimedean container
    bound, and the target-container/normalization conditions. Then
    `F=Q_C-h_C>=80.55>0`, so `h_C<Q_C`; P6 is FALSE for that C. This is a
    genuine counterexample, not a positivity theorem. It would refute P6.

(B) **No actual realization branch.** For every complete C, at least one of
    the conditional inputs fails: B=O_K is not the actual branch (B is
    type-gapped/undetermined, or B=I), the finite D_3 formula is not a
    target theorem, the archimedean container bound/normalization does not
    apply as a target inequality, the target hull/TC-A..H/TC-S fail, or no
    complete C is constructed. Then the profile-level `F=80.55` is only a
    conditional scenario; no actual counterexample follows, and P6 remains
    open.

There is no third possibility in which `F=+80.55` is 'positivity'. The
sign is fixed: positive F is failure of P6.

Similarly, for B=I b=3:

- `h_inf>-S_3` gives F<0: P6 holds for that C;
- `h_inf<-S_3` gives F>0: P6 fails;
- boundary F=0.

The B=I branch is unproved/type-gapped, so this corridor does not decide
P6 either.

## 5. Consequences for downstream claims

1. Any statement of the form 'B=O_K b=3 gives positivity' must be replaced
   by 'conditional counterexample with margin 80.55'.
2. Any statement that B=I b=3 F<0 is a counterexample must be replaced by
   'P6 holds in that corridor'; the counterexample corridor is F>0
   (h_inf<-S_3).
3. b=273 B=O_K and B=I are conditional counterexample directions, not
   positivity.
4. Task-252's negative `L_diff` is consistent; a 'positive Arakelov term'
   cannot exist on the current b=3 B=O_K object. Adding one changes the
   target inequality to `Q<=h+80.55`.
5. The actual E_j/alternative-E profiles do not supply a complete C, B
   branch, or h_inf; they do not decide between (A) and (B).
6. No arbitrary auxiliary cycle/height can be used to convert the
   counterexample into a positivity theorem; that would change the object.

## 6. Proved / conditional / impossible

PROVED (exact algebra under the stated profile formulas):

- Sign convention: P6 <=> F=Q_C-h_C<=0; positive F is a counterexample.
- b=3 B=O_K: F>=80.5505775873>0, hence conditional counterexample.
- b=3 B=I: F=-S_3-h_inf; F<0 iff h_inf>-S_3; F=-15.9207 at h_inf=A.
- b=273 both known branches: F>8834 or 8918-h_inf >0; conditional
  counterexamples.
- Task-252: deg L_diff=h-Q=-80.55 after arch; no effective section; a
  positive term proves Q<=h+80.55, not P6.

CONDITIONAL:

- B=O_K/B=I branch actuality, finite D_3 formula, target/TC conditions,
  actual archimedean h_inf, complete C.
- The dichotomy (A)/(B); no decision in corpus.

IMPOSSIBLE/WITHDRAWN:

- 'B=O_K b=3 F=+80.55 is positivity / proves P6' (sign inversion).
- 'B=I b=3 F<0 is a counterexample' (sign inversion).
- 'b=273 F>0 is positivity' (sign inversion).
- A positive Arakelov term on the current negative L_diff.
- Any unconditional P6 proof or unconditional counterexample from profile
  data.

OPEN/MISSING:

- actual complete C and B branch (H_A-full/full barGamma);
- actual finite donor/target/TC conditions and archimedean h_inf;
- decision between branch (A) counterexample and branch (B) no realization;
- global P6.

## 7. Conclusion

`F=Q_C-h_C=+80.55` for the b=3 B=O_K profile is a **conditional P6
counterexample**, not positivity. Task-245 systematically inverts the
sign: its 'positivity' F>0 is a counterexample direction, and its B=I
'counterexample' F<0 is the P6-holding corridor. Task-252's line-bundle
orientation is correct: `deg L_diff=h-Q` is negative, no positive
section/cycle exists on the current object, and adding a +80.55 term would
prove a different inequality `Q<=h+80.55`.

The truth dichotomy is therefore: either the B=O_K aligned profile and the
target/TC/arch inputs are actual, in which case P6 is false with margin
80.55; or at least one conditional input fails for every actual C, in which
case no counterexample is proved and P6 remains open. No third 'positivity'
reading exists. No actual complete C decides the dichotomy in the current
corpus.

## 8. Status

Stage1 sign audit/exact arithmetic only. No arbitrary data, no Lean/Project
edits. Only this file written. `target_accepted=false`; P6 open; no
genuine counterexample constructed.
