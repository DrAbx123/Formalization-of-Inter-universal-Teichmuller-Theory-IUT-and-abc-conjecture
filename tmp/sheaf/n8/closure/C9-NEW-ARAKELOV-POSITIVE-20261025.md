# C9 new source theorem: positive Arakelov cycle/Green term

Task: task-252 (New source theorem: positive Arakelov cycle/Green term).
Owner: volumedet. Date: 2026-10-25. Stage1 natural-language theorem/
construction attempt only. No arbitrary auxiliary height/divisor, no
Lean/Project/target edits. Only this file written. `target_accepted=false`.

Inputs: C9-NEW-ARAKELOV-LINE-20261025.md, C9-NEW-HEIGHT-FALTINGS-20261025.md,
C9-GLOBAL-ASSEMBLY-CORRECTED2, C9-ARCH-NORMALIZATION-CORRECTION,
C9-FULLC-WEIGHTS-ATTACK, C9-NEGATIVE-GLOBAL, C9-EJ-COMPLETION,
C9-MOD41-EXACT-G.

## 0. Verdict

Let

    L_diff := L_Theta tensor L_Q^{-1},   deg_Ar(L_diff)=h_C-Q_C.   (0.1)

The proposed positive cycle/Green term of degree at least +80.55 on
L_diff is **not source-constructible** in the current corpus, and in the
b=3 B=O_K profile it is arithmetically impossible as a term of L_diff:

- b=3 B=O_K local values: Q_p=-3/41 log p, h_A=-411/41 log p, so
  `h_A-Q_p = -408/41 log p = -93.714971...`.
- The archimedean upper bound is A=13.164394..., so even after the maximal
  archimedean Green contribution the current degree is at most
  `-80.550578...`.
- An effective/positive cycle or a nonzero section of controlled norm on
  L_diff would force `deg L_diff>=0`, contradicting this bound. A positive
  term of degree +80.55 would make the degree zero only after being added;
  the resulting inequality is `Q_C <= h_C+80.55`, not `Q_C<=h_C`.

Thus the only way to obtain the proposed theorem is to add a new positive
line bundle/cycle/Green term not present in the current h_C. That is a new
source input, not a consequence of theta/BPS/Theta-gluing; without it no
such term exists.

## 1. Orientation and current degree

P6 is `h_C>=Q_C`, i.e. `deg_Ar(L_diff)>=0` for (0.1). For the b=3 B=O_K
profile (conditional finite donor, p=12301, e=41):

    Q_p=-3/41 log p = -0.689... (natural),
    h_A=-411/41 log p = -94.404... (natural),
    h_A-Q_p=-408/41 log p = -93.71497127459669...,          (1.1)
    h_inf<=A=(l+5)/4 log pi=13.164393687268102...,
    max current degree = -93.7149712746+13.1643936873
                        = -80.5505775873... <0.            (1.2)

These are the same residual values as in the negative-global/height notes.
At b=273 the negative degree is far larger; b=3 is already the best case.

Therefore, on the current L_diff, an effective/positive term of degree
at least +80.55 cannot exist: it would raise the degree to at least 0 while
the archimedean bound caps it below 0. This is a sign/degree obstruction, not
a missing estimate.

## 2. Candidate source terms and why they fail

### 2.1 Theta divisor

The theta divisor D_Theta is the natural effective cycle on the Theta-pilot
side. On an elliptic curve a theta divisor has degree 1 (a point), and its
arithmetic degree is a Faltings-type height, not a free +80.55. Its
self-intersection/Hodge-index positivity is quadratic, not a linear positive
term of prescribed size. Taking a large multiple `n D_Theta` would add
`n`-dependent degree, but the coefficient `n` is an arbitrary auxiliary
choice and the object is no longer the target L_diff; this is forbidden by
the no-arbitrary-divisor rule.

### 2.2 BPS/Theta-gluing

BPS/Theta-gluing supplies local finite volume data/transition and the
q-pilot/Theta identification. It does not supply a global effective section
of L_diff. The finite data already enter Q_C and h_C; the difference is the
negative degree (1.2). Re-reading the same gluing cannot add a new positive
80.55: if it did, it would change Q_C or h_C, i.e. the target object.

### 2.3 Archimedean Green functions

Under the binding B_I-zero normalization, the archimedean radial readout is
`h_inf=log r`, and the IV container upper bound is A=13.1643936873. Even the
maximal archimedean Green contribution is already included in (1.2) and leaves
-80.55. A Green function with a larger integral would require a different
metric normalization; rescaling a metric is arbitrary and changes the
Arakelov degree. The finite Green functions at good places are zero relative
to the reference.

### 2.4 Faltings/Theta height of E_j

E_j/Q gives an actual elliptic curve and a Faltings height, but no complete C
or target hull; the Faltings height is an auxiliary height of E_j, not the
C9 L_diff. Adding it to h_C is an arbitrary auxiliary height and is forbidden.
Even if positive, it is not identified with the C9 target column.

### 2.5 Principal divisors/global functions

A global principal divisor has arithmetic degree 0. It cannot supply +80.55.
An effective principal divisor is zero; a nontrivial principal divisor has
negative and positive parts whose total degree vanishes, so it cannot create
a net positive cycle.

### 2.6 Effective section of a modified bundle

If one tensors L_diff by a positive line bundle P of degree 80.55 and finds a
section of `L_diff tensor P`, one proves

    h_C + deg(P) - Q_C >=0,   i.e. Q_C <= h_C+80.55,       (2.1)

not P6. Restoring the original inequality would require P to be part of the
actual h_C; but then h_C changes, and the current target arithmetic (1.2) no
longer applies. This is the precise circularity: the needed positive term is
exactly the missing positivity/height.

## 3. Conditional theorem and its hypothesis

The only valid conditional statement is:

Theorem 3.1. Suppose there are canonical Hermitian line bundles M_C,N_C
on the compactified arithmetic C with

    deg_Ar(M_C)=h_C,  deg_Ar(N_C)=Q_C,  L_diff=M_C tensor N_C^{-1},

and a nonzero global section s of L_diff whose divisor is effective and
whose adelic norm is at most 1 (or L_diff is nef/effective in the Arakelov
sense). Then `deg_Ar(L_diff)=h_C-Q_C>=0`, hence P6.

Proof: arithmetic effectivity/positivity and degree additivity.

Status: this is a valid conditional theorem. Its hypothesis is not supplied:
the actual compactified C, the canonical metrics, the theta section, and the
norm control are missing. In the b=3 B=O_K profile its conclusion is false
for the current degree (1.2), so the hypothesis cannot hold for the current
L_diff. The theorem is therefore empty/conditional, not a source proof.

## 4. Why no positive term can be extracted from the current source

1. The current L_diff has degree at most -80.55 in the b=3 B=O_K profile.
   A positive cycle/section **of L_diff** would contradict that degree.
2. To get a positive term one must modify the bundle/metric/divisor. The only
   canonical modifications available are the theta divisor, BPS/Theta gluing,
   and the archimedean Green metric; each either gives degree zero/negative,
   is bounded by A, or is an arbitrary multiple/rescaling.
3. A finite-support effective cycle supported at bad places would require
   actual bad places and actual q-pilot/Theta divisors; the complete S_bad and
   target column are missing. E_j supplies only local data at p and D-primes,
   not a complete C.
4. Hodge index/adjunction give quadratic inequalities, not the required
   linear +80.55. They cannot bound the degree from below in the needed
   direction without an effective divisor.
5. A Green term with large positive integral is indistinguishable from a
   metric rescaling; the normalization is fixed by IV B_I-zero, and arbitrary
   rescaling is forbidden.

Thus the proposed positive Arakelov term is not a consequence of the source;
it is the desired positivity itself.

## 5. Branch dependence and b=3 test

The negative degree (1.2) is the **B=O_K aligned conditional** branch. Under
the B=I b=3 branch, h_B=9/41 log p and h_B-Q_p=+12/41 log p=+2.756..., so
L_diff has positive local degree and no +80.55 term is needed. But B=I is
conditional/type-gapped and not actual under the natural trace alignment;
b=273 B=I is still negative. A branch-independent positive-term theorem
would have to work for B=O_K too, where (1.2) forbids any effective term of
L_diff. Hence no branch-independent construction follows.

The b=3 test therefore says: compression/positivity of the current L_diff is
false by -80.55; a positive term of exactly that size is needed but absent.

## 6. Proved / conditional / impossible / open

PROVED (exact arithmetic/standard positivity):

- `L_diff=L_Theta tensor L_Q^{-1}` has degree h_C-Q_C.
- b=3 B=O_K: `h_A-Q_p=-408/41 log p=-93.714971...`; with arch A=13.164394,
  current degree is at most -80.550578... <0.
- Any nonzero effective/nef section of the current L_diff would force degree
  >=0; hence none exists in this profile.
- A global principal divisor has degree 0; a positive multiple of theta or an
  arbitrary Green rescaling is a different/arbitrary object, not L_diff.

CONDITIONAL:

- Theorem 3.1 (conditional Arakelov positivity): valid but its hypothesis
  (canonical L_diff, effective theta section/norm<=1, actual C/metrics) is
  missing.
- B=I b=3 branch gives positive local degree but is not actual/type-safe.

IMPOSSIBLE as source construction:

- a positive cycle/Green term of degree >=80.55 on the current b=3 B=O_K
  L_diff (would contradict its negative degree);
- deriving the positive term from theta/BPS/Theta-gluing alone;
- using an arbitrary auxiliary effective divisor, Faltings height, metric
  rescaling, or theta multiple;
- a branch-independent positivity theorem that ignores B=O_K.

OPEN/MISSING:

- actual complete C, compactified arithmetic curve, L_Q/L_Theta with
  canonical metrics;
- a genuine theta section/effective divisor with controlled norms and its
  degree identified with h_C-Q_C;
- actual B branch/H_A-full/TC-A..H/TC-S; actual archimedean hull;
- any source-derived positive term of the required size or a proof that none
  exists for all admissible C.

## 7. Conclusion

The program cannot construct the required +80.55 Arakelov term from the
current source. In the b=3 B=O_K profile the current L_diff has degree at
most -80.550578; a positive effective/nef term of L_diff is impossible, and
adding one changes the target inequality by exactly the missing amount.
The conditional Arakelov positivity theorem is valid but its section/
effective-cycle hypothesis is precisely the desired positivity. No arbitrary
auxiliary height or divisor is used, and no branch-independent positive term
is obtained. P6 remains open.

## 8. Status

Stage1 natural-language/exact-arithmetic theorem attempt only. No Lean/
Project edits. Only this file written. `target_accepted=false`; complete
C9/P6 not proved.
