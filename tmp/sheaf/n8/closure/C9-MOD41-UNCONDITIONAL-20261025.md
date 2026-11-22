# C9 mod-41 unconditional degree and GL2 theorem

Task: task-236. Date: 2026-10-25. Author: transport.
Stage: self-contained natural-language derivation/verification. No Lean/Project
edits. Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-FSEM-DEGREE-EXACT-20261025.md (task-234) | 171 | FFEDC1EE1912C97538AB13CB0409FC6DB4C186621BB015B084516B1DB1F46CC1 |
| C9-MOD41-EXACT-G-20261025.md (task-231) | 213 | 443A59656B1C1A7DDF3E921307FDFAE54BEAF50CDAF4542624AB3FD3A1B18ECC |

The task is to derive, from the exact degree data, that [F:Q] is 2,3-smooth
and 41-free, and then that the mod-41 image over F is exactly GL2(F41).
No U/W/B normalization is used.

## 1. Field notation

Let

    F0 = Q(i,E[6]),
    F_sem = semistabilization compositum for E_j,
    F = Q(i,E[6],F_sem) = F0 * F_sem.

Task-234 gives:

    F_sem = F_D * K3,
    F_D = Q(i, q_1^{1/4}, ..., q_4^{1/4}),
    [F_D:Q]=512,
    K3 is a quadratic p=3 semistabilization field,
    K3 in F0,
    [F_sem:Q]=1024.

Also [F0:Q] divides 2*|GL2(Z/6)|=2*288=576.

## 2. Degree bound

Theorem 2.1 (degree bound). The compositum F=F0*F_sem has

    [F:Q] <= 1024*576/2 = 294912 = 2^15 * 3^2.              (2.1)

In particular [F:Q] is 2,3-smooth and 41 does not divide [F:Q].

Proof. For finite extensions F0,Q and F_sem/Q inside a common algebraic
closure, the compositum degree is

    [F:Q] = [F0:Q][F_sem:Q]/[F0 cap F_sem:Q].               (2.2)

The intersection contains Q(i): i is in F0 by definition, and i is in
F_D subset F_sem (task-234). Therefore

    [F0 cap F_sem:Q] >= 2.                                 (2.3)

Using [F0:Q]|576, [F_sem:Q]=1024, and (2.3) in (2.2):

    [F:Q] <= 576*1024/2 = 294912 = 2^15*3^2.                (2.4)

Every prime divisor of [F:Q] divides the integer on the right, hence is 2 or
3. In particular 41 does not divide [F:Q]. QED.

### 2.1 Hidden-gap checks

(a) Intersection degree cannot be 1. Both F0 and F_sem contain i, so the
intersection contains Q(i), degree 2. The lower bound 2 used in (2.4) is safe.

(b) In fact the intersection may be larger than Q(i). Task-234 has
K3 subset F0, while K3 subset F_sem, and i is in both. Thus the intersection
contains Q(i,K3), which is Q(zeta_12) of degree 4 (for either quadratic
K3=Q(sqrt(3)) or Q(sqrt(-3))). If the intersection has degree at least 4,
then the bound improves to

    [F:Q] <= 576*1024/4 = 147456 = 2^14*3^2,                (2.5)

which is still 2,3-smooth. Using only 2 is conservative and cannot introduce
a hidden prime.

(c) The p=3 quadratic is absorbed in F0. This does not invalidate the
compositum formula: F_sem still has its degree-2 factor, and the intersection
F0 cap F_sem contains that factor (and i). The formula (2.2) accounts for it
through the denominator. Equivalently, since K3 subset F0 and i in F_D, one
may write F=F0*F_D with [F_D]=512; the bound then is even smaller. The
conclusion is unchanged.

(d) F_sem is taken as the compositum of the local Galois closures (M_q for
the D-part, quadratic K3, and 2,3 semistabilization). Hence F_sem/Q and
F0/Q are Galois, and F/Q is Galois. This is used for normality of H in
Section 3; if one used a non-Galois semistabilization field, F should be
replaced by its Galois closure and the degree bound would need rechecking.
The task-234 exact description supplies the Galois closures.

(e) The exact integer [F:Q] is not computed. The proof only needs the upper
bound (2.4); upper bounds are preserved when the true intersection is larger.
There is no hidden gap in the 2,3-smooth or 41-free conclusion.

## 3. Mod-41 image H and GL2

Let

    G = image(G_Q -> GL2(F_41)),
    H = image(G_F -> GL2(F_41)).

Task-231 proves:

(G1) G=GL2(F_41), |G|=2,755,200, using the corrected l=37 and l=127 classes
     for SL2 containment and the l=7 class (determinant of order 40) for full
     determinant;
(G2) F/Q is unramified at 41, hence F cap Q(zeta_41)=Q and the determinant
     character is still surjective on G_F; det(H)=F_41^times.

We also use:

(G3) F/Q is Galois, so H is normal in G and G/H is a quotient of Gal(F/Q);
     [G:H] divides [F:Q].

The last divisibility also follows directly from G_F subset G_Q and the
index formula, so it does not require a separate normality argument.

Theorem 3.1 (SL2 in H). SL2(F_41) subset H.

Proof. Suppose not. Then

    K = H cap SL2(F_41)

is a proper normal subgroup of SL2(F_41). Since PSL2(F_41) is simple for
p=41>=5, the proper normal subgroups of SL2(F_41) are 1 and {+-I}. Hence

    [SL2(F_41):K] is either 68,880 or 34,440.

The quotient SL2(F_41)/K embeds in G/H: the map s -> sH has kernel K. Thus
[G:H] is divisible by 68,880 or 34,440.

But [G:H] divides [F:Q] by (G3), and [F:Q] is 2,3-smooth by Theorem 2.1.
Both 68,880 and 34,440 contain the prime 5 (indeed 7 and 41 too), so [G:H]
cannot divide a 2,3-smooth integer. Contradiction. Hence SL2(F_41) subset H.
QED.

Theorem 3.2 (H=GL2). H=GL2(F_41), |H|=2,755,200.

Proof. By (G2), det(H)=F_41^times. Let h in GL2(F_41). Choose g in H with
det(g)=det(h). Then det(g^{-1}h)=1, so g^{-1}h in SL2(F_41) subset H by
Theorem 3.1. Therefore h=g(g^{-1}h) in H. Thus GL2(F_41) subset H; the reverse
inclusion is by definition, so H=GL2(F_41). The order is 2,755,200. QED.

## 4. What is used and what is not

Used:

- task-234 exact [F_sem:Q]=1024, [F0:Q]|576, i in F0 cap F_sem;
- task-231 exact G=GL2, determinant full over F, F unramified at 41;
- simplicity of PSL2(F41) and Dickson's classification (standard group theory).

Not used:

- U=<y1>, W=ker Tr, H_A-full, or a B=O_K/B=I branch;
- any arbitrary normalization of 1 or of the H action;
- LMFDB/Cremona data;
- any complete-C or target-containment assumption.

## 5. Classification

| statement | status |
|---|---|
| [F_sem:Q]=1024 | EXACT/GIVEN task-234 |
| [F0:Q] divides 576 | EXACT/GIVEN |
| F0 cap F_sem contains Q(i), degree >=2 | EXACT |
| [F:Q] <= 294912=2^15 3^2 | PROVED here |
| [F:Q] 2,3-smooth, 41-free | PROVED here |
| sharper bound <=147456 if intersection contains K3 | PROVED (optional) |
| F/Q Galois | CONDITIONAL on task-234 Galois closures; stated |
| G=GL2(F41) over Q | GIVEN task-231 exact |
| det(H)=F41^times | GIVEN task-231 |
| SL2(F41) subset H | PROVED here |
| H=GL2(F41), |H|=2,755,200 | PROVED here |

## 6. What remains for C9/P6

This theorem settles the degree and mod-41 image part:

    [F:Q] is 2,3-smooth and 41-free,
    H=image(G_F)=GL2(F_41) exactly.

It does not construct a complete C, does not resolve H_A/B, does not prove
target containment TC-A..TC-H/TC-S, does not compute the archimedean radius,
and does not prove P6. The remaining construction gaps are unchanged.

## 7. Conclusion

From the exact semistabilization degree [F_sem:Q]=1024 and the bound
[F0:Q]|576, with F0 cap F_sem containing Q(i), the compositum formula gives

    [F:Q] <= 1024*576/2 = 294912 = 2^15*3^2.

The bound is valid without knowing the exact intersection; a larger
intersection only decreases the degree. Hence [F:Q] is 2,3-smooth and
41-free. Combined with the exact G=GL2 and determinant-full-over-F results,
the SL2-transfer applies and

    H = image(G_F) = GL2(F_41),   |H| = 2,755,200.

No U/W/B normalization is used. P6 remains open.

target_accepted=false.
