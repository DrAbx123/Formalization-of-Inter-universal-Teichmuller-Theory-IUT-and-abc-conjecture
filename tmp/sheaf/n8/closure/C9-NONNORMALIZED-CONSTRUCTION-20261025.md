# C9 normalization-independent construction theorem

Task: task-228. Date: 2026-10-25. Author: transport.
Stage: self-contained natural-language theorem/proof. No Lean/Project edits.
Only this file written. target_accepted=false.

Inputs:

| file | lines | SHA256 |
|---|---:|---|
| C9-CONSTRUCT-KCK-20261025.md | 173 | E250D5C545AC6F152275B0FC9EC0E4966FF2917318D01B4C684143645C7FD40A |
| C9-EJ-COMPLETION-20261025.md | 192 | 08F308CD1F656520BE3668B0C62776BA8CD38AFB66A34C7BD5522696BC7EA226 |
| C9-DPRIMES-KODAIRA-20261025.md | 142 | DA7DFD3137E0D0287403390DAEE4039F5681648748E0366FF8D7A0A8A382AC70 |
| C9-MOD41-IMAGE-CORR2-20261025.md | 215 | 78FD8184AD13DC1C1DFCB2BDB90A7B92A5ECE737A6B92F83945844AEBF727140 |
| C9-NORMALIZATION-DECISION-CORR2-20261025.md | 196 | EE3D8EF9AECB98733E7B350935AAD40BC98DC6CA07E3F3CFCB5A0EF2E31DE9C6 |
| C9-MASTER-CONTRADICTION-20261025.md | 824 | 84213536D916567AE8C0053EE7DBBD325A877C38E68D05D56E704DFEB4CF2FC1 |

## 0. Purpose and scope

This document proves the part of the C9 construction that is independent of
the H_A/U/B normalization choice. It does not choose a Q_p-line U=<y1>, a
coordinate y1, or a B=O_K/B=I branch. It proves:

1. the actual E_j data and local b=3 profile;
2. the fields F,K and the source-level X_K/C_K/C_F/V/epsilon skeleton;
3. the per-D Kodaira type III* and F_sem degree 2,3-smoothness;
4. the conditional mod-41 SL2 containment with corrected exact counts;
5. the B_I-zero archimedean procession bound A_proc;
6. the conservative residual formula under CFTH, using the branch-independent
   lower bound, and the exact point where U/B would be needed for sharpening.

No P6 conclusion is claimed. The H_A/B underdetermination and the missing
complete C remain.

## 1. Normalization-independent data

Let p=12301. Define

    D = 1-1728 p^6 = -1009 * 50833 * 1799579 * 64860221162029,
    j0 = 1/p^6,
    E_j: y^2 = x^3 - 3j0/(j0-1728) x - 2j0/(j0-1728).

Equivalently, with A=-3/D, B=-2/D,

    E_j: y^2=x^3+A x+B,
    Delta = 2985984 p^6/D^3 = 2^12 3^6 p^6/D^3.

These data are fixed by E_j alone. They do not depend on a choice of the Kondo
y-basis, on U, or on a B branch.

## 2. Actual E_j theorem

Theorem 2.1 (E_j local type and qhat).

(a) E_j is an elliptic curve over Q with j(E_j)=j0=1/p^6.
(b) v_p(Delta)=6 and v_p(j0)=-6. Hence E_j has multiplicative reduction of
    type I_6 at p=12301. The Tate parameter q has v_p(q)=6.
(c) The Tate q-expansion gives

       q = p^6 + 744 p^12 + O(p^18) != p^6,
       q/p^6 in 1+p^6 Z_p.

(d) p does not divide 82, and the 82nd-power map is a bijection on
    1+p Z_p. Thus q has a unique 82nd root

       qhat = q^{1/82} = pi^3 v,   v in 1+p Z_p subset O_K^times.

    In particular qhat^82=q, v_p(qhat)=3, and qhat has order 3 in K^times/
    O_K^times.

(e) The order b=3 and the local type I_6 depend only on v_p(qhat)=3, not on
    the unit v. The exact qhat is pi^3 v, not pi^3; v is a unit, not arbitrary
    data.

Proof. (a),(b) are the standard discriminant/j computations for the displayed
Weierstrass equation: the identity

    1728*4A^3/(4A^3+27B^2)=j0,
    -16(4A^3+27B^2)=2985984 j0^2/(j0-1728)^3

gives j0 and the stated Delta; D is prime to p and v_p(Delta)=6.
(c) is the standard inversion of j(q)=q^{-1}+744+196884q+... at q=p^6.
(d) follows because p is odd and p does not divide 82; the p-adic pro-p group
1+p Z_p is a Z_p-module on which 82 is invertible. pi is a uniformizer of the
local field containing qhat, and v_p(q/p^6)=0; the root has the form
pi^3 v with v a unit. (e) is immediate from the valuation. QED.

Remark 2.2. The exact equality q=p^6 is false; it is also impossible for a
global elliptic curve by Mahler-Manin (the q=p^6 candidate is excluded). The
actual E_j realizes b=3 through qhat=pi^3 v, and all b=3 data below are
independent of v because v is a unit.

## 3. Fields F and K

Let F_sem be a semistabilization field for the bad primes of E_j as in
C9-DPRIMES-KODAIRA, and put

    F = Q(i,E[6],F_sem),   K = F(E[41]).

Theorem 3.1 (field degree).

(a) [Q(i):Q]=2.
(b) [Q(E[6]):Q] divides |GL2(Z/6)|=288=2^5*3^2.
(c) The D-part of F_sem has degree a power of 2 and at most 512=2^9; the
    2,3-parts have semistabilization degrees built only from 2 and 3.
(d) Therefore [F:Q] divides 2 * 288 * 2^9 * 2^a 3^b for some a,b; in
    particular [F:Q] is 2,3-smooth and 41 does not divide [F:Q].
(e) F/Q is Galois and K=F(E[41]) is finite Galois over F, provided F_sem is
    taken to be the Galois semistabilization compositum as in the completion
    files.

Proof. (a),(b) are standard (E[6] splitting field embeds in GL2(Z/6); i
quadratic). For the D-primes, C9-DPRIMES-KODAIRA proves exact Kodaira type III*
at each q|D and local semistabilization degree 4; for q=1799579≡3 mod4 the
Galois closure degree is 8, for q≡1 mod4 it is 4. Hence the D-part is a
2-power and at most 4*4*4*8=512. The 2,3-local semistabilization degrees are
built from 2 and 3 by the local wild-ramification constants; exact local types
at 2,3 are not computed here, but no prime other than 2,3 enters. Multiplying
degrees gives a 2,3-smooth bound. Galoisness is by taking the compositum of
the local Galois closures. QED.

Remark 3.2. The exact global [F:Q] is not computed; only the 2,3-smoothness
and 41∤ are used. The 2,3-local exact Kodaira types remain missing (see
C9-DPRIMES-KODAIRA); this does not affect the prime support.

## 4. Source-level X_K, C_K, C_F, V, epsilon

Theorem 4.1 (skeleton). With K and F as above:

(a) X_K=E_K minus {O} is a once-punctured elliptic curve over K.
(b) E[41] is an etale finite group scheme over F; C_K=[X_K/E[41]] is an
    orbicurve/stack of type (1,41-tors)^pm.
(c) C_F=[X_F/E[41]] and the K-core of C_K is C_F times_F K.
(d) V is a section of V(K)->V_mod over the bad rational primes; after
    semistabilization only p=12301 remains bad, so V is supported over p.
(e) epsilon is the origin/canonical cusp of X_K.

These are formal source-level constructions. The explicit equations, stacky
points, 41-division coordinates, and the actual cusp/place coordinates are
not constructed in the frozen files.

Proof. The quotient by the finite etale E[41] exists in the orbifold category;
the K-core identity is base change; V is a choice of a place over the unique
bad prime after semistabilization; epsilon is the puncture at the origin. The
existence is formal; explicit coordinates are the missing part. QED.

## 5. Per-D Kodaira III* and F_sem

Theorem 5.1 (D-primes). For each q|D:

    E_j at q is potential good of exact Kodaira type III*,
    (v(c4),v(c6),v(Delta))=(3,5,9),
    local semistabilization degree = 4.

Consequently the D-part of F_sem is a compositum of quartic/Galois-closure
extensions of degree at most 8 at each prime, and its total D-part degree is a
2-power at most 512=2^9. In particular 41 does not divide the D-part degree.

Proof. At q|D, v_q(a)=v_q(b)=-1 in the given model; the scaling x=q^2X,
y=q^3Y yields v_q(a')=3, v_q(b')=5, v_q(Delta')=9, v_q(c4')=3,
v_q(c6')=5. The Kodaira table at q>=5 identifies this as III*. The same
scaling over the quartic extension q^{1/4} makes Delta a unit; lower degrees
1,2,3 leave v(Delta) positive, so the semistabilization degree is exactly 4.
The Galois closure degree is 4 or 8 according to q mod4; the compositum bound
follows. QED.

Remark 5.2 (2,3 correction). The earlier completion file C9-EJ-COMPLETION
claimed 2,3 are good. C9-DPRIMES-KODAIRA corrects this: reduction at 2 and 3 is
singular, so 2,3 are bad additive. Their exact Kodaira types and local
semistabilization degrees are not computed, but the semistabilization degrees
involve only the primes 2 and 3. Thus F_sem degree remains 2,3-smooth and
41∤[F:Q].

## 6. Mod-41 image: corrected computation

Let G be the image of G_Q in GL2(F41).

Theorem 6.1 (mod-41 bounds).

(a) The exact point counts and traces are

       #E(F_37)=32, a_37=6, t_37=6, d_37=37;
       #E(F_127)=140, a_127=-12, t_127=29, d_127=4.

(b) The Frobenius charpolys are

       l=37: x^2-6x+37, discriminant 11 (nonsquare), projective order 7;
       l=127: x^2-29x+4, discriminant 5 (square), projective order 5.

(c) The two classes exclude all maximal subgroups of GL2(F41) that do not
    contain SL2(F41), by Dickson's classification. Hence

       SL2(F41) subset G subset GL2(F41).

(d) The determinant classes 37 and 4 generate a subgroup of order
    lcm(5,10)=10. The displayed data do NOT prove determinant fullness or
    G=GL2(F41).

(e) If [F:Q] is 2,3-smooth, then the image H of G_F also contains SL2(F41).

Proof. (a),(b) are the corrected Legendre-sum computation. (c) uses the
Borel/split Cartan/nonsplit Cartan/exceptional index list 42, 861, 820,
114800, 57400, 22960, all containing 5 or 7; the l=37 class excludes Borel,
split Cartan and exceptional; the l=127 class excludes nonsplit Cartan.
(d) 37^5=1, 4^10=1. (e) Suppose H does not contain SL2. Then
K=H cap SL2 is a proper normal subgroup of SL2(F41); since PSL2(F41) is simple,
K is 1 or {+-I}; hence SL2/K has order 68880 or 34440 and embeds in G/H.
Thus [G:H] has a prime 5 or 7, contradicting [G:H]|[F:Q] with [F:Q] 2,3-smooth.
QED.

Remark 6.2. This result does not use U, W, B, or a normalization of 1. It uses
only the actual E_j and the field degree. Exact G/H order and full determinant
image remain open.

## 7. Archimedean B_I-zero bound

Theorem 7.1 (arch bound). Under the binding B_I-zero normalization:

(a) F=Q radial: h_inf=log r_inf.
(b) For the fixed-j IV container pi^{j+1}B_I,
       logvolume(pi^{j+1}B_I)=(j+1)log pi.
(c) After weighted average and procession normalization,
       A_proc=((l+5)/4)log pi=11.5 log pi=13.1643936873...
    for l=41.
(d) If r_v<=pi for all v, then h_inf<=log pi=1.1447298858..., not 0.

A_proc is a procession-normalized upper bound, not a raw pointwise maximal
container for arbitrary fixed j. It is independent of U and B.

Proof. The B_I-zero normalization is the IV normalization logvolume(B_I)=0
(proof of IV Thm1.10 Step(vii)), and the local unit-ball formula gives
h_inf=log r. The fixed-j bound and procession average are the standard IV
computations. No U/B enters. QED.

Remark 7.2. In contrast, a lower bound on h_inf, and the numerical radius
p^{d_p}, depend on the finite deficit d_p and hence on the conditional
donor/CFTH data. The arch bound alone is only an upper bound.

## 8. Residual formula without a B choice

Let the finite bad profile be uniform, and let H_p^Sp be the aligned
conservative finite lower bound

    H_p^Sp/log p = -(1/m0) sum_j (s_j+1/e),
    d_p = b(e+1)/12 - (b-1)/e - T_p.                       (8.1)

In the evaluated b=3 and b=273 profiles one has h_B >= h_A, where h_A is the
B=O_K value H_p^Sp and h_B is the conditional B=I value. Hence the aligned
value is the weaker of the two branch values; a lower bound by H_p^Sp does not
require selecting B=O_K.

Theorem 8.1 (conditional residual). Assume:

(CFTH) corrected finite donor, basis alignment, trace target, low-ramification,
standard lattice, local naturality, and target-container conditions
TC-A..TC-H/TC-S;

(LB) for every bad p, h_p >= H_p^Sp (the aligned conservative lower bound;
this is the B-independent part; B=I, if realized, can only add a surplus).

Then

    h_C >= sum_p alpha_p H_p^Sp log p + h_inf,
    D_C^Sp := sum_p alpha_p d_p log p,
    Q_C - h_C <= D_C^Sp - h_inf.                          (8.2)

The archimedean maximal-container comparison gives h_inf<=A_proc, so for the
b=3/b=273 profiles the finite deficits

    b=3:   (408/41)log12301 = 93.714971... > A_proc,
    b=273: (38883/41)log12301 = 8931.174579... > A_proc,

cannot be archimedean-compensated. Under shell containment the sharper
h_inf<=log pi gives the same exclusion.

Proof. Sum the local lower bounds with weights, use the arch bound for h_inf,
and subtract. The B choice enters only in the possible positive surplus
h_B-h_A; it is not needed for the conservative inequality (8.2). QED.

Remark 8.2. Theorem 8.1 is conditional on CFTH and on (LB). It is not a
B-free proof of a global inequality: (LB), the donor, and TC are not actual
complete-C data in the frozen corpus. It shows exactly how far the
normalization-independent construction reaches without choosing U/B.

## 9. What remains

1. Actual H_A-full/full Out integrality and the U/B choice: the source
   underdetermination and the missing integral lift (tasks 202/207/222).
2. Exact 2,3 Kodaira types and exact global F_sem degree; only 2,3-smoothness
   is proved.
3. Explicit C_F/C_K/V/epsilon equations and 41-division coordinates.
4. Exact mod-41 G/H order and determinant image; only SL2 containment.
5. Actual archimedean radius/angular term; A_proc is only an upper bound.
6. CFTH, TC-A..TC-H/TC-S, complete C/S_bad/weights/fixed q class.
7. Global h_C>=Q_C or a genuine counterexample.

## 10. Conclusion

The normalization-independent construction proves:

    E_j/Q, j0=1/p^6, Delta, v_p(Delta)=6,
    q=p^6+744p^12+..., qhat=pi^3 v, b=3;
    F=Q(i,E[6],F_sem) with [F:Q] 2,3-smooth and 41∤;
    K=F(E[41]), X_K/C_K/C_F/V/epsilon source skeleton;
    per-D Kodaira III*, local semistabilization degree 4,
    D-part F_sem degree a 2-power <=512;
    corrected mod-41: SL2(F41) subset G, conditional SL2 subset H;
    B_I-zero arch bound A_proc=11.5log pi=13.164394;
    conservative residual Q_C-h_C <= D_C^Sp-h_inf under CFTH/LB.

No U/W normalization or H_A/B branch is selected. No complete C, no global
closure, and no contradiction is obtained. P6 remains open.

target_accepted=false.
