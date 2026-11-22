# C9 new target: actual B=I and the b=3 negative corridor

Task: task-247. Date: 2026-10-25. Author: transport.
Stage: natural-language/exact local analysis. No Lean/Project/target edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-NEW-VARIATIONAL-COUNTEREXAMPLE-20261025.md | 157 | 100AF6DF5D98B850E1F13D9E259EF360E7D1B70B64F3C7753A038EBAFC3DCBA3 |
| C9-ARCH-ACTUAL-RINF-20261025.md (task-232) | 319 | 6AC23B85163E11706F8E26D96671437D8CFE80953FE5BA535BBA92FD5B15F236 |
| C9-AUDIT-UNIT-FILTRATION-20261025.md | 318 | 8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09 |
| C9-HAFULL-CORRECTED-ATTACK-20261025.md | 271 | A1BDFD61B7FB90D1D24EC9A3D770C308360A095F435D4A2C9F35509775356BF0 |
| C9-NL-UNDERDETERMINATION-20261025.md | 301 | AAFE2BC84D93DEBACF06298B38D7B20694B6A04A0ADBF262DDB87D366E4D0582 |

## 1. Verdict

The proposed construction of actual B=I from a non-filtration alpha does NOT
go through from the current source.

What is actual:

- H=Phi^{-1}(Sp_{40}(Z_p)) is infinite, while the field-theoretic subgroup
  Aut(K) is finite. Therefore there exist actual alpha in H minus Aut(K), and
  by Kondo 2025 Theorem A such alpha do not preserve the full upper
  ramification filtration / unit filtration.
- H_A-lite gives alpha_+(J)=J and the canonical element
  a(alpha)=alpha_+(1)=p^{-1}log(alpha^times(exp p)) in I.
- In the H-coordinates, a(alpha_A)=u_0+A w_0, where 1=u_0+w_0,
  u_0=c y_1, c=41/Tr(y_1).

What is missing:

- The actual element w_0 (equivalently y_1,Tr(y_1),c) is not determined by
  the recorded Kondo data (underdetermination).
- A non-filtration alpha need not have a(alpha) outside O_K. The filtration
  failure may occur at a different unit level than exp(p), and more basically
  the coordinate w_0 is independent of the filtration property.
- Even knowing a(alpha) outside O_K does not by itself prove B=I: one needs
  w_0 in the right lattice and the H-orbit to generate I/J.
- The actual archimedean h_inf is not constructed; only an upper bound
  A_proc is available (task-232). Therefore the b=3 negative corridor cannot
  be decided.

No arbitrary alpha or w_0 is chosen. The honest classification is:

    non-filtration alpha: ACTUAL EXISTENCE, no explicit computation;
    actual B=I: CONDITIONAL/OPEN;
    negative corridor F<0: CONDITIONAL, not realized;
    genuine P6 counterexample: NOT PRODUCED.

## 2. Data and coordinate formula

Let K=Q_p(pi), e=41, p=12301, O_K=Z_p[pi], J=m=pi O_K, I=p^{-1}J, and
W=ker Tr. The Kondo y-basis gives

    K=U direct-sum W, U=<y_1>, W=kerTr,
    y_i in J, Tr(y_1) in p Z_p nonzero.                       (2.1)

Write the field unit

    1=u_0+w_0,  u_0 in U, w_0 in W,
    u_0=c y_1,  c=41/Tr(y_1).                                (2.2)

For alpha in H acting by diag(1,A), A in Sp_40(Z_p),

    a(alpha):=alpha_+(1)=u_0+A w_0=1-w_0+A w_0=1+(A-1)w_0.  (2.3)

Also a(alpha) in I=p^{-1}J by H_A-lite.

## 3. What non-filtration gives

Theorem 3.1 (existence). H is infinite; Aut(K) is finite. Hence H is not
contained in Aut(K): there exists alpha in H minus Aut(K). By Kondo 2025
Theorem A, such alpha does not preserve the full upper ramification
filtration, equivalently the corresponding unit filtration.

Proof. H is a closed subgroup whose image Phi(H)=Sp_40(Z_p) is infinite.
Aut(K) is a finite subgroup of Out(G_K). Therefore H is not contained in
Aut(K). Kondo 2025 Theorem A identifies the stabilizer of the upper
ramification filtration with the field-theoretic subgroup Aut(K); hence an
alpha outside Aut(K) fails the filtration. QED.

This proves actual existence, not an explicit matrix. It also does not tell
which unit level fails.

Remark 3.2. Kondo's theorem concerns the whole upper filtration. It does not
assert that alpha^times(exp(p)) is outside U^e=1+pO_K. The single element
exp(p) may be fixed by a non-field-theoretic alpha even if the filtration is
moved elsewhere. Therefore non-filtration alone does not imply
a(alpha) not in O_K.

## 4. Why non-filtration is not enough for B=I

Lemma 4.1. If w_0 in J, then

    a(alpha)=1+(A-1)w_0 in O_K                                 (4.1)

for every A in Sp_40(Z_p), and B=O_K.

Proof. Since w_0 in J and A preserves J, (A-1)w_0 in J; hence
a(alpha) in 1+J=O_K. Its class modulo J is 1, nonzero, so
alpha_+(O_K)=Z_p a+J=O_K. Therefore every alpha preserves O_K and B=O_K. QED.

Corollary 4.2. The mere existence of non-filtration alpha does not force B=I.
If w_0 in J, all H_A-lite alphas fix l and B=O_K, even though H contains
non-field-theoretic elements that move some other unit filtration.

Thus a proof of B=I needs more than "alpha is outside Aut(K)"; it needs
w_0 not in J and the H-orbit to produce the I/J directions. The recorded data
do not determine w_0 (underdetermination theorem, Model A has w_0=0 and
B=O_K; Model B has w_0=-pi/p and B=I).

## 5. Conditional criterion for B=I

Theorem 5.1 (conditional B=I criterion). Suppose:

(C1) w_0 in I but not in J;
(C2) there is an actual alpha_0 in H with a(alpha_0) not in O_K minus J
     (in particular a(alpha_0) not in O_K);
(C3) the H-orbit of the class of w_0 in I/J spans the W-part of I/J.

Then B=I.

Sketch. By (C2), some alpha_0(O_K)=Z_p a(alpha_0)+J is not O_K. By H_A-lite
all alpha preserve J and I, and the class a(alpha)=1+(A-1)w_0 modulo J moves
with A. Condition (C3) makes the classes span Wbar; the class of 1 supplies
l. Hence B/J is all of I/J while B is contained in I (this containment needs
w_0 in I and A preserving the relevant lattice), so B=I. The proof is
analogous to Model B of the underdetermination theorem.

This theorem is conditional: C1 is exactly the unknown w_0 coordinate, C2 is
an actual nonintegral alpha at exp(p), and C3 is a lattice/orbit condition.
None is computed for the actual E_j/Kondo donor. The existence of some
non-filtration alpha (Theorem 3.1) does not establish C2 at exp(p).

## 6. Can B=I be proved impossible for the actual donor?

No such impossibility is proved. The only conditional exclusions are:

- w_0 in J => B=O_K (Lemma 4.1);
- if a(alpha) in O_K minus J for every actual alpha => H_A-full => B=O_K
  (corrected attack theorem);
- if all actual alpha fix l => B=O_K.

To prove B=I impossible for H, one would need at least one of:

1. w_0 in J (equivalently 1 has no W-component in the y-basis);
2. a(alpha) in O_K minus J for all alpha in H (H_A-full);
3. a direct theorem that every actual alpha(O_K)=O_K.

None is in the current source. Conversely, to prove B=I actual one needs
C1-C3. Both are open. The actual B branch is therefore still underdetermined/
type-gapped, not decided.

## 7. b=3 corridor: exact conditional evaluation

The profile values from C9-GLOBAL/variational are conditional on the finite
donor and target container. Let

    S_3=(12/41)log 12301=2.7563226845469613...                (7.1)

For the b=3 B=I profile:

    h_fin^B= (9/41)log p,   Q_p=(-3/41)log p,
    F=Q_C-h_C = (-3/41-9/41)log p - h_inf
             = -S_3 - h_inf.                                 (7.2)

Therefore:

    F<0  iff h_inf > -S_3 = -2.7563226845469613...            (7.3)
    F>=0 iff h_inf <= -S_3.                                   (7.4)

This is exact conditional arithmetic. It requires the B=I local value h_B,
which is conditional on C1-C3 and the finite donor/target conditions.

For B=O_K b=3:

    h_fin^A=(-411/41)log p, Q_p=(-3/41)log p,
    D_3=(408/41)log p=93.7149712746...,
    F=D_3-h_inf.                                              (7.5)

Under the IV upper bound h_inf<=A_proc=11.5log pi=13.1643936873...,
F>=80.5505775873...>0. This is a conditional positivity, not a global theorem.

For b=273 B=I:

    h_fin=( -38736/41)log p, Q=(-273/41)log p,
    F=(38463/41)log p - h_inf
     =8834.7032846... - h_inf >0                              (7.6)

for h_inf<=A_proc. B=O_K b=273 is larger. Hence the only known negative
corridor is b=3 B=I with h_inf>-S_3.

## 8. Archimedean input

Task-232 proves that the E_j skeleton does not determine the actual
archimedean Θ-pilot hull or h_inf. The available information is:

- B_I-zero normalization: h_inf=sum alpha_v [h_v^ang+log r_v];
- IV upper bound h_inf<=A_proc=11.5log pi=13.1643936873...;
- shell containment conditional gives h_inf<=log pi;
- no lower bound h_inf>=-S_3, and no actual h_inf.

Consequences:

1. The upper bound h_inf<=A_proc does not imply h_inf>-S_3; it is compatible
   with h_inf very negative. So it cannot establish the negative corridor.
2. The formal boundary value at h_inf=A_proc is
       F=-S_3-A_proc=-15.9207163718...,
   but A_proc is only an upper bound and its attainment is not proved. This is
   not an actual C.
3. No lower bound h_inf>-S_3 is known; product-formula constraints give only
   point-modulus bounds, not a hull-volume lower bound. Therefore even if
   actual B=I were proved, the sign of F would remain undecided without an
   actual archimedean hull.

## 9. Counterexample status

A genuine P6 counterexample in this corridor would require:

(i) an actual complete C with all IUT data;
(ii) actual B=I (C1-C3 for its H-action);
(iii) actual h_inf>-S_3;
(iv) target/TC-A..TC-H/TC-S conditions and normalization.

None is available:

- actual B=I is open;
- actual h_inf is open;
- complete C/TC are open.

Therefore no genuine counterexample is produced. The B=I b=3 corridor is a
conditional scenario, not a C. It remains the only known negative corridor in
the uniform table, but it is not realized.

## 10. Exact/conditional/impossible summary

ACTUAL:

- H infinite, Aut(K) finite, so non-field-theoretic/non-filtration alpha exist
  in H (existence only).
- H_A-lite a(alpha)=1+(A-1)w_0 in I; w_0 in J implies B=O_K.
- b=3/b=273 profile arithmetic and the conditional corridor criterion
  F=-S_3-h_inf.
- Task-232: no actual h_inf/lower bound; upper A_proc only.

CONDITIONAL:

- actual w_0 (or y_1,Tr(y_1),c) and actual alpha matrices;
- C1-C3 => B=I;
- h_inf>-S_3 plus B=I => F<0;
- target/TC and complete C.

NOT PROVED / OPEN:

- construction of actual B=I from non-filtration alpha;
- impossibility of B=I for actual donor;
- actual h_inf sign;
- genuine P6 counterexample.

## 11. Conclusion

Non-filtration alpha exist in H, but they do not give actual B=I: the missing
w_0 coordinate and the value a(alpha) at exp(p) are not determined, and if
w_0 in J then B=O_K regardless of non-filtration. The exact conditional B=I
criterion is C1-C3. The b=3 corridor F=-S_3-h_inf is negative iff
h_inf>-S_3, but actual B=I and actual h_inf are both missing. No genuine
counterexample to P6 follows; the corridor remains conditional.

No arbitrary alpha or data was chosen. target_accepted=false.
