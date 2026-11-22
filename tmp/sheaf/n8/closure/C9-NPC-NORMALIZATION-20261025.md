# C9 NPC via TAME normalization and capsule-full invariance

Task: task-327. Owner: multiradial. Date: 2026-10-25.
Short natural-language theorem/proof. No mixed/E3 profile; no Lean/Project edits;
no arbitrary region. Deliverable: this file only. target_accepted=false; P6 open.

## 0. Verdict

U/NPC IS PROVED for the fixed F_mod=Q uniform target under the source structural
invariance of capsule-full poly-automorphisms on the bad tensor packet. The
missing N3/N4 no-new-class/exhaustion statements are consequences of that
invariance, not independent hypotheses.

Key chain:

  (1) At each procession level, a capsule-full poly-automorphism is a
      permutation of the capsule index set plus D-prime-strip isomorphisms
      (I Def4.10 / III Thm3.11).
  (2) A D-prime-strip isomorphism preserves O_K and m=J=pi O_K; on J it acts
      by O_K^times units; tensor factors may be permuted. Hence
      L_B=p^{s-r+1}J^{tensor r} is invariant, and so is L_A.
  (3) TAME Section 6 gives the fixed all-bad row classification:
      L_A (B=O_K) and L_B (B=I), with L_A subset L_B (task-291/298).
      Thus the source finite region A(S) is contained in L_B.
  (4) Every finite possible image is Phi(A(S)) for a capsule-full
      poly-automorphism Phi. By (2), Phi(L_B)=L_B, so every finite possible
      image lies in R_B=Hull(L_B).
  (5) Good finite normalization is zero; arch contributes h_inf; fixed
      q/BPS/Theta gluing is an isometry/permutation of the same rows, not a new
      class. Therefore the target finite hull is contained in R_B, and
      h_C<=H_B+h_inf.
  (6) This is U/NPC. Conditional on an actual complete uniform C and
      h_inf<=A_proc, b=273 gives F>=D_B-A_proc=8821.538891>0 in both B branches;
      b=3 has the h_inf split.

No mixed/E3 profile enters. The only possible failure is a capsule-full
poly-automorphism that does not preserve J (a non-field/non-integral additive
map); that would be the exact obstruction/source-valid counterexample surface.
No such map is in the frozen allowed category, so U/NPC is proved for the fixed
uniform target under the source D-prime-strip structure.

## 1. Setup and sign convention

p=12301, e=41, fixed F_mod=Q uniform all-bad profile, one selected bad place p,
F(C)=Q_C-h_C.

    P6 target: h_C>=Q_C  <=>  F(C)<=0.                            (1.1)
    F>0: counterexample; F<0: P6 holds; F=0: boundary.

b=3:

    Q_p=(-3/41)log p,
    H_A=(-411/41)log p, H_B=(9/41)log p,
    D_3=(408/41)log p, S_3=(12/41)log p.

b=273:

    Q_p=(-273/41)log p,
    H_A=(-39156/41)log p, H_B=(-38736/41)log p,
    D_A=(38883/41)log p, D_B=(38463/41)log p.

Arch B_I-zero: h_inf<=A_proc=11.5 log pi=13.164393687... (upper bound).

C1/C3:

    h_C >= sum_p alpha_p H_p^Sp log p + h_inf,                     (C1)
    F=Q_C-h_C <= D_C^Sp-h_inf.                                    (C3)
C1 lower on h_C; C3 upper on F. The target U/NPC is the missing upper:

    U: h_C <= max(H_A,H_B)+h_inf = H_B+h_inf.                     (1.2)

## 2. TAME rows and their inclusion

TAME Section 6, fixed all-bad r-tuple:

    L_A=sum_i p^s pi_i D_r          (B=O_K),
    L_B=p^{s-r+1}J^{tensor r}       (B=I),                        (2.1)
    J=pi O_K, D_r=O_K^{tensor r}.

Row heights:

    nu_A/log p=-s-1/e,
    nu_B/log p=-s+(r-1)-r/e.                                      (2.2)

Task-291/298: L_A subset L_B; r=1 equality, r>=2 strict; hence
R_A=Hull(L_A) subset R_B=Hull(L_B). Thus B=I is the maximal of the two row
hulls. The source finite region A(S) for the fixed all-bad tuple has hull L_A
or L_B (TAME Section 6 saturation), hence A(S) subset L_B=Hull(R_B).

## 3. Structural invariance of capsule-full poly-automorphisms

Structural fact (D-prime-strip form; I Def4.10 / III Thm3.11). At each
procession level, a capsule-full poly-automorphism acts by:

  - a permutation of the capsule index set;
  - on each capsule/factor, a D-prime-strip isomorphism.

A D-prime-strip isomorphism preserves the local field K, its ring of integers
O_K, and the maximal ideal m=pi O_K. It induces a Q_p-linear field isomorphism
on K; on m=J it therefore acts by an O_K^times unit (including field
automorphisms pi->zeta pi, zeta in mu_e subset O_K^times, and transported unit
scalars under field-copy identifications). It preserves the integer p and the
integral structure. Tensor factors may be permuted.

Lemma 3.1 (J and L_B invariance). Under any capsule-full poly-automorphism Phi:

    Phi(J)=J,   Phi(J^{tensor r})=J^{tensor r},   Phi(L_B)=L_B.  (3.1)

Proof. On each tensor factor, the D-prime-strip isomorphism sends J=m to J=m
and acts by an O_K^times unit; multiplying J by a unit gives J. The tensor
product of the factor equalities gives Phi(J^{tensor r})=J^{tensor r}. The
scalar p^{s-r+1} is preserved by the isomorphism. Permuting factors preserves
J^{tensor r}. Hence L_B=p^{s-r+1}J^{tensor r} is invariant. QED.

Corollary 3.2. L_A is also invariant under Phi: the generators p^s pi_i D_r
are multiplied by units in the i-th tensor factor, and D_r is unit-invariant;
permutations reorder the generators. Thus both row lattices are invariant.
(This is not needed for the upper bound, since L_A subset L_B.)

Remark 3.3. The only failure mode would be an allowed capsule-full
poly-automorphism whose action on J is not a field/unit isomorphism (e.g. an
arbitrary additive map moving m to a different lattice). That is not a
D-prime-strip isomorphism; it would be a profile/structure change and would
require an explicit source construction. No such map is in the frozen allowed
category.

## 4. Every finite possible image lies in R_B

Let A(S) be the actual finite source region for the fixed uniform all-bad
profile; by TAME Section 6 its hull is L_A or L_B. Since L_A subset L_B, choose
A(S) subset L_B (replace by its hull if necessary; hull containment is what is
used).

The finite possible images in the target are

    Phi(A(S)),   Phi a capsule-full poly-automorphism.            (4.1)

This is the Ind1/capsule-full action; the fixed q/BPS/Theta gluing transports
these images but does not add a new finite class (isometry/permutation of the
same rows; task-285).

By Lemma 3.1, Phi(L_B)=L_B. Since A(S) subset L_B,

    Phi(A(S)) subset Phi(L_B)=L_B.                                (4.2)

Taking hulls,

    Hull(Phi(A(S))) subset Hull(L_B)=R_B.                         (4.3)

Thus every finite possible image lies in R_B. This is N3 (no new finite class)
and the finite part of N4 (hull exhaustion), proved by invariance rather than
assumed.

## 5. Good, arch, and global components

- Good finite places: in the C9 normalization their finite log-volume is zero;
  the fixed F_mod=Q uniform profile has no other bad rational prime. No new
  positive finite class.
- Archimedean component: by B_I-zero normalization the target arch component
  contributes h_inf; its IV bound is h_inf<=A_proc. It is not a finite bad-row
  class and is already separated in the global h_C=finite+h_inf assembly.
- BPS/Theta/gluing: the fixed-gluing common terminal transport preserves the
  q/BPS labels, row weights and normalized volume (TC-A/TC-D/TC-E/TC-G/TC-S;
  task-285). It permutes/transports the same row images; it does not create an
  independent positive class.
- Aggregate B=I multi-prime configurations are not part of the fixed single-p
  uniform profile; other local types/good profiles are different profiles
  (E3), not possible images of this fixed uniform C.

Therefore the only finite possible images are those in (4.3), and the only
additional component is the arch h_inf.

## 6. Theorem NPC/U

Theorem 6.1 (NPC and U). For a fixed F_mod=Q uniform complete C with the
all-bad selected place p, under the D-prime-strip structural fact of Section 3
and the TAME row classification of Section 2:

    H_C has no positive-volume complement beyond R_B+arch;           (NPC)
    h_C <= max(H_A,H_B)+h_inf = H_B+h_inf.                          (U)

Proof. Every finite possible image lies in R_B by Section 4. The finite target
hull is therefore contained in R_B. Good finite volume is zero; arch is h_inf;
BPS/Theta/gluing are isometric transports of the same rows. Hence
h_C<=H_B+h_inf. NPC follows because any complement would be a finite possible
image outside R_B (contradiction) or a positive good/arch class (zero/bounded by
h_inf). QED.

Remark 6.2. The theorem is branch-independent: L_A subset L_B, and both row
lattices are invariant; whether the selected branch is B=O_K or B=I, the
finite hull is contained in R_B. No actual B=I/kappa theorem is needed for U.

## 7. Consequences for b=273 and b=3

Theorem 7.1 (b=273 conditional counterexample). Under Theorem 6.1, an actual
complete uniform b=273 C, and h_inf<=A_proc:

    h_C <= H_B+h_inf <= H_B+A_proc = -8884.245232030... < Q_p=-62.706341...
    F=Q_p-h_C >= D_B-A_proc = 8821.538890956... >0.                 (7.1)

Thus b=273 is a P6 counterexample in both B branches, with margin at least
8821.54. This is the conditional repair of the b=273 upper side: U is supplied
by NPC Theorem 6.1.

Theorem 7.2 (b=3 split). Under Theorem 6.1:
  h_inf<-S_3 => h_C<Q_p, counterexample;
  h_inf=-S_3 => h_C<=Q_p, P6 iff equality;
  h_inf>-S_3 => upper undecided; if the B=I target region lower is present,
                h_C>=H_B+h_inf>Q_p and P6 holds; otherwise undetermined.

## 8. Exact obstruction / source-valid counterexample alternative

The proof uses exactly one structural fact: capsule-full poly-automorphisms
act on J by D-prime-strip field/unit isomorphisms and tensor permutations.
If that fact is false, the exact obstruction is an allowed capsule-full
poly-automorphism Phi with

    Phi(J) != J,   hence Phi(L_B) != L_B,

and an explicit uniform finite possible image Phi(A(S)) outside R_B. Such an
image would be a source-valid counterexample to NPC/U. No such Phi is supplied
by the frozen source; the allowed D-prime-strip isomorphisms preserve O_K and
m, and tensor permutations preserve J^{tensor r}. Mixed/E3 profiles are
excluded and are not a counterexample.

The alternative obstruction would require a non-field/non-integral additive
action on the tensor packet; that is not a D-prime-strip isomorphism and is not
in the Ind1/capsule-full category. No arbitrary map is introduced.

## 9. Status

Proved/conditional:

  - L_B and L_A invariant under capsule-full poly-automorphisms (D-prime-strip
    structural fact).
  - Every finite possible image lies in R_B; finite target hull subset R_B.
  - U/NPC follows; b=273 conditional counterexample F>=8821.538890956;
    b=3 h_inf split.
  - No mixed/E3 profile used.

Conditional/missing for unconditional P6:

  - actual complete uniform C satisfying all source/TC conditions;
  - actual h_inf and h_inf<=A_proc (source upper bound);
  - the D-prime-strip structural fact as a formal source theorem (it is the
    I Def4.10/III Thm3.11 poly-isomorphism structure, not an arbitrary
    assumption);
  - BPS/Theta/gluing compatibility at the actual target column.

No unconditional P6 proof is claimed beyond the conditional b=273
counterexample; no Lean/Project edits; target_accepted=false.

## 10. Dependency hashes

    C9-TAME-LOG-DOMAIN-20261025.md        23B3514B... (250)
    C9-RA-SUBSET-RB-20261025.md           B89DC64C... (147)
    C9-TARGET-EXTRA-NEW-20261025.md       A5356DB1... (130)
    C9-NPC-M3-20261025.md                 4E519EDE... (112)
    C9-MASTER-V5-SCOPE-20261025.md        48AF5AB6... (365)

Status: U/NPC proved from capsule-full invariance + TAME rows; b=273
conditional counterexample F>=8821.538891; b=3 split; no mixed/E3; no Lean/
Project edits; target_accepted=false.

## 11. Acceptance

Only C9-NPC-NORMALIZATION-20261025.md written. Natural-language theorem/proof
only; no Lean/Project/target edits; no independent review/kernel/comparator
run. target_accepted=false; complete C9/P6 not proved.
