# C9 verify NPC proof: D^dag preserves J and L_B

Task: task-332. Owner: kummer. Date: 2026-10-25.
Critical verification; no Lean/Project edits; no mixed/E3.
Only this file written. target_accepted=false; P6 conditional on G1, otherwise open.

## 0. Inputs

- C9-NPC-IND2-20261025.md (task-325), 137 lines,
  SHA256 60b24d744a1e509a9f04eefc05d5f06ad4517c5684e1cb290e35b9f7b4b07184.
- C9-IND1-J-ACTION-20261025.md (task-330), 101 lines,
  SHA256 d82e6bd0ac9361c29a8ea4cdc2717e1beb0a2616548ab2d0c5fff5c718596c89.
- C9-NPC-IND1-20261025.md (task-324), 104 lines,
  SHA256 1f11d666f5e6df4e3e67c622385c645901cecdf5a732254e282abd02530494d4.
- C9-NPC-LATTICE-INVARIANCE-20261025.md (task-326), 203 lines,
  SHA256 5c0eb872b976150f6fd9db35864542db202fcf2fa0ef580807b61ee04644c2df.
- C9-HAFULL-CONSTRUCT-20261025.md, 128 lines,
  SHA256 06299f26383af7da73dc8bb844f2fef7c939d486bd922cec5e1785f0df0cbbf4.
- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.

## 1. Verdict

The transport proof is **partly valid and partly overclaimed**.

Valid:

- A D^dag-prime-strip isomorphism preserves the local J-lattice: it induces a
  Z_p-linear automorphism of J=piO_K, so alpha_+(J)=J. This follows from the
  D-structure/log-unit compatibility (or H_A-lite); it does **not** require the
  action to be multiplication by O_K^times.
- At a fixed procession level, capsule-full poly-automorphisms are capsule-index
  permutations plus factor D^dag-prime-strip isomorphisms. Each factor maps J
  onto J; tensor powers preserve J^{tensor r}; p^{s-r+1} and r are fixed by a
  fixed-length procession automorphism. Hence L_B=p^{s-r+1}J^{tensor r} is
  invariant.
- The same-path log-link/Theta-pilot powers considered in task-325 do not create
  a new finite bad row: first log image lies in J, length>=2 has empty domain,
  roots log0, Theta powers are indexed by the fixed level.

Overclaimed / not verified:

- The statement that the action on J is by O_K^times units is **FALSE**.
  H=Phi^{-1}(Sp) acts nontrivially by Sp_40(Z_p) on J_W; a transvection is not
  scalar multiplication by a unit. L_B invariance only needs J->J factorwise,
  which is true; the unit-only wording is wrong.
- The transport proof does **not** prove full NPC/U. TAME section6 row
  classification is not an upper bound for the entire target output family.
  The missing row-exhaustion condition (G1) remains: no source proof that every
  full Ind1/Ind2/Ind3/log/Theta/BPS/gluing target possible image is a row image.
  Task-325 Theorem4.1 effectively assumes this; task-330 flags it as G1.

Therefore the valid conclusion is:

    Ind1/D^dag preserves J and L_B (conditional on the D-structure/log-unit
    compatibility), hence Ind1 creates no uniform row image outside R_B.

But full NPC/U, and the b=273 F>=8821.538 counterexample, remain conditional
on G1 (row exhaustion/other target branches), not proved by the transport
argument alone.

## 2. Verification of load-bearing lemma 1: J-preservation

Lemma 1.1. A D^dag-prime-strip isomorphism at a finite nonarchimedean factor
acts on J=piO_K by a Z_p-linear automorphism; in particular J maps onto J.

Proof/status. A D^dag-prime-strip isomorphism preserves the local
prime-strip/Frobenioid integral data and the unit/log-shell structure; the
induced additive action on K_+ satisfies alpha_+ log(u)=log(alpha^times u).
Since log(O_K^times)=J for the tame e=41 type, alpha_+(J)=J. This is the
H_A-lite property used in C9-HAFULL-CONSTRUCT (3.2), and is the standard
D-prime-strip/TC-A compatibility. It does not use O_K-preservation.

Correction: the action on J is in Aut_{Z_p}(J) ~ GL_41(Z_p), not generally
multiplication by O_K^times. For example, the Sp_40(Z_p) action on J_W is
non-scalar. This correction does not affect L_B invariance.

What is conditional: the identification of the D^dag-prime-strip isomorphism
with this J-action. If one interpreted D-prime-strip isomorphisms as arbitrary
Q_p-linear maps, J need not be preserved; but that is not the D^dag source
category. The source D-structure/TC-A preserves J.

## 3. Verification of load-bearing lemma 2: L_B invariance

At a fixed procession level j, let r=j+1, s=s_j, and let a capsule-full
poly-automorphism be

    (sigma; A_1,...,A_r),   sigma in S_r,  A_i in Aut_{Z_p}(J).       (3.1)

Then

    (A_1 tensor ... tensor A_r) J^{tensor r}
      = A_1J tensor ... tensor A_rJ = J^{tensor r}.                 (3.2)

The permutation sigma reorders factors; J^{tensor r} is invariant. The scalar
p^{s-r+1} is fixed because a fixed-length procession automorphism preserves the
level j and hence r,s_j. Therefore

    L_B,j = p^{s-r+1}J^{tensor r} is invariant.                     (3.3)

This verifies the L_B invariance part of task-325. L_A subset L_B by task-298,
so B=O_K row images also lie in R_B.

If some action scaled J to p^k J with k!=0, then L_B would map to p^{kr}L_B,
outside R_B for k<0. No such operation is in the D^dag capsule-full action
described by IUT I Def4.10; if one existed, it would be the explicit uniform
counterexample. It is not constructed.

## 4. Verification of log-link/Theta powers

Task-325's log/Theta lemma covers:

- same-path log iterations: first image in J, length>=2 has empty domain
  (TAME section1: next log-link input must be a unit, but first image is in m);
- new unit paths: first log-link image in J, already the J-factor of L_B;
- Teichmuller/root-unit inputs: log0, no volume class;
- Theta-pilot q^{j^2} powers: indexed by fixed level j/exponent s_j, i.e. the
  row family L_B(j), not an s-independent class.

These are valid for the listed operations.

They do **not** verify full Ind3 upper-semi-compatible log branches or other
target possible-image classes (other local types, good/aggregate, additional
q/BPS/Theta rows). That is the missing (G1) row-exhaustion statement. The
transport proof assumes it without proof.

## 5. Corrected NPC/U statement

Theorem 5.1 (what is actually proved). Assume:

(A) D^dag-prime-strip isomorphisms act on J by Z_p-lattice automorphisms
    (D-structure/TC-A or H_A-lite);
(B) capsule-full poly-automorphisms at fixed levels are permutations plus
    factor isomorphisms, with r,s fixed;
(C) the finite bad target possible-image family is exactly the TAME row
    family L_A/L_B (the missing G1 row-exhaustion);
(D) good finite places have zero/negative normalized contribution and the
    arch component is h_inf, bounded by A_proc.

Then NPC: H_C finite is contained in R_B; U follows:

    h_C <= H_B+h_inf.

For b=273, with D_B=Q-H_B=(38463/41)logp=8834.703284... and
A_proc=11.5logpi=13.164393...,

    h_C <= H_B+A_proc=-931.616095...,
    F=Q-h_C >= D_B-A_proc=8821.538890... >0.                        (5.1)

This is a conditional counterexample, not a consequence of (A)/(B) alone.
(C) is the exact remaining gap.

## 6. Exact gap

The transport proof proves:

- J-preservation under D^dag (conditional on D-structure);
- L_B invariance under Ind1 capsule-full actions;
- no Ind1 row image outside R_B;
- listed log/Theta iterates do not add a row class.

It does not prove:

- (G1) full row exhaustion: every possible image under full Ind1/Ind2/Ind3/
  log/Theta/BPS/gluing is a row image;
- no additional target possible-image class outside R_B+arch;
- actual complete C, TC-B/TC-S, good/arch normalization.

Without G1, full NPC/U is not proved. If G1 fails, there would be an extra
target possible image class; no source-valid one is constructed, but absence
of construction is not a proof.

## 7. Classification

| item | status |
|---|---|
| D^dag preserves J as Z_p-lattice | CONDITIONAL on D-structure/TC-A/H_A-lite |
| action on J by O_K^times | FALSE; GL_41(Z_p)/Sp_40 action |
| capsule permutation + factor J-automorphisms | PROVED from IUT I Def4.10 |
| L_B invariant under Ind1 capsule actions | PROVED conditional |
| same-path log/Theta powers only row | VALID for listed operations |
| full Ind3/other branches exhausted | NOT PROVED; G1 missing |
| full NPC/U | NOT PROVED unconditionally |
| b=273 F>=8821.538 | CONDITIONAL on G1 + arch + complete C |
| source-valid extra image outside R_B | NONE constructed |

## 8. Conclusion

The D^dag/J part of the transport NPC proof is valid with a correction: J is
preserved as a Z_p-lattice, not by O_K^times units; L_B is invariant under
capsule permutations and factor J-automorphisms. The same-path log/Theta
estimates are valid. But the proof does not establish full NPC/U because the
row-exhaustion/G1 statement and the exclusion of other target possible-image
branches are missing. Therefore the b=273 F>=8821.538 consequence is
conditional on G1, not proved by the transport argument alone. No uniform
counterexample outside R_B is constructed; no mixed/E3 is used.

No arbitrary data; no Lean/kernel closure; target_accepted=false; P6
conditional on G1, otherwise open.

## 9. Status

- Short verification theorem/proof only; no Lean/Project edits.
- D^dag/J and L_B invariance verified conditionally; O_K^times overclaim
  corrected; G1 gap identified.
- target_accepted=false.
