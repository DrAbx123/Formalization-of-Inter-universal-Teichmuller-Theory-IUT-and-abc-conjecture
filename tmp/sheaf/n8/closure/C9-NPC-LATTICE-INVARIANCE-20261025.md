# C9 NPC via Ind1 lattice invariance

Task: task-326. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits; no mixed/E3.
Only this file written. target_accepted=false; P6 conditional on NPC, otherwise open.

## 0. Inputs

- C9-HAFULL-CONSTRUCT-20261025.md, 128 lines,
  SHA256 06299f26383af7da73dc8bb844f2fef7c939d486bd922cec5e1785f0df0cbbf4.
- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- C9-IND1-GLOBAL-20261025.md, 532 lines,
  SHA256 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8.
- C9-RA-SUBSET-RB-20261025.md, 147 lines,
  SHA256 b89dc64ccbe6d6b564f629947b7cba0346cab8fa2ba58703ed5ab7b56e3ecc4e.
- C9-SATURATION-MAXIMALITY-20261025.md, 108 lines,
  SHA256 daa9cd08c20b06594c6622e1806fdce22831baa275e7bdd4f98c1597591bc5ac.

Uniform profile only; no mixed rho; no E3 profile change.

## 1. Theorem

Theorem 1.1 (Ind1 lattice invariance => NPC). Assume the source-level
identification of the D-prime-strip/procession action with the outer
automorphism action on J:

(H1) every D-prime-strip local isomorphism at a bad factor acts on
     J=pi O_K by a Z_p-linear automorphism; equivalently alpha_+(J)=J for
     every actual alpha (H_A-lite, C9-HAFULL-CONSTRUCT (3.2));
(H2) an automorphism of the fixed-length procession preserves the level j and
     tensor order r=j+1; a capsule-full poly-automorphism is a permutation of
     the capsule index set times D-prime-strip isomorphisms at the factors;
(H3) Ind2 Ism/order-2 acts on J by units/roots (hence preserves J);
(H4) the Ind3 log-link image lies in J and does not multiply the actual image
     lattice by p^{-1}; the p^{-1} log-shell is a reference construction, not
     an extra log-link arrow (TAME section1);
(H5) Theta/gluing/BPS/root transport preserves the row/tensor/p-exponent data
     or permutes rows; root choices are roots of unity.

Then for every j:

    L_B,j = p^{s_j-r+1} J^{tensor r},  r=j+1,                     (1.1)

is invariant under Ind1/Ind2/Ind3/log/Theta finite local action. Consequently
every finite bad-place possible image lies in R_B=Hull(L_B) (and L_A subset L_B
by task-298), so NPC/M3 holds at the finite bad place. Good finite factors
contribute zero or negative normalized volume (TAME); they add no positive
class. Therefore the uniform finite hull satisfies

    h_C,fin <= H_B,   H_B=(1/m)sum_j nu_B,j,                      (1.2)

and with the arch bound h_inf<=A_proc,

    U: h_C <= H_B+h_inf,                                          (1.3)

and for b=273,

    F=Q_C-h_C >= D_B-A_proc
      = 8821.538890... >0.                                       (1.4)

This is the promised NPC/U and b=273 consequence, conditional on H1-H5.

## 2. Proof of L_B invariance

### 2.1 Ind1 factor action preserves J^{tensor r}

Let a capsule-full poly-automorphism at level j act on the r=j+1 tensor
factors by

    (A_1,...,A_r) composed with a permutation sigma in S_r.            (2.1)

By H1, each A_i is a Z_p-linear automorphism of J. Therefore

    (A_1 tensor ... tensor A_r)(J^{tensor r})
      = A_1 J tensor ... tensor A_r J
      = J^{tensor r}.                                             (2.2)

The permutation sigma only reorders the tensor factors, and
J^{tensor r} is invariant under permutation. The scalar p^{s_j-r+1} is fixed
because the level j (hence s_j) and r are fixed by H2. Hence

    (A_1 tensor ... tensor A_r) sigma (L_B,j) = L_B,j.            (2.3)

### 2.2 Ind2

Ind2 Ism/order-2 acts by units/roots on each factor (H3). Unit multiplication
and roots of unity preserve J and J^{tensor r}; the p-scalar is unchanged.
Hence L_B,j is invariant.

### 2.3 Ind3/log

The actual finite log-link sends O_K^times to J=log(O_K^times) (TAME section1).
The p^{-1} log-shell I=p^{-1}J is a construction of the shell/reference, not an
additional log-link arrow. Thus Ind3 does not replace J by p^{-1}J on the
actual possible image; it is an upper semi-compatibility on the log-shell, not
a lattice dilation of L_B,j. It therefore creates no new p-exponent class and
does not move L_B,j outside R_B.

### 2.4 Theta/gluing/BPS/roots

Theta-gluing/fixed transport preserves row, q/BPS labels and normalized volume
(H5); row permutations/procession relabeling permute the L_B,j and therefore
preserve their union R_B. BPS/root choices are roots of unity, which preserve
J and the p-scalar. Hence these operations do not create a lattice class outside
R_B.

### 2.5 Good finite factors

Good finite factors have unit/zero normalized contribution in the B_I-zero
normalization (TAME); they do not add a positive finite class. Thus the finite
bad row family is the only positive finite contribution.

Therefore all finite bad possible images lie in R_B, and the finite target hull
is bounded by H_B. QED.

## 3. Consequence

Under H1-H5, NPC/M3 is proved for the uniform profile at the finite bad place.
Then U follows with the arch container:

    h_C <= H_B+h_inf <= H_B+A_proc.                                (3.1)

For b=273:

    Q_C=(-273/41)log12301=-62.706341...,
    H_B=(-38736/41)log12301=-944.780488...,
    D_B=Q_C-H_B=(38463/41)log12301=8834.703284...,
    A_proc=11.5log pi=13.164393...,
    h_C <= H_B+A_proc=-931.616095...,
    F=Q_C-h_C >= D_B-A_proc=8821.538890... >0.                    (3.2)

Thus b=273 would be a P6 counterexample with margin >=8821.538 in both B
branches. b=3 likewise gives the U3 split (under U3).

## 4. Exact status and caveats

The proof is source-conditional on H1-H5:

- H1 is the H_A-lite/reciprocity compatibility alpha_+(J)=J, conditional on
  Kondo 2026 Theorem2.6 and local reciprocity; it is not H_A-full/O_K
  preservation.
- H2 is the IUT I Definition4.10 fixed-length procession automorphism
  semantics: level injection identity, capsule-full poly-automorphisms =
  index permutation plus D-prime-strip isomorphisms.
- H3 is the Ind2 Ism/order-2 unit action.
- H4 is the TAME section1 log-link/domain statement; if one allowed an
  additional p^{-1} log-link action, L_B would move to p^{-1}L_B and leave
  R_B. That would be an extra p^{-1} arrow, not supplied by the source.
- H5 is the Theta/gluing/BPS/root volume/label preservation (TC-C/D/E/G and
  task-294 root absorption).
- The arch upper h_inf<=A_proc is a separate TC/arch input; U uses it but NPC
  itself is finite.

If any of H1-H5 fails, the proof stops. In particular:

- An Ind3 p^{-1} action on the actual image (not just the reference shell)
  would produce p^{-1}L_B outside R_B; that would be an explicit uniform
  image outside R_B, refuting NPC, and the b=273 counterexample would fail.
- A D-prime-strip action not preserving J (if H1 failed) would also move
  L_B.
- A new positive finite local/good class outside R_B would refute NPC.

No such source-valid counterexample is constructed in the frozen corpus. The
invariance proof above is the strongest uniform NPC result available, but it is
conditional, not an unconditional source theorem.

## 5. Classification

| item | status |
|---|---|
| Ind1 factor action A_i in GL(J) | H1 conditional (H_A-lite) |
| capsule permutation preserves J^{tensor r} | PROVED |
| L_B,j invariant under Ind1/Ind2 | PROVED conditional H1-H3 |
| Ind3 actual log-link image in J | H4 conditional (TAME sec1) |
| Theta/gluing/BPS/root preserve row/scalar | H5 conditional |
| NPC/M3 finite bad | PROVED conditional H1-H5 |
| U uniform | PROVED conditional NPC + arch |
| b=273 F>=8821.538 | PROVED conditional H1-H5 |
| source-valid image outside R_B | NONE constructed |
| unconditional NPC/U | NOT PROVED |

## 6. Conclusion

Under the H_A-lite J-stability, the IUT procession/capsule permutation
semantics, Ind2 unit action, Ind3 log-link-in-J, and Theta/gluing/BPS/root
preservation, the B=I row lattice L_B,j is invariant under the full finite
Ind1/Ind2/Ind3/log/Theta action. Hence every finite bad possible image lies in
R_B, NPC/M3 follows, and U gives b=273 F>=8821.538 (conditional on a complete
uniform C and the arch bound). The critical hypotheses are H1-H5; if the Ind3
action is an actual p^{-1} image dilation or H1 fails, L_B moves outside R_B
and NPC/U fail. No such source-valid counterexample is constructed. No
mixed/E3 profile is used; no arbitrary region.

No Lean/kernel closure; target_accepted=false; P6 conditional on H1-H5,
otherwise open.

## 7. Status

- Short natural-language theorem/proof only; no Lean/Project edits.
- Conditional NPC via Ind1 lattice invariance and b=273 F>=8821.538 recorded.
- target_accepted=false.
