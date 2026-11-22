# C9 R_A subset R_B: inclusion theorem

Task: task-298. Owner: kummer. Date: 2026-10-25.
Short theorem/proof; no Lean/Project edits, no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- C9-TARGET-EXTRA-NEW-20261025.md (task-285), 130 lines,
  SHA256 a5356db164e2cbf62f8382dd5a9574ed587a73aff1bdc90efa15974ed8668dfd.
- C9-SATURATION-UPPER-20261025.md (task-290), 185 lines,
  SHA256 eb171c17ce6a9363e4f8df4abdfc9a9bc2047b7ef83cdcdfa619d13a3a8a6030.

Let e=41, p=12301, O=O_K, J=pi O, D_r=O^{tensor r}, and for the fixed
all-bad r-tuple let

    L_A = sum_{i=1}^{r} p^s pi_i D_r        (B=O_K row lattice),
    L_B = p^{s-r+1} J^{tensor r}            (B=I row lattice).        (0.1)

Here pi_i means pi in the i-th tensor factor and the unit in the other
factors; J^{tensor r}=pi_1...pi_r D_r. Let R_A=Hull(L_A), R_B=Hull(L_B).

## 1. Theorem

Theorem 1.1 (R_A subset R_B). For every r>=1,

    L_A subset L_B,  hence  R_A subset R_B.                            (1.1)

For r=1 the two lattices are equal. For r>=2 the inclusion is strict, and

    nu_B-nu_A = (r-1)(1-1/e) log p >0.                                (1.2)

This is independent of b=3 or b=273: the inclusion is a property of the
TAME row lattices, not of the q-order b.

## 2. Proof

For each j, because pi_j^e=p u_j with u_j in Z_p^times,

    p/pi_j = pi_j^{e-1} u_j^{-1} in O_{K_j}.                          (2.1)

Consider the i-th generator of L_A (up to the unit D_r):

    e_i = p^s pi_i.                                                   (2.2)

The corresponding generator of L_B is

    b = p^{s-r+1} pi_1...pi_r.                                       (2.3)

Multiply b by the integral element

    q_i := product_{j != i} (p/pi_j) in D_r.                         (2.4)

Then

    b q_i
      = p^{s-r+1} pi_1...pi_r * product_{j != i}(p/pi_j)
      = p^{s-r+1} pi_i * product_{j != i}(pi_j * p/pi_j)
      = p^{s-r+1} pi_i * p^{r-1}
      = p^s pi_i = e_i.                                              (2.5)

Thus every generator e_i of L_A lies in L_B; since L_B is a Z_p-lattice,
L_A=span_{Z_p}{e_i} subset L_B. The hull is monotone under lattice inclusion
(with the same tensor order and normalization), so R_A subset R_B.

For r=1, q_i is empty and both lattices are p^s pi_1 O; equality.

For r>=2, b=p^{s-r+1} pi_1...pi_r lies in L_B but not in L_A: every
generator of L_A has pi-adic content in exactly one tensor factor (pattern
(1,0,...,0) up to permutation), while b has content one in every factor.
Hence the inclusion is strict.

The normalized heights from TAME section6 are

    nu_A/log p=-s-1/e,
    nu_B/log p=-s+(r-1)-r/e,
    nu_B-nu_A=(r-1)(1-1/e)>0.                                        (2.6)

QED.

## 3. Consequence for the B branches

For every r, the B=I row hull contains the B=O_K row hull. Therefore:

- the larger of the two row hulls is R_B;
- any target upper envelope consisting only of these two row hulls reduces to
  R_B;
- for b=3/b=273 the same inclusion holds, because it does not involve b.

This is the S1 statement requested for the saturation upper bound.

## 4. What inclusion does not prove

Inclusion R_A subset R_B is **not** the saturation upper bound

    h_C <= H_B+h_inf.                                                (4.1)

TC-B says the target H_C contains the actual possible-image family; it is a
lower-bound/saturation statement. H_C may contain additional regions: other
local types, good places, aggregate B=I contributions, archimedean regions,
or other q/BPS classes. Inclusion only says that **within the two branch rows**
the B=I row is maximal; it does not say that H_C is contained in R_B.

Thus task-290's missing upper statement remains:

    (S2) H_C subset Hull(R_B) + arch,  or an exact target-volume equality.

Without (S2), inclusion alone gives no upper bound h_C<=H_B+h_inf and no
b=273 P6 counterexample. The correct inequality remains F<=D-h_inf
(task-281).

## 5. Classification

| item | status |
|---|---|
| L_A subset L_B for all r>=1 | PROVED |
| R_A subset R_B | PROVED by hull monotonicity |
| strict for r>=2; equality r=1 | PROVED |
| nu_B-nu_A=(r-1)(1-1/e)log p>0 | PROVED |
| inclusion independent of b=3/b=273 | PROVED |
| inclusion => h_C<=H_B+h_inf | FALSE; needs target-upper S2 |
| saturation upper bound (SAT) | NOT PROVED |
| b=273 P6 counterexample | NOT OBTAINED |

## 6. Conclusion

R_A is contained in R_B: the B=I row hull contains the B=O_K row hull, strictly
for r>=2. This proves the S1 inclusion needed by the saturation-upper attack,
and shows that among the two branch row hulls the B=I hull is maximal.

But inclusion is not an upper bound on the target hull. TC-B gives only lower
containment of possible images; the target may contain additional regions, so
H_C is not proved to lie in R_B. The exact missing statement for the
saturation upper bound is target-upper row-saturation H_C subset Hull(R_B)
(or an exact volume equality), not R_A subset R_B. Therefore the inclusion
does not repair the b=273 upper side; no b=273 counterexample follows.

No arbitrary data; no Lean/kernel closure; target_accepted=false; P6 open.

## 7. Status

- Short natural-language theorem/proof only; no Lean/Project edits.
- R_A subset R_B proved; saturation upper still blocked by target-upper S2.
- target_accepted=false.
