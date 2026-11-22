# C9 upper bound theorem: h_C <= sum H_p^Sp + h_inf

Task: task-267. Date: 2026-10-25. Author: transport.
Short theorem/proof; no arbitrary data; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-P6-NOGO-20261025.md | 180 | 7B9BB3256363B6A8D0931E4E55C62D6FFA27E1FD2A0BF421DC35744D9167557D |
| C9-TAME-LOG-DOMAIN-20261025.md | 250 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06 |
| C9-GLOBAL-ASSEMBLY-BINDING-20261025.md | 271 | 0888F47DC5D5DC21410F39FF7A81D4315E55FABD84E882BC3D17FDB27A25D9FA |

## 0.1 Result

The requested upper bound

    h_C <= sum_bad alpha_p H_p^Sp log p + h_inf                (U)

is NOT obtainable from the target container in the frozen source.
The target container gives only

    h_C <= nu(C_C),                                             (U-cont)

where C_C is the target container and nu(C_C) is its normalized volume. The
TAME finite formula gives the opposite inequality

    h_C >= sum_bad alpha_p H_p^Sp log p + h_inf.               (L)

Combining (U) with (L) would force equality, i.e. the target hull would have
exactly the source-generated hull volume. That sharpness is not a source
theorem. Therefore (U) is not proved and the b=273 counterexample logic is
not repaired by the target container.

## 1. The two inequalities

Let C be an admissible complete C, H_C its target holomorphic hull,
C_C the target container with H_C subset C_C, h_C=nu(H_C), and
nu(C_C) the normalized target-container volume.

### 1.1 Lower bound from source hull

TAME (13)-(15), especially (14)/(15), proves that the source-generated
integral hull is contained in the target hull after the allowed Ind1
transport:

    Hull(source region) subset H_C,
    h_C >= sum_p alpha_p H_p^Sp log p + h_inf.                 (1.1)

Here

    H_p^Sp/log p = -(1/m0) sum_j (s_j+1/e) < 0                 (1.2)
    h_inf = sum_v alpha_v [h_v^ang + log r_v].

This is a lower bound: the source region is inside the target hull, so the
target hull has at least its volume. It does not bound h_C from above.

### 1.2 Upper bound from target container

By definition of the target container,

    H_C subset C_C,
    h_C <= nu(C_C).                                             (1.3)

This is an upper bound, but its finite part is the container volume
nu(C_C), not the source number H_p^Sp. In the B_I-zero normalization the
archimedean part of C_C is bounded by A_proc, but this gives only

    h_C <= sum_p alpha_p b_p^cont log p + A_proc                (1.4)

for some container volumes b_p^cont, with no identification
b_p^cont=H_p^Sp. In fact H_p^Sp is a lower bound coming from the source
hull, while b_p^cont is a volume of a container that contains it.

## 2. The requested upper bound would force sharpness

Theorem 2.1 (obstruction). The frozen source does not prove (U). Moreover,
(U) together with the TAME lower bound (1.1) implies

    h_C = sum_p alpha_p H_p^Sp log p + h_inf.                  (2.1)

Thus (U) is equivalent to the statement that the target hull is exactly the
source-generated hull, not a larger container. No such equality is proved.

Proof. Immediate from (1.1) and (U). The equality is a sharpness statement
about the target hull; it is strictly stronger than the inclusion
Hull(source) subset H_C. The source has no theorem forcing the target hull to
have no additional directions or volume. QED.

Corollary 2.2. The target-container bound (1.3) does not imply (U). To get
(U) from (1.3) one would need the additional comparison

    nu(C_C) <= sum_p alpha_p H_p^Sp log p + h_inf,              (2.2)

which is not in the frozen source. Since H_p^Sp is negative and C_C contains
the source hull, (2.2) is a very strong sharpness/equality condition, not a
container inclusion.

## 3. Consequence for b=273

For b=273:

    Q_p=(-273/41)log p,
    H_p^Sp=h_A=(-39156/41)log p,
    D_A=(38883/41)log p=8931.174578...,
    A_proc=11.5log pi=13.164393... .                           (3.1)

The no-go argument of task-256 uses

    F=Q_p-h_C >= D_A-h_inf >= D_A-A_proc >0.                   (3.2)

The first inequality in (3.2) is equivalent to

    h_C <= h_A+h_inf = H_p^Sp+h_inf,                           (3.3)

which is exactly (U). The TAME result gives the opposite inequality
h_C>=h_A+h_inf. Therefore (3.2) is not justified by the frozen source.

The correct CFTH residual formula is

    Q_C-h_C <= D_C^Sp-h_inf,                                  (3.4)

an upper bound on F=Q_C-h_C, not a lower bound. It is compatible with F large
positive, zero, or negative; it cannot prove F>0. The no-go's F>0 needs (U),
which is missing.

## 4. Can the target container give a stronger bound?

The target container is built from local/arch containers. It supplies:

- archimedean bound h_inf<=A_proc;
- finite container volumes b_p^cont, positive or at least not equal to H_p^Sp;
- no upper bound equal to the source-generated H_p^Sp.

The source-generated H_p^Sp is a negative number (1.2). A container that
contains the source hull must have volume at least H_p^Sp; the natural
container volume is strictly larger because the source hull is a strict subset.
No theorem proves the target hull fills its container or that the container
volume equals the source lower bound.

Therefore the target container gives an upper bound of the form
sum b_p^cont+h_inf, not the requested sum H_p^Sp+h_inf. The difference between
these two upper bounds is exactly the extra container volume that b=273 would
need to control; it is not bounded in the source.

## 5. Proved / conditional / obstruction

PROVED:

- TAME lower bound h_C>=sum H_p^Sp+h_inf (source hull inside target hull).
- Target container upper bound h_C<=nu(C_C).
- (U) plus lower bound forces equality h_C=sum H_p^Sp+h_inf.
- The b=273 no-go's F>0 requires (U), not the lower bound.
- CFTH residual is an upper bound on F, not a lower bound.

CONDITIONAL/MISSING:

- identification nu(C_C)=sum H_p^Sp+h_inf (sharpness/equality);
- actual target container finite volumes;
- actual h_inf and TC/CFTH;
- actual complete C.

IMPOSSIBLE FROM CURRENT SOURCE:

- deriving (U) from container inclusion alone;
- proving F>0 for b=273 from the TAME lower bound;
- repairing the b=273 counterexample logic by the target container.

## 6. Conclusion

The requested upper bound h_C<=sum H_p^Sp+h_inf is not available. The target
container gives h_C<=nu(C_C); the finite source formula gives the opposite
inequality h_C>=sum H_p^Sp+h_inf. Combining them would force the sharp
equality h_C=sum H_p^Sp+h_inf, which is not proved. Hence the b=273
counterexample logic is not repaired: its F>0 conclusion needs an upper bound
that the frozen source does not supply. No genuine P6 counterexample follows
from the target container; no arbitrary container volume is chosen.

target_accepted=false.
