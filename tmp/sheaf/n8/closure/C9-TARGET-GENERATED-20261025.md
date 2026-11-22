# C9 target hull vs B=O_K/B=I rows

Task: task-299. Date: 2026-10-25. Author: transport.
Short theorem/proof. No arbitrary regions; no Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-TAME-LOG-DOMAIN-20261025.md | 250 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06 |
| C9-BI-REGION-HULL-20261025.md | 160 | 66F7871676321F8E15C5F6D24F013A85BC9AFEE138FCEF9FA8C2E02B7E8B6B76 |
| C9-UPPER-BOUND-20261025.md | 180 | 888413C9F3241BA6464D43C8C952EF50FBA1DEC0C1DE0FD86CEBF169A7EFE8EB |
| C9-IND1-GLOBAL-20261025.md | 531 | 94785726EE890F6BC672861C570238F040636A6273A7722B2621949C48AF9AB8 |

## 1. Verdict

The target hull H_C is NOT generated exactly by the B=O_K/B=I bad-row
families. The statement fails already at the level of the target's
archimedean, good-place and mixed-profile components, and TAME itself scopes
Section 6 to a fixed all-bad subfamily, not the whole target family.

The exact classification of TAME Section 6 is:

    B=O_K:  L_A = sum_i p^s pi_i D_r,
    B=I:    L_B = p^{s-r+1} J^{tensor r},                        (1.1)

for a fixed all-bad r-tuple, with volumes

    nu_A/log p = -s-1/e,
    nu_B/log p = -s+(r-1)-r/e.                                  (1.2)

This is a local finite bad-row classification. It does not say that the global
target hull H_C is the hull of only these two rows.

## 2. Three concrete reasons

### 2.1 TAME Section 6's own scope limitation

TAME explicitly says the Section 6 classification is only for the listed
actual subfamily, "not an upper bound for the entire C's log/Theta/infinity
output family." Therefore a theorem identifying H_C with the hull of L_A/L_B
rows is not in TAME. Any S2 claim using TAME Section 6 as exact generation is
an overread.

### 2.2 Mixed bad/good profiles give extra volume classes

TAME Section 5 constructs mixed bad/good profiles. If a tuple has k<r bad
factors, choose an allowed permutation to move the Gaussian marker to a good
factor. The resulting actual region D_tuple is in the target after the
allowed Ind1 transport, and its normalized lower bound is

    ell_j^aligned >= -rho^(j+1)(s_j+1/e),
    h_p^aligned/log p >= -(1/m) sum_j rho^(j+1)(s_j+1/e),       (2.1)

with 0<rho<1 for a mixed profile. This is different from both B=O_K and B=I
all-bad row values (1.2), which have rho=1 and no good-factor permutation
loss. Since H_C is the hull of the full possible-image union (TC-B), it
contains this mixed region by definition. Hence H_C is not generated only by
the two all-bad B rows.

### 2.3 Archimedean and good-place components

H_C is a global target hull. It has an archimedean component H_C,inf and good
finite components. The B-row classification (1.1) is a finite bad local
lattice family; it has no archimedean coordinate and no good-place label. Even
if good finite volume is zero, the archimedean component contributes h_inf and
the target hull has the product/global structure. A hull generated only by
finite bad rows cannot equal the global H_C.

In particular, any actual archimedean possible image of nonempty volume gives
a component not present in (1.1). The B_I-zero normalization fixes the
reference volume, it does not remove the archimedean factor from H_C.

## 3. Theorem and proof

Theorem 3.1 (non-generation). Assume the target hull H_C is the hull of the
full possible-image union (TC-B) of an actual complete C. Then

    H_C != hull(rows_B=O_K, rows_B=I)                           (3.1)

as a global normalized-volume/label object. The exact obstruction is that
TC-B includes archimedean, good-place and mixed-profile possible images whose
volume classes and labels are not among the fixed all-bad B rows (1.1).

Proof. By TAME Section 5, the mixed-profile region (2.1) is an actual source
possible image under the allowed Gaussian/permutation construction, with a
volume class different from (1.2). By TC-B it lies in H_C. The archimedean
component H_C,inf also lies in H_C and is not a finite bad row. Therefore the
union generating H_C has components outside the two B rows. The hull of the
B rows alone cannot contain the global H_C. QED.

Corollary 3.2. The S2 saturation-upper route cannot use exact generation by
B=O_K/B=I rows. If an upper bound h_C<=sum H_p^Sp+h_inf is to be proved, it
must control all components in Theorem 3.1, not only the two B rows.

## 4. Relation to the upper-bound problem

This is the same obstruction as task-267, now localized:

- B rows give lower bounds from source-generated lattices;
- the target hull includes mixed/arch/good components, so it is not equal to
  the B-row hull;
- an exact-generation statement would be a strong no-extra-region theorem,
  which is false/not proved.

Consequently no exact saturation upper bound follows. The b=273 counterexample
side still needs the missing upper bound; the b=3 B=I P6 side uses a lower
bound from the B=I region and remains conditional on TC-B and h_inf>=-S3.

## 5. What would be needed

A valid exact-generation or upper-bound theorem would need:

1. a complete classification of all target possible images, including mixed
   bad/good rows, good-place integral regions, archimedean components, aggregate
   multi-prime B=I configurations, and Ind1-3 transports;
2. a proof that their hull has normalized volume at most sum H_p^Sp+h_inf;
3. TC-A..H/TC-S and an actual complete C.

None is in the frozen source.

## 6. Conclusion

The target hull is not generated exactly by B=O_K/B=I rows. TAME Section 6 is
only a fixed all-bad subfamily classification; the target also contains mixed
profiles, archimedean and good-place components. This is an exact structural
obstruction to S2 exact generation and to the upper-bound route. No arbitrary
region is chosen; the mixed region is the TAME Section 5 source construction,
and the arch component is part of the target definition.

target_accepted=false.
