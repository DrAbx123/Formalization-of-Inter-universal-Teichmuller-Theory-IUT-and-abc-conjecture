# C9 mixed-profile arch component and B_I containment

Task: task-311. Date: 2026-10-25. Author: transport.
Short theorem/proof; conditional result and exact obstruction. No arbitrary
r_v/region; no Lean/Project edits. Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-MIXED-UPPER-20261025.md | 172 | 681FB626F7A491569CBA8FF27786EE3B5B68925648FC68BC24F771D825D4A7BE |
| C9-TAME-LOG-DOMAIN-20261025.md | 250 | 23B3514B94972DE511F1B17E23AB3DA832ED5BC63E89DACA3875ADEB07961F06 |
| C9-ARCH-LOWER-S3-20261025.md | 162 | 3847F1DEE3F3F73322A2F5F74E5ECC936E3FF0113BA3319FF76EA1D20904F73F |
| C9-ARCH-ACTUAL-RINF-20261025.md | 319 | 6AC23B85163E11706F8E26D96671437D8CFE80953FE5BA535BBA92FD5B15F236 |

## 1. Verdict

The mixed-profile arch component does NOT give B_I subset H_C,inf or h_inf>=0
in the frozen source. The implication is valid conditionally, but both the
containment and the arch lower bound are missing.

Conditional theorem:

    mixed profile with finite lower value m(rho) >= Q_p
    + B_I subset H_C,inf
    => h_inf>=0
    => h_C >= m(rho)+h_inf >= Q_p (for Q_p<0),
    i.e. P6 for that mixed profile.

Exact obstruction: the mixed profile is a **finite-place** construction; its
good finite factors do not force the archimedean possible-image hull to
contain B_I. IV gives the opposite container inclusion H_C,inf subset
pi^{j+1}B_I. No source theorem constructs the actual H_C,inf or proves
B_I subset H_C,inf. Thus h_inf>=0 remains open.

## 2. Mixed finite value

For 0<rho<1, TAME Section 5 gives

    m(rho):=-(1/m) sum_j rho^(j+1)(s_j+1/e),                   (2.1)
    h_p^mixed >= m(rho) log p.                                (2.2)

As rho->0, m(rho)->0. For any fixed Q_p=-(b/e)log p<0, one can choose a mixed
profile with m(rho)>=Q_p/log p (equivalently the finite lower value is above
the negative native q value). This is a source-valid choice of mixed profile,
not an arbitrary numerical region.

If also h_inf>=0, then

    h_C >= m(rho)log p + h_inf >= Q_p,
    F=Q_p-h_C<=0,                                               (2.3)

so P6 holds for that mixed profile.

## 3. Why B_I containment would give h_inf>=0

Under B_I-zero, logvolume(B_I)=0. If B_I subset H_C,inf, monotonicity gives

    h_inf >= logvolume(B_I)=0.                                 (3.1)

Thus the mixed route reduces P6 to the single arch containment B_I subset
H_C,inf. This is exactly the same missing arch input as task-270/arch.

## 4. Exact obstruction

The B_I containment does NOT follow from:

1. **B_I-zero normalization.** logvolume(B_I)=0 fixes a reference; it does not
   say B_I is contained in the actual possible-image hull.

2. **IV container inclusion.** IUT IV gives H_C,inf subset pi^{j+1}B_I, the
   opposite direction. B_I is contained in pi^{j+1}B_I, but that does not put
   it in H_C,inf.

3. **Mixed finite good factors.** A mixed profile has some good finite factors,
   but the archimedean possible-image set is a separate source object. A good
   finite factor does not imply a unit ball at the archimedean place; the
   Theta/Gaussian arch action depends on the actual local values, not on the
   finite good label.

4. **Tensor structure.** Even if one tensor factor contributes a unit ball,
   B_I is a product of unit balls over all direct-summand copies. Containing
   one factor's unit ball does not give the full B_I in the total arch packet.

5. **No actual H_C,inf.** Task-232 establishes that the actual archimedean
   possible-image set/radius is not constructed; only the IV upper container
   and the B_I-zero formal normalization are available.

Therefore B_I subset H_C,inf and h_inf>=0 are not proved. The mixed profile
does not by itself give the arch component; it only gives the finite value
approaching 0.

## 5. Could the mixed arch component contain B_I for a different reason?

A genuine source argument would need to show that the Θ-pilot archimedean
possible images of a mixed profile fill a unit ball in H_C,inf. The source
provides the tensor/BPS action and the IV container, but not such a filling
statement. The container is an upper bound; a filling statement is a lower
bound/sharpness property analogous to the missing task-267 upper bound. No
source theorem supplies it.

Absent that, the mixed route cannot prove P6 for negative Q_p profiles; it only
gives the conditional implication (2.3).

## 6. Conclusion

The mixed-profile arch component does not prove B_I subset H_C,inf or
h_inf>=0. The exact obstruction is the missing actual archimedean possible-image
hull: IV gives only H_C,inf subset pi^{j+1}B_I, while B_I containment is the
opposite lower-volume statement. The conditional theorem

    mixed profile with m(rho)>=Q_p + B_I subset H_C,inf
    => P6 for that mixed profile

is valid, but both inputs are missing. No arbitrary r_v or region was chosen.
The b=273 counterexample side and the b=3 B=I P6 side remain open.

target_accepted=false.