# C9 possible-image branches vs actual B branch

Task: task-362. Owner: kummer. Date: 2026-10-25.
Short audit/theorem; no Lean/Project edits; no mixed/E3; no arbitrary data.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs

- C9-TAME-LOG-DOMAIN-20261025.md, 251 lines,
  SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06;
  especially section6 (B=closed span over actual Gamma; L_A/L_B classification).
- C9-IND1-GLOBAL-20261025.md, 532 lines,
  SHA256 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8;
  IUT I Def4.10/Prop4.11, IUT III Thm3.11/Cor3.12.
- C9-BI-REGION-CONSTRUCTION-20261025.md (task-274),
  SHA256 3726f7300cd099e4da97f9fb0c5b810df11f9a7bf62e8ed48bac5a987ca53655.
- C9-B3-P6-ASSEMBLY-20261025.md, SHA256
  a674fd983f1cbea7b5293559a37cc4cd613ba4de8ebcfea4822cee7a2c55e4a1.
- C9-HAFULL-CONSTRUCT-20261025.md, 128 lines,
  SHA256 06299f26383af7da73dc8bb844f2fef7c939d486bd922cec5e1785f0df0cbbf4.

## 1. Verdict

H_C is the hull of possible images under the **actual** source/Ind1 action of
the fixed C. It is **not** the hull of an arbitrary union of both abstract
B=O_K and B=I branches. The B branch is a property of the actual
barGamma/Out action, not a free label choice.

Consequences:

- If the actual branch is B=I, then the TAME/BI row family L_B is a source
  possible-image family and R_B subset H_C is legitimate (conditional on the
  B=I source object and TC-B).
- If the actual branch is B=O_K, then the source row family is L_A; L_A subset
  L_B, but L_B is **not** an actual possible-image family of that C, so
  R_B subset H_C is not available unconditionally.
- Therefore b=3 P6 via R_B is **conditional on actual B=I**, not independent
  of kappa. The "both branches are possible images" reading is not supported
  by TAME section6/IUT Ind1.

## 2. What TAME section6 says

Let Gamma be the actual image of Aut(G_K) in GL(K_+) and

    B = closed Zp-span union_{alpha in Gamma} alpha(O_K).             (2.1)

TAME section6 proves:

    B=O_K if barGamma preserves the line l=O_K/J;
    B=I if some actual gamma moves l.                              (2.2)

The exact classification of the fixed all-bad subfamily is:

    if B=O_K: L_A=sum_i p^s pi_i D_r;
    if B=I:   L_B=p^{s-r+1} J^{tensor r}.                          (2.3)

Crucially, (2.2)-(2.3) is a classification of **the actual Gamma**. The source
does not say that both L_A and L_B occur for one fixed C, nor that the target
hull is the hull of both branch lattices. It says the actual input determines
which lattice is generated; if B=O_K, L_B is not produced by the actual
Gamma-orbit, even though L_A subset L_B as abstract lattices.

TAME also states that one cannot choose the second branch by enumerating all
of GL_e(F_p); the actual barGamma/line-l question must be computed. This is a
statement about the actual branch, not an invitation to include both.

## 3. What IUT Ind1 says

IUT I Def4.10/Prop4.11: Ind1 is the indeterminacy from automorphisms of the
procession of D-prime-strips; at a fixed level it is a capsule-full
poly-automorphism (index permutation plus constituent D-prime-strip
isomorphisms). IUT III Cor3.12 defines the target hull as the holomorphic hull
of the union of possible images under (Ind1),(Ind2),(Ind3) of the actual
Theta-pilot object.

The automorphism group used is the **actual** source/procession automorphism
group of the fixed C, not an abstract direct product of B=O_K and B=I choices.
The B branch is determined by the actual outer automorphism action on I/J
(TAME (2.2)); Ind1 transports that actual action. It does not add an
independent second branch.

Thus the possible-image family of the fixed C has one actual B branch. The
hull H_C is not the hull of "all abstract B branches"; it is the hull of the
actual source orbit (plus the actual arch component).

## 4. Conditional b=3 P6

Let C be a fixed b=3 uniform target. If the actual B branch is B=I and the
B=I row family is realized/transported (TC-B), then

    R_B subset H_C,   h_C >= H_B+h_inf.                            (4.1)

With H_B=(9/41)logp and S3=(12/41)logp, this gives

    F=Q_C-h_C <= -S3-h_inf.                                       (4.2)

If additionally h_inf>=-S3, P6 holds (F<=0) for that C. This is the b=3 B=I
corridor.

But:

- B=I actual is **not proved**; kappa/B is source-undetermined (task-269/273);
- h_inf>=-S3 is not proved;
- R_B subset H_C is conditional on TC-B/B=I.

If the actual branch is B=O_K, then only L_A is an actual source row; R_B is
not a subset of H_C from this argument, and the b=3 P6 claim cannot be made
from H_B.

The "both branches possible images" assumption would make R_B subset H_C
independent of actual kappa, but that assumption is a **branch-choice/
profile change**, not a source theorem. It is excluded here.

## 5. Exact gap

The exact missing source input is:

(G-B) an actual B=I realization/generator whose barGamma moves l=O_K/J and
      whose B=I row family L_B is an actual possible-image family of the fixed
      C (not an abstract alternative).

Without (G-B), R_B is conditional. With (G-B) and h_inf>=-S3 and TC-B, b=3
P6 follows in the B=I corridor. No source-valid b=3 P6 exists without it.

No mixed/E3 profile is used. The B=O_K and B=I branches are not mixed or
averaged; only the actual branch is allowed.

## 6. Classification

| item | status |
|---|---|
| B branch determined by actual Gamma/barGamma | TAME section6 |
| both B=O_K and B=I are possible images of one fixed C | FALSE/NOT STATED |
| H_C hull of actual source possible images | IUT Cor3.12 |
| B=I actual / kappa in [1,40] | NOT PROVED |
| R_B subset H_C | CONDITIONAL on B=I + TC-B |
| b=3 B=I + h_inf>=-S3 => P6 | CONDITIONAL |
| b=3 P6 independent of actual kappa | NO |
| exact gap G-B | actual B=I source realization |

## 7. Conclusion

The possible-image family is the actual Ind1/Ind2/Ind3 orbit of the fixed C,
not an abstract union of both B branches. TAME section6's L_A/L_B classification
is conditioned on the actual barGamma: only one branch is generated. Therefore
R_B subset H_C is available only if the actual branch is B=I (and TC-B holds),
and b=3 P6 via H_B additionally needs h_inf>=-S3. This is a conditional
corridor, not an unconditional P6 theorem independent of kappa. The exact
missing input is an actual B=I realization (G-B); no arbitrary branch union or
mixed profile is used.

No Lean/kernel closure; target_accepted=false; P6 open.

## 8. Status

- Short source audit/theorem only; no Lean/Project edits.
- Actual-branch interpretation of TAME section6/IUT Ind1 recorded; b=3 P6
  conditional on actual B=I + h_inf>=-S3 + TC-B.
- target_accepted=false.
