# C9 independent possible-branch audit

Task: task-367 (Independent possible-branch audit). Owner: volumedet.
Date: 2026-10-25. Short theorem/exact gap only. Uniform scope, no mixed/E3,
no arbitrary data, no Lean/Project edits. Only this file written.
`target_accepted=false`.

## 0. Verdict

The target hull H_C is the hull of the **actual source possible-image family**
of the fixed C. It is not the hull of a free union of the two hypothetical
B=O_K and B=I branch alternatives. The B=O_K/B=I dichotomy in TAME §6 is an
actual classification of the finite image barGamma, not a pair of target
branches both included by definition.

Therefore:

- R_B is contained in H_C only when the **actual** branch is B=I (or an
  actual source generator moves the mod-p line l); under actual B=O_K/H_A-full,
  R_B is not a target possible image.
- The b=3 rescue `R_B subset H_C` is NOT independent of kappa/B; it is
  conditional on the actual branch. It is not a kappa-independent target
  theorem.
- If actual B=I and `R_B subset H_C` (target saturation/TC-B) and
  `h_inf>=-S_3`, then b=3 P6 follows. If actual B=O_K, this route is absent;
  P6 stays open (and no counterexample follows from C1).

Exact gap: actual B branch (equivalently actual barGamma/kappa and the
target-saturation inclusion), not a missing all-branch target definition.

## 1. What TAME §6 actually says

TAME §6 defines, for the actual additive image Γ of Aut(G_K),

    B := closed_Zp-span union_{alpha in Gamma} alpha(O_K).          (1.1)

It proves J⊂B⊂I and the dichotomy

    B=O_K or B=I.                                                (1.2)

The proof/interpretation is **actual**:

    if barGamma preserves l=O_K/J, then B=O_K;
    if some actual gamma moves l, the orbit and the realized symplectic
    action generate I/J, so B=I.                                 (1.3)

Thus B is the closed span of the actual Γ-orbit of O_K, not a formal choice
of one of two target branches. For a fixed all-bad tuple, only the actual
Gaussian integral regions, the full per-factor Γ action, and factor
permutations are used; the classification (1.2) is the possible outcome of
that actual subfamily, not an instruction to include both outcomes in H_C.

In particular R_A=Hull(L_A) and R_B=Hull(L_B) are the two local row hulls;
R_A⊂R_B is proved. But if the actual Γ satisfies B=O_K, no actual generator
produces L_B/R_B; L_B is the hull of a counterfactual larger orbit, not an
actual possible image.

## 2. What Ind1/target saturation actually says

TAME §5 and the Ind1 target analysis use the **actual** full Ind1 orbit:

    H_C contains F(Hull(union_gamma gamma_+(A(S))))                (2.1)

for the actual allowed gamma/beta gamma in the fixed source Ind1 family.
TC-B states H_C is the hull of the full union of target possible images
`T(beta gamma)(A(S))` for the **full source Ind1 orbit**, or F is an allowed
target automorphism. The quantifier is over actual source automorphisms of
the fixed C, not over both hypothetical B branches.

Consequently:

- If actual B=I, the full orbit includes both O_K-images (Aut(K)-type) and
  the B=I images; the target possible-image family can contain R_B.
- If actual B=O_K, all actual gamma(O_K)=O_K; the orbit generates R_A, not
  R_B. The hull of the actual union need not contain R_B.

Nothing in TAME §5-§6 or Ind1 says H_C is the hull of a formal union over
'B=O_K possibility' and 'B=I possibility' simultaneously.

## 3. Conditional b=3 theorem

The correct implication is branch-conditional:

Theorem 3.1. Assume the fixed uniform C has:

(C1) actual B=I (equivalently actual barGamma moves l; under the kappa
     criterion, 1<=kappa<=40);
(C2) target saturation/TC-B: `R_B subset H_C`;
(C3) archimedean `h_inf>=-S_3=-12/41 log p`.

Then `h_C>=h_B+h_inf>=Q_p`, i.e. b=3 P6 holds for that C.

Proof. B=I gives R_B as actual target possible image; (C2) gives
`h_C>=h_B+h_inf` by monotonicity; h_B=9/41 logp, Q_p=-3/41 logp, so
`Q_p-h_C<=-S_3-h_inf<=0`. QED.

Conversely, if actual B=O_K, (C2) is not a target fact; R_B is not actual,
and the rescue theorem has no hypothesis. C1 alone cannot prove P6 for
B=O_K, and no counterexample follows either (C1 is a lower bound on h_C).

## 4. Why this is not kappa-independent

The B branch is controlled by the actual trace/kappa data:

    kappa=e v_p(Tr y_1)-v_pi(y_1),
    kappa<=0: B=O_K;  1<=kappa<=40: B=I;  kappa>=41: not well-posed. (4.1)

Kondo 2026 does not supply the trace normalization/A=1 (task-359), so kappa
is uncomputed. Therefore neither B=O_K nor B=I is actual in the current
corpus; both are conditional. The possible-branch audit cannot remove this:
H_C is only over the actual orbit, and the actual orbit itself awaits kappa.

In particular, one may not argue:

    'B=O_K and B=I are both possible, so R_B is in H_C regardless;
     hence b=3 P6 is independent of kappa.'

That argument misreads a dichotomy of actual outcomes as a union over
hypothetical possibilities. It also conflicts with TAME §6's explicit
actual-generator criterion (1.3).

## 5. Possible target-branch formulations that would change this

An all-branch target would require an additional target definition:

(T-both) H_C := Hull( R_A union R_B union other actual images ),

i.e. a target explicitly saturated over both local row hulls independent of
the actual Γ. No such definition appears in TAME/Ind1/TC-B; TC-B uses the
actual full Ind1 orbit. Adopting (T-both) would be a target change
(arbitrary), not a source theorem.

Under (T-both), R_B⊂H_C would be definitional and b=3 P6 would follow with
`h_inf>=-S_3`, independent of kappa. But that is precisely the target
enlargement excluded by the original target and by task-286/task-323.

## 6. Classification

PROVED/ACTUAL:

- TAME §6 B is the closed span of the actual Γ-orbit of O_K; B=O_K or B=I
  is an actual dichotomy, not both included by definition.
- Ind1/TC-B target uses the actual full source Ind1 orbit.
- R_A⊂R_B is proved, but does not make R_B actual when B=O_K.
- Conditional theorem 3.1: actual B=I + R_B⊂H_C + h_inf>=-S3 => b=3 P6.

CONDITIONAL:

- actual B branch/kappa; target saturation R_B⊂H_C; arch h_inf>=-S3.

IMPOSSIBLE/WITHDRAWN:

- kappa-independent R_B⊂H_C from the bare B-dichotomy;
- treating both B outcomes as simultaneous target possibilities;
- adopting (T-both) without a target change;
- deriving b=3 P6 independent of actual B.

OPEN/MISSING:

- actual kappa/B (Kondo trace normalization); actual target saturation;
  actual arch lower bound; P6.

## 7. Conclusion

H_C is the hull of the actual source possible-image family, not of all
hypothetical B=O_K/B=I branches. TAME §6's B=O_K/B=I is the actual outcome of
barGamma; if B=O_K, R_B is not a target possible image. The b=3 rescue via
R_B is therefore conditional on actual B=I (hence on kappa in [1,40]), target
saturation, and h_inf>=-S3; it is not kappa-independent. A kappa-independent
version would require the extra target definition (T-both), which is a target
change and is not used.

## 8. Status

Short independent audit/theorem only. No arbitrary data, no mixed/E3, no
Lean/Project edits. Only this file written. `target_accepted=false`; P6 open.
