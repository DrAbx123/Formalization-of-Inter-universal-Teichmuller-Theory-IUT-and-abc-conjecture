# C9 attack: H_A-full with non-filtration alpha in H=Phi^-1(Sp)

Task ID: task-214 / C9-HAFULL-NONFILTRATION-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact local research only; no Lean/Project edits; no target changes; no arbitrary alpha; no filtration assumption; no W subset J; only this file written.

## 0. Inputs and binding corrections

- C9-AUDIT-UNIT-FILTRATION-20261025.md (task-208), SHA256 8d715581577f057c151cc7023b98f5a896a04121efc32d13b6ebaef21c563e09.
- C9-HAFULL-INTEGRALITY-20261025.md (task-204), SHA256 16523153a35bf386899ac2f36eb6db53c777f7ca704034615646bd84df002929.
- C9-HAFULL-ALPHA1-20261025.md (task-195), SHA256 ba8459c4500b8e73acfa12a3c20431c5fdf8ed1af077ddd453f5d3c4f2e6a43b.
- C9-SYMPLECTIC-SOURCE-20261025.md (task-147), SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (task-180), SHA256 7cc2ddd03cfefa97e38049ca1ccb90016e944dece0185f706e42f7f97cd61fd8.

Binding: task-208 audits that task-204's filtration premise is false. Kondo 2025 Theorem A says the subgroup of Out(G_K) preserving the upper ramification filtration is exactly the finite field-theoretic subgroup Aut(k); the corrected donor H=Phi^-1(Sp_{2g}(Z_p)) has infinite symplectic image and is not contained in Aut(k). Hence H contains actual alpha outside Aut(k), and those alpha do not preserve the upper filtration. This file does not assume filtration preservation.

Goal: compute or bound alpha^times(exp p), a(alpha)=p^{-1}log(alpha^times(exp p)), and alpha_+(1) for such alpha; decide whether a(alpha) lies in O_K, in I minus O_K, or gives B=I; decide the full B branch or isolate the exact obstruction. No W subset J and no y-basis/I-J assumption.

## 1. Actual non-filtration alpha in H

Kondo 2026 Definition3.2 and Lemma3.3 give the closed subgroup

    H = Phi^{-1}(Sp_{2g}(Z_p)) subset Out(G_K),   Phi(H)=Sp_{2g}(Z_p),   (1.1)

with H acting on k_+(G_K) as diag(1,A) in a fixed Q_p-basis U direct-sum W, A in Sp_{2g}(Z_p), dim U=1, dim W=2g=40 for d=41. H is infinite.

Kondo 2025 Theorem A: if alpha in Out(G_K) preserves the upper ramification filtration, then alpha lies in the finite subgroup Aut(k). Since H is infinite and Aut(k) is finite, H is not contained in Aut(k). Therefore there exist actual

    alpha in H minus Aut(k),                                      (1.2)

and by Theorem A such alpha does not preserve the upper ramification filtration. Consequently alpha^times(U^n) is not equal to U^n for at least one n; in particular the task-204 filtration argument is unavailable for these alpha.

This establishes existence of a non-filtration actual donor element; it does not by itself produce a fully explicit matrix for alpha. The matrix of alpha_+ in the 2026 U/W basis is diag(1,A) for some nontrivial A in Sp_{2g}(Z_p), but the actual preimage alpha and its action on O_K require the reconstruction identification. No arbitrary alpha is introduced: the statement is quantified over H minus Aut(k).

## 2. Canonical part: a(alpha)=alpha_+(1) still holds

Kondo 2026 Theorem2.6 proof gives the log compatibility

    alpha_+ log_k = log_k alpha^times                              (2.1)

for every alpha in Out(G_K), independently of filtration. For exp_k(p),

    exp_k(p) in 1+pO_K,   log_k(exp_k(p))=p,                       (2.2)

so

    log_k(alpha^times(exp_k(p))) = alpha_+(log_k(exp_k(p))) = alpha_+(p)
                                  = p alpha_+(1),                 (2.3)
    a(alpha)=p^{-1} log_k(alpha^times(exp_k(p))) = alpha_+(1).    (2.4)

Thus, for non-filtration alpha as well, a(alpha) is exactly alpha_+(1). The question of whether a(alpha) is integral is exactly the question of whether the vector alpha_+(1) lies in O_K.

## 3. Structure of alpha_+(1) in the U/W basis

Let the 2026 symplectic decomposition be K=U direct-sum W, with U the line fixed by H and W the 2g-dimensional Sp-module. Write

    1 = u_0 + w_0,   u_0 in U,   w_0 in W.                       (3.1)

For alpha in H with alpha_+|U=id and alpha_+|W=A in Sp_{2g}(Z_p),

    alpha_+(1) = u_0 + A w_0.                                   (3.2)

Therefore

    a(alpha)=u_0 + A w_0.                                       (3.3)

This is the exact computation of a(alpha)/alpha_+(1) in terms of the U/W coordinates of 1. It does not use filtration and does not use W=ker Tr subset J.

## 4. Integrality and B-branch criteria

Let B_O be a Z_p-basis of O_K and C the change-of-basis matrix from the 2026 U/W Q_p-basis to B_O. Then

    a(alpha) in O_K  iff  C^{-1}(u_0 + A w_0) in Z_p^{41}.       (4.1)

Equivalently, if M_A is the matrix of alpha_+ in the O_K basis, integrality of a(alpha) is the condition that the first column of M_A (image of 1) is integral.

Since alpha_+(J)=J follows from (2.1) and alpha^times(O_K^times)=O_K^times (independent of filtration), one has

    alpha_+(O_K)=Z_p a(alpha)+J.                                 (4.2)

Thus:

1. If a(alpha) in O_K, then alpha_+(O_K) subset O_K; with the inverse argument (same J) equality holds, and this alpha preserves O_K.
2. If a(alpha) in I minus O_K (I=p^{-1}J), then alpha_+(O_K) subset I but not O_K; the B-span of this alpha lies in I and can contribute to B=I.
3. If a(alpha) not in I, then alpha_+(O_K) is not contained in I; the B=O_K/B=I dichotomy is not defined for this alpha.

The full H_A-full for H is therefore equivalent to

    (H_A-full_H)  u_0 + A w_0 in O_K for every A in Sp_{2g}(Z_p)   (4.3)

and the full B branch for H is:

- B_H=O_K if (4.3) holds;
- B_H=I if every a(alpha) lies in I and the orbit generates I/J;
- B_H not in the O_K/I dichotomy if some a(alpha) is outside I.

## 5. What can be decided from the current sources

The cited papers supply H, its abstract diag(1,A) action on a Q_p-basis U/W, and the log compatibility. They do **not** supply:

1. the coordinates u_0,w_0 of the actual element 1 in the 2026 U/W basis;
2. the change-of-basis matrix C from that Q_p-basis to a Z_p-basis of O_K (equivalently, the integral normalization of W);
3. a fully explicit preimage alpha in H of a nontrivial A, together with its matrix on O_K.

Without (1)-(3), (4.3) cannot be evaluated and the integrality of a(alpha) is not determined. This is the exact obstruction. Note:

- Non-filtration of alpha (Theorem A) does not imply a(alpha) not in O_K; a could be integral even if alpha fails to preserve some U^n.
- Filtration preservation of alpha is not needed for (2.4), but task-204 used it to prove a in O_K; task-208 correctly invalidates that route.
- The compactness of H gives only a bound: the orbit H.1 is bounded in K, so there is an integer N (depending on C) with a(alpha) in p^{-N}O_K for all alpha in H. This does not imply a in O_K or even in I, and N is not computed.
- No filtration or W subset J is used in the formula (3.3); the missing data are the integral coordinates of 1 and the actual O_K action.

## 6. Conditional decisions

Under the natural trace alignment U=trace line (not proved; E16), if 1 were in U, then w_0=0 and a(alpha)=1 in O_K; H_A-full for H and B_H=O_K would follow. This is only a conditional special case; no source states 1 in U, and the alignment is inferred, not a theorem.

Under a generic non-aligned decomposition, u_0,w_0 may have denominators; for A in Sp_{2g}(Z_p) the vector A w_0 need not lie in O_K. This is a possible nonintegral branch, but it is not an actual counterexample without the missing coordinates/matrices.

If one assumes the 2026 symplectic basis is integral for O_K and 1 lies in its U-part, then H_A-full holds; if one assumes only Q_p alignment, no conclusion. These are assumptions, not source facts.

## 7. B branch verdict

The full B branch for H is **not decided** by the current source data. The exact obstruction is the triple (u_0,w_0,C) / actual alpha matrices in (4.3). The possibilities are:

- H_A-full_H and B_H=O_K if (4.3) holds;
- B_H=I if all a(alpha) lie in I minus O_K and the orbit generates I/J;
- B_H outside the O_K/I dichotomy if some a(alpha) is outside I.

Task-204's B=O_K/B=I exclusion for full Out is withdrawn (task-208 already invalidated its filtration premise). Task-195's W/trace route remains an independent conditional construction; task-214 does not use it. The full H_A-full question is open unless the missing integral coordinates are supplied.

## 8. Actual / conditional / missing

Actual:

- H=Phi^{-1}(Sp_{2g}(Z_p)) is infinite; Aut(k) is finite; there exist actual alpha in H minus Aut(k), non-filtration (Kondo 2025 Theorem A).
- Log compatibility gives a(alpha)=alpha_+(1) for every alpha, including non-filtration ones.
- In the U/W basis, a(alpha)=u_0+A w_0; this is exact.

Conditional:

- The identification of the 2026 U/W basis with k_+ and the coordinates of 1; the integral normalization C; the actual preimage alpha.
- Any decision of H_A-full_H or B_H.

Missing:

- u_0,w_0,C, actual alpha matrices; explicit integrality test (4.1); full B branch.
- Complete C, TC-A..TC-H/TC-S, archimedean h_inf, global h_C>=Q_C; no target closure.

Withdrawn:

- Task-204's all-Out filtration claim; its B=O_K/B=I exclusion; any unconditional a(alpha) in O_K.

## 9. Next executable steps

1. Compute the 2026 U/W coordinates u_0,w_0 of 1 from the actual Kondo reconstruction basis and the change-of-basis C to O_K. This is the first missing exact object.
2. Choose an actual alpha in H minus Aut(k) (nonfiltration existence) and compute its preimage matrix on O_K; test (4.1).
3. If a nonintegral alpha is found, test whether a(alpha) lies in I minus O_K and whether the H-orbit generates I/J; this decides B=I versus an intermediate/undefined B.
4. If all a(alpha) are integral, prove (4.3) for all Sp matrices; then H_A-full_H and B_H=O_K follow.
5. Probe whether the H action can be conjugated to an integral O_K action; the present data only give Q_p alignment, so this is not assumed.

Status: stage1 natural-language/exact local arithmetic only. No Lean/Project/kernel/comparator/edit; only this file written. target_accepted=false; complete C9/P6/ABC not proved.
