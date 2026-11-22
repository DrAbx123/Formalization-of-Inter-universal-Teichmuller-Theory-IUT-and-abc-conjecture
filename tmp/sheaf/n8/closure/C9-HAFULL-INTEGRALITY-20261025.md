# C9 H_A-full integrality: a(alpha)=p^{-1} log(alpha^times(exp p))

Task ID: task-204 / C9-HAFULL-INTEGRALITY-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact local mathematics only; no Lean/Project edits; no target changes; no arbitrary element; no W subset J used; only this file written.

## 0. Inputs and status

- C9-HAFULL-ALPHA1-20261025.md (task-195), SHA256 ba8459c4500b8e73acfa12a3c20431c5fdf8ed1af077ddd453f5d3c4f2e6a43b.
- C9-HAFULL-CONSTRUCT-20261025.md (task-194), SHA256 c02d4a24cd201ad6f0fc2d5e308772f943ae29c911058f40ed19a2c8d7ba6878.
- C9-SYMPLECTIC-SOURCE-20261025.md (task-147), SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (task-180), SHA256 7cc2ddd03cfefa97e38049ca1ccb90016e944dece0185f706e42f7f97cd61fd8.
- C9-ERROR-LEDGER-20261025.md (task-164, current), SHA256 0dbd2b61e4e8944508e2cee6de6c0aa6e5fe26484eb2c9b174dfc72fe77d4b5b; E16/E20 binding.

Target: decide whether

    a(alpha) := p^{-1} log_k(alpha^times(exp_k(p)))                       (0.1)

lies in O_K for every full Out(G_K) generator, and whether this constructs H_A-full without using W=ker Tr subset J. The answer is yes, subject to the standard ramification-filtration/reciprocity input and the Kondo log compatibility; the proof is independent of the trace/W route of task-195.

## 1. Local setup and exact observations

Let K/Q_p be tame totally ramified cyclic, e=l=41, p=12301, f=1, d=41, K^{d=1}=Q_p, O_K=Z_p[pi], pi^e=p u, u in Z_p^times, m=(pi), J=log_k(O_K^times)=m, I=p^{-1}J. Let

    U^n := 1 + pi^n O_K,  n>=1,   U^e=1+pO_K.              (1.1)

Because p is odd and K/Q_p is finite, exp_k converges on pO_K and log_k converges on 1+pO_K; they are inverse there. In particular

    exp_k(p) in 1+pO_K=U^e,   log_k(exp_k(p))=p.             (1.2)

The p-adic log is defined on U^1 and maps U^e=1+pO_K into pO_K: for x in O_K,

    log_k(1+p x) = p x - p^2 x^2/2 + ...  in pO_K.           (1.3)

Therefore, for any unit u in U^e, p^{-1}log_k(u) is in O_K. This is the integrality mechanism used below; no trace kernel and no W subset J is involved.

## 2. The action alpha^times on the unit filtration

Local class field theory gives the reciprocity isomorphism rec_K: K^times -> G_K^ab. The higher ramification subgroups of G_K (upper numbering) are group-theoretic; under rec_K their images are the standard subgroups U^n=1+pi^nO_K of O_K^times. Therefore every automorphism of G_K preserves the filtration {U^n}; equivalently, for every alpha in Out(G_K),

    alpha^times(U^n)=U^n  for all n>=1.                       (2.1)

This is standard local class field theory: the upper ramification filtration is intrinsic to the absolute Galois group, and reciprocity is compatible with automorphisms. It is not a new hypothesis about the Kondo donor; it is the same inertia/reciprocity interface used in task-194. In the audit language, this is the paper-level filtration input.

In particular, alpha^times preserves U^e=1+pO_K, and

    alpha^times(exp_k(p)) in U^e.                             (2.2)

Hence

    log_k(alpha^times(exp_k(p))) in pO_K,                     (2.3)
    a(alpha)=p^{-1}log_k(alpha^times(exp_k(p))) in O_K       (2.4)

for every alpha in Out(G_K). This is the first conclusion: **a(alpha) lies in O_K for all full Out generators**, under (2.1).

## 3. Identification a(alpha)=alpha_+(1)

Use the Kondo 2026 Theorem2.6 proof compatibility (the diagram in the proof of Theorem2.6)

    alpha_+ log_k = log_k alpha^times,                        (3.1)

for the reconstructed additive action alpha_+ on k_+(G_K) and the unit action alpha^times. This is the same paper-level diagram cited in task-195, now applied only to the single element exp_k(p).

By (1.2) and (3.1),

    log_k(alpha^times(exp_k(p))) = alpha_+(log_k(exp_k(p)))
                                  = alpha_+(p).                (3.2)

Since alpha_+ is Q_p-linear and p is the rational prime seen in K,

    alpha_+(p) = p alpha_+(1).                                (3.3)

Therefore

    a(alpha) = p^{-1} alpha_+(p) = alpha_+(1).                (3.4)

The integrality (2.4) is exactly

    alpha_+(1) in O_K  for every alpha in Out(G_K).           (3.5)

This constructs alpha_+(1) explicitly as a(alpha)=p^{-1}log_k(alpha^times(exp p)), without using W or the trace decomposition of task-195.

## 4. H_A-full from alpha_+(1) in O_K

It remains to recover J and O_K preservation. By (3.1) and alpha^times(O_K^times)=O_K^times,

    alpha_+(J) = alpha_+(log_k(O_K^times)) = log_k(O_K^times) = J.   (4.1)

Thus alpha_+ preserves J and I=p^{-1}J, and acts F_p-linearly on I/J. Since O_K=Z_p 1+J and alpha_+ is Q_p-linear,

    alpha_+(O_K)=Z_p alpha_+(1)+alpha_+(J) subset Z_p O_K+J=O_K.    (4.2)

Applying the same argument to alpha^{-1}: alpha^{-1}_+(1) in O_K and alpha^{-1}_+(J)=J, so alpha^{-1}_+(O_K) subset O_K. Applying alpha_+ gives O_K subset alpha_+(O_K). Hence

    alpha_+(O_K)=O_K                                             (4.3)

for all alpha in Out(G_K). This is H_A-full; it uses no W subset J and no y-basis.

## 5. B branch consequences

By (4.3) and (4.1), every full Out generator satisfies

    alpha(O_K)=O_K, alpha(J)=J, alpha(I)=I.                       (5.1)

The branch span

    B=closed Z_p-span union_{alpha in Out} alpha(O_K)             (5.2)

is therefore O_K. So:

- B=O_K for the full Out action;
- B=I is excluded;
- the conditional b=3 B=I value 9/41 is not actual;
- the B=O_K branch is the actual full-Out branch under the stated paper-level dependencies.

Moreover alpha_+(1) mod J = a(alpha) mod J; since alpha_+(O_K)=O_K and alpha_+(J)=J induce an F_p-linear automorphism of the one-dimensional quotient O_K/J, the class of a(alpha)=alpha_+(1) modulo J is nonzero; hence l is stable. B=I cannot arise.

## 6. Relation to task-195 and the no-W condition

Task-195 proved alpha_+(1) in O_K by the trace-kernel route: W=ker Tr=span(pi,...,pi^40) subset J, alpha_+(W)=W, Tr o alpha_+=lambda Tr, lambda in Z_p^times, and alpha_+(1)=lambda1+w. That route is independent and remains valid as audited in task-200.

This file gives a **second, independent construction** that avoids W entirely:

    a(alpha)=p^{-1}log(alpha^times(exp p))=alpha_+(1) in O_K.       (6.1)

The integrality comes from U^e=1+pO_K and the reciprocity/ramification filtration, not from ker Tr subset J. The two constructions agree because both compute alpha_+(1).

No use of the y-basis as an I/J basis is made; E16 is respected.

## 7. Actual / conditional / missing

Actual local algebra:

- e=41, p=12301, U^e=1+pO_K, exp_k(p) in U^e, log_k(U^e) subset pO_K, so p^{-1}log_k(U^e) subset O_K.
- The identity a(alpha)=alpha_+(1) is exact from the log compatibility and Q_p-linearity.

Conditional / paper-level:

- The reciprocity/ramification filtration preservation (2.1) (standard local class field theory; the upper filtration is group-theoretic).
- The Kondo 2026 Theorem2.6 proof diagram (3.1) and the identification of alpha^times/alpha_+ with the actual actions.
- The reconstruction identification k_+(G_K)=K and O^times(G_K)=O_K^times.

Missing:

- Explicit a(alpha)/alpha_+(1) matrices for full generators beyond the field subgroup.
- A formal Lean/kernel verification of the reciprocity filtration and Kondo diagram.
- Complete C, S_bad, q/BPS/gluing, row/Theta weights, TC-A..TC-H/TC-S, actual archimedean h_inf; no global h_C>=Q_C.

Withdrawn:

- Any B=I branch for full Out under these inputs; the b=3 9/41 surplus; any use of W subset J for this particular integrality proof.

## 8. Verdict

**a(alpha) lies in O_K for every full Out(G_K) generator**, and equals alpha_+(1), under the standard reciprocity/ramification filtration and the Kondo log compatibility. Consequently H_A-full holds for full Out, B=O_K, and B=I is excluded. This is a second construction independent of the task-195 W/trace route; there is no obstruction in this route.

The result is paper-level/natural-language, not Lean/kernel verified. It does not construct a complete C or prove the global target. target_accepted=false; complete C9/P6/ABC not proved.
