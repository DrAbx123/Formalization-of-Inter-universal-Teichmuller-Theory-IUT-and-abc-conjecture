# C9 attack: alpha_+(1) and full O_K preservation for the B branch

Task ID: task-195 / C9-HAFULL-ALPHA1-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact local mathematics only; no Lean/Project edits; no target changes; no arbitrary element; only this file written.

## 0. Inputs and status

- C9-HAFULL-CONSTRUCT-20261025.md (task-194), SHA256 c02d4a24cd201ad6f0fc2d5e308772f943ae29c911058f40ed19a2c8d7ba6878.
- C9-SYMPLECTIC-SOURCE-20261025.md (task-147), SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (task-180), SHA256 7cc2ddd03cfefa97e38049ca1ccb90016e944dece0185f706e42f7f97cd61fd8.
- C9-MODP-BRANCH-PROOF-20261025.md (task-154), SHA256 af543bbbc50e8ec8cf9909cd5675d830018254760abc66410c81501a7227eade.
- C9-ERROR-LEDGER-20261025.md (task-164, current), SHA256 0dbd2b61e4e8944508e2cee6de6c0aa6e5fe26484eb2c9b174dfc72fe77d4b5b; E16/E20 binding.

Binding: the Kondo y-basis is not an I/J basis (E16). This file does not use the y-basis as an I/J basis, and does not assume B=I or B=O_K. The only inputs beyond task-194 are the H_A-lite action on J/I, the group-theoretic trace-kernel theorem (Kondo Theorem E/1.3), and the compactness of Out(G_K). The result is a conditional construction: if H_A-lite is accepted, full H_A-full follows and B=O_K for the full Out action. No complete C, target containment, or global inequality is claimed.

## 1. Exact local setup

Let K/Q_p be tame totally ramified cyclic, e=l=41, p=12301, f=1, d=[K:Q_p]=e=41, K^{d=1}=Q_p (the only proper subfield of the prime-degree extension is Q_p), O_K=Z_p[pi], pi^41=p u, u in Z_p^times, m=(pi), J=log(O_K^times)=m, I=p^{-1}J.

Since p=12301 does not divide 41, Tr_{K/Q_p}(1)=41 is nonzero mod p; the trace map is nonzero. The line l=O_K/J is the image of Z_p 1 in I/J; its trace is nonzero. The trace table in the pi-power basis is

    Tr(pi^a)=0 for 1<=a<=e-1=40,   Tr(1)=e=41.                  (1.1)

Thus W:=ker Tr is spanned by pi, pi^2, ..., pi^40 and has dimension 40; in particular

    W subset m=J.                                                (1.2)

The Kondo y_i=F(x_i) lie in J and vanish in I/J; they are not used below. The canonical F_p basis of I/J remains the pi-power basis of task-194.

## 2. H_A-lite input from task-194

Task-194 constructs, under the Kondo log compatibility

    alpha_+ log_k = log_k alpha^times,                           (2.1)

the H_A-lite action of full Out(G_K): every alpha preserves J and I, acts Z_p-linearly on J and F_p-linearly on I/J. This is the only integral-lattice input used here. If (2.1) is not accepted, the conclusion below becomes conditional on it; no other arbitrary element or generator is introduced.

The task-194 finite-index subgroup Gamma_0=Stab(O_K) is not used as a substitute for the full group.

## 3. Trace-kernel preservation

Kondo 2025 Theorem E (Theorem 1.3 in the 2025 numbering) gives the group-theoretic description

    W = ker(Tr_{K/K^{d=1}}) = <y_2,...,y_d>_{Q_p}                  (3.1)

for odd d, with d=e=41 and K^{d=1}=Q_p. The description is group-theoretic: it is preserved by the action of Out(G_K) on k_+(G_K). Therefore, for every alpha in Out(G_K),

    alpha_+(W)=W.                                                (3.2)

Since W is the kernel of the actual trace functional Tr, (3.2) implies that the functional Tr o alpha_+ has the same kernel W. Any two nonzero Q_p-linear functionals on the d-dimensional K with the same kernel are scalar multiples, so there is a unique

    lambda(alpha) in Q_p^times  such that
    Tr o alpha_+ = lambda(alpha) Tr.                             (3.3)

The map alpha -> lambda(alpha) is a continuous homomorphism Out(G_K) -> Q_p^times: composition of functionals multiplies the scalars. Out(G_K) is compact (profinite topology), so the image of this continuous homomorphism is a compact subgroup of Q_p^times. Since Q_p^times = p^Z x Z_p^times with p^Z discrete, every compact subgroup lies in Z_p^times. Hence

    lambda(alpha) in Z_p^times for all alpha.                    (3.4)

In particular lambda(alpha) is nonzero and p-adically integral.

## 4. Construction of alpha_+(1) and full O_K preservation

Decompose K as a Q_p-vector space:

    K = Q_p 1 direct-sum W,    Tr(1)=e=41 !=0.                  (4.1)

Write

    alpha_+(1) = c(alpha) 1 + w(alpha),  c(alpha) in Q_p, w(alpha) in W.   (4.2)

Apply Tr to both sides and use (3.3):

    lambda(alpha) Tr(1) = Tr(alpha_+(1)) = c(alpha) Tr(1) + Tr(w(alpha)).

Since w(alpha) in W=ker Tr, this gives c(alpha)=lambda(alpha). Therefore

    alpha_+(1) = lambda(alpha) 1 + w(alpha),                    (4.3)
    lambda(alpha) in Z_p^times,   w(alpha) in W subset J.        (4.4)

Hence

    alpha_+(1) in Z_p + J = O_K.                                (4.5)

Now use H_A-lite alpha_+(J)=J. Since O_K=Z_p 1 + J and alpha_+ is Q_p-linear,

    alpha_+(O_K) = Z_p alpha_+(1) + alpha_+(J) subset Z_p O_K + J = O_K.   (4.6)

Apply the same argument to alpha^{-1}: alpha^{-1}_+(1) in O_K and alpha^{-1}_+(J)=J, so alpha^{-1}_+(O_K) subset O_K. Applying alpha_+ gives O_K subset alpha_+(O_K). Therefore

    alpha_+(O_K)=O_K for every alpha in Out(G_K).                (4.7)

This is H_A-full for the full Out(G_K), conditional only on the H_A-lite input (2.1) and the group-theoretic trace-kernel theorem (3.1). The construction of alpha_+(1) is explicit: lambda(alpha) is the scalar in (3.3) and w(alpha)=alpha_+(1)-lambda(alpha) lies in W. No y-basis and no arbitrary choice are used.

## 5. Consequences for the B branch

By (4.7), every actual gamma in full Out(G_K) preserves O_K; by H_A-lite it also preserves J and I. Therefore

    gamma(O_K)=O_K, gamma(J)=J, gamma(I)=I                  (5.1)

for all gamma in Out(G_K). The branch span is

    B = closed Z_p-span union_{gamma in Out} gamma(O_K) = O_K.   (5.2)

Thus, under the stated conditional inputs, the full B branch is B=O_K, and B=I does not occur. In particular:

1. The conditional b=3 B=I value 9/41 is not selected by full Out. The B=O_K residual 408/41 is the relevant conditional finite value.
2. The earlier finite-index subgroup Gamma_0 is not proper in its effect: H_A-full holds on all of Out by (4.7), so the coset gap of task-194 is eliminated at the level of lattice preservation.
3. The line l=O_K/J is stable: (4.3) gives alpha_+(1) mod J = lambda(alpha) mod J, a nonzero scalar, so alpha(l)=l for all alpha. The B=I generator cannot exist.
4. The branch B=I is excluded, not merely unconstructed, conditional on (2.1) and (3.1).

## 6. What is actual, conditional, and missing

Actual local arithmetic:

- K/Q_p tame totally ramified e=41, d=41, K^{d=1}=Q_p, Tr(1)=41, W=ker Tr=span(pi,...,pi^40) subset J; p=12301 prime and 41 unit mod p.
- The trace-kernel description (3.1) as a paper theorem (Kondo 2025), and the compactness/profinite topology of Out(G_K).

Conditional:

- H_A-lite (2.1), the Kondo log compatibility for all Out(G_K); if this is not accepted, (4.7) is conditional on it.
- The scalar lambda(alpha) in (3.3); its construction is conditional on the group-theoretic trace kernel being preserved as a Q_p-subspace.

Missing:

- A source-level proof of (2.1) for all Out(G_K) (the Kondo 2026 Theorem2.6 interface may be only for the range stated there).
- Explicit matrices/lambda(alpha)/w(alpha) for actual generators beyond the field subgroup; the abstract scalar formula does not compute full generator matrices.
- A complete C, S_bad, q/BPS/gluing, row/Theta weights, TC-A..TC-H/TC-S, actual archimedean h_inf; no global h_C>=Q_C.

Withdrawn:

- Any B=I branch for full Out under the accepted H_A-lite/trace inputs; the conditional 9/41 surplus; any target closure from B=O_K alone.

## 7. Exact local check

For the concrete e=41 local type, W=span(pi,...,pi^40) is computed from the exact trace table (1.1). The decomposition (4.1) is exact because Tr(1)=41 is a p-adic unit. No numerical approximation is used for lambda; lambda is a scalar in Z_p^times and is not assumed to be 1. The field automorphism sigma(pi)=zeta pi has alpha_+(1)=1, so lambda=1 and w=0, consistent with (4.3)-(4.5).

## 8. Verdict and next step

Under H_A-lite and the Kondo trace-kernel theorem, full Out(G_K) preserves O_K, J, I and acts on I/J; alpha_+(1) has the exact form lambda(alpha) 1 + w(alpha) with lambda in Z_p^times and w in ker Tr subset J. Consequently H_A-full holds for the full group and B=O_K; B=I is excluded. This is a conditional construction, not a complete-C/target proof.

Next executable step: verify whether the Kondo log compatibility (2.1) is stated for all Out(G_K) or only for the subgroup used in the paper; if only a subgroup, compute the full image/quotient and apply the trace/compactness argument to the actual subgroup. Then compute lambda and w for explicit full generators and test the finite matrices on I/J.

Status: stage1 natural-language/exact local arithmetic only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6/ABC not proved.
