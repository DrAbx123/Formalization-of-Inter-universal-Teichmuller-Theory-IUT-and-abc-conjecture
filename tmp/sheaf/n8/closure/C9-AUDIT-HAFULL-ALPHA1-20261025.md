# C9 audit: H_A-full alpha_+(1) construction

Task ID: task-200 / C9-AUDIT-HAFULL-ALPHA1-20261025. Owner: primespine. Date: 2026-10-25.
Audited file: C9-HAFULL-ALPHA1-20261025.md (task-195), SHA256 ba8459c4500b8e73acfa12a3c20431c5fdf8ed1af077ddd453f5d3c4f2e6a43b.
Context: C9-HAFULL-CONSTRUCT-20261025.md (task-194), SHA256 c02d4a24cd201ad6f0fc2d5e308772f943ae29c911058f40ed19a2c8d7ba6878; C9-SYMPLECTIC-SOURCE-20261025.md, SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
Nature: independent natural-language audit only; no new attack, no Lean/Project edits; only this file written.

## 0. Audit verdict

The task-195 argument is **structurally valid** at the paper-level natural-language standard, subject to two explicitly identifiable reconstruction inputs:

1. the Kondo 2026 Theorem2.6 proof diagram alpha_+ log_k = log_k alpha^times, which supplies the H_A-lite action on J and I;
2. the Kondo 2025 Theorem E/1.3 group-theoretic description of W=ker Tr_{k/k^{d=1}}, which makes W stable under alpha_+.

Under those inputs, the following steps are correct:

- W=ker Tr=span(pi,...,pi^40) subset J;
- alpha_+(W)=W;
- Tr o alpha_+ = lambda(alpha) Tr;
- lambda(alpha) is a continuous homomorphism Out(G_K)->Q_p^times with compact image, hence lambda(alpha) in Z_p^times;
- K=Q_p 1 direct-sum W and alpha_+(1)=lambda(alpha)1+w(alpha) with w in W subset J, so alpha_+(1) in O_K;
- alpha_+(O_K)=Z_p alpha_+(1)+J subset O_K; applying the same to alpha^{-1} gives equality;
- hence H_A-full for full Out(G_K), B=O_K, and B=I excluded.

The audit finds **no hidden arbitrary element** and **no use of the y-basis as an I/J basis**. The construction recovers alpha_+(1) canonically as lambda 1+w; lambda is the trace-scaling scalar, not a chosen parameter.

Classification: **valid paper-level/conditional** (valid modulo the two Kondo reconstruction inputs and the standard identification k_+(G)=K, O^times(G)=O_K^times). It is not a Lean/kernel proof. The earlier task-194 'full H_A-full obstruction' is superseded by this trace/compactness argument; E16 remains binding for y-basis/I-J statements but is not violated here.

## 1. Step-by-step audit

### 1.1 W=ker Tr=span(pi,...,pi^40) subset J

Local type: K/Q_p tame totally ramified cyclic, e=l=41, p=12301, f=1, d=[K:Q_p]=41, K^{d=1}=Q_p, O_K=Z_p[pi], pi^41=p u, m=pi O_K=J, I=p^{-1}J.

Exact trace table: Tr(pi^a)=0 for 1<=a<=40, Tr(1)=41. Since p=12301 does not divide 41, Tr is nonzero and

    W=ker Tr=span(pi,...,pi^40),   dim W=40,   W subset J.        (1.1)

VERDICT: valid; exact local algebra. The use of W rather than the Kondo y-basis avoids E16.

### 1.2 alpha_+(W)=W

Kondo 2025 Theorem E (Theorem 1.3 in that paper) gives, for odd d,

    Ker(Tr_{k/k^{d=1}})=<y_2,...,y_d>_{Q_p}.                       (1.2)

for the 2025 Jannsen-Wingberg basis y_i=F(x_i); this description is group-theoretic. In the present case k=K, k^{d=1}=Q_p (prime degree extension), d=41 odd. The description is preserved by the reconstructed action of Out(G_K) on k_+(G_K), so

    alpha_+(W)=W.                                                  (1.3)

VERDICT: valid conditional on Kondo Theorem E being used in its stated group-theoretic form. This is a paper-level input; the audit did not re-prove it. The local trace table (1.1) independently identifies W.

### 1.3 Tr o alpha_+ = lambda Tr

Since alpha_+ is bijective and alpha_+(W)=W, the kernel of the functional Tr o alpha_+ is W. Both Tr and Tr o alpha_+ are nonzero Q_p-linear functionals with the same kernel W; hence there is lambda(alpha) in Q_p^times with

    Tr o alpha_+ = lambda(alpha) Tr.                                (1.4)

VERDICT: valid; no hidden choice. The scalar lambda is unique.

### 1.4 lambda in Z_p^times

For alpha,beta in Out(G_K), composition gives lambda(alpha beta)=lambda(alpha)lambda(beta); lambda is a continuous homomorphism Out(G_K)->Q_p^times (matrix coefficients of alpha_+ are continuous in the profinite topology). Out(G_K) is compact (Kondo 2026 uses its natural profinite structure). The image of a compact group under a continuous homomorphism to Q_p^times is compact. Since Q_p^times=p^Z x Z_p^times with p^Z discrete, every compact subgroup lies in Z_p^times. Thus

    lambda(alpha) in Z_p^times.                                    (1.5)

VERDICT: valid conditional on Out(G_K) compact/profinite. Kondo states Out has the natural profinite structure; this is the paper-level topology used in Theorem C.

### 1.5 alpha_+(1)=lambda 1+w, w in J

Tr(1)=41 is a p-adic unit, so K=Q_p 1 direct-sum W. Write

    alpha_+(1)=c 1+w,  c in Q_p, w in W.                            (1.6)

Apply Tr: lambda Tr(1)=Tr(alpha_+(1))=c Tr(1)+Tr(w)=c Tr(1), so c=lambda. Therefore

    alpha_+(1)=lambda(alpha)1+w(alpha),  w(alpha) in W subset J.    (1.7)

Since lambda in Z_p and w in J, alpha_+(1) in Z_p+J=O_K.

VERDICT: valid. This is the construction of alpha_+(1); no arbitrary lift or generator is used.

### 1.6 alpha(O_K) subset O_K and equality

O_K=Z_p 1+J. By H_A-lite, alpha_+(J)=J; by (1.7), alpha_+(1) in O_K. Hence

    alpha_+(O_K)=Z_p alpha_+(1)+alpha_+(J) subset Z_p O_K+J=O_K.    (1.8)

Apply the same argument to alpha^{-1}: alpha^{-1}_+(1) in O_K and alpha^{-1}_+(J)=J, so alpha^{-1}_+(O_K) subset O_K. Applying alpha_+ gives O_K subset alpha_+(O_K). Therefore

    alpha_+(O_K)=O_K.                                              (1.9)

VERDICT: valid. The inverse step is necessary; without it one only has a sublattice inclusion. It is present in task-195 and is correct.

### 1.7 H_A-full, B=O_K, B=I exclusion

By (1.9), every alpha in Out(G_K) preserves O_K; H_A-lite gives preservation of J and I. Therefore

    B=closed Z_p-span union_{alpha} alpha(O_K)=O_K.                 (1.10)

The branch B=I does not occur. In particular, the conditional b=3 B=I value 9/41 is not selected; the B=O_K value is the relevant one under these inputs. The line l=O_K/J is stable because alpha_+(1) mod J=lambda mod J is nonzero, so alpha(l)=l.

VERDICT: valid consequence of 1.6 and H_A-lite. This is the main audit conclusion.

## 2. Dependencies and hidden assumptions

### 2.1 Paper-level dependencies

1. Kondo 2026 Theorem2.6 proof: the log compatibility diagram

       alpha_+ log_k = log_k alpha^times                          (2.1)

   for a continuous automorphism alpha of G_k. The audit located this diagram in the proof of Theorem2.6 (local frozen HTML), not merely in the task-147 paraphrase. This supplies H_A-lite: alpha^times preserves O_K^times; log(O_K^times)=J; hence alpha_+(J)=J.
2. Kondo 2025 Theorem E/1.3: group-theoretic kernel of Tr_{k/k^{d=1}}. This supplies alpha_+(W)=W.
3. Kondo 2026/Section 3: Out(G_K) with natural profinite topology, used for compactness of lambda.

These are paper-level inputs. If a formal proof demands them as Lean/kernel facts, they remain unformalized; this audit is natural-language only.

### 2.2 Standard reconstruction identifications

4. The identification of k_+(G_K) with the additive group of K, and of O^times(G_K) with O_K^times, via the Kondo/AbsTopIII reconstruction. If one refuses this identification, the argument is conditional; under the cited papers it is the standard reconstruction interface.
5. The actual p-adic log `log_k:O_K^times->K` is the source log; (2.1) is the compatibility of the reconstructed actions with this log.

### 2.3 Local arithmetic

6. K/Q_p tame totally ramified cyclic e=41, p=12301, f=1: K^{d=1}=Q_p because [K:Q_p]=41 is prime; Tr(1)=41 unit mod p; W=span(pi,...,pi^40) subset J.
7. No use of the y-basis as I/J basis; E16 is respected. The basis of I/J is the pi-power basis; the trace-kernel W is used only inside J.

### 2.4 What is not assumed

8. No arbitrary element, generator, lattice, scalar, or branch. lambda is the trace-scaling scalar; w=alpha_+(1)-lambda is determined by alpha.
9. No B=I assumption and no H_A-full as a hypothesis: H_A-full is the conclusion.
10. No use of the Gamma_0 finite-index subgroup as a substitute; the argument applies to full Out.

## 3. Classification

PROVED (paper-level natural language, conditional only on the standard reconstruction identifications):

- W=ker Tr=span(pi,...,pi^40) subset J;
- alpha_+(W)=W; Tr o alpha_+=lambda Tr; lambda in Z_p^times;
- alpha_+(1)=lambda 1+w with w in J;
- alpha_+(O_K)=O_K; H_A-full for full Out; B=O_K; B=I excluded.

CONDITIONAL / UNFORMALIZED:

- The Kondo log compatibility (2.1) and trace-kernel group-theoretic statement as source-level facts; the reconstruction identifications; the compact/profinite topology of Out.
- The exact lambda(alpha), w(alpha) matrices for all generators are not computed; only their existence/structural form is proved.

INVALID / WITHDRAWN:

- The earlier statement that full H_A-full is an unresolvable obstruction, if meant as a no-go. The finite-index Gamma_0 result of task-194 is superseded at the natural-language level by (1.9).
- Any B=I conclusion or use of the conditional 9/41 surplus under H_A-full.
- Any use of the y-basis as an I/J basis (E16).

NOT AFFECTED:

- The trace table and W computation are exact local arithmetic; they remain valid.
- Complete C, target containment, TC-A..TC-H/TC-S, archimedean h_inf, and global h_C>=Q_C are outside this audit; B=O_K alone does not prove them.

## 4. Audit of possible failure points

### 4.1 Is alpha_+(W)=W too strong?

W is the kernel of the actual trace functional. Kondo's theorem describes this kernel group-theoretically; if that description is accepted as functorial, preservation is immediate. The audit found no basis-dependent step: the trace table in the pi-power basis and the Kondo kernel are the same subspace. If one doubts the group-theoretic functoriality, this is the first dependency to formalize; it is not a gap introduced by task-195.

### 4.2 Is lambda necessarily a p-adic unit?

lambda is a continuous homomorphism to Q_p^times. A compact image cannot contain a nontrivial p-power factor (p^Z discrete), so it lies in Z_p^times. This uses only standard p-adic topology. No bound on lambda beyond unit is assumed.

### 4.3 Is alpha_+(1) possibly outside O_K if lambda is a unit but w has negative valuation?

w lies in W=ker Tr=span(pi,...,pi^40) subset J=pi O_K, so w is p-adically integral. lambda is in Z_p. Thus lambda 1+w in O_K. The decomposition K=Q_p1 direct-sum W is exact because Tr(1)=41!=0.

### 4.4 Does alpha(O_K)=O_K require alpha to be multiplicative?

No. The proof uses only additive Q_p-linearity, alpha_+(1) in O_K, and alpha_+(J)=J. O_K=Z_p1+J as a Z_p-lattice. The inverse inclusion uses the same argument for alpha^{-1}; multiplicativity of alpha is not needed.

### 4.5 Does B=O_K follow only after Gamma_0?

No; (1.9) is for every alpha in Out. Gamma_0=Out in effect; B is the span of O_K itself. The task-194 finite-index gap is eliminated.

## 5. Consequences and remaining gaps

Consequences (conditional on the paper-level dependencies):

- alpha_+(1) is constructed as lambda(alpha)1+w(alpha); lambda in Z_p^times, w in ker Tr subset J.
- H_A-full holds for full Out(G_K); B=O_K; B=I is excluded; b=3 B=I 9/41 is not actual.
- The earlier branch classification B=O_K vs B=I is resolved toward B=O_K, not merely conditional on Gamma_0.

Remaining gaps:

1. A source-level proof/formalization of Kondo 2026 log compatibility and Kondo 2025 trace-kernel functoriality; this audit did not re-prove them.
2. Explicit lambda(alpha), w(alpha) and matrices on I/J for actual full generators.
3. Complete C, S_bad, per-p types, q/BPS/gluing, row/Theta weights, TC-A..TC-H/TC-S, actual archimedean h_inf; no global closure.

## 6. Final audit status

The task-195 construction passes the structural audit. The trace-kernel/lambda/alpha1/O_K/B=OK chain is internally consistent; no arbitrary choice, no y-basis I/J mixing, no circular B assumption. The only substantive dependencies are the two Kondo reconstruction inputs and the standard identification of k_+(G_K) with K. Under those, H_A-full is constructed and B=O_K; B=I is excluded. This remains natural-language/paper-level, not Lean/kernel verification; target_accepted=false and complete C9/P6/ABC are not proved.
