# C9 attack: H_A-full integral lift and full Out action on I/J

Task ID: task-194 / C9-HAFULL-CONSTRUCT-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact local research only; no Lean/Project edits; no target changes; no arbitrary generator; only this file written.

## 0. Inputs and binding corrections

- C9-FULL-OUT-COLUMN-ATTACK-20261025.md (task-180), SHA256 7cc2ddd03cfefa97e38049ca1ccb90016e944dece0185f706e42f7f97cd61fd8.
- C9-SYMPLECTIC-SOURCE-20261025.md (task-147), SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
- C9-MODP-BRANCH-PROOF-20261025.md (task-154), SHA256 af543bbbc50e8ec8cf9909cd5675d830018254760abc66410c81501a7227eade.
- C9-IND1-GLOBAL-20261025.md (task-149), SHA256 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8.
- C9-ERROR-LEDGER-20261025.md (task-164, current), SHA256 0dbd2b61e4e8944508e2cee6de6c0aa6e5fe26484eb2c9b174dfc72fe77d4b5b; E16/E20 are binding.
- C9-TAME-LOG-DOMAIN-20261025.md, SHA256 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06.
- C9-GLOBAL-ASSEMBLY-CORRECTED2-20261025.md (task-176), SHA256 83d33415f6a046e49e4c1a734095ae502a3dc94562a563af506ea640ebb5d781.

Binding E16/E20: the Kondo y-basis is a Q_p-basis of k_+=K; y_i=F(x_i) lies in m=J and maps to 0 in I/J. It is not an F_p-basis of I/J. Any argument using 'alpha(y_1) has nonzero W-component in the trace basis of I/J' without an integral lift is type-gapped. Full Out(G_K) is Q_p-linear only; the cited papers do not prove that arbitrary outer automorphisms preserve O_K, J, I or act on I/J. H_A/H_A-full are explicit source hypotheses.

This file reports a new conditional construction, a finite-index H_A-full construction, and the exact full-H_A obstruction. It also verifies/corrects the task-183 q=p^6/j-rationality claim. No complete C, no B=I, and no target closure is claimed.

## 1. Exact local data and Python verification

Take K/Q_p tame totally ramified cyclic, e=l=41, p=12301, pi^e=p u, f=1, O_K=Z_p[pi], m=(pi), J=log(O_K^x)=m, I=p^{-1}J=pi^{1-e}O_K, l=O_K/J.

Exact Python (integer arithmetic) checks:

    p = 12301 is prime (trial division up to sqrt p); p mod 41 = 1; p mod 12 = 1;
    q = p^6 = 3464515518466761109423801;
    q mod 10^12 = 761109423801; q^2 is divisible by p^12.        (1.1)

The local identity for qhat=pi^3 is exact:

    q_Tate = qhat^{2l} = pi^{246} = (pi^{41})^6 = p^6.            (1.2)

Python also constructs a primitive 41st root zeta mod p (2 is a primitive root mod p; zeta=2^{300}=8906 mod p, order 41) and the diagonal matrix of the field automorphism sigma(pi)=zeta pi on the pi-power basis:

    diag(1, zeta, zeta^2, ..., zeta^40) on (1, pi, ..., pi^40).    (1.3)

The matrix has order 41, fixes the line l=span(1 mod J), and is an actual H_A action for the field subgroup Aut(K). This is exact and unconditional local arithmetic.

## 2. Canonical F_p basis of I/J and the E16 type gap

Because pi^e=p u with u in Z_p^x, I/J=pi^{1-e}O_K/pi O_K is an e-dimensional F_p-vector space with basis

    B = (1, pi^{-40}, pi^{-39}, ..., pi^{-1}) mod J.                (2.1)

Equivalently e_a=pi^a for the exponents a=0 and a=-40,...,-1. The line l=O_K/J is span(1). The trace functional is nonzero on l and has kernel W=ker Tr of dimension 40. This basis is canonical up to F_p^x and is the correct I/J basis; the Kondo y_i=F(x_i) lie in J and reduce to 0 in I/J, so they are not a basis of I/J (E16).

Any H_A-full action must be expressed on B, not on the y-basis. This file uses B throughout.

## 3. Constructed: full Out action on J, I, and I/J (H_A-lite)

### 3.1 Paper-level inputs

1. Local reciprocity gives a canonical isomorphism K^x -> G_K^ab. The inertia subgroup of G_K is characteristic; under reciprocity it corresponds to O_K^x. Hence Out(G_K) acts on O_K^x.
2. Kondo 2026 Theorem 2.6 proof gives the compatibility

       alpha_+ log_k = log_k alpha^times                            (3.1)

for the reconstructed additive action alpha_+ on k_+(G_K) and the unit action alpha^times. This is the paper-level interface used below.
3. In the present tame low-ramification type, log_k(O_K^x)=J=m and J is a Z_p-lattice in K=k_+(G_K).

### 3.2 The action on J and I

By (3.1), for alpha in Out(G_K),

    alpha_+(J) = alpha_+(log(O_K^x)) = log(alpha^times(O_K^x)) = log(O_K^x) = J.   (3.2)

Thus every actual outer automorphism preserves J. Since I=p^{-1}J, it also preserves I. The restriction alpha_+|J is Q_p-linear and maps the Z_p-lattice J to itself; hence it is a Z_p-linear automorphism of J. There is no need for the y-basis or for a chosen generator: a Z_p-basis of J (for example pi, pi^2, ..., pi^{40}, p, with pi^{41}=p) may be used, and the matrix is in GL_41(Z_p).

The induced action on I/J is F_p-linear and is computed by reducing the J-matrix modulo p. This constructs a genuine full Out(G_K) action on I/J, conditional only on the paper-level compatibility (3.1) and the standard inertia/reciprocity identification. It does not use H_A-full and does not require O_K preservation. It also does not assign a meaning to alpha(O_K).

### 3.3 What this does not give

The H_A-lite action is an action on the log lattice J and the shell quotient I/J, not on the ring of integers O_K. It does not prove alpha(O_K)=O_K, and it does not define alpha on O_K/J as the image of 1 in a ring. In particular, the line l=O_K/J is a subspace of I/J, but H_A-lite only gives an action on I/J; it does not assert that alpha(l) is the reduction of alpha(O_K).

## 4. Constructed: H_A-full on a finite-index subgroup, and B=O_K there

### 4.1 The stabilizer of O_K is open

Out(G_K) is compact and acts continuously on K_+ by Q_p-linear automorphisms (Kondo 2026 Lemma 1.6). The stabilizer

    Gamma_0 := { gamma in Out(G_K) : gamma(O_K)=O_K }                  (4.1)

is open in Out(G_K), hence of finite index. This is a general fact about the continuous action of a compact group on the discrete set of lattices commensurable with O_K; no choice of a lattice or generator is involved. (The action gamma(O_K) is the Q_p-linear image of the Z_p-lattice O_K in K_+.)

By (3.2), every gamma in Out(G_K), in particular in Gamma_0, preserves J and I. Therefore Gamma_0 preserves O_K, J, I and induces an F_p-linear action on I/J. This is H_A-full on the finite-index subgroup Gamma_0:

    gamma(O_K)=O_K, gamma(J)=J, gamma(I)=I for every gamma in Gamma_0.   (4.2)

### 4.2 B for Gamma_0

For the subgroup Gamma_0, the branch span is

    B_{Gamma_0} = closed Z_p-span union_{gamma in Gamma_0} gamma(O_K).    (4.3)

Every gamma(O_K)=O_K, so the union is O_K and its closed Z_p-span is O_K. Thus

    B_{Gamma_0}=O_K.                                                     (4.4)

This is an actual conditional H_A-full construction for the finite-index subgroup, with a definite B=O_K. It does not imply B=O_K for the full Gamma.

### 4.3 Finite quotient

The quotient Out(G_K)/Gamma_0 is finite, but no cited source gives its coset representatives or their action on the lattice O_K. For a coset gamma Gamma_0, gamma(O_K) is a lattice in K_+ commensurable with O_K; it need not equal O_K and need not lie in I. The full B definition uses gamma(O_K) for full Gamma, so it is not computed by the subgroup result.

## 5. Obstruction to H_A-full for full Out(G_K)

The construction above gives H_A-lite for full Out and H_A-full only for Gamma_0. The following is the exact obstruction to extending (4.2) to all of Out(G_K).

1. Out(G_K) acts Q_p-linearly on K_+. The local reciprocity/log interface (3.1) determines the action on J and I, but not the additive element 1 in O_K. The ring lattice O_K=Z_p+J has an extra generator 1 whose image alpha_+(1) is not determined by alpha^times on O_K^x: the p-adic log kills the Teichmuller roots, including the identity, and provides no additive coordinate for 1.
2. The compactness of the image gives some invariant lattice L, but compactness does not select the source lattice O_K. A compact subgroup of GL_d(Q_p) can preserve many lattices; the stabilizer Gamma_0 is finite index but can be proper. No cited source proves Phi(Out(G_K)) is contained in the stabilizer of O_K.
3. The trace map Tr_{K/Q_p} is group-theoretic (Kondo Theorem E), but it is a Q_p-linear functional, not the trace pairing x,y -> Tr(xy). The trace pairing uses multiplication, which is not part of the Q_p-linear reconstruction k_+(G). Therefore one cannot dualize J or I to recover O_K from the trace alone.
4. The y-basis is not an I/J basis (E16); any attempt to use 'the first column of alpha on the y-basis' as a column on O_K/J is type-gapped unless an integral normalization is supplied. The H_A-lite construction uses the canonical pi-power basis of J/I/J and does not repair the O_K issue.
5. Non-normal conjugates alpha Aut(K) alpha^{-1} from Kondo 2025 Theorem I preserve alpha(O_K), not O_K; without alpha(O_K)=O_K they do not induce an action on O_K/J. The theorem proves non-normality, not lattice preservation.

Consequently the full H_A-full statement (every actual gamma in full Out preserves O_K,J,I and acts compatibly on I/J) is not constructed and not proved. The branch B for full Gamma remains not well-posed: B is defined using gamma(O_K), and for cosets outside Gamma_0 the lattice gamma(O_K) is not shown to lie in I.

## 6. B=O_K versus B=I: current exact status

Actual:

- Aut(K): the K/Q_p cyclic tame field automorphisms sigma(pi)=zeta pi preserve O_K,J,I and fix l; matrix (1.3) on I/J. Their span is O_K, so B_{Aut(K)}=O_K. They do not produce B=I.
- Gamma_0: H_A-full holds by (4.2), B_{Gamma_0}=O_K by (4.4).
- H_A-lite full Out: actual action on I/J; no O_K action.

Conditional:

- H_A-full for full Out would give, under the trace/U/W finite criterion, either B=O_K (all generators fix l) or B=I (some generator moves l). The finite matrices on the canonical I/J basis are still missing; the H_A-lite action gives an abstract action but not explicit matrices for full generators beyond the field subgroup.
- The corrected donor H=Phi^{-1}(Sp) does not by itself give H_A-full; its action on J/I is covered by H_A-lite, but the O_K extension is not.

Missing:

- A proof that every gamma in full Out stabilizes O_K (equivalently Gamma_0=Out), or an explicit coset gamma with gamma(O_K) not in I.
- Explicit matrices of full Out generators on the canonical I/J basis (or on J), beyond the field subgroup.
- The actual finite image barGamma on l; B=I realizability. No B=I generator is constructed.

## 7. Correction to task-183: q=p^6 is exact, but j(q) is not rational

Task-183 proposed the Tate specialization j(p^6) as a rational-j candidate. The first part is exact:

    qhat=pi^3, q_Tate=qhat^{82}=pi^{246}=p^6.                     (7.1)

The second part is not justified. The Tate j-function is the p-adic analytic series

    j(q) = q^{-1} + 744 + 196884 q + 21493760 q^2 + ...            (7.2)

At q=p^6 it converges p-adically to a p-adic number; this value is not automatically rational: q^{-1}=p^{-6} is not integral, the positive-q terms are p-adically small, and the infinite sum is not a finite rational expression. No rationality proof is supplied by the q-expansion. The correct congruence is

    p^6 j(p^6) = 1 + 744 p^6 + 196884 p^12 + ...
    p^6 j(p^6) = 1 + 744 p^6 mod p^12,                            (7.3)

checked exactly by Python: q^2 is divisible by p^12, so all terms from q^2 vanish modulo p^12.

A global elliptic curve E/Q with local Tate parameter p^6 at p would need j(E)=j(p^6) in Q. No theorem in the frozen corpus proves j(p^6) rational; in fact the q-expansion does not terminate, and q rational does not imply j(q) rational. Therefore the task-183 Tate j(p^6) candidate is not an actual global curve; it is at most a p-adic local model. This is an additional construction obstruction, not a complete-C construction.

## 8. Actual / conditional / missing

Actual local algebra and paper-level:

1. p=12301 prime, p=1 mod41, q=p^6 exact, qhat=pi^3, pi^41=p u, field automorphism sigma(pi)=zeta pi and matrix (1.3).
2. Inertia/unit action of Out(G_K) on O_K^x and local reciprocity; Kondo log compatibility (3.1).
3. H_A-lite: full Out preserves J and I and acts F_p-linearly on I/J (conditional only on (3.1) and the identification of k_+(G) with K).
4. Gamma_0 stabilizer of O_K is open finite index; H_A-full on Gamma_0; B_{Gamma_0}=O_K.

Conditional:

5. The compatibility (3.1) for all Out (paper-level reconstruction interface, not a theorem of the frozen local files); the source identification K=k_+(G).
6. H_A-full for full Out, and the finite matrices on I/J beyond Aut(K).

Missing/obstruction:

7. Preservation of O_K by full Out; additive 1/integral lift; Gamma_0 proper/full unknown; B full not well-posed.
8. Explicit full Out generators on canonical I/J basis; full barGamma; B=I not constructed.
9. Complete C, S_bad, q/BPS/gluing, weights, TC-A..TC-H/TC-S, archimedean h_inf; no global closure.

Withdrawn: any claim that B=O_K or B=I for full barGamma is actual; any use of the y-basis as I/J basis; task-183 rational-j assumption.

## 9. Next executable steps

1. Prove or disprove Gamma_0=Out: equivalently, decide whether every Q_p-linear automorphism in Phi(Out(G_K)) stabilizes O_K. This is the exact H_A-full gap; the compactness/finite-index construction gives only the subgroup.
2. Compute the finite quotient Out/Gamma_0 action on the set of lattices commensurable with O_K, or exhibit a coset gamma with gamma(O_K) not in I.
3. Compute explicit matrices of full Out generators on the canonical pi-power basis of J and I/J; decide the l-orbit and B branch.
4. For the complete-C route, verify q=p^6 and j(q) rationality/global curve separately; do not use the p-adic Tate value as a rational j.
5. Keep TC-A..TC-H/TC-S and target conditions separate from H_A-full; no target closure follows from H_A-lite or from B_{Gamma_0}=O_K.

Status: stage1 natural-language/exact local arithmetic only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6/ABC not proved.
