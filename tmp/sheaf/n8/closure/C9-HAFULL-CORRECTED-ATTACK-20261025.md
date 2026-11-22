# C9 corrected attack: H_A-full integral lift without W subset J

Task: task-202. Date: 2026-10-25. Owner/executor: transport.
Stage: stage1 natural-language/local-algebra attack only. No Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-HAFULL-CONSTRUCT-20261025.md | 187 | C02D4A24CD201AD6F0FC2D5E308772F943AE29C911058F40ED19A2C8D7BA6878 |
| C9-AUDIT-HAFULL-LITE-20261025.md | 377 | EF755618B74DC45913A6DD148E1E60ABC97CB6C4188748AC6F907EF9305FF223 |
| C9-FULL-OUT-COLUMN-ATTACK-20261025.md | 135 | 7CC2DDD03CFEFA97E38049CA1CCB90016E944DECE0185F706E42F7F97CD61FD8 |

Binding corrections: E16/E20 (y-basis is not an I/J basis; full Out is only
Q_p-linear; H_A/H_A-full are source hypotheses); E24 is invalid at W subset J
(W=ker Tr is a Q_p-hyperplane, not contained in the Z_p-lattice J=m).

## 1. Verdict

The corrected attack gives a canonical formula for alpha_+(1) and an exact
integrality criterion, without assuming W subset J. The main results are:

1. H_A-lite: every actual alpha in Out(G_K) preserves J and I, and acts
   Z_p-linearly on J and F_p-linearly on I/J, conditionally on the
   reciprocity/Kondo/AbsTopIII interface.

2. alpha_+(1) IS determined by this action. The previous claim that
   alpha_+(1) is "not determined by the unit/log action" is FALSE. Since
   p in J and J spans K over Q_p,

       alpha_+(1) = p^{-1} alpha_+(p) = p^{-1} log(alpha^times(exp p)),

   canonically in I=p^{-1}J. No arbitrary lift is chosen.

3. H_A-full for alpha is equivalent to

       alpha_+(1) in O_K minus J.

   Equivalently, the W-coordinate w of alpha_+(1)=lambda 1+w lies in J cap W;
   equivalently alpha_+(1) has nonzero class in O_K/J=l.

4. Conditional theorem, no W subset J:

       H_A-full for all actual alpha  =>  every alpha fixes l=O_K/J
                                      =>  B_Gamma=O_K.

   Proof: alpha_+(1) in O_K; write alpha_+(1)=lambda 1+w with w in W. Then
   w=alpha_+(1)-lambda 1 lies in O_K cap W=J cap W, so w in J; modulo J,
   alpha_+(1)=lambda 1 with lambda nonzero. Thus l is fixed.

5. H_A-full itself is NOT proved. The exact remaining obstruction is the
   integrality of the canonical a(alpha)=alpha_+(1) in O_K minus J for every
   alpha, equivalently an explicit computation of alpha_+(p) or alpha^times on
   exp(p). No cited source supplies it; Gamma_0=Stab(O_K) is only finite index.

6. Under the conditional theorem, B=I cannot occur while H_A-full holds.
   If H_A-full fails for some alpha, alpha(O_K) need not lie in I, so the
   source branch B is not well-posed for that alpha. Thus B=I is not a
   source-defined alternative under the current data; B=O_K is conditional on
   H_A-full.

This corrects E24 and also the earlier audit's H5 wording: the problem is not
that alpha_+(1) is undetermined, but that the determined element may fail to
lie in O_K. The invalid step W subset J is never used.

## 2. Local setup

K/Q_p tame totally ramified cyclic, e=ell=41, p=12301, pi^e=p u,
u in Z_p^times, f=1, O_K=Z_p[pi], m=(pi), J=m, I=p^{-1}J, l=O_K/J.

Choose the Z_p-basis of J

    (p, pi, pi^2, ..., pi^40).                           (2.1)

It is a basis of J=m because p=u^{-1}pi^41 and J=pi O_K. The field trace

    Tr=Tr_{K/Q_p}: K -> Q_p

satisfies Tr(1)=e=41, Tr(pi^a)=0 for 1<=a<=40. Therefore

    W := ker Tr  is a Q_p-hyperplane, dim_Qp W=40,
    W cap J = Z_p-span(pi, pi^2, ..., pi^40),             (2.2)
    O_K = Z_p 1 direct-sum (J cap W).                     (2.3)

The decomposition (2.3) is a Z_p-decomposition: 1 has trace e not 0, while
J cap W is trace-zero; both sides have rank 41 total. Note W itself is not
contained in J: p^{-1}pi in W but not in m. This is the exact invalid step of
E24 and it is not used below.

## 3. H_A-lite: action on J and I

Paper/interface inputs (conditional):

- Local reciprocity identifies inertia with O_K^times; Out(G_K) acts on
  O_K^times.
- Kondo 2026 Theorem 2.6 proof gives
  alpha_+ log = log alpha^times for the reconstructed additive action alpha_+
  and the unit action alpha^times.
- In the present low-ramification tame type, log(O_K^times)=J=m and
  I=p^{-1}J.

Then for alpha in Out(G_K):

    alpha_+(J)=alpha_+(log(O_K^times))
             = log(alpha^times(O_K^times))
             = log(O_K^times)=J,                    (3.1)
    alpha_+(I)=p^{-1}alpha_+(J)=I.                  (3.2)

Hence alpha_+ restricts to a Z_p-linear automorphism of J and induces an
F_p-linear automorphism of I/J. This does not require O_K preservation and
does not use the Kondo y-basis (which is not an I/J basis; E16).

Status: CONDITIONAL/VALID on the paper interface. It does not give H_A-full.

## 4. Canonical alpha_+(1)

Because p in J and alpha_+(J)=J, the action on J determines alpha_+(p).
Since exp(p) in U^1=1+m (for e<p-1, exp converges on m) and log(exp p)=p,

    alpha_+(p)=alpha_+(log(exp p))
             = log(alpha^times(exp p)) in J.        (4.1)

Using Q_p-linearity and 1=p^{-1}p:

    a(alpha) := alpha_+(1)
              = p^{-1} alpha_+(p)
              = p^{-1} log(alpha^times(exp p))  in I=p^{-1}J.   (4.2)

This is canonical: no basis, generator, or arbitrary lift is chosen. It is
determined by alpha^times on O_K^times, hence by H_A-lite. Therefore:

CORRECTION: the earlier statement "alpha_+(1) is not determined by the
unit/log action" is FALSE. The error was to look for alpha_+(1) only in the
trace decomposition without using p^{-1}p and the action on J.

The actual obstruction is not determination but integrality:

    a(alpha) in I, but not necessarily in O_K.        (4.3)

## 5. Exact H_A-full criterion

Since alpha_+(J)=J,

    alpha_+(O_K)=alpha_+(Z_p 1 + J)
                = Z_p a(alpha) + J.                    (5.1)

Thus:

    H_A-full(alpha)  <=>  alpha_+(O_K)=O_K
                     <=>  a(alpha) in O_K minus J.     (5.2)

Proof of (5.2):

- If a in J, then Z_p a+J=J, not O_K.
- If a not in O_K, then Z_p a+J is not contained in O_K, so cannot equal O_K.
- If a in O_K but a not in J, then a has nonzero class in O_K/J (one-
  dimensional), so Z_p a+J=O_K.

Equivalently, decompose uniquely by (2.3):

    a(alpha)=lambda(alpha) 1 + w(alpha),  lambda in Q_p, w in W.  (5.3)

Since 1 in O_K and O_K cap W=J cap W subset J:

    a in O_K  <=>  w in J cap W.                        (5.4)

Thus H_A-full iff w(alpha) in J cap W and lambda(alpha) not in pZ_p.
No W subset J is assumed; the condition w in J is the integrality condition,
not an identity.

## 6. Conditional theorem H_A-full implies l fixed

Assume H_A-full for alpha. Then a(alpha) in O_K minus J. Decompose by (5.3).
Because a in O_K and 1 in O_K, w=a-lambda 1 lies in O_K. Since w in W also,

    w in O_K cap W = J cap W subset J.                  (6.1)

Therefore, modulo J,

    a(alpha) = lambda 1 mod J,  lambda not 0 mod p.      (6.2)

So alpha_+(1) reduces to a nonzero scalar multiple of 1 in l=O_K/J, and alpha
fixes the line l.

Consequently, if H_A-full holds for every actual alpha in the full finite
image or full Out subgroup under consideration, then every alpha fixes l, and

    B_Gamma = closed span union_gamma gamma(O_K) = O_K.  (6.3)

This is the corrected conditional H_A-full => B=O_K theorem. It uses only
J preservation and integrality; the E24 assumption W subset J is absent.

## 7. H_A-full is not automatic: abstract example

H_A-lite alone does not imply H_A-full. Let U be the Q_p-linear automorphism
of K defined on the J-basis (2.1) by

    U(p)=pi,  U(pi)=p,  U(pi^a)=pi^a for 2<=a<=40.      (7.1)

Extend U Q_p-linearly. Then U(J)=J and U(I)=I, so U satisfies the H_A-lite
lattice properties. But

    U(1)=p^{-1}U(p)=p^{-1}pi=u^{-1}pi^{1-e} not in O_K,   (7.2)

so U(O_K)=Z_p U(1)+J is not O_K. Thus U is not H_A-full.

This abstract example is not asserted to lie in Phi(Out(G_K)); it only proves
that the integrality condition (5.2) is a genuine additional condition and
that H_A-lite does not force O_K preservation. The actual source question is
whether every actual alpha satisfies (5.2).

## 8. What is actually known about full Out

- H_A-lite: full Out preserves J and I and acts on I/J, conditionally on the
  paper interface.
- Gamma_0={gamma: gamma(O_K)=O_K} is open of finite index (compactness and
  stabilizer of a lattice). For Gamma_0, H_A-full holds and B_Gamma0=O_K.
- Gamma_0=Out is NOT proved. The finite quotient Out/Gamma_0 and its action on
  the commensurable lattices are not computed.
- For alpha outside Gamma_0, alpha(O_K) is a commensurable lattice, not
  necessarily O_K and not necessarily inside I. The full B definition is not
  well-posed for such alpha.
- The canonical a(alpha) formula (4.2) gives a computable criterion for
  membership in Gamma_0: alpha in Gamma_0 iff a(alpha) in O_K minus J.
- No cited source computes alpha_+(p) or alpha^times(exp p) explicitly for
  full Out generators, so H_A-full remains OPEN. This is the exact obstruction:
  explicit matrix/unit action, not an undetermined alpha_+(1).

## 9. Consequences for the B branch

Under H_A-full, l is fixed and B=O_K (Section 6). Therefore:

    H_A-full  =>  B=O_K,
    B=I is impossible while H_A-full holds.

If H_A-full fails for some actual alpha, then:

- alpha(O_K) need not lie in I, so the source branch definition
  B=span gamma(O_K) is not well-posed;
- no actual generator moving l is constructed in the cited sources;
- B=I is not an actual source-defined alternative.

Status: B=O_K is CONDITIONAL on H_A-full; B=I is not available under H_A-full
and not constructed outside it. Full H_A-full and full B remain open.

## 10. Corrections and classifications

| item | classification |
|---|---|
| H_A-lite preserves J,I and acts on I/J | CONDITIONAL/VALID paper interface |
| alpha_+(1)=p^{-1}log(alpha^times(exp p)) | ACTUAL/CANONICAL from H_A-lite |
| alpha_+(1) not determined | FALSE (corrected) |
| H_A-full iff a(alpha) in O_K minus J | EXACT CRITERION |
| H_A-full => l fixed, B=O_K | CONDITIONAL THEOREM |
| W subset J / E24 proof | INVALID; not used |
| full Out preserves O_K | NOT PROVED |
| Gamma_0=Out | NOT PROVED |
| B=I actual | INVALID/NOT CONSTRUCTED |
| B=O_K for full Gamma | CONDITIONAL on H_A-full |
| explicit matrices/full finite image | MISSING |
| complete C/target | MISSING |

## 11. Status

This file constructs alpha_+(1) canonically and proves the exact integrality
criterion and the conditional implication H_A-full => B=O_K. It does not prove
H_A-full for full Out and does not construct a B=I generator. No arbitrary
lift or W subset J is used.

No Lean/Project edits; target_accepted=false.
