# C9 decisive P: Out(G_K) does not preserve the principal unit filtration

Task: task-209. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 decisive natural-language/local-mathematics verification.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Sources

- Kondo 2025, *Anabelian aspects of the outer automorphism groups of the
  absolute Galois groups of mixed-characteristic local fields*,
  arXiv:2512.09231v1; local snapshot
  sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f.
  Theorem A, condition (3); Theorem B.
- Kondo 2026, *Lubin-Tate representations ... not Aut-intrinsically
  Hodge-Tate*, arXiv:2605.25428v2; local snapshot
  sources/Kondo-2605.25428v2.html,
  SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86.
  Definition 3.2, Lemma 3.3, Theorem 2.6 proof.
- C9-SYMPLECTIC-SOURCE-20261025.md,
  SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.
- C9-AUDIT-UNIT-FILTRATION-20261025.md,
  SHA256 8d715581577f057c151cc7023b98f5a896a04121efc32d13b6ebaef21c563e09.
- Serre, *Local Fields*, GTM 67, Ch. IV, §3 (upper numbering of the
  ramification filtration and its compatibility under field extensions).
  The decisive refutation below is Kondo 2025 Theorem A; no numerical
  computation is used.

## 1. Verdict

**P is FALSE for the full Out(G_K).** It is not true that every
alpha in Out(G_K) preserves the principal unit filtration

    U^n = 1 + m_K^n,

in particular not U^e = 1 + p O_K for e=41.

The exact reason is:

1. Local reciprocity identifies the principal unit filtration U^n with the
   upper ramification filtration of G_K^ab, up to a fixed index shift depending
   on K/e and the upper-numbering convention. Using upper (not lower) numbering
   is correct; lower numbering would not repair P.
2. Kondo 2025 Theorem A: for an automorphism alpha of G_K, the following are
   equivalent:
   (1) the outer class of alpha lies in the finite field-theoretic subgroup
       Aut(K) subset Out(G_K);
   (2) Hodge-Tate transport for all finite-dimensional continuous p-adic
       representations;
   (3) alpha is compatible with the filtration on G_K given by the
       [positively indexed] higher ramification subgroups in the **upper**
       numbering;
   (4) an additive transport condition on the completed algebraic closure.
3. Therefore the stabilizer of the full upper ramification filtration is
   exactly Aut(K), a finite subgroup; it is not all Out(G_K).
4. The corrected symplectic donor H=Phi^{-1}(Sp_{2g}(Z_p)) has infinite image
   Sp_{2g}(Z_p) (Kondo 2026 Definition 3.2/Lemma 3.3), while Aut(K) is finite.
   Choose alpha in H minus Aut(K). By Theorem A, alpha is not compatible with
   the upper ramification filtration; some G_K^u is not preserved, and under
   reciprocity some principal unit group U^n is not preserved. This is an
   actual counterexample from the cited source, not an abstract GL_d model.
5. Kondo 2025 Theorem B gives a second, independent actual automorphism phi of
   some G_k (even-degree abelian k/Q_p) for which a Hodge-Tate representation
   becomes non-Hodge-Tate; by Theorem A, phi cannot preserve the upper
   filtration. It is a second counterexample to the claim that every group
   automorphism preserves the filtration.

## 2. Serre and reciprocity indexing: why "characteristic" fails

Serre Local Fields Ch. IV §3 sets up the lower and upper numberings of the
higher ramification subgroups of G_K and their compatibility under field
extensions/quotients. The upper numbering is canonical **relative to the field
K** and is the correct numbering for the unit filtration comparison. It is,
however, not characteristic in the abstract profinite group G_K: preserving it
is a nontrivial property of an automorphism.

The inertia subgroup and wild inertia subgroup are characteristic in G_K, but
the higher upper ramification subgroups are not characteristic under all
abstract automorphisms. Kondo 2025 Theorem A is the exact theorem identifying
the automorphisms compatible with the full upper filtration: they are precisely
the field-theoretic subgroup Aut(K), which is finite.

Local reciprocity gives

    rec_K : profinite-completion(K^times) -> G_K^ab,

and the principal unit filtration U^n corresponds to the upper ramification
filtration of G_K^ab up to a fixed index shift depending on K/e and the chosen
normalization. A fixed shift cannot repair P: if every upper subgroup were
preserved, every U^n would be preserved after any fixed shift. The failure is
that not all automorphisms preserve the upper filtration, not an indexing
ambiguity.

For the C9 type e=41, p=12301, pO_K=m_K^e, hence U^e=1+pO_K=1+m_K^e. This is a
genuine member of the principal filtration, but membership does not make it
characteristic in G_K.

## 3. Exact counterexample argument

### 3.1 Infinite actual donor

Kondo 2026 Definition 3.2 embeds Sp_{2g}(Z_p) in GL_d(Q_p) by A -> diag(1,A)
for odd d=2g+1, and Lemma 3.3 gives

    Sp_{2g}(Z_p) subset Phi(Out(G_K)),

where Phi is the continuous closed reconstruction map. Thus

    H = Phi^{-1}(Sp_{2g}(Z_p)) subset Out(G_K)

is closed with infinite image. It is the corrected donor of task-147, not the
image of rho and not a splitting.

### 3.2 Finite stabilizer

Kondo 2025 Theorem A says the outer class preserving the full upper
ramification filtration is exactly an element of the finite subgroup Aut(K).
Therefore

    {alpha in Out(G_K): alpha preserves all upper G_K^u} = Aut(K),
    |Aut(K)| < infinity.

### 3.3 Counterexample alpha

H is infinite, Aut(K) is finite, so H is not contained in Aut(K). Choose
alpha in H minus Aut(K). By Theorem A, alpha fails condition (3): there exists
an upper ramification subgroup G_K^u with

    alpha(G_K^u) != G_K^u.

Under the reciprocity identification this gives, for the corresponding unit
level n,

    alpha^times(U^n) != U^n.

Hence P fails for the actual subgroup H and therefore for full Out(G_K).

No explicit matrix for alpha is needed: H is an actual infinite donor and
Aut(K) is finite, so an element outside the stabilizer exists. The failure is
an existence theorem, not a numerical guess.

### 3.4 Second independent counterexample

Kondo 2025 Theorem B constructs an actual finite abelian k/Q_p of even degree
and an actual automorphism phi of G_k such that rho o phi is not Hodge-Tate
for an irreducible Hodge-Tate rho. By Theorem A, phi cannot preserve the upper
filtration. This independently confirms that the abstract automorphism group
does not preserve it. It is not claimed that this phi lies in H; the H
argument is the donor-specific obstruction for the C9 K.

## 4. Does U^e specifically fail?

Kondo Theorem A guarantees failure of compatibility with the **full** upper
filtration, hence failure at some upper level u and some principal level n. It
does not by itself identify n=e. Therefore the precise status is:

- P as the all-n/all-Out statement: **FALSE** (counterexample above).
- The narrower statement "alpha^times(U^e)=U^e for every alpha in Out(G_K)"
  is **NOT PROVED** by Theorem A; a separate level-e argument is required.
  No such argument is supplied in the frozen corpus.
- Task-204 used exactly that narrower U^e preservation to prove
  a(alpha) in O_K. Since the narrower statement is unsupported, that proof
  fails; H_A-full for full Out remains OPEN.
- For the field-theoretic subgroup Aut(K), and for the finite-index subgroup
  Gamma_0=Stab(O_K), the filtration/compatibility claims are valid subgroup
  results; they do not extend to full Out.

The local facts that survive are:

    exp(p) in U^e, log(U^e) subset pO_K,
    p^{-1} log(U^e) subset O_K,
    alpha_+ log = log alpha^times,
    a(alpha)=alpha_+(1)=p^{-1}log(alpha^times(exp p)) in I.

The missing step is exactly alpha^times(U^e)=U^e for all alpha; without it,
log(alpha^times(exp p)) need not lie in pO_K, hence a(alpha) need not lie in
O_K. The canonical a(alpha) remains in I.

## 5. Consequences for H_A-full and B branches

- H_A-full for full Out(G_K): NOT PROVED.
- B=O_K for full Out: NOT PROVED; conditional only on H_A-full.
- B=I for full Out: NOT excluded and not constructed; branch remains
  type-gapped/undetermined.
- Any proof of H_A-full based on "Out preserves U^n" is invalid; Kondo Theorem
  A contradicts it.
- The only filtration-preserving automorphisms are the finite Aut(K); Gamma_0
  is finite index but does not make all Out filtration-preserving.
- The canonical alpha_+(1) formula and exact integrality criterion
  a(alpha) in O_K minus J survive; the obstruction is integrality, not
  determination.
- H_A-full for Aut(K)/Gamma_0 remains a conditional subgroup result only.

## 6. Classification

| item | classification |
|---|---|
| Serre upper numbering and reciprocity comparison | VALID/STANDARD (up to fixed index shift) |
| Inertia and wild inertia characteristic | VALID |
| Every alpha in Out preserves all upper ramification subgroups | FALSE (Kondo Thm A) |
| Every alpha preserves every U^n | FALSE |
| alpha^times(U^e)=U^e for every alpha | NOT PROVED/UNSUPPORTED |
| alpha_+ log=log alpha^times | VALID paper-level |
| a(alpha)=alpha_+(1) in I canonical | VALID conditional |
| a(alpha) in O_K for all alpha | NOT PROVED; integrality obstruction |
| H_A-full full Out | OPEN/NOT PROVED |
| B=O_K full Out | CONDITIONAL on H_A-full |
| B=I full Out | NOT EXCLUDED/NOT CONSTRUCTED |
| Aut(K)/Gamma_0 subgroup results | CONDITIONAL subgroup only |

## 7. Conclusion

P is false for full Out(G_K). The upper ramification filtration is not
characteristic under all abstract automorphisms; Kondo 2025 Theorem A identifies
its stabilizer with the finite field-theoretic Aut(K). The corrected donor H is
infinite and not contained in Aut(K), so an alpha in H outside Aut(K) fails to
preserve some upper ramification subgroup and, under local reciprocity, some
principal unit group U^n. Kondo Theorem B gives a second independent actual
counterexample.

Therefore Out does not preserve the principal unit filtration U^n. The
U^e-specific preservation used in task-204 is not proved, and H_A-full, B=O_K
for full Out, and the exclusion of B=I are not established. The canonical
alpha_+(1) formula and integrality criterion survive; the exact open
obstruction is a(alpha) in O_K minus J for all actual alpha.

No complete C, no target containment, no global inequality. P6 open;
target_accepted=false.

## 8. Status

- Natural-language decisive verification only; no Lean/Project edits.
- P refuted by Kondo 2025 Theorem A/B and the infinite symplectic donor H.
- U^e-specific preservation remains unproved; H_A-full open.
- No new attack, no fabricated closure.
