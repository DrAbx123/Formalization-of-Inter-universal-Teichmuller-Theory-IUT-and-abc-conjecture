# C9 trace pairing vs Kondo symplectic form

Task: task-237. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 new-math exploration, natural-language only.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Sources

- Kondo 2026 local snapshot,
  sources/Kondo-2605.25428v2.html,
  SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86;
  Lemma 1.6, Definition 3.2, Lemma 3.3.
- Kondo 2025 local snapshot,
  sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f;
  Theorem D, Theorem E/1.3, Section2 mapping-class/intersection-form construction.
- C9-U-LINE-20261025.md,
  SHA256 d6fe76d2fdeafce850640f6e04ae7e7291c6c15272bac6fea0ee80e4fe152ef3.
- C9-U-ORTHOGONAL-20261025.md,
  SHA256 43a71d66f4d83053c34a419612cda8153de06ff20d9e259273694c93548fb5a8.

## 1. Question and verdict

Question: does the Kondo mapping-class Sp_{40}(Z_p)-action on W=ker Tr
preserve the trace pairing beta(x,y)=Tr_{K/Q_p}(xy), or a scaled version
lambda beta? If yes, then W^perp=Q_p1 would be Sp-invariant, hence the fixed
line U=<y1> would equal W^perp, giving 1 in U and H_A/B=O_K without extra
normalization.

Verdict:

1. **Trace pairing is symmetric, not alternating.** It is nondegenerate on K
   and restricts to a nondegenerate symmetric form on W=kerTr.
2. **A Kondo/Kondo-mapping-class symplectic form is alternating.** The
   mapping-class intersection form on H_1 is alternating; the Sp_{40}(Z_p)
   matrix group of Definition 3.2 is a symplectic group, i.e. the automorphism
   group of an alternating form. Kondo 2026 states the matrix embedding and the
   Sp containment, not an explicit formula for that form.
3. **Therefore trace pairing cannot equal the Kondo symplectic form (or a
   nonzero scalar multiple).** A symmetric bilinear form and an alternating
   one cannot be equal over Q_p with p odd. Explicitly, beta(w,w) need not
   vanish, while every alternating form has Omega(w,w)=0.
4. **The Sp action does not preserve beta (or lambda beta).** The trace
   pairing on W is a nonzero symmetric Sp-invariant candidate; transvections
   in Sp force any invariant symmetric bilinear form to be zero. Since beta is
   nonzero, beta is not Sp-invariant.
5. Consequently the hoped deduction U=W^perp is **not available**. The trace
   computation still gives W^perp=Q_p1 (task-224), but this line is not the
   Kondo fixed line U in general; U=W^perp remains an extra condition.

The first branch of the task is therefore **impossible**, not merely
unproved. The second branch (if preservation held) does not occur.

## 2. Trace pairing: exact properties

Let K/Q_p be finite, beta(x,y)=Tr_{K/Q_p}(xy). It is a nondegenerate symmetric
Q_p-bilinear form. For the C9 type K=Q_p(pi), e=41, p=12301, pi^e=p u,
O_K=Z_p[pi], m=(pi), J=m:

    Tr(1)=41,  Tr(pi^a)=0 (1<=a<=40),
    W=ker Tr=Q_p-span(pi,...,pi^40).                           (2.1)

### 2.1 Restriction to W is symmetric nondegenerate

In the basis e_a=pi^a (1<=a<=40), the trace pairing matrix is

    beta(pi^a,pi^b)=Tr(pi^{a+b}).                              (2.2)

Since 1<=a,b<=40, a+b ranges 2..80. For a+b<=40, Tr=0. For a+b=41,
pi^{41}=p u is a scalar and Tr(p u)=41 p u !=0. For 42<=a+b<=80,
pi^{a+b}=p u pi^{a+b-41}, whose trace is zero because 1<=a+b-41<=39. Thus

    beta(pi^a,pi^b) = 41 p u  if a+b=41,  else 0.             (2.3)

The matrix is the anti-diagonal permutation matrix times 41pu. It is
symmetric, invertible, and nondegenerate on W. It is not alternating: for
example

    w=pi+pi^40,
    beta(w,w)=Tr(pi^2)+2Tr(pi^41)+Tr(pi^80)
             = 0 + 2*41 p u + 0 = 82 p u !=0.                 (2.4)

Thus beta|W is a nonzero symmetric nondegenerate form, not an alternating
form.

### 2.2 W^perp with respect to beta

Since beta(1,w)=Tr(w)=0 for w in W, 1 in W^perp; beta is nondegenerate and
dim W=40, so

    W^perp = Q_p 1.                                             (2.5)

This is the task-224 result. It does not identify U with W^perp.

## 3. Kondo symplectic form and what the source actually states

Kondo 2026 Definition 3.2, for odd d=G, defines g=(d-1)/2 and embeds
Sp_{2g}(Z_p) into GL_d(Q_p) by A -> diag(1,A) in the y-basis
y1,...,y_d. Lemma 3.3 proves Sp_{2g}(Z_p) is contained in Phi(Out(G_K)).

Kondo 2026 does **not** write an explicit alternating bilinear form
Omega on K_+ or on W in the frozen text. The notation Sp means the matrix
group preserving an implicit standard symplectic form in the chosen y-basis;
the mapping-class origin (Kondo 2025 Section 2) uses the alternating
intersection form on H_1 of the once-punctured surface.

Therefore:

- The Kondo object available in the source is a **symplectic matrix group**,
  equivalently an implicit alternating form in the y-basis; no formula for
  Omega on K is given.
- If one interprets "Kondo symplectic form" as any alternating nondegenerate
  form preserved by the Sp action, then it is alternating by definition.

To prove an equality with beta one would need either:

(a) an explicit formula Omega(x,y)=... in K-coordinates, or
(b) a theorem that the implicit form equals beta after the y-to-K
    identification.

Neither appears in Kondo 2025/2026 or the frozen corpus. This is a missing
source formula, but the impossibility below does not depend on it.

## 4. Impossibility of beta = Omega

Let Omega be any alternating bilinear form on W (symplectic form). Then

    Omega(w,w)=0 for every w in W.                              (4.1)

By (2.4), beta(w,w)=82pu !=0 for w=pi+pi^40. Hence beta!=Omega as bilinear
forms. The same holds for lambda beta with lambda!=0: (lambda beta)(w,w)
=lambda*82pu !=0.

Over Q_p with p odd, a bilinear form that is both symmetric and alternating is
zero: Omega(w,w)=0 for all w and symmetry gives
2 Omega(v,w)=Omega(v+w,v+w)-Omega(v,v)-Omega(w,w)=0, so Omega=0. A nonzero
scalar multiple of beta cannot be alternating.

Thus the first branch is impossible at the level of the bilinear forms
themselves, without needing the explicit Kondo Omega.

## 5. Impossibility of Sp-invariance of beta

Even if one did not compare beta with Omega, the Sp action cannot preserve beta
(or a nonzero scalar multiple). Proof by transvections.

Let V=W be the 2g-dimensional Q_p-vector space with an alternating form Omega
preserved by Sp(V). For a nonzero vector v in V, the symplectic transvection

    T_v(x)=x+Omega(x,v)v                                      (5.1)

lies in Sp(V) (it fixes v^perp and preserves Omega; standard, and integral for
primitive v).

Suppose B is a symmetric bilinear form invariant under all such T_v. Compute:

    B(T_v x,T_v y)
      = B(x,y)+Omega(x,v)B(v,y)+Omega(y,v)B(x,v)
        + Omega(x,v)Omega(y,v)B(v,v).                         (5.2)

Invariance gives, for all x,y,v,

    Omega(x,v)B(v,y)+Omega(y,v)B(x,v)
      + Omega(x,v)Omega(y,v)B(v,v)=0.                         (5.3)

Take x with Omega(x,v)=0. Then

    Omega(y,v)B(x,v)=0 for all y,                            (5.4)

so B(x,v)=0 for all x in v^perp (choose y with Omega(y,v) !=0). Hence
B(v,.) vanishes on v^perp, so B(v,.) is a multiple of Omega(.,v):

    B(v,w)=c(v)Omega(w,v).                                   (5.5)

By symmetry,
B(v,w)=B(w,v)=c(w)Omega(v,w)=-c(w)Omega(w,v), so c(v)=-c(w) for all
non-orthogonal v,w; hence c is a constant c on all nonzero vectors. Then
B=c Omega. But B is symmetric and Omega is alternating, so over p odd c=0.
Thus B=0.

The trace pairing beta|W is nonzero and symmetric. Therefore beta cannot be
invariant under the Sp action (nor can lambda beta, lambda!=0). This is an
explicit obstruction: the Sp transvections do not preserve the trace pairing.

Consequences:

- W^perp=Q_p1 is not Sp-invariant in the trace pairing; the Sp-fixed line U is
  not forced to be W^perp.
- The hope "trace pairing preserved => U=W^perp" fails at the first premise.
- U=W^perp remains an extra condition (task-227); it is not a consequence of
  the Kondo reconstruction.

## 6. What is conditional / possible

Conditional construction: if an extra source supplied an **alternating**
Sp-invariant form Omega on W and an explicit identification of W with K's
trace-zero hyperplane, then one could ask whether U is Omega-orthogonal to W
or whether Omega is related to beta by a complex structure J,
Omega(x,y)=beta(Jx,y). No such J or Omega formula is in the frozen source.
Without that data, the comparison is underdetermined.

Possible weaker statements:

- beta|W is a nondegenerate symmetric form; it gives an identification
  W ≅ W^dual and W^perp=Q_p1.
- If one declares the "symplectic form" to be beta|W, it is not symplectic
  (not alternating); this is a terminology change, not a source theorem.
- The Kondo Sp action preserves an implicit alternating form; any concrete
  formula for it is missing.

Impossible:

- beta = Omega for an alternating Omega (or nonzero scalar multiple).
- Sp invariance of beta|W (or nonzero scalar multiple).
- Derivation of U=W^perp from beta alone.

## 7. Classification

| item | verdict |
|---|---|
| beta(x,y)=Tr(xy) symmetric nondegenerate | PROVED |
| beta|W nondegenerate symmetric, matrix anti-diagonal 41pu | PROVED |
| beta(pi+pi^40,pi+pi^40)=82pu !=0 | PROVED |
| trace pairing alternating | FALSE |
| Kondo 2026 explicit Omega formula | NOT IN SOURCE |
| Kondo Sp matrix group implicit alternating form | PAPER-LEVEL |
| beta=Omega or lambda beta=Omega | IMPOSSIBLE |
| Sp preserves beta|W | IMPOSSIBLE (transvection argument) |
| W^perp=Q_p1 | PROVED |
| U=W^perp forced by Sp/trace | FALSE/NOT PROVED |
| U=W^perp extra source condition | CONDITIONAL/OPEN |
| H_A/B=O_K via this route | NOT OBTAINED |

## 8. Conclusion

The trace pairing beta(x,y)=Tr(xy) is a symmetric nondegenerate form; on
W=kerTr it has a nondegenerate symmetric restriction with
beta(pi+pi^40,pi+pi^40)=82pu !=0. A symplectic form is alternating, so beta
cannot equal the Kondo symplectic form or a nonzero scalar multiple. Moreover
the Sp transvections force any invariant symmetric bilinear form on W to be
zero; since beta|W is nonzero, beta is not Sp-invariant. Thus the hoped
preservation does not hold, W^perp=Q_p1 is not an Sp-fixed line, and U=W^perp
is not derived. The task's first branch is impossible; the second is not
available. U=W^perp remains an extra normalization; H_A/B=O_K is not obtained
by this route.

No Lean/kernel closure; P6 open; target_accepted=false.

## 9. Status

- Natural-language new-math exploration only; no Lean/Project edits.
- trace pairing properties and Sp non-invariance proved; equality with
  symplectic form impossible; Kondo explicit Omega missing.
- No target closure, no arbitrary assumption.
