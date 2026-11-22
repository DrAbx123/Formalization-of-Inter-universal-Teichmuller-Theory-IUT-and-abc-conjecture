# C9 Kondo source recheck: F(x_i), y1, Tr, C

Task: task-221. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 source recheck/local mathematics only.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Sources

- Kondo 2025 local snapshot, sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f.
  Especially lines 363-366: the definition of F, y_i, and the fixed JW
  generators as in Theorem D.
- Kondo 2026 local snapshot, sources/Kondo-2605.25428v2.html,
  SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86.
  Theorem 1.2, Definition 3.2, Lemma 3.3, Theorem 2.6 proof.
- C9-Y1-TRACE-20261025.md,
  SHA256 a33ebdb8d0d0551b1391cf3069c71b8cf3255d8b56f20f96513c7f33e22f425c.
- C9-F-XI-CONSTRUCT-20261025.md,
  SHA256 a301bbeb1204e84ecaa2d0c6a6a94967d88a789088e56ea4471b7a4f3f09b924.
- C9-PRINCIPAL-FILTRATION-P-20261025.md,
  SHA256 f125420f44405b360a289cdf1787c6c4f979d122eb6e65072639df1b6e160599.

## 1. The actual local definition of F

Kondo 2025 lines 363-366 state (paraphrased with formulas):

- Let hat{k^times} be the profinite completion of k^times, and k_+ the
  underlying additive Q_p-vector space.
- When p is odd, **fix** topological generators sigma, tau, x_0,...,x_d of G_k
  as in Theorem D.
- Let F:G_k→k_+ be the homomorphism obtained as the composite

      G_k -> G_k^ab
          -> hat{k^times}   (inverse of local reciprocity)
          -> O_k^times       (projection determined by a choice of
                              uniformizer of O_k)
          -> k_+             (p-adic logarithm log_k).

- For i=1,...,d, y_i in k_+ is the image of x_i under F; the y_i form a
  Q_p-basis (Kondo 2025 after Theorem D; Kondo 2026 Theorem 1.2 text).

Kondo 2026 uses the reconstructed version: y_i is the image of x_i under the
composite P(G) hook -> I(G) -> O^times(G) -> k_+(G).

The definition is explicit **once the actual x_i are fixed**. The local source
fixes some JW tuple as in Theorem D, but Theorem D is an existence theorem and
the frozen text does not list the actual elements x_i, their unit images, or
their p-adic log values. This is the first source gap.

### 1.1 Uniformizer projection

The projection hat{k^times}->O_k^times depends on a choice of uniformizer of
O_k. For elements in inertia (in particular wild inertia x_i), the reciprocal
image lies in the unit part; the projection is therefore independent of the
uniformizer for x_i. The uniformizer choice affects only non-inertia elements
and does not normalize Tr(y1) or the trace pairing. No additional trace
normalization comes from this choice.

## 2. What Theorem D does and does not determine

Theorem D gives generators sigma, tau, x_0,...,x_d and relations, including
for odd d

    sigma x_0 sigma^{-1}
      = (x_0')^t x_1^{p^s} [x_1,x_1'][x_2,x_3]...[x_{d-1},x_d],   (2.1)

with x_0' in closure<tau,x_0>, x_1' in closure<sigma,tau,x_1>, positive
integers s,t.

It gives no explicit p-adic values for x_i, nor explicit values of their
reciprocity images in O_K^times. The y_i are determined by the actual x_i, but
the frozen source only supplies the presentation/relations.

Apply F to (2.1). Since F is a homomorphism into the additive group k_+, it
kills commutators, and F(sigma x_0 sigma^{-1})=F(x_0) (additive cancellation).
Hence

    F(x_0) = t F(x_0') + p^s y_1.                              (2.2)

This is an exact relation, but it involves F(x_0) and F(x_0'), neither of which
is one of the y_i (the y-basis is indexed by x_1,...,x_d only). x_0' lies in
closure<tau,x_0>, so F(x_0') is a Z_p-multiple of F(x_0) when F(tau)=0, or a
combination of F(tau),F(x_0) in general; no source gives that multiple or F(tau).
Therefore (2.2) does not determine y1 numerically. The x_2,...,x_d appear in
(2.1) only inside commutators, which F kills; the presentation gives no linear
constraint on y2,...,yd at all.

The other JW conditions (x_i topologically normally generate wild inertia,
x0' in closure<tau,x0>, x1' in closure<sigma,tau,x1>, p-power relations) also
involve only group-theoretic relations. They do not supply the p-adic unit
values needed to compute F(x_i).

Conclusion: Theorem D plus the F definition determines y_i **functionally**
from x_i, but not numerically; the actual x_i/F(x_i) are not in the frozen
source. The only relation obtained under F, (2.2), involves unknown F(x0),
F(x0'), t, and neither fixes y1 nor Tr(y1).

## 3. Kummer theory does not fill the gap

K=Q_p(pi), e=41, p=12301, mu_41 subset Q_p. Kummer theory gives:

- the finite-order Kummer class of pi and a noncanonical F_41-basis of
  K^times/(K^times)^41;
- a finite-order pairing with G_K on mu_41.

But the x_i are pro-p generators of wild inertia, and F(x_i)=log(unit) is a
pro-p p-adic logarithm in J. Kummer theory is finite-order 41-torsion data; it
does not identify the pro-p JW generators x_i, does not determine their
reciprocity-unit images, and does not normalize their p-adic logs. The dual
Kummer basis is noncanonical and is not tied to the JW presentation. Hence
Kummer theory cannot compute y1, Tr(y1), c, or C either.

## 4. Trace and C remain source-undetermined

Kondo 2025 Theorem E/1.3 gives

    W=ker Tr=<y2,...,y_d>,   Tr(y1) != 0,                      (4.1)

and, in the tame totally ramified case, Tr=Tr_{K/Q_p}. It does not give
Tr(y1). The trace pairing x,y -> Tr(xy) uses multiplication, which is not part
of the Q_p-linear reconstruction; it is not supplied by the Kummer or JW data.

Consequently:

- c=41/Tr(y1) and u0=c y1, w0=1-u0 are not determined;
- C=([y1]_{B_O},...,[y_d]_{B_O}) in GL_41(Q_p) is defined only after actual
  y_i are chosen; it is not determined;
- the H_A-full_H criterion u0+A w0 in O_K for all A in Sp_40(Z_p) cannot be
  evaluated;
- B_H=O_K versus B_H=I remains undetermined.

## 5. Conditional relation and models

If an external source supplied the actual x_i or y_i, then:

    y_i=F(x_i),  1=u0+w0, u0=c y1, c=41/Tr(y1), w0=1-c y1,
    a(alpha)=u0+A w0,
    H_A-full_H <=> u0+A w0 in O_K for all A in Sp_40(Z_p).     (5.1)

The task-217 coordinate models still show that the recorded structural data
admit opposite outcomes:

- y1=p: Tr=41p, c=1/p, u0=1, w0=0, H_A true, B_H=O_K.
- y1=p+pi: Tr=41p, c=1/p, u0=1+pi/p, w0=-pi/p; A=-I gives 1+2pi/p notin O_K,
  H_A false, B_H not O_K.
- y1=2p: Tr=82p, c=1/(2p), H_A true, B_H=O_K.

The JW relation (2.2) does not select among these because F(x0),F(x0'),t are
unknown. Kummer theory does not select either.

## 6. Refined obstruction

The local Kondo F definition is more explicit than the generic trace data, but
the frozen source still does not determine F(x_i):

1. F is a composite of known maps, but its inputs x_i are only specified by
   the existence part of Theorem D; no explicit x_i or their reciprocity-unit
   values are listed.
2. Under F, the JW relation collapses to (2.2), involving F(x0),F(x0') outside
   the y-basis; it does not determine y1..yd.
3. Kummer theory gives finite-order 41-torsion, not the pro-p log-unit values
   F(x_i) in J, and its dual basis is noncanonical.
4. The trace theorem gives W=kerTr and Tr(y1) nonzero but not Tr(y1); C is not
   determined.
5. The task-217 models satisfy the recorded structural axioms with opposite
   H_A/B outcomes, so no source choice is forced.

Therefore the source obstruction is refined, not removed:

    y1, Tr(y1), c, C, u0, w0 are NOT determined;
    H_A-full_H and B_H are UNDETERMINED;
    full H_A-full/B branch open.

## 7. Classification

| item | status |
|---|---|
| Kondo F definition (lines 363-366) | SOURCE ACTUAL |
| y_i=F(x_i) basis, y_i in J, W=kerTr | PAPER-LEVEL ACTUAL |
| Theorem D presentation/relations | PAPER-LEVEL ACTUAL |
| explicit x_i/unit values/F(x_i) | NOT IN FROZEN SOURCE |
| F(JW relation) gives (2.2) | VALID CONDITIONAL |
| (2.2) determines y1/Tr(y1) | FALSE: F(x0),F(x0'),t unknown |
| Kummer extraction of F(x_i) | FALSE: finite-order vs pro-p |
| Tr(y1), c, C | NOT DETERMINED |
| H_A-full_H/B_H | UNDETERMINED |
| full H_A-full/B branch | OPEN |

## 8. Conclusion

Rechecking the local Kondo F definition and Theorem D does not remove the
source obstruction. F is explicit as a composite and y_i=F(x_i) is determined
once the actual JW generators are fixed, but the frozen source supplies only
the existence of such generators and their relations, not their p-adic values
or reciprocity-unit images. The relation (2.2) is exact but involves unknown
F(x0),F(x0') and does not fix y1. Kummer theory supplies only finite-order
41-torsion data, not the pro-p log values. Hence y1, Tr(y1), c, C, u0, w0
remain source-undetermined, and H_A-full_H/B_H remain undetermined. No
arbitrary coordinates are used; no Lean/kernel closure; P6 open.

## 9. Status

- Natural-language/source recheck only; no Lean/Project edits.
- Refined obstruction recorded; task-217 underdetermination survives.
- target_accepted=false.
