# C9 new program: integral Tannakian trace-canonical theorem

Task: task-242. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 creative new-math program, natural-language only.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Inputs and scope

- Kondo 2026 local snapshot,
  sources/Kondo-2605.25428v2.html,
  SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86;
  Lemma 1.6, Definition 3.2, Lemma 3.3, Theorem 2.6 proof.
- Kondo 2025 local snapshot,
  sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f;
  Theorem D, Theorem E/1.3, Section2 mapping class/intersection form.
- C9-TRACE-SYMPLECTIC-20261025.md,
  SHA256 5bdd9c699fa436a83e2823adc9535b7eaa85c50b0d80ecc87d93564d892409c9.
- C9-U-LINE-20261025.md,
  SHA256 d6fe76d2fdeafce850640f6e04ae7e7291c6c15272bac6fea0ee80e4fe152ef3.
- C9-U-ORTHOGONAL-20261025.md,
  SHA256 43a71d66f4d83053c34a419612cda8153de06ff20d9e259273694c93548fb5a8.

The program asks whether a canonical **integral Tannakian trace form** can
supply the missing normalization U=W^perp/1 in U and hence H_A/B=O_K, without
adding a normalization by hand.

Verdict in advance:

- The original conjecture "the field trace pairing beta(x,y)=Tr(xy) is the
  unique Sp-invariant symplectic form compatible with the integral structure"
  is **IMPOSSIBLE**. beta is symmetric, not alternating, and is not
  Sp-invariant (task-237).
- A **modified** Tannakian program is possible only with a genuinely new
  integral polarization/tensor functor. The frozen Kondo source does not supply
  it. We state the modified conjecture, the conditional theorem it would give,
  and the exact obstructions.
- No 1 in U, no H_A/B=O_K, no target closure is obtained.

## 1. The naive trace form and why it cannot be the symplectic form

Let K=Q_p(pi), e=41, p=12301, O_K=Z_p[pi], m=(pi), J=m,
I=p^{-1}J, W=ker Tr=Q_p-span(pi,...,pi^40), U=<y1> with the Kondo y-basis.

The field trace pairing

    beta(x,y)=Tr_{K/Q_p}(xy)                                   (1.1)

is symmetric and nondegenerate. On W its matrix in the pi-power basis is
anti-diagonal:

    beta(pi^a,pi^b)=41 p u if a+b=41, else 0      (1<=a,b<=40).  (1.2)

It is symmetric and nondegenerate, but not alternating:
beta(pi+pi^40,pi+pi^40)=82 p u !=0.

A symplectic form Omega is alternating: Omega(w,w)=0 for all w. Therefore

    beta != Omega and lambda beta != Omega (lambda !=0).          (1.3)

This is already an impossibility at the level of bilinear forms over Q_p, p
odd. No Tannakian construction changes the symmetry of the field trace.

Moreover, the Kondo Sp_{40}(Z_p) action does not preserve beta: any symmetric
bilinear form invariant under all symplectic transvections is zero
(task-237), while beta|W is nonzero. Thus the first branch of the original
conjecture fails even before integrality.

## 2. What an integral Tannakian structure could add

The following is a **construction/hypothesis**, not a source theorem.

### 2.1 A neutral integral Tannakian datum

Let T be a neutral Tannakian category over Z_p (or a rigid tensor category of
integral p-adic Galois/Frobenioid objects) with a fiber functor

    omega : T -> Mod_Zp,

and a distinguished object V (the theta-pilot additive object) with:

- an integral lattice L=O_K inside V⊗Q_p=K;
- a symmetric trace form beta_T: V⊗V -> 1, obtained from duality and the
  trace of the identity (the Tannakian trace form);
- a symplectic object W_T with an alternating form
  Omega_T: Lambda^2 W_T -> 1 (a polarization);
- a morphism V -> W_T direct-sum U_T (the U/W decomposition);
- a trace-canonical line L_T (the image of the unit object 1 in V under the
  Tannakian trace normalization).

The field trace beta is the symmetric trace form beta_T after the fiber
identification V⊗Q_p=K. The Kondo Sp action is a tensor automorphism action if
a tensor functor from the mapping-class/Sp source to T is supplied.

### 2.2 The modified conjecture (Trace-Canonical Program)

Conjecture TC1 (integral symplectic realization). There is a neutral integral
Tannakian datum as above such that:

(a) the symplectic object W_T has fiber W=ker Tr and its alternating form
    Omega_T is the Kondo Sp_{40}(Z_p)-form (the form implicitly preserved by
    Definition 3.2);
(b) the Sp action is by tensor automorphisms of T and is Omega_T-symplectic;
(c) the U/W decomposition is Omega_T-orthogonal, so U_T=W_T^perp under
    Omega_T;
(d) the trace-canonical line L_T equals Q_p 1 (equivalently 1 in U_T) and the
    integral lattice L is the Tannakian lattice O_K;
(e) the polarization J=beta_T^{-1}Omega_T is an integral endomorphism with
    J(1)=1 (or at least J(L_T)=L_T).

If TC1 holds, then U=W^perp under the Kondo form, the fixed line is the trace
line, 1 in U, w0=0, a(alpha)=1, H_A-full holds and B=O_K.

This is a **conjecture**, not a theorem. It has the right shape: it isolates
the missing structures (tensor functor, alternating form, integral
polarization, trace-canonical line) instead of assuming the desired equality.

## 3. Conditional theorem (what TC1 would give)

The following conditional theorem is elementary and has no arbitrary choice
beyond its hypotheses.

Theorem 3.1. Assume an integral Tannakian datum with:

(T1) fiber K, lattice L=O_K, W=ker Tr, U the Sp-fixed line;
(T2) an alternating nondegenerate form Omega on W, extended to V=U direct-sum W
     by making U orthogonal to W;
(T3) the Sp action is Omega-symplectic and the U/W decomposition is
     Omega-orthogonal;
(T4) the trace-canonical line L_T is Q_p1, equivalently 1 in U.

Then:
(a) U=W^perp with respect to Omega;
(b) 1 in U, hence w0=0 and a(alpha)=1 for all alpha in the Sp action;
(c) alpha_+(O_K)=O_K for all alpha, H_A-full holds, and B=O_K.

Proof. (a) is the orthogonal decomposition U direct-sum W. (b) is T4.
(c) uses the coordinate formula 1=u0+w0: if 1 in U and U cap W=0, then
w0=0 and u0=1; a(alpha)=u0+A w0=1; hence alpha_+(O_K)=Z_p1+J=O_K; B=O_K. QED.

This theorem is **conditional** on the Tannakian structures T1-T4. It does not
prove TC1 and does not derive 1 in U from Kondo.

## 4. Exact obstructions to the original and to TC1

### 4.1 Field trace is not symplectic

beta is symmetric, Omega alternating; equality impossible (Section 1). The
original conjecture "beta is the unique Sp-invariant symplectic form" is
therefore **impossible**, not an open problem.

### 4.2 Field trace is not Sp-invariant

The transvection argument (task-237) shows any symmetric form invariant under
all symplectic transvections is zero. Since beta|W is nonzero, beta is not
Sp-invariant. No scalar multiple works. Thus the interpretation "the Sp action
preserves beta, hence W^perp=Qp1 is Sp-fixed" is false.

### 4.3 Kondo source does not give a tensor functor

Kondo 2025 defines rho: Mod(S minus P)->Out(G_K) as a **set-theoretic** map,
not a group homomorphism; there is no homomorphism from the mapping-class group
to Out(G_K) supplied. Kondo 2026 gives the closed preimage
H=Phi^{-1}(Sp) with Phi(H)=Sp, but H is a subgroup of Out(G_K), not a tensor
automorphism group of Rep(G_K) with a chosen lift. An outer automorphism class
does not define a strict tensor autoequivalence of the representation category
without a lift; different lifts differ by inner automorphisms, which act
trivially on representations but are needed to define a tensor functor at the
level of objects/morphisms. The source does not supply a tensor functor
Mod(S)->T or Sp->T.

### 4.4 Kondo source does not give Omega or J

Kondo 2026 Definition 3.2 states the Sp matrix embedding but no explicit
alternating form Omega on K_+ or W. Kondo 2025 uses the surface intersection
form, but does not identify it with a form on K_+ under the y-basis or construct
the integral polarization J=beta^{-1}Omega. Thus TC1(a),(b),(e) are not
source-supported.

### 4.5 The trace-canonical line is not constructed

TC1(d), L_T=Q_p1, is exactly the missing normalization. The Tannakian trace of
the identity gives the symmetric trace beta_T, not an alternating form or a
canonical identification of its unit line with Q_p1. The field trace beta has
kernel W and orthogonal complement Q_p1, but the Sp-fixed line U can be any
complement of W (task-227); the unit line Q_p1 is not selected by the trace
form alone.

### 4.6 No integral comparison beta_T vs Omega_T

Even if a tensor form Omega_T existed, comparing it with beta_T requires an
integral complex structure J=beta_T^{-1}Omega_T and a proof that J is integral
and preserves L_T. Kondo provides no p-adic Hodge polarization or integral
comparison. Without J, beta_T and Omega_T are two unrelated bilinear forms
(symmetric and alternating).

## 5. Modified construction: what would actually be needed

The program can be reformulated as a list of missing source theorems:

N1. A tensor functor from the mapping-class/Sp source to the Tannakian
    category T, or a homomorphism Sp_{40}(Z_p)->Aut_tensor(T). Kondo's rho is
    only a set map; H=Phi^{-1}(Sp) is only an outer-automorphism subgroup.
N2. An integral symplectic object W_T with alternating form Omega_T whose
    fiber is W and whose form is the Kondo Sp form. Kondo 2026 gives only the
    matrix group.
N3. An integral polarization J with Omega_T(x,y)=beta_T(Jx,y), J integral, and
    J(L_T)=L_T (or J(1)=1). This is the trace-canonical theorem missing from
    the source.
N4. A proof that the trace-canonical line L_T is Q_p1 (the unit line), not just
    the fixed line U of the Sp action. This is equivalent to the H_A/U
    normalization.
N5. TC1's orthogonal decomposition U/W for Omega_T. This is automatic only
    after choosing the extension of Omega_T by U orthogonal to W; it is not a
    Kondo statement.

If N1-N5 are supplied, Theorem 3.1 gives 1 in U and H_A/B=O_K. None is supplied
by Kondo 2025/2026 or the frozen corpus.

## 6. Classification

| item | status |
|---|---|
| beta(x,y)=Tr(xy) symmetric nondegenerate | PROVED |
| beta is not alternating; beta(pi+pi40,pi+pi40)=82pu | PROVED |
| beta is Sp-invariant | IMPOSSIBLE (task-237) |
| beta equals Kondo symplectic form/lambda multiple | IMPOSSIBLE |
| Kondo 2026 explicit Omega/Tannakian tensor functor | NOT IN SOURCE |
| TC1 integral Tannakian symplectic realization | CONJECTURE |
| Theorem 3.1 (TC1 => U=Wperp,1 in U,H_A/B=O_K) | PROVED CONDITIONAL |
| N1-N5 source theorems | MISSING |
| H_A/B=O_K from Tannakian program | NOT OBTAINED |
| original conjecture | IMPOSSIBLE |
| modified TC1 | HYPOTHESIS/OPEN |

## 7. Conclusion

The original integral trace-canonical conjecture cannot work with the field
trace pairing: beta is symmetric, non-alternating, and not Sp-invariant. The
Kondo symplectic form is an alternating object, and the source does not supply
an explicit Omega, a tensor functor realizing the Sp action, or an integral
polarization J identifying Omega with beta. The trace-canonical line Q_p1 is
not selected by beta or by the Sp fixed line U.

A modified program is stated: construct an integral Tannakian symplectic
object W_T with alternating form Omega_T, a tensor Sp action, an integral
polarization J, and a trace-canonical line L_T=Q_p1. If these are supplied,
Theorem 3.1 yields U=W^perp, 1 in U, H_A-full and B=O_K. This is a conditional
theorem plus a precise new-math program, not a proof from the frozen source.
No arbitrary assumption is made.

No Lean/kernel closure; P6 open; target_accepted=false.

## 8. Status

- Natural-language creative program only; no Lean/Project edits.
- Original conjecture refuted; modified TC1 and conditional Theorem 3.1 stated;
  exact obstructions N1-N5 listed.
- No target closure, no H_A/B=O_K.
