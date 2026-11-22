# A natural-language underdetermination theorem for H_A and B

Task: task-222. Date: 2026-10-25. Author: transport.
Stage: self-contained natural-language theorem and proof. No Lean/Project edits.
Only this file written. target_accepted=false.

Inputs used for context only:

| file | lines | SHA256 |
|---|---:|---|
| C9-Y1-TRACE-20261025.md | 179 | A33EBDB8D0D0551B1391CF3069C71B8CF3255D8B56F20F96513C7F33E22F425C |
| C9-HAFULL-CORRECTED-ATTACK-20261025.md | 271 | A1BDFD61B7FB90D1D24EC9A3D770C308360A095F435D4A2C9F35509775356BF0 |
| C9-AUDIT-HAFULL-LITE-20261025.md | 254 | 5FA594D485B2A9D1618F21AA22CAC9CE63746AE489F177E76F700745C8A10BAD |

## 1. Purpose

This note proves, in theorem-proof style, that the recorded structural Kondo
data do not determine the H_A-full property or the branch B. The proof uses
two explicit abstract coordinate models, A and B, satisfying the same recorded
axioms and giving opposite outcomes:

    Model A: H_A-full true,  B=O_K;
    Model B: H_A-full false, B=I.

The models are not claims about actual Kondo F(x_i) values. They show exactly
which additional source input is needed to decide the branch.

## 2. Recorded data and notation

Let p=12301, e=41, K=Q_p(pi) with pi^e=p u, u in Z_p^times. Put
O_K=Z_p[pi], m=pi O_K, J=m, I=p^{-1}J, and Tr=Tr_{K/Q_p}.
In the tame totally ramified case K^{d=1}=Q_p, so this is the trace target of
Kondo 2025 Theorem E.

The recorded data consist of:

(R1) a Q_p-basis y_1,...,y_41 of K with
       y_i in J,  W:=ker Tr=<y_2,...,y_41>_{Q_p},
       U:=<y_1>_{Q_p},  K=U direct-sum W,
       Tr(y_1) in p Z_p and Tr(y_1) != 0;

(R2) the decomposition of the field unit
       1 = u_0 + w_0,  u_0 in U, w_0 in W,
       u_0 = c y_1,   c=41/Tr(y_1),
       w_0 = 1-u_0;

(R3) the action of H on K in the y-basis:
       alpha_+|U=id,  alpha_+|W=A,  A in Sp_{40}(Z_p),
       i.e. diag(1,A) in the y-basis;

(R4) for alpha=alpha_A,
       a(alpha):=alpha_+(1)=u_0+A w_0;

(R5) the source-generated lattice
       B= closed Z_p-span of the union of alpha_+(O_K) over the recorded H,

       alpha_+(O_K)=Z_p a(alpha)+J.

(The last identity uses alpha_+(J)=J, which is part of the recorded H_A-lite
data.)

The H_A-full property is defined as

    H_A-full  :  alpha_+(O_K)=O_K for every recorded alpha.       (2.1)

For a single alpha, because alpha_+(J)=J,

    alpha_+(O_K)=Z_p a(alpha)+J.                                  (2.2)

The recorded task criterion "H_A-full iff all a(alpha) in O_K" is the
integrality half of this condition; the nondegeneracy needed for equality is
discussed in Lemma 3.

## 3. Exact criterion for one alpha

Lemma 1. For alpha=alpha_A:

    alpha_+(O_K)=O_K  <=>  a(alpha) in O_K minus J.               (3.1)

Proof. By (2.2), alpha_+(O_K)=Z_p a+J with a=a(alpha).

If a in J, then Z_p a+J=J, which is not O_K.

If a not in O_K, then Z_p a+J is not contained in O_K, so it cannot equal O_K.

If a in O_K but a not in J, then a has nonzero class in the one-dimensional
quotient O_K/J, so Z_p a+J=O_K. QED.

Lemma 2 (decomposition). Write a(alpha)=lambda(alpha)1+w(alpha) with
lambda(alpha) in Q_p and w(alpha) in W. Then

    a(alpha) in O_K  <=>  w(alpha) in O_K cap W = J cap W.         (3.2)

In particular, if a(alpha) in O_K then w(alpha) in J.

Proof. 1 in O_K and W is the trace kernel. O_K=Z_p1+(J cap W). Therefore
a in O_K iff its W-component lies in J cap W. QED.

## 4. Field facts used by the models

The following are standard and exact for K=Q_p(pi), pi^41=p u:

    Tr(1)=41,  Tr(pi^a)=0 for 1<=a<=40,  Tr(p)=41p,
    J=m=Z_p-span(p,pi,...,pi^40),
    W=ker Tr=Q_p-span(pi,...,pi^40),
    J cap W=Z_p-span(pi,...,pi^40),
    O_K=Z_p1 direct-sum (J cap W),
    I=p^{-1}J=pi^{1-e}O_K.                                      (4.1)

Also pi/p=u pi^{-40} has p-adic valuation -40/41, hence is not in O_K.

## 5. Model A: H_A-full true, B=O_K

Define

    y_1=p,  y_i=pi^{i-1} for 2<=i<=41.                            (5.1)

Then:

- y_1,...,y_41 is a Q_p-basis of K; y_i in J; y_2,...,y_41 is a basis of W;
  Tr(y_1)=41p in pZ_p and nonzero.
- J=Z_p-span(y_1,...,y_41).
- c=41/Tr(y_1)=1/p; u_0=c y_1=1; w_0=0.
- For every A in Sp_{40}(Z_p),
      a(alpha_A)=u_0+A w_0=1.                                   (5.2)
- Thus a(alpha_A)=1 in O_K minus J for every A; Lemma 1 gives
  alpha_A(O_K)=O_K for every A. Hence H_A-full holds.
- Since every alpha_A(O_K)=O_K, the branch is B=O_K.

Proposition 2 (Model A). The assignment (5.1) satisfies (R1)-(R5), gives
H_A-full true and B=O_K. QED.

## 6. Model B: H_A-full false, B=I

Define

    y_1=p+pi,  y_i=pi^{i-1} for 2<=i<=41.                          (6.1)

Then:

- y_1,...,y_41 is a Q_p-basis; y_2,...,y_41 is a basis of W; y_i in J;
  Tr(y_1)=Tr(p)+Tr(pi)=41p+0=41p in pZ_p and nonzero.
- Because p=y_1-y_2, J=Z_p-span(y_1,...,y_41).
- c=41/Tr(y_1)=1/p, so
      u_0=c y_1=1+pi/p,   w_0=1-u_0=-pi/p.                      (6.2)

### 6.1 H_A-full fails

Take A=-I in Sp_{40}(Z_p). Then

    a(alpha_{-I})=u_0-I w_0=u_0-w_0=1+2pi/p.                    (6.3)

Now pi/p=u pi^{-40} has p-adic valuation -40/41<0, so 1+2pi/p is not in
O_K. By Lemma 1, alpha_{-I}(O_K) != O_K. Hence H_A-full is false.

### 6.2 B=I

We compute the Z_p-span of the images alpha_A(O_K).

For each A,

    a(alpha_A)=u_0+A w_0=1+pi/p - A(pi/p).                      (6.4)

Write z=pi/p=p^{-1}pi in W and L=Z_p-span(pi,...,pi^40)=J cap W.
Since A preserves L and w_0=-z, A w_0=-p^{-1}A pi with A pi in L. Hence

    a(alpha_A) in Z_p 1 + p^{-1}L + p^{-1}L subset I,            (6.5)

because p^{-1}L has exponents -40,...,0 and lies in I=p^{-1}J, and J subset I.
Therefore every alpha_A(O_K)=Z_p a(alpha_A)+J is contained in I, so

    B subset I.                                                  (6.6)

Now reduce modulo J. The elements

    p^{-1}pi, p^{-1}pi^2, ..., p^{-1}pi^40

are a Z_p-basis of p^{-1}L, and modulo J their classes are exactly the
W-part basis

    pi^{-40}, pi^{-39}, ..., pi^{-1}

of I/J. Since A runs over Sp_{40}(Z_p), the classes A(p^{-1}pi) run over the
standard Sp_{40}(F_p)-orbit of a nonzero W-vector in I/J. The standard
representation of Sp_{40}(F_p) on its 40-dimensional module is irreducible,
so this orbit spans the whole W-part W of I/J. Together with the class of
u_0=1+pi/p, whose class has the nonzero l-component 1, this spans all of I/J.

Thus B maps onto I/J. Since B subset I and B contains J (by definition), B/J
is all of I/J, hence B=I.

Proposition 3 (Model B). The assignment (6.1) satisfies (R1)-(R5), gives
H_A-full false and B=I. QED.

## 7. Underdetermination theorem

Theorem 4 (source underdetermination). The recorded data (R1)-(R5) admit two
coordinate assignments, Model A and Model B, both satisfying all recorded
axioms, such that:

    Model A: H_A-full is true,  B=O_K;
    Model B: H_A-full is false, B=I.

Consequently H_A-full and the branch B are not determined by the recorded
data.

Proof. Propositions 2 and 3 give the two assignments. Their underlying
recorded data are identical: same K,p,e, same y-basis cardinality and trace
kernel W, y_i in J, Tr(y_1) in pZ_p nonzero, same diag(1,A) Sp-action, same
decomposition 1=u_0+w_0 with c=41/Tr(y_1), and same definitions of a and B.
Only the actual coordinates of y_1 (and hence u_0,w_0) differ. Model A has
u_0=1,w_0=0; Model B has u_0=1+pi/p,w_0=-pi/p. The first gives H_A-full and
B=O_K; the second violates integrality at A=-I and gives B=I. Therefore the
recorded axioms do not force a unique pair (H_A-full,B). QED.

Remark 5. Model B is not a claim that an actual Kondo F(x_i) tuple realizes
y_1=p+pi. It is an admissible coordinate model for the recorded axioms. The
theorem says the axioms alone are insufficient; actual F(x_i) values would be
additional input.

## 8. Conditional theorem H_A-full implies B=O_K

Theorem 6. Assume H_A-full:

    alpha_+(O_K)=O_K for every recorded alpha.                     (8.1)

Then B=O_K.

Proof. For each alpha, by Lemma 1, a(alpha)=alpha_+(1) lies in O_K minus J.
Hence alpha_+(O_K)=Z_p a(alpha)+J=O_K. Therefore every alpha_+(O_K)=O_K, and
the closed Z_p-span of their union is O_K. Thus B=O_K. QED.

Corollary 7. If B != O_K, then H_A-full fails: there is some alpha with
a(alpha) not in O_K minus J. In the nondegenerate case this means a(alpha) is
not in O_K, i.e. the nonintegral branch occurs.

Proof. Immediate contrapositive of Theorem 6. QED.

Remark 8 (the invalid W subset J shortcut). One must not prove
a(alpha) in O_K by assuming W subset J. W=ker Tr is a Q_p-hyperplane and is
not contained in the Z_p-lattice J=m; only W cap J is contained in J. The
correct derivation of w(alpha) in J from a(alpha) in O_K uses Lemma 2, not
W subset J. The models above respect this distinction.

## 9. B=I requires a nonintegral branch

Proposition 9. In Model B, B=I arises exactly because a(alpha_{-I})=1+2pi/p
is nonintegral: alpha_{-I}(O_K) is not O_K and its negative W-component,
together with the Sp-orbit, generates the extra I/J directions. If all
a(alpha) lay in O_K minus J, Theorem 6 would give B=O_K.

Consequently a source proof of B=I must exhibit an actual alpha with
a(alpha) not in O_K minus J (in the nondegenerate case, a(alpha) not in O_K),
or equivalently an actual integrality failure. A B=I conclusion cannot be
obtained from the recorded structural axioms alone.

## 10. Exact additional input needed

The theorem identifies the missing source data. To decide H_A-full/B one must
supply at least one of:

1. The actual elements F(x_i)=y_i in K, not merely their existence and trace
   kernel properties. In particular y_1 and Tr(y_1).
2. The scalar c=41/Tr(y_1) and the decomposition 1=u_0+w_0, equivalently the
   W-coordinate w_0 of 1.
3. The change-of-basis matrix C from the y-basis to an actual Z_p-basis of
   O_K, i.e. the actual coordinates of y_i (or of 1) in O_K.
4. The actual full Out generators and their matrices on O_K/J, or a theorem
   proving its integrality for all actual alpha.
5. Equivalently, an explicit computation of
       a(alpha)=p^{-1}log(alpha^times(exp p))=alpha_+(1)
   for the actual full Out generators and a proof that these lie in O_K.

Without one of these, Models A and B show that the recorded axioms have
opposite outcomes; no branch is forced. No arbitrary choice of coordinates is
permitted as a substitute for actual source data.

## 11. Conclusion

The recorded Kondo structural data determine:

- a Q_p basis y_i with W=ker Tr;
- y_i in J and Tr(y_1) in pZ_p nonzero;
- the diag(1,A) Sp-action;
- the formula a(alpha)=u_0+A w_0 and the definitions of H_A-full and B.

They do not determine the actual values y_1, w_0,c or the integrality of
a(alpha). Two admissible coordinate models satisfy all recorded axioms:

    Model A: u_0=1, w_0=0  =>  H_A-full true,  B=O_K.
    Model B: u_0=1+pi/p, w_0=-pi/p => H_A-full false, B=I.

Therefore H_A-full and B are source-underdetermined. The conditional theorem

    H_A-full  =>  B=O_K

is valid and is proved without W subset J. The alternative B=I requires a
nonintegral branch, as in Model B. The exact additional input needed is the
actual F(x_i)/y_1/Tr(y_1)/c/C or actual full-Out integrality data.

target_accepted=false.
