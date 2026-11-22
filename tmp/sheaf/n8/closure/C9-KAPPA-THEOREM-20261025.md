# C9 kappa theorem: trace pairing anti-diagonal and the B branch

Task: direct work (no board task). Date: 2026-10-25. Author: transport.
Stage: short natural-language theorem/proof attempt. No Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Result in one paragraph

Assume the Kondo W-basis has trace-pairing Gram matrix anti-diagonal with
constant c=41pu, and y_i in J. Then the W-basis y_2,...,y_41 is actually a
Z_p-basis of J cap W, Tr(y1) has v_p=1, and

    kappa = e v_p(Tr(y1)) - v_pi(y1) = 41 - v_pi(y1).

Since y1 in J has v_pi(y1) in [1,41], kappa lies in [0,40]:

    kappa=0  <=> v_pi(y1)=41  <=> y1 is p times a unit  => B=O_K;
    1<=kappa<=40 <=> v_pi(y1)<=40 <=> B=I.

Thus the anti-diagonal trace pairing reduces the B branch to the valuation of
y1 and excludes the ill-posed range kappa>=41. But it does not decide the
actual B: Kondo/JW relations do not compute v_pi(y1), and both v_pi(y1)=41
(kappa=0,B=O_K) and v_pi(y1)=1 (kappa=40,B=I) are compatible with the
anti-diagonal Gram matrix and the structural axioms. The exact missing input is
v_pi(y1) (equivalently the W-coordinate l in y1=a p+l).

## 1. Setup

Let p=12301, e=41, K=Q_p(pi), pi^e=p u, u in Z_p^times,
O_K=Z_p[pi], J=m=pi O_K, I=p^{-1}J, W=ker Tr.
Kondo gives a Q_p-basis y_1,...,y_41 of K with

    y_i in J,  W=Q_p-span(y_2,...,y_41),
    U=Q_p y_1,  K=U direct-sum W,
    Tr(y1) in p Z_p and nonzero.

Write

    1=u0+w0,  u0=c y1,  c=41/Tr(y1),  w0=1-u0.               (1.1)

Define

    vpi=v_pi,  vp=v_p,  vpi(pi)=1, vpi(p)=41,
    kappa=e v_p(Tr(y1))-vpi(y1).                               (1.2)

## 2. Assumption: anti-diagonal trace Gram on W

Assume:

(A) For 2<=i,j<=41,

    beta(y_i,y_j)=Tr(y_i y_j)
      = 41 p u   if i+j=43,
      = 0        otherwise.                                   (2.1)

This is the anti-diagonal form with constant c=41pu. It is true for the
explicit naive basis (p,pi,...,pi^40), but it is NOT a theorem of Kondo's
Q_p-basis statement; it is an additional normalization assumption here.
The conclusion below is conditional on (A).

Let

    L = Z_p-span(y_2,...,y_41) subset J cap W,
    L0 = J cap W = Z_p-span(pi,pi^2,...,pi^40).                (2.2)

## 3. The W-basis is an integral basis

Lemma 3.1. Under (A), L=L0. Consequently y_2,...,y_41 is a Z_p-basis of
J cap W.

Proof. The Gram matrix of L with respect to y_2,...,y_41 is anti-diagonal with
entries 41pu. Its determinant is (41pu)^40 up to sign, with p-adic valuation
40. The standard basis pi,...,pi^40 of L0 has Gram matrix

    Tr(pi^i pi^j)=Tr(pi^{i+j}),
    nonzero only if i+j=41, value Tr(pi^41)=Tr(pu)=41pu,    (3.1)

also anti-diagonal with the same entries. Hence det Gram(L0)=(41pu)^40 up to
sign, and the p-adic valuations of the two determinants are equal (both 40).

Since L subset L0 are free Z_p-lattices of rank 40, the index [L0:L] is finite
and

    det Gram(L)=[L0:L]^2 det Gram(L0).                         (3.2)

The two determinants are equal (same anti-diagonal matrix shape and entries),
so [L0:L]^2=1, hence [L0:L]=1 and L=L0. QED.

Remark 3.2. No integrality of y_i beyond y_i in J is used; the anti-diagonal
Gram plus containment in J cap W forces the integral basis.

## 4. Form of y1 and Tr(y1)

Corollary 4.1. Under (A), there are a in Z_p^times and l in L0 such that

    y1 = a p + l,   J = Z_p p direct-sum L0.                   (4.1)

Proof. Since y1 in J and y1 not in W (Tr(y1) nonzero), its class modulo
L0=J cap W is nonzero in J/L0 = Z_p p. Hence y1=a p+l with a in Z_p^times.
QED.

Corollary 4.2. Under (A),

    Tr(y1)=a Tr(p)+Tr(l)=a e p,  v_p(Tr(y1))=1.                (4.2)

Thus

    kappa = 41 - vpi(y1).                                      (4.3)

Proof. l in L0 subset W, so Tr(l)=0; Tr(p)=e p; a unit; e=41 unit mod p.
Then (1.2) with vp(Tr)=1 gives (4.3). QED.

## 5. Valuation range and B branch

Lemma 5.1. Under (A), vpi(y1) is an integer in [1,41].

Proof. y1 in J gives vpi(y1)>=1. Write y1=a p+l as in (4.1). The p-term
a p=pi^41(a/u) has valuation 41. The element l lies in
Z_p-span(pi,...,pi^40), so its pi-adic expansion uses only exponents 1,...,40
with Z_p coefficients; after multiplying coefficients by powers of p one may
get higher exponents, but the coefficient of pi^41 cannot occur (p is not in
L0). Hence y1 has no cancellation of its pi^41 term, and
vpi(y1)<=41. QED.

Theorem 5.2 (kappa dichotomy under (A)).

    vpi(y1)=41  <=>  kappa=0  <=>  y1=a p with a unit  => B=O_K.
    1<=vpi(y1)<=40 <=> 1<=kappa<=40 <=> B=I.                    (5.1)

In particular, under (A) the ill-posed range kappa>=41 does not occur.

Proof. Use kappa=41-vpi(y1) and Lemma 5.1. If vpi(y1)=41, then u0=c y1 with
c=41/Tr(y1)=1/(a p) (up to unit); u0=a p/(a p)=unit, actually u0 in O_K^×;
w0=1-u0 in m=J, so kappa=0 and B=O_K by task-250. If vpi(y1)<=40, then
kappa in [1,40], and task-250 gives B=I (actual A=-I nonintegral, Sp-orbit
spans). QED.

## 6. Does JW/Kondo determine vpi(y1)?

No. The Jannsen-Wingberg relation gives x_1^{p^s} multiplied by commutators
and x_0-powers; Kondo's F maps x_i to log of a unit y_i in J. The abelianized
log relation does not determine the pi-adic expansion or valuation of y1. The
trace theorem gives only Tr(y1) in p Z_p nonzero; under (A) it improves this to
v_p(Tr(y1))=1, but Tr(y1)=a e p still leaves the unit a and the W-coordinate l
free.

Both explicit structural models satisfy (A) and all Kondo structural axioms:

    Model A: y1=p,      l=0,  vpi(y1)=41, kappa=0, B=O_K;
    Model B: y1=p+pi,   l=pi, vpi(y1)=1,  kappa=40, B=I.

They have the same anti-diagonal W Gram (41pu), the same Tr(y1)=41p, the same
H=diag(1,Sp40), and the same underdetermination as the NL theorem. Neither
JW relations nor the trace pairing (A) distinguish them. Therefore (A) alone
does not prove actual kappa=40 or kappa=0.

## 7. Exact obstruction

The attempted source theorem has two independent gaps:

1. The anti-diagonal Gram matrix (A) is true for the explicit naive basis but
   is NOT proved for the actual Kondo y_i. Kondo 2026 gives only a Q_p-basis
   and W=kerTr; no Gram normalization. If (A) fails, Lemma 3.1 and the
   formula kappa=41-vpi(y1) fail.
2. Even granting (A), the actual vpi(y1) (equivalently the W-coordinate l in
   y1=a p+l) is not computed by JW/Kondo/F. Both endpoints kappa=0 and kappa=40
   are compatible with all recorded data.

Thus the exact missing input is:

    either a proof of (A) for the actual Kondo basis plus a computation of
    vpi(y1), or a direct computation of y1=F(x1) and Tr(y1).

No such computation is in the frozen source.

## 8. Conclusion

Under the anti-diagonal trace-pairing assumption (A), a genuine theorem holds:

    kappa = 41 - vpi(y1),   0 <= kappa <= 40,
    kappa=0  (vpi(y1)=41)  => B=OK;
    1<=kappa<=40 (vpi(y1)<=40) => B=I.

This eliminates the ill-posed case kappa>=41 and reduces B to the valuation of
y1. But (A) is not proved for the actual Kondo basis, and JW/Kondo do not
determine vpi(y1): y1=p (B=OK) and y1=p+pi (B=I) are both compatible. Hence no
actual kappa=40/B=I or kappa=0/B=OK is proved; the exact obstruction is
(A)+valuation of y1.

No arbitrary coordinates were chosen; the two endpoint models are explicit
consistency models, not actual F(x_i). target_accepted=false.
