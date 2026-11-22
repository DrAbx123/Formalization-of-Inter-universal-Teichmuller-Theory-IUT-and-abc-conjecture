# C9 new source theorem: B=I from non-filtration and integrality

Task: task-250. Date: 2026-10-25. Author: transport.
Stage: new-math theorem/construction attempt from the recorded source data.
No Lean/Project/target edits. Only this file written. target_accepted=false.

## 0. Inputs and scope

| file | lines | SHA256 |
|---|---:|---|
| C9-NEW-BI-COUNTEREXAMPLE-20261025.md | 272 | 730A282EF8A55EE1FFBC2C97835BE91D59B52CEFE836BA7E778347B29EB39039 |
| C9-AUDIT-UNIT-FILTRATION-20261025.md | 318 | 8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09 |
| C9-Y1-TRACE-20261025.md | 179 | A33EBDB8D0D0551B1391CF3069C71B8CF3255D8B56F20F96513C7F33E22F425C |
| C9-NL-UNDERDETERMINATION-20261025.md | 301 | AAFE2BC84D93DEBACF06298B38D7B20694B6A04A0ADBF262DDB87D366E4D0582 |

Goal: try to force B=I from an actual non-filtration alpha in H\Aut(K) plus
the integrality of a(alpha). The result below is a genuine conditional source
theorem, but it does NOT force B=I from non-filtration alone. The branch is
reduced to an explicit valuation invariant kappa of the actual y1/Tr(y1).
Non-filtration does not determine kappa; no current source computes it.

## 1. Data and elementary identities

Let p=12301, e=41, K=Q_p(pi), pi^e=p u, O_K=Z_p[pi], J=m=pi O_K,
I=p^{-1}J, W=ker Tr. The Kondo y-basis satisfies

    K=U direct-sum W, U=<y1>, W=kerTr,
    y_i in J, Tr(y1) in pZ_p nonzero,
    1=u0+w0, u0=c y1, c=41/Tr(y1), w0=1-u0.                   (1.1)

For alpha in H acting by diag(1,A) on the y-basis,

    a(alpha)=alpha_+(1)=u0+A w0=1+(A-1)w0.                     (1.2)

H_A-lite gives alpha_+(J)=J and alpha_+(I)=I; a(alpha) in I.

Define the p-adic valuations

    vpi = v_pi (v_pi(pi)=1),  vp = v_p (v_p(p)=1),  vpi(p)=e=41. (1.3)

Then

    vpi(Tr(y1)) = e vp(Tr(y1)),
    vpi(c) = -e vp(Tr(y1))   (41 is a p-adic unit).             (1.4)

Define the integrality invariant

    kappa := e vp(Tr(y1)) - vpi(y1).                           (1.5)

Since Tr(y1) in pZ_p and y1 in J, kappa is an integer. It measures the
pi-adic depth of the U-coordinate of 1.

## 2. The exact integrality dichotomy

Lemma 2.1 (location of u0,w0 in terms of kappa). With u0=c y1 and
w0=1-u0:

    kappa <= 0         <=>  u0 in O_K  <=>  w0 in J;
    1 <= kappa <= e-1  <=>  u0 in I minus O_K  <=>  w0 in I minus J;
    kappa >= e=41      <=>  u0 not in I  <=>  w0 not in I.     (2.1)

Proof. vpi(u0)=vpi(y1)-e vp(Tr(y1))=-kappa.

- u0 in O_K iff vpi(u0)>=0 iff kappa<=0. Since w0=1-u0 and
  O_K cap W=J cap W, w0 in J in that case.
- u0 in I=pi^{1-e}O_K iff vpi(u0)>=1-e iff -kappa>=1-e iff
  kappa<=e-1=40. If 1<=kappa<=40, u0 in I but not O_K; since 1 in O_K,
  w0=1-u0 is in I but not O_K, hence in I minus J (because w0 in W).
- If kappa>=41, vpi(u0)<=-41, so u0 not in I; then w0=1-u0 not in I
  (otherwise u0=1-w0 would be in I). QED.

## 3. Genuine source theorem: kappa decides B

Theorem 3.1 (kappa-B dichotomy). For the actual data:

(a) If kappa<=0, then H_A-full holds and B=O_K.
(b) If 1<=kappa<=40, then B=I. The actual alpha with A=-I has
    a(alpha_{-I})=u0-w0=1-2w0 not in O_K, and the H-orbit of the classes
    of a(alpha_A) spans I/J; hence B=I.
(c) If kappa>=41, every alpha_+(O_K)=Z_p a(alpha)+J is not contained in I;
    the branch B is not well-posed inside I, and B=I is not obtained.

Proof.

(a) kappa<=0 gives u0 in O_K and w0 in J (Lemma 2.1). For every A,
    a(alpha)=u0+A w0; since A preserves J, A w0 in J, so a in O_K minus J
    (u0 has nonzero class 1 mod J because w0 in J). Thus
    alpha_+(O_K)=Z_p a+J=O_K for all A; H_A-full and B=O_K.

(b) Suppose 1<=kappa<=40. Then w0 in I minus J. Take A=-I in Sp_40(Z_p),
    an actual element of H. Then
        a(alpha_{-I})=u0-w0=1-2w0.
    If this were in O_K, then 2w0=1-a in O_K; since 2 is a p-adic unit,
    w0 in O_K cap W=J, contradiction. Hence a(alpha_{-I}) not in O_K.

    For the orbit: for every A,
        a(alpha_A)=1+(A-1)w0 in I,
    because 1 and w0 are in I and A preserves I (H_A-lite). Hence
    B subset I.

    Modulo J, the class of w0 is a nonzero element of the 40-dimensional
    Wbar. The standard Sp_40(F_p) representation is irreducible, so the
    orbit {A w0 mod J} spans Wbar. Therefore the differences
    (A-1)w0 mod J also span Wbar (since w0 itself lies in the span of its
    orbit). The class of 1 supplies the l-direction. Thus B/J is all of
    I/J. Since J subset B and B subset I, B=I.

(c) If kappa>=41, w0 not in I. For every A, a(alpha)=1+(A-1)w0 need not
    lie in I; alpha_+(O_K) is not contained in I. The definition of B as a
    closed Z_p-span inside I is not well-posed for such alpha; in particular
    B=I is not obtained from the source branch definition. QED.

This is the exact source theorem the data support: the branch is controlled
by the single integer kappa. No arbitrary alpha is chosen; the explicit
A=-I is an actual element of Sp_40(Z_p), hence of H.

## 4. Non-filtration alone does not decide kappa or B

Theorem 4.1 (non-filtration is insufficient). The existence of an actual
alpha in H\Aut(K) and the fact that it fails the upper unit filtration do not
force kappa into the B=I range 1<=kappa<=40.

Proof/argument. Non-filtration is a property of the unit action
alpha^times. The invariant kappa is determined by y1 and Tr(y1), hence by the
coordinate u0 of 1. The recorded H_A-lite data couple the additive action
alpha_+ to the unit action only through the log compatibility
alpha_+ log = log alpha^times; this compatibility does not determine the
U-coordinate of 1. Two admissible structural models illustrate the point:

- Model A: y1=p,..., gives kappa=0, H_A-full and B=O_K. One can still choose
  A in Sp_40(Z_p) which does not preserve the higher pi-adic filtration on J;
  the induced alpha^times=exp o alpha_+ o log then moves some U^n, so it is
  non-filtration, while a(alpha)=1 remains integral and B=O_K.
- Model B: y1=p+pi,..., gives kappa=40, B=I, and the same non-filtration
  phenomenon occurs at other unit levels.

Both models satisfy the recorded structural axioms. Therefore non-filtration
plus structural integrality does not force B=I; it does not even decide kappa.
A genuine source theorem of the requested form would need an additional
computation of y1/Tr(y1), not merely another non-filtration theorem.

Remark 4.2. The actual H is infinite and contains non-field-theoretic
elements (Kondo 2025 Theorem A), but the theorem above does not convert this
into kappa>0. The missing object is the actual y1=log(F(x1)) and its trace.

## 5. Trace pairing and the non-alternating obstruction

The trace pairing beta(x,y)=Tr(xy) identifies

    O_K^vee = I = pi^{-40}O_K,   J^vee = p^{-1}I.              (5.1)

This is the canonical integral structure, but it does **not** force O_K
preservation: H_A-lite gives alpha_+(I)=I, and I is the dual of O_K; a
Q_p-linear map preserving I need not preserve O_K unless it also preserves
the trace pairing. The cited source does not prove that every alpha_+ is a
beta-isometry.

The trace functional gives

    Tr(a(alpha))=Tr(1)=e=41                                     (5.2)

for every A, because A w0 in W has trace 0. Hence the single trace value does
not distinguish kappa or B. Higher beta-pairings with I would be needed to
test O_K-membership; they are not computed by the source.

The symplectic form preserved by the Kondo Sp_40 action is alternating, while
the trace pairing is symmetric. There is no source theorem identifying the two
forms or forcing the trace-dual lattice to be stable under H. Thus the
non-alternating/trace-dual idea does not produce a new integrality invariant
beyond kappa.

## 6. What is proved, conditional, missing

PROVED (source-conditional theorem):

- kappa=e vp(Tr(y1))-vpi(y1) is an integer invariant of the actual data.
- kappa<=0 => H_A-full/B=O_K.
- 1<=kappa<=40 => B=I (using actual A=-I and the Sp-orbit).
- kappa>=41 => branch not well-posed in I; B=I not obtained.
- Non-filtration alone does not determine kappa/B.

CONDITIONAL:

- Identification of the actual y1=log(F(x1)), Tr(y1), kappa for the E_j/Kondo
  source;
- actual unit action/filtration failure at higher U^n;
- target/TC and complete C.

MISSING/IMPOSSIBLE FROM CURRENT SOURCE:

- actual kappa computation from F(x_i) / trace data;
- a theorem forcing kappa>0 from non-filtration;
- a theorem excluding kappa>=41 for the actual source;
- actual B=I realization and actual arch h_inf.

## 7. Application to the b=3 corridor

If actual kappa lies in [1,40], B=I and the b=3 corridor is

    S3=(12/41)log12301=2.7563226845469613...,
    F=Q_C-h_C=-S3-h_inf,
    F<0 iff h_inf>-S3.                                        (7.1)

But actual h_inf is not constructed; task-232 gives only the upper bound
A_proc=11.5log pi=13.1643936873 and no lower bound. Therefore even in the
kappa-range that would give B=I, the sign of F is undecided. At the formal
container top h_inf=A_proc, F=-15.9207163718, but A_proc is not attained.

If kappa<=0, B=O_K and the b=3 profile is positive under the IV upper bound:
F>=D3-A_proc=80.550577...>0. If kappa>=41, no B=I branch is defined.

Thus:

    kappa [1,40] + actual h_inf > -S3 + actual complete C
    would give a genuine P6 counterexample;

none of these is available.

## 8. Conclusion

The genuine source theorem is the kappa-dichotomy:

    kappa<=0: H_A-full, B=O_K;
    1<=kappa<=40: B=I (actual A=-I nonintegral; Sp-orbit spans I/J);
    kappa>=41: B not well-posed inside I.

Non-filtration alpha exist and are actual, but they do NOT determine kappa and
do not force B=I. The exact missing input is the actual y1=log(F(x1)) and
Tr(y1), equivalently kappa; no source theorem computes it. The b=3 negative
corridor remains conditional on kappa in [1,40] and on an actual h_inf>-S3.
No genuine P6 counterexample and no proof of B=O_K for the actual source is
obtained.

target_accepted=false.
