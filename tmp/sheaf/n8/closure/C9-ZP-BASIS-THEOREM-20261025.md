# C9 Z_p-basis theorem for y_i=F(x_i) and the kappa invariant

Task: task-255. Date: 2026-10-25. Author: transport.
Stage: new source theorem attempt. No Lean/Project/target edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-NEW-BI-SOURCE-20261025.md | 234 | A90CC1B516A9AFC784A20A8CE2FAFB6CF16752459D73562D36C3093B85B294B3 |
| C9-AUDIT-UNIT-FILTRATION-20261025.md | 318 | 8D715581577F057C151CC7023B98F5A896A04121EFC32D13B6EBAEF21C563E09 |
| Kondo 2026 snapshot | 1606 | FE7C464E2AE09FFC85C4B02CAD8B10B7EEBEF351113975A34C53A62169A27D86 |
| Kondo 2025 snapshot | 2222 | FF39006CF92EC22E1A39CAA89FEE9B86080953861D7AC6405E6919338C5C9E6F |

## 1. Verdict

The hypothesis of the task is FALSE as stated, and it does not yield B=I.

Main conclusions:

1. Local reciprocity does NOT map the pro-p wild inertia group P_K
   isomorphically onto U^1=1+m. P_K is a nonabelian pro-p group; U^1 is an
   abelian pro-p group of Z_p-rank e=41. The reciprocity map K^times->G_K^ab
   identifies O_K^times with the inertia subgroup of G_K^ab; the image of P_K
   is the pro-p part U^1, with kernel the closure of [P_K,P_K], not an
   isomorphism P_K -> U^1.

2. Kondo's y_i=F(x_i) are proved to be a Q_p-basis of K, not a Z_p-basis of
   J=m. No cited theorem gives integral generation.

3. Even IF y_i were a Z_p-basis of J, it is impossible that every y_i has
   v_pi(y_i)=1. J/pi J has F_p-dimension 1, while a Z_p-basis has 41
   elements; at most one basis element can reduce nonzero modulo pi J. The
   other 40 have v_pi>=2. Explicit Z_p-bases realize both kappa=0 and
   kappa=40.

4. The task's numerical conclusion holds only in the special case
   v_pi(y1)=1 and v_p(Tr(y1))=1: then kappa=41*1-1=40, and by the task-250
   theorem B=I. If v_p(Tr(y1))>=2, then kappa>=81, which is outside the B=I
   range 1<=kappa<=40; the branch is not well-posed in I, not B=I.

5. The actual value of v_pi(y1) and v_p(Tr(y1)), hence kappa, is not
   computed by Kondo/local reciprocity. The route gives an exact conditional
   criterion, not an actual B=I.

## 2. Local reciprocity and wild inertia

Let K/Q_p be finite, e=e(K/Q_p), f=f(K/Q_p), O_K, m=(pi), U^1=1+m.
The inertia group sits in

    1 -> P_K -> I_K -> I_K/P_K -> 1,

with P_K the wild inertia (pro-p) and I_K/P_K tame cyclic of order prime to p.

Local class field theory gives the reciprocity isomorphism

    rec_K: K^times -> G_K^ab,

and identifies

    rec_K(O_K^times) = I_K^ab (the inertia subgroup of G_K^ab).

The image of U^1 under rec_K is the pro-p part of inertia. The wild inertia
P_K is a pro-p **nonabelian** group; its image in G_K^ab is the maximal abelian
pro-p quotient U^1. The kernel is the closure of [P_K,P_K]. Therefore the
natural map is

    P_K / closure([P_K,P_K])  ->  U^1,

not an isomorphism P_K -> U^1.

Rank check: U^1 is a Z_p-module of rank e (log(U^1)=m has Z_p-rank e).
P_K is not a free abelian pro-p group and has no Z_p-rank e in the sense of
U^1; a nonabelian pro-p group cannot be isomorphic to an abelian one.

Consequently the task's first premise

    "local reciprocity maps wild inertia P_K isomorphically onto U^1"

is FALSE. What is true is only:

    rec_K(U^1) = pro-p part of I_K^ab,
    log(U^1) = m  (Z_p-rank e),                                  (2.1)

for the tame low-ramification case where log is defined on U^1.

This already breaks the proposed rank count: Kondo's d=41 y-vectors and the
Z_p-rank e=41 of J match numerically, but there is no group isomorphism from
P_K to U^1 and no theorem that the y-vectors form a basis of J.

## 3. Kondo's y_i are only a Q_p-basis

Kondo 2026 Lemma 1.3 states that y_1,...,y_d (d=41) is a Q_p-basis of
k_+(G_K)=K, with y_i in J=m and W=kerTr=<y2,...,yd>. It does NOT state:

- that y_i form a Z_p-basis of J;
- that the change-of-basis matrix from y_i to a Z_p-basis of O_K has
  determinant in Z_p^times;
- that every y_i has v_pi(y_i)=1;
- any relation between the JW generators x_i and a Z_p-basis of wild inertia.

The JW presentation has symbols x_0,...,x_d (d+1=42 symbols for d=41) plus
sigma,tau; the F-basis y_1,...,y_d has d=41 elements. The x_0 generator is an
extra rational/cyclotomic direction; it does not add a 42nd vector to the
F-basis. Any rank/truncation argument must account for this index shift. It
does not produce a Z_p-basis of J.

Wild inertia has a totally different group structure; the F map goes through
P(G)->O^times(G)->k_+(G), and its image is not a basis of U^1 or J by any
cited theorem.

## 4. Why "all v_pi(y_i)=1" is impossible for a Z_p-basis

Lemma 4.1. Let J=pi O_K, so pi J=pi^2 O_K and

    J/pi J = pi O_K/pi^2 O_K ~= O_K/pi O_K ~= F_p,               (4.1)

a one-dimensional F_p-vector space.

If y_1,...,y_41 is a Z_p-basis of J, then their reductions mod pi J are 41
vectors in a one-dimensional F_p-space. At most one reduction is nonzero.
Therefore at most one y_i has v_pi(y_i)=1; the other 40 have
v_pi(y_i)>=2.

Corollary 4.2. The hypothesis "y_i is a Z_p-basis of J, hence every y_i has
v_pi=1" is internally contradictory. Even granting a Z_p-basis, one cannot
conclude v_pi(y_i)=1 for all i.

Concrete Z_p-bases:

    B_A=(p,pi,...,pi^40):       v_pi=(41,1,2,...,40),
    B_B=(p+pi,pi,...,pi^40):    v_pi=(1,1,2,...,40).            (4.2)

Both are Z_p-bases of J; B_A has kappa=0 (y1=p, Tr=41p), B_B has kappa=40
(y1=p+pi, Tr=41p). B_A gives B=O_K; B_B gives B=I by the task-250 theorem.
This is an explicit disproof of any implication
"Z_p-basis => all v_pi=1 => kappa=40".

## 5. The correct conditional computation of kappa

Recall from task-250:

    kappa=e v_p(Tr(y1)) - v_pi(y1),  e=41.                      (5.1)

Under the special assumptions

    v_pi(y1)=1,  v_p(Tr(y1))=1,                                 (5.2)

we get

    kappa=41*1-1=40,                                           (5.3)

which lies in the B=I range 1<=kappa<=40. The task-250 theorem then gives
B=I.

But if v_p(Tr(y1))>=2 while v_pi(y1)=1, then

    kappa>=82-1=81,                                             (5.4)

which is outside the B=I range; the branch is not well-posed inside I and
B=I is not obtained. If v_pi(y1)>=2, kappa can be much smaller or larger
depending on Tr; no fixed conclusion.

Thus the route only yields a conditional:

    v_pi(y1)=1 and v_p(Tr(y1))=1  => kappa=40 => B=I.          (5.5)

Neither hypothesis is proved by Kondo/local reciprocity. The actual y1 is a
log of a unit; its pi-adic valuation is not fixed by the structural theorems.

## 6. Kondo F and the wild-inertia route: exact obstruction

The proposed route uses the following chain:

    P_K ~= U^1  =>  F(x_i) basis of J  =>  v_pi(y_i)=1
                =>  kappa=40  =>  B=I.                          (6.1)

Each arrow is unsupported or false:

1. P_K ~= U^1: FALSE (P_K nonabelian vs U^1 abelian; reciprocity kernel is
   [P_K,P_K]).
2. F(x_i) Z_p-basis of J: NOT PROVED; Kondo gives Q_p-basis only.
3. Z_p-basis => all v_pi(y_i)=1: FALSE by J/piJ dimension (Lemma 4.1).
4. v_pi(y1)=1 => v_p(Tr(y1))=1: NOT PROVED; Tr(y1) in pZ_p only says
   valuation >=1, not exactly1.
5. kappa=40 => B=I: TRUE conditionally, by task-250, but only if (5.2).

Therefore the proposed source theorem is not valid. A valid theorem is the
conditional (5.5), not an unconditional B=I.

The exact missing source input remains:

    the actual y1=log(F(x1)) and Tr(y1), or equivalently kappa.

No computation of these values from Kondo/Theil generators exists in the
frozen corpus.

## 7. Could a different Z_p-basis argument work?

If one had a theorem that y_i is a Z_p-basis of J, Lemma 4.1 would still
prevent all v_pi(y_i)=1. One would need the specific y1 valuation and
Tr(y1) valuation. The only way to force kappa=40 is:

    v_pi(y1)=1 and v_p(Tr(y1))=1.

Even a theorem that the change-of-basis matrix C is in GL_41(Z_p) would not
give these. The F-basis values are not determined by integrality; the
underdetermination models B_A and B_B both have GL_41(Z_p) change-of-basis
and opposite B outcomes.

## 8. Proven / conditional / impossible

PROVED in this note:

- reciprocity does not identify P_K with U^1; the kernel is [P_K,P_K];
- Kondo only gives a Q_p-basis, not a Z_p-basis of J;
- a Z_p-basis of J cannot have all v_pi=1 (J/piJ is one-dimensional);
- explicit Z_p-bases B_A (kappa=0, B=O_K) and B_B (kappa=40, B=I);
- conditional implication (5.2) => kappa=40 => B=I;
- if v_p(Tr y1)>=2, kappa>=81, no B=I.

CONDITIONAL / MISSING:

- actual y1 and Tr(y1), hence kappa;
- actual Z_p-basis property (not available);
- actual F(x_i) values;
- target/TC, actual arch h_inf, complete C.

IMPOSSIBLE AS STATED:

- P_K ~= U^1 (nonabelian vs abelian);
- "Z_p-basis => all v_pi=1";
- unconditional B=I from this data.

## 9. Conclusion

The proposed wild-inertia/Z_p-basis theorem does not go through:

    P_K is not isomorphic to U^1;
    y_i=F(x_i) is only a Q_p-basis in the cited Kondo theorem;
    even a Z_p-basis of J cannot have all v_pi(y_i)=1.

The correct conditional statement is:

    v_pi(y1)=1 and v_p(Tr(y1))=1  =>  kappa=40  =>  B=I,

under the task-250 kappa theorem. If v_p(Tr(y1))>=2, kappa>=81 and B=I is
not obtained. The actual kappa remains missing, so no actual B=I and no
P6 counterexample follows.

No arbitrary coordinates or data were chosen. target_accepted=false.
