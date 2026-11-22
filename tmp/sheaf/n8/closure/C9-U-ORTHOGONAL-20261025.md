# C9 U = W^perp and the 1 in U condition

Task: task-224. Owner: kummer. Date: 2026-10-25.
Stage: SHEAF stage1 natural-language/local mathematics only.
No Lean/Project edits, no new attack, no target changes. Only this file written.
target_accepted=false; P6 open.

## 0. Inputs

- Kondo 2025 local snapshot,
  sources/Kondo-2512.09231v1.html,
  SHA256 ff39006cf92ec22e1a39caa89fee9b86080953861d7ac6405e6919338c5c9e6f;
  Theorem D, Theorem E/1.3.
- Kondo 2026 local snapshot,
  sources/Kondo-2605.25428v2.html,
  SHA256 fe7c464e2ae09ffc85c4b02cad8b10b7eebef351113975a34c53a62169a27d86;
  Theorem 1.2 text, Lemma 1.6, Definition 3.2, Lemma 3.3.
- C9-Y1-TRACE-20261025.md (E35),
  SHA256 a33ebdb8d0d0551b1391cf3069c71b8cf3255d8b56f20f96513c7f33e22f425c.
- C9-AUDIT-NL-UNDERDETERMINATION-20261025.md (E38 audit),
  SHA256 bf9c2d8ff14315162dfc9ff96e520edb7f9245797f7f891e4ecf0feaedbb5d99.

Binding: Kondo y_i=F(x_i) is a Q_p-basis; W=ker Tr=<y2,...,yd>;
U=<y1>; y_i in J=m; full Out does not preserve the principal filtration
(task-209 P false). Overbar means trace pairing in this file.

## 1. Verdict

Two separate statements must be distinguished.

1. **For the natural trace pairing** beta(x,y)=Tr_{K/Q_p}(xy), one can prove
   exactly

       W^perp = Q_p 1,   W=ker Tr.                              (1.1)

   Hence, since U=Q_p y1,

       U = W^perp  <=>  y1 in Q_p 1  <=>  1 in U.              (1.2)

2. **Kondo reconstruction does not prove (1.2).** The Kondo data supply the
   Q_p-basis y_i, the trace-kernel identity W=ker Tr, and the Sp embedding
   diag(1,A); they do not supply the trace pairing, the value Tr(y1), or the
   line U relative to 1. The actual y1 is not determined by the frozen source
   (E35). The task-217 structural models include y1=p with U=Q_p1 (so
   U=W^perp) and y1=p+pi with U!=Q_p1 (so U!=W^perp). Thus U=W^perp is not a
   consequence of Kondo; it is an additional condition equivalent to 1 in U.

3. **If 1 in U**, then the conditional theorem is valid:

       1 in U  =>  w0=0  =>  a(alpha)=1 for all alpha
              =>  alpha_+(O_K)=O_K  =>  H_A-full true and B=O_K.   (1.3)

   No arbitrary coordinates are used in this implication; it is exactly the
   w0=0 case of the coordinate formulas.

## 2. Trace pairing computation

Let K/Q_p be finite, Tr=Tr_{K/Q_p}, and beta(x,y)=Tr(xy). The trace pairing is
nondegenerate (K/Q_p is separable). Fix the C9 type K=Q_p(pi), e=41, p=12301,
O_K=Z_p[pi], pi^e=p u, m=(pi), J=m.

From the trace table,

    Tr(1)=41,  Tr(pi^a)=0 (1<=a<=40),
    W=ker Tr=Q_p-span(pi,...,pi^40).                           (2.1)

For every w in W, beta(1,w)=Tr(1*w)=Tr(w)=0; hence 1 in W^perp. Since beta is
nondegenerate and dim W=40, dim W^perp=1, so

    W^perp = Q_p 1.                                             (2.2)

This is an exact computation, independent of Kondo's y-basis. It uses only the
trace table and nondegeneracy. In particular:

- W^perp does not depend on y1 or F(x1);
- W^perp is the line of 1, not the line U in general;
- U=W^perp iff y1 is a nonzero Q_p-multiple of 1 (equivalently 1 in U).

Note that y1 in J does not exclude y1 in Q_p 1: y1=p is in J and spans Q_p1.
Thus the trace computation alone neither proves nor disproves U=W^perp for the
actual Kondo y1.

## 3. What Kondo actually states

Kondo 2025 Theorem D gives the JW generators and relations; Theorem E/1.3 gives

    W=ker Tr=<y2,...,y_d>,   Tr(y1)!=0,                         (3.1)

in the tame totally ramified case. This is a statement about the kernel of the
trace **functional**, not about the trace pairing and not about W^perp.

Kondo 2026 Lemma 1.6 gives Phi:Out(G_K)->GL_d(Q_p) continuous closed; Definition
3.2/Lemma 3.3 give the U/W y-basis with U=<y1> and Sp_{2g} acting as diag(1,A)
on W. Neither paper states:

- that U is the orthogonal complement of W for the trace pairing;
- that y1 lies in Q_p 1;
- that 1 lies in U;
- a value for Tr(y1).

The reconstruction is Q_p-linear and basis/trace-kernel structural; it does not
provide the trace pairing x,y->Tr(xy), which uses multiplication and is not part
of the Q_p-linear reconstruction. Therefore Kondo does not imply U=W^perp.

## 4. Conditional theorem: 1 in U implies H_A-full/B=O_K

Assume U=W^perp, equivalently 1 in U (Section 2). Since K=U direct-sum W and
1=u0+w0 with u0 in U, w0 in W, we have w0=0 and u0=1. With u0=c y1,
c=1/Tr(y1) is determined by y1, but we do not need its value:

    a(alpha)=alpha_+(1)=u0+A w0=1 for every A in Sp_40(Z_p).    (4.1)

Then

    alpha_+(O_K)=alpha_+(Z_p 1+J)=Z_p 1+J=O_K                  (4.2)

for every alpha in H. Hence H_A-full holds for H, and

    B=closed Z_p-span union_alpha alpha_+(O_K)=O_K.             (4.3)

This proves the implication

    1 in U  =>  H_A-full_H true and B_H=O_K.                    (4.4)

It is conditional on the assumption U=W^perp/1 in U; it does not prove that
assumption from Kondo. The identity element is included in H and gives
O_K, consistent with B=O_K.

## 5. What happens without 1 in U

If 1 notin U, then w0=1-u0 is nonzero. The coordinate formulas give

    1=u0+w0,  u0=c y1,  c=41/Tr(y1),  w0=1-c y1,
    a(alpha)=u0+A w0,                                            (5.1)

and H_A-full requires u0+A w0 in O_K minus J for all A. No source value of y1,
Tr(y1), w0, or C is available (E35/E37); the task-217 models include:

- y1=p: U=Q_p1=W^perp, w0=0, H_A true, B=O_K;
- y1=2p: U=Q_p1=W^perp, w0=0, H_A true, B=O_K, different c;
- y1=p+pi: U!=Q_p1=W^perp, w0=-pi/p, A=-I gives a=1+2pi/p notin O_K,
  H_A false, B not O_K (and B=I in the R6 model).

Thus the source data alone do not decide whether 1 in U; they admit both
U=W^perp and U!=W^perp. The implication (4.4) is valid, but its premise is not
source-determined.

## 6. Exact source obstruction

- W^perp=Q_p1 is proved from the trace pairing and the trace table.
- U=W^perp is equivalent to 1 in U and is NOT proved by Kondo; it is an extra
  condition on y1.
- Kondo does not provide the trace pairing, Tr(y1), or y1's line; E35 source
  obstruction applies.
- If 1 in U is supplied, H_A-full_H and B_H=O_K follow exactly (no arbitrary
  coordinates).
- Without it, H_A-full/B remains underdetermined; task-217 models show both
  outcomes. No unconditional B=O_K/B=I.

This is a conditional theorem plus a precise source obstruction, not a proof
that U=W^perp or H_A-full.

## 7. Classification

| item | status |
|---|---|
| beta(x,y)=Tr(xy) nondegenerate | ACTUAL |
| W=ker Tr=Q_p-span(pi,...,pi^40) | ACTUAL local algebra |
| W^perp=Q_p1 | PROVED |
| U=W^perp iff 1 in U | PROVED |
| Kondo implies U=W^perp | FALSE/NOT STATED |
| Kondo gives trace pairing/Tr(y1) | FALSE; only kernel functional |
| 1 in U => w0=0, a=1 | PROVED conditional |
| 1 in U => H_A-full_H/B=O_K | PROVED conditional |
| premise 1 in U source-determined | NO; E35 underdetermination |
| H_A-full/B unconditional | NOT PROVED |
| task-217 models both U=W^perp and U!=W^perp | CONSISTENT |

## 8. Conclusion

The trace pairing calculation proves exactly W^perp=Q_p1, hence
U=W^perp iff 1 in U. Kondo's reconstruction only gives the trace-kernel
functional W=ker Tr and the U/W basis/Sp action; it does not give the trace
pairing, Tr(y1), or the line U relative to 1. Therefore Kondo does not prove
U=W^perp. If 1 in U is added, then w0=0, a(alpha)=1, H_A-full holds and
B=O_K; this conditional theorem is valid. Without that extra input, the
underdetermination remains and no unconditional branch conclusion follows.

No Lean/kernel closure; P6 open; target_accepted=false.

## 9. Status

- Natural-language/local algebra only; no Lean/Project edits.
- U=W^perp proved equivalent to 1 in U; Kondo source obstruction recorded.
- Conditional 1 in U => H_A/B=O_K proved; no arbitrary assumption.
