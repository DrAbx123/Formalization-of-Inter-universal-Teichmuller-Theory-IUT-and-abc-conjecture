# C9 archimedean normalization decision

Task: task-182. Date: 2026-10-25. Owner/executor: transport.
Stage: decisive natural-language normalization verification only.
No Lean/Project/target edits. Only this file written.

## 0. Decision

BINDING CONVENTION: B_I-zero.

The paper's global log-volume normalization is

    log-volume(B_I) = 0,

where B_I is the direct product of the unit balls in the archimedean tensor
packet. It is NOT the shell-pi normalization log-volume(I_v)=0.

Consequences for the F=Q contradiction route:

    h_inf(C) = log r_inf                         (F=Q, radial arch hull)
    r_inf <= pi  =>  h_inf <= log pi             (not h_inf <= 0)
    h_inf >= D    =>  r_inf >= p^{d_p}           (no pi factor)

The shell-pi formulas h_inf=log(r/pi), h_inf<=0, and r>=pi*p^{d_p} are a
different normalization and are NOT binding.

## 1. Paper citations

### 1.1 IUT IV: B_I and log-volume(B_I)=0

IUT IV, Proposition 1.5 (iii), pp. 15-16:

- B_I is defined as the integral structure "given by the direct product of
  the unit balls of the copies of C that occur in the direct sum decomposition
  of M_I".
- The tensor/direct-sum metrics and B_I are preserved by primitive
  automorphisms.

IUT IV, proof of Theorem 1.10, Step (vii), pp. 29-30, especially lines
1848-1859 of the local corpus:

    the container is pi^{j+1} B_I,
    the log-volume of B_I is equal to 0,
    hence the upper bound (j+1) log(pi).

The exact sentence is: "one is obliged to adopt normalizations which imply
that the log-volume of B_I is equal to 0". This is the global arithmetic-degree
normalization used in the proof of IV Thm1.10(vii). It is a B_I-zero
normalization, not a shell-pi normalization.

### 1.2 IUT IV: normalized weights

IUT IV, Remark 1.7.1, pp. 17-18:

- The computations in IV §1 are performed relative to the normalized
  log-volumes of Proposition 1.4(i).
- The weights of III Remark3.1.1(ii) must be replaced by
  [(F_mod)_v : Q_{vQ}]-normalized weights.
- For F_mod=Q, this collapses to the usual degree weight with total
  archimedean weight 1.

Thus the B_I-zero normalization is the one tied to the global IV weights,
not an ad hoc local convention.

### 1.3 AbsTopIII: unit ball zero, shell positive

AbsTopIII, Proposition 5.7(ii)(a), pp. 137-138:

    mu_k(O_k) = 1,       mu_k^log = log(mu_k),
    O_k = { |a| <= 1 }.

Therefore the unit ball has log-volume 0, and a radial ball of radius r has
radial log-volume

    mu_k^log(B(r)) = log r.

AbsTopIII, Proposition 5.8(vi), p. 141:

    mu^log(I(G)) = log(pi) * F(G)/(2 pi).

The archimedean log-shell I(G) has log-volume log(pi), not 0. Hence the shell
is NOT the zero reference. This directly rules out the shell-pi-zero
convention as a reading of the paper's normalization.

### 1.4 Relation of I_v and B_I

The two objects are different:

- I_v = { |a|_v <= pi } is the archimedean log-shell of radius pi
  (IUT III Remark1.2.2(ii)).
- B_I is the unit-ball integral structure of the tensor packet
  (IUT IV Prop1.5(iii)).

In AbsTopIII normalization, mu^log(O_k)=0 and mu^log(I_k)=log pi.
In IV global normalization, mu^log(B_I)=0 and
mu^log(pi^{j+1}B_I)=(j+1)log pi.

There is no paper statement setting mu^log(I_v)=0. The shell-pi convention
would require subtracting log pi from every archimedean readout; that is not
the paper's normalization.

## 2. Correct formulas under the binding convention

### 2.1 Local and global readout

For a radial archimedean ball B_v(r) in F_v:

    h_v^rad(B_v(r)) = log r.                                  (N1)

Do NOT use d_v log r locally together with alpha_v=d_v/[F:Q]; that
double-counts the local degree. The global readout is

    h_inf(C) = sum_{v|infty} alpha_v log r_v,
    alpha_v = d_v/[F:Q],  sum_v alpha_v = 1.                   (N2)

For F=Q, d_v=1 and alpha_inf=1:

    h_inf(C) = log r_inf.                                      (N3)

For nonradial hulls, the angular term must be retained:

    h_inf(C) = sum_v alpha_v [h_v^ang(A_v) + log r_v].          (N4)

### 2.2 Shell containment sign

If the actual archimedean hull lies in the shell, r_v<=pi, then

    h_inf(C) <= sum_v alpha_v log pi = log pi = 1.1447298858... (N5)

The old h_inf<=0 is WITHDRAWN. The shell has positive normalized log-volume
log pi.

Qualitative survivor: if the finite deficit satisfies

    D_C^Sp > log pi,

then shell containment still excludes archimedean compensation, because
h_inf<=log pi<D_C^Sp. For the uniform profiles this is true; stronger still,
the IV maximal-container bound is

    A_arc = ((l+5)/4) log pi = 11.5 log pi = 13.164394...     (N6)

and both b=3 and b=273 deficits exceed A_arc.

### 2.3 Compensation radius

For F=Q and one bad p,

    D_C^Sp = d_p log p,   h_inf=log r_inf.                    (N7)

Compensation h_inf>=D_C^Sp is therefore

    log r_inf >= d_p log p,
    r_inf >= exp(d_p log p) = p^{d_p}.                        (N8)

There is no pi factor. In the other (shell-pi) normalization one would get
pi*p^{d_p}; that is not the binding convention.

### 2.4 Product formula

Under the B_I-zero normalization,

    sum_v alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0,   (N9)
    h_inf >= - sum_p alpha_p v_p(x) log p.                     (N10)

No -log pi term appears. This is a point-modulus constraint, not a hull
volume lower bound.

### 2.5 Sign versus Lean

The paper's radial log-volume is positive for r>1. The Lean readout is

    absLogAddHom K u = -Real.log ||u||,
    archimedeanDelta r = -Real.log r.

Any comparison of a Lean value with the paper formula must flip sign or use
-archimedeanDelta. This warning is independent of the B_I/shell choice.

## 3. Corrected numeric thresholds

Uniform rho=1, e=41, p=12301, F=Q, one real place.

### 3.1 b=3

    d_3 = 408/41,
    D_3 = (408/41) log 12301 = 93.7149712746... natural,
    log10 D_3 = 40.6998948963...,
    r_inf >= 12301^{408/41} = 5.0106595585e40,
    log10 r_inf = 40.6998948963... .                           (R3)

The shell-pi value pi*12301^{408/41}=1.574145e41 (log10 41.1970) is
withdrawn as a binding threshold.

### 3.2 b=273, A=O_K branch

    d_273 = 38883/41,
    D_273 = (38883/41) log 12301 = 8931.17457860... natural,
    log10 D_273 = 3878.759836402...,
    r_inf >= 12301^{38883/41},  log10 r_inf = 3878.759836402... .  (R273)

The B=I branch value is 38463/41, giving radius 12301^{38463/41}
(log10 3836.862885...). Both are positive; the branch is not decided by this
normalization decision.

### 3.3 Withdrawn radii

- task-156 A18/A19 pi*exp(d_p): withdrawn (no log p and wrong normalization).
- task-162 D1/D2 pi*41^{d_p}: withdrawn (wrong base).
- task-167 and task-176 shell-pi radii pi*p^{d_p}: numerically correct for the
  shell-pi convention but not the binding B_I-zero convention. Under B_I-zero
  the pi factor is absent; the binding values are R3/R273 above.

## 4. Why the shell-pi confusion arose

The shell I_v has radius pi, and the IV container is pi^{j+1}B_I.
It is tempting to measure radii relative to pi and write log(r/pi), which
makes the shell boundary zero. But:

- IV explicitly normalizes B_I, the unit-ball packet, to zero;
- the container bound (j+1)log pi is then a positive upper bound, not a
  zero reference;
- AbsTopIII's archimedean log-volume of the log-shell is log pi, not 0.

The shell-pi formula is an internally consistent alternative normalization,
but it is not the paper's global normalization and it changes the sign of
shell containment and the pi factor in the radius. It must not be mixed with
B_I-zero formulas.

## 5. Binding statements for the contradiction route

Use exactly these:

1. Normalization: logvol(B_I)=0 (IUT IV proof Thm1.10(vii)).
2. F=Q radial: h_inf=log r_inf.
3. General: h_inf=sum_v alpha_v log r_v,
   alpha_v=d_v/[F:Q]; no local d_v factor.
4. Shell containment: r_v<=pi gives h_inf<=log pi, not 0.
5. Max container: h_inf<=A_arc=((l+5)/4)log pi=13.164394...
6. Compensation: h_inf>=D_C^Sp iff r_inf>=p^{d_p} (F=Q, one bad p).
7. Product formula: h_inf>=-sum alpha_p v_p(x)log p; no -log pi.
8. Sign: paper positive; Lean negative; flip when comparing.

The residual formula is unchanged in structure:

    Q_C - h_C <= D_C^Sp - h_inf(C).                            (B1)

With the binding convention substitute h_inf=log r_inf; under shell
containment the right side is at least D_C^Sp-log pi, and since
D_C^Sp>A_arc>=log pi, archimedean-only compensation is excluded for the
uniform b=3/b=273 profiles. This does not prove global closure: CFTH/TC and
the actual complete C remain open.

## 6. Status

This decision is based on:

- IUT IV Prop1.5(iii), pp.15-16 (definition of B_I);
- IUT IV proof of Thm1.10, Step(vii), pp.29-30 (log-volume(B_I)=0;
  container pi^{j+1}B_I; bound (j+1)log pi);
- IUT IV Remark1.7.1, pp.17-18 (normalized weights);
- AbsTopIII Prop5.7(ii)(a), pp.137-138 (unit ball normalization, log r);
- AbsTopIII Prop5.8(vi), p.141 (log-shell log-volume log pi).

Binding convention: B_I-zero.

No new attack, no Lean/Project edits, no target acceptance.
target_accepted=false.
