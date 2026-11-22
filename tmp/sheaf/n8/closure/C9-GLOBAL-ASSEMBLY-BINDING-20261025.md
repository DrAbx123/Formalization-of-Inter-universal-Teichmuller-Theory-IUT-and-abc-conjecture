# C9 binding global assembly v3 (B_I-zero normalization)

Task: task-185. Date: 2026-10-25. Owner/executor: transport.
Stage: stage1 natural-language binding assembly only. No Lean/Project edits.
Only this file written. target_accepted=false.

## 0. Inputs

| file | lines | SHA256 |
|---|---:|---|
| C9-NORMALIZATION-DECISION-20261025.md (binding decision) | 267 | 5E969DFBFB3E08B2C2CA5A7859683F914FEB3236486B51691FD4D77BE774C78D |
| C9-GLOBAL-ASSEMBLY-CORRECTED2-20261025.md (v2) | 310 | 83D33415F6A046E49E4C1A734095AE502A3DC94562A563AF506EA640EBB5D781 |
| C9-ARCH-NORMALIZATION-CORRECTION-20261025.md | 253 | 2174C3EE75FB9DFB83D1BC3E8EF43587F6FBF6D0A1D33538EECC6E0160C769F8 |
| C9-AUDIT-ARCH-BOUND-20261025.md | 182 | 1442822A1F43FE653687BD45BD0527E99A4A6DEB14A810ABFEFA8736DDD7C50B |

Prior binding corrections remain in force:

- task-147: corrected donor H=Phi^{-1}(Sp); rho not a homomorphism; no
  boundary-word source; basis alignment inferred.
- task-149: full Ind1 is the procession automorphism group; TAME (11)-(14)
  are not a target proof; TC-A..TC-H plus TC-S required.
- task-160: B_H=O_K only for the subgroup H under natural alignment; full
  barGamma branch undetermined.
- task-170: log converges on all U^1; exp threshold strict; J=m restricted;
  volume keeps f.
- task-182: binding archimedean normalization is B_I-zero.

## 1. Binding normalization

The binding convention is B_I-zero:

    log-volume(B_I)=0,

where B_I is the direct product of unit balls in the archimedean tensor packet
(IUT IV Prop1.5(iii), pp.15-16; proof of Thm1.10 Step(vii), pp.29-30, lines
1848-1859). The shell I_v={|a|<=pi} is not the zero reference; AbsTopIII
Prop5.8(vi), p.141 gives log-volume(I_v)=log pi.

The shell-pi convention (normalize I_v to zero) is a different normalization
and is not used below. The formulas h_inf=log(r/pi), h_inf<=0 on shell
containment, and radii pi*p^{d_p} are WITHDRAWN as non-binding.

## 2. Archimedean readout

For a radial archimedean ball B_v(r) in F_v, under B_I-zero:

    h_v^rad(B_v(r)) = log r.                                  (A1)

Do not multiply the local readout by d_v and by alpha_v=d_v/[F:Q] at the same
time. The global readout is

    h_inf(C) = sum_{v|infty} alpha_v log r_v,
    alpha_v = d_v/[F:Q],  sum_v alpha_v = 1.                  (A2)

For F=Q, d_v=1 and alpha_inf=1:

    h_inf(C) = log r_inf.                                     (A3)

For a nonradial hull, the angular term must be retained:

    h_inf(C) = sum_v alpha_v [h_v^ang(A_v) + log r_v].         (A4)

No actual complete-C hull/radius is constructed; r_v remains open.

## 3. Shell containment and maximal container

If the actual hull lies in the source shell, r_v<=pi for all v, then

    h_inf(C) <= sum_v alpha_v log pi = log pi
             = 1.1447298858...                                 (A5)

The old h_inf<=0 is withdrawn: under B_I-zero the shell has positive
log-volume log pi.

The IV maximal-container bound is independent of the local radial formula:

    the source container is pi^{j+1}B_I,
    log-volume(B_I)=0,
    log-volume(pi^{j+1}B_I)=(j+1)log pi.                      (A6)

Averaging j=1,...,m=(l-1)/2 gives

    h_inf(C) <= A_arc = ((l+5)/4) log pi
                     = 11.5 log pi = 13.164394...            (A7)

for l=41.

A7 is a paper-level container bound (conditional on the actual possible-image
hull lying in the IV container); it does not require the shell containment
r_v<=pi. Shell containment only gives the weaker A5.

For the uniform conditional profiles:

    b=3:   D_C^Sp = (408/41) log 12301 = 93.714971... > A_arc
    b=273: D_C^Sp = (38883/41) log 12301 = 8931.174579... > A_arc.

Thus archimedean-only compensation is excluded for these conditional profiles,
even without r_v<=pi. This is not a global closure.

## 4. Conditional residual and CFTH

CFTH is the conjunction:

- corrected donor H=Phi^{-1}(Sp), mapping-class/Dehn-twist source, inferred
  natural basis alignment, trace target, low-ramification input, standard
  lattice, local naturality (TC-S);
- TC-A through TC-H for the target container.

Under CFTH, for a uniform bad profile in the tame local type,

    h_C >= sum_{p in S_bad} alpha_p H_p^Sp log p + h_inf(C),   (B1)
    D_C^Sp := sum_{p in S_bad} alpha_p d_p log p,              (B2)
    Q_C - h_C <= D_C^Sp - h_inf(C).                           (B3)

Compensation requires

    h_inf(C) >= D_C^Sp.                                       (B4)

For F=Q one bad p, using h_inf=log r_inf:

    log r_inf >= d_p log p,
    r_inf >= p^{d_p}.                                         (B5)

There is no pi factor under B_I-zero. No complete C satisfying CFTH is
constructed; B1-B5 are conditional.

## 5. Finite local data and B labels

Local type: e=41, p=12301, pi^41=p, m=(pi), f=1, J=m, I=p^{-1}m,
m0=20. For e=41<p-1=12300, the task-170 log correction gives n_exp=1; the
restricted/full log domain distinction does not enlarge the local integer
lattice O_K. Volume formula keeps f generally:
logvol_O(m^n)=(n f/e)log p; here f=1.

The finite values, conditional on CFTH/TC-S:

    H_p^Sp/log p = -(1/m0) sum_j (s_j+1/e),                    (C1)
    d_p = b(e+1)/12 - (b-1)/e - T_p,
    T_p = (1/(e m0)) sum_j t_j,  0<=T_p<1.                     (C2)

B labels:

- B_H=O_K for H=Phi^{-1}(Sp) under the inferred natural alignment.
- Full barGamma branch is UNDETERMINED. B_Gamma=O_K requires every actual
  generator to fix l=O_K/J; if some actual generator moves l, or alignment
  fails with v!=0, B_Gamma=I.
- B=O_K finite residuals below are conditional on barGamma(l)=l.
- b=3 B=I 9/41 is not actual under the natural alignment.
- Full-B=O_K label from natural alignment alone is withdrawn.

## 6. b=3 and b=273

Uniform rho=1, e=41, m0=20, p=12301, T_p=1/2.

| b | d_p | H_p^Sp/log p (B_H=O_K) | Q_p/log p | deficit d_p | B=I deficit |
|---:|---:|---:|---:|---:|---:|
| 3 | 408/41 | -411/41 | -3/41 | 408/41 | -12/41 (h_B=9/41) |
| 273 | 38883/41 | -39156/41 | -273/41 | 38883/41 | 38463/41 (h_B=-38736/41) |

All table entries are dimensionless log-p values. Natural-log deficits are
obtained by multiplying by log p.

- b=3: B_H=O_K natural deficit 93.714971...; B=I is -12/41 and is not actual
  under the natural alignment.
- b=273: both B_H=O_K and B=I give positive natural deficits
  (8931.174579... and 8834.703285...). The positivity is robust under the B
  branch, but both labels remain conditional on CFTH and on the actual full
  image behavior.

## 7. Binding radii and withdrawn shell-pi radii

Under B_I-zero and F=Q radial, compensation requires

    r_inf >= p^{d_p}.                                         (D1)

b=3:

    d_3=408/41,
    log10 r_inf=(408/41)log10(12301)=40.6998948963...,
    r_inf=12301^{408/41}=5.0106595585e40.                     (D2)

b=273, A=O_K branch:

    d_273=38883/41,
    log10 r_inf=3878.759836402...,
    r_inf=12301^{38883/41}.                                   (D3)

B=I branch b=273: r_inf=12301^{38463/41}, log10 r=3836.862885...
Not selected by the natural alignment; conditional.

Withdrawn as non-binding:

- pi*exp(d_p) (task-156 A18/A19);
- pi*41^{d_p} (task-162 D1/D2);
- pi*12301^{d_p} (task-167/task-176 shell-pi radii);
- any log10(r/pi) figure quoted as log10(r).

The factor pi is absent under B_I-zero. The base is the rational prime
p=12301, not e=41. The number 41 is e and appears in d_p and Q_p, not in the
exponential base.

## 8. Product formula and sign

Under B_I-zero,

    sum_v alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0,   (E1)
    h_inf >= -sum_p alpha_p v_p(x) log p.                     (E2)

No -log pi term appears. This is a point-modulus constraint, not a hull
volume lower bound; it neither forces positive h_inf nor excludes the
positive-radius branch.

Paper sign versus Lean sign:

    paper radial log-volume: positive for r>1;
    Lean absLogAddHom = -log ||u||, archimedeanDelta = -log r.

Flip sign or use -archimedeanDelta when comparing.

## 9. Status of statements

Valid/source-level:

- IV B_I container normalization, A6/A7 max-container bound;
- AbsTopIII O_k unit-ball normalization and log r readout;
- product formula and degree weights;
- log-domain arithmetic of task-170;
- conditional residual algebra B2/B3 under B1.

Conditional:

- CFTH/TC and C1/C2 finite values;
- B_H=O_K, full barGamma undetermined;
- b=3/b=273 residuals and B labels;
- A7 vs finite deficits arch-only exclusion (finite side conditional);
- radii D2/D3 (no actual radius constructed).

Withdrawn/invalid:

- shell-pi h_inf=log(r/pi), h_inf<=0, pi*p^{d_p};
- v2/task-176 radii pi*p^{d_p};
- full-B=O_K from natural alignment alone;
- b=3 B=I 9/41 as actual;
- any unconditional h_C>=Q_C or global counterexample;
- TAME (11)-(14) as target proof.

Unproved:

- actual complete-C archimedean hull/radii and angular terms;
- actual full barGamma action on l (v/coordinates);
- TC-A..TC-H and TC-S for a complete C;
- global finite good/bad sums, fixed q/Theta/target-column class;
- global h_C>=Q_C or a genuine counterexample.

## 10. Verdict

Binding v3 replaces the shell-pi normalization of v2 with B_I-zero:

    h_inf(C)=sum_v alpha_v log r_v,
    F=Q: h_inf=log r_inf,
    shell r_v<=pi: h_inf<=log pi (not 0),
    max container: h_inf<=A_arc=13.164394...,
    compensation: r_inf>=p^{d_p} (no pi).

b=3: r_inf>=12301^{408/41}=5.0106595585e40 (log10 40.6998948963).
b=273 A=O_K: r_inf>=12301^{38883/41} (log10 3878.759836402).

The archimedean-only insufficiency for the conditional b=3/b=273 profiles
survives via A_arc. No global closure, no complete C, no target acceptance.

target_accepted=false.
