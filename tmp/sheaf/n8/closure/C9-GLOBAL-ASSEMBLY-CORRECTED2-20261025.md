# C9 corrected global assembly v2

Task: task-176. Date: 2026-10-25. Owner/executor: transport.
Stage: stage1 natural-language assembly only. No Lean/Project/target edits.
Only this file written.

Inputs:

| file | lines | SHA256 |
|---|---:|---|
| C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md (v1) | 229 | 8E7EF66A737BBFE73ED13EA568875A4D1305F48D814DE4B3773BEBB3DB2F3548 |
| C9-AUDIT-GLOBAL-ASSEMBLY-20261025.md (task-173) | 279 | 916DC332D9AA15D5898062EC73C3D37E56A6CA682A9411DA0470C68647E22E6B |
| C9-RADIUS-CORRECTION-20261025.md (task-167) | 118 | D563226D8FCDE7E01F06BCDDD5195F19530182F828C3B419997F78AB3188405D |
| C9-LOG-DOMAIN-CORRECTION-20261025.md (task-170) | 306 | 882DFDEF2BF11377EBC6FDC488205623804100CC54DEEACD5EC805E75F481655 |
| C9-AUDIT-BRANCH-20261025.md (task-160) | 239 | C914E001B45EFE3755D09463DA4D85C78214B56975FAE7042E52BB8A5A56777D |
| C9-AUDIT-ARCH-GLOBAL-20261025.md (task-163) | 294 | 7D719850564C1550D9D525EBE01AE395FE2AE5D70214F21AA83293EC73154825 |

Prior binding corrections remain in force:

- task-147: corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)); rho is not known to be
  a homomorphism; no boundary-word source; basis alignment is inferred.
- task-149: full Ind1 is the procession automorphism group; TAME (11)-(14) are
  not a target proof; TC-A..TC-H plus TC-S are required.
- task-160: B_H=O_K only for the subgroup H under natural alignment; the full
  barGamma branch is UNDETERMINED.
- task-163: archimedean h_inf normalization and base-p radius require care.
- task-167: radii use base p=12301, not e=41.
- task-170: log converges on all U^1; exp threshold is strict; J=m only for
  the restricted convention; volume keeps f.

## 1. Scope and status

This file replaces the numerical and branch labels of v1. It does not add a
new attack, does not construct a complete C, does not prove CFTH/TC, and does
not prove h_C>=Q_C.

The only unconditional arithmetic/paper statements below are source-level
identities explicitly marked VALID. Every global inequality remains
CONDITIONAL on CFTH (defined in Section 3). No complete C satisfying CFTH is
known in the frozen files.

## 2. Archimedean readout and maximal-container bound

Let F=F_mod, and for v|infty let

    I_v = { a in F_v : |a|_v <= pi }

be the source log-shell. The radial readout used in v1, under the shell-pi
normalization, is

    h_v^rad(B_v(r)) = d_v log(r/pi),
    h_inf(C) = sum_{v|infty} alpha_v log(r_v/pi),
    alpha_v = d_v/[F:Q],  sum_v alpha_v = 1.                         (A1)

Task-163 flagged that this is conditional on the shell-pi reference; the
audited IV normalization log-volume(B_I)=0 would instead give log r and change
the pi factor. Therefore (A1) is retained here only as the v1 conditional
normalization; the maximal-container comparison below is a source-container
bound and is independent of the actual radius.

For F=Q, radial case:

    h_inf = log(r_inf/pi).                                           (A2)

The donor-independent source-container bound is

    h_inf(C) <= A_arc = ((l+5)/4) log pi,   l=e=41,
    A_arc = 11.5 log pi = 13.164394...                                (A3)

(A3) is conditional on the source container pi^{j+1}B_I and on the angular +
radial readout; it is not a bound on an actual complete C radius.

The finite conditional deficit from Section 4 is in natural-log units:

    D_C^Sp = sum_{p in S_bad} alpha_p d_p log p.                     (A4)

For b=3, p=12301, d_p=408/41:

    D_C^Sp = (408/41) log 12301 = 93.714971...                        (A5)

Since 93.715 > 13.164, the archimedean maximal container cannot compensate
this conditional finite deficit. For b=273 the deficit is
(38883/41)log 12301 ~ 8931.175, also far above A_arc.

Classification: A3/A5 give a VALID CONDITIONAL arch-only exclusion for the
stated profiles. They do NOT prove global h_C>=Q_C, because finite good-place
terms, other bad places, and CFTH/TC are not supplied.

## 3. CFTH and the conditional residual

CFTH is the conjunction of:

- corrected donor H=Phi^{-1}(Sp), mapping-class/Dehn-twist source, inferred
  natural basis alignment, trace target, low-ramification input, standard
  lattice, local naturality (TC-S);
- TC-A through TC-H: source procession isomorphisms and beta in full Ind1,
  target saturation/allowedness, normalized-volume preservation, row/place/
  profile preservation, Theta/gluing/q-class preservation, log/Ind3 branch,
  n/infinity branch, Ism/Ind2 indeterminacy.

Under CFTH, for a uniform bad profile in the tame local type,

    h_C >= sum_{p in S_bad} alpha_p H_p^Sp log p + h_inf(C),          (B1)
    D_C^Sp := sum_{p in S_bad} alpha_p d_p log p,                     (B2)
    Q_C - h_C <= D_C^Sp - h_inf(C).                                  (B3)

(B3) is exact conditional algebra. It closes only if

    h_inf(C) >= D_C^Sp.                                              (B4)

No complete C satisfying CFTH is constructed; (B1)-(B4) are conditional
formulas, not actual global inequalities.

## 4. Finite local data after log-domain correction

Local type: e=41 prime, p=12301, p>e+1, pi^41=p, m=(pi), f=1,
J=m, I=p^{-1}J, b j^2=s_j e+t_j, 0<=t_j<e, m0=(e-1)/2=20.

The corrected log-domain statement at this local type is:

- e=41 < p-1=12300, so n_exp=1; log converges on U^1 and exp/log are inverse
  on m. The task-170 strict-threshold correction is essential for general e,
  but at e=41 it gives n_exp=1, not a higher exponent.
- Under the restricted Teichmuller convention, J=log(mu·U^1)=m and
  I=p^{-1}m. This is the convention used by the tame local formulas.
- The full log(U^1) is not proved equal to m; only the restricted image m is
  used. The integer lattice remains O_K because log(U^1) subset m.
- The volume formula keeps f:
  logvol_O(m^n)=(n f/e)log p. For f=1 this is (n/e)log p.

The inferred aligned finite values (conditional on CFTH/TC-S) are:

    H_p^Sp/log p = -(1/m0) sum_j (s_j+1/e),                          (C1)
    d_p = D_p^Sp/log p = b(e+1)/12 - (b-1)/e - T_p,
    T_p = (1/(e m0)) sum_j t_j,  0<=T_p<1.                           (C2)

These are not Kondo theorems. They depend on the corrected donor, basis
alignment, trace target, standard-lattice lemma, and local naturality.

## 5. B branches, with corrected labels

Let l=O_K/J in I/J=Ubar direct-sum Wbar, and write l=span(1,v) in the
trace-adapted basis.

- For the subgroup H=Phi^{-1}(Sp), under the inferred natural alignment
  U=trace line, v=0 and H fixes l. Thus B_H=O_K.
- For the full actual finite image barGamma, B_Gamma=O_K only if every
  actual generator fixes l; if some actual gamma moves l, or if the alignment
  fails with v!=0, then B_Gamma=I. The full branch is UNDETERMINED in the
  frozen files (task-160).

Consequences for the labels:

1. B=O_K finite residuals are conditional on the additional hypothesis
   barGamma(l)=l, not on natural alignment alone.
2. b=3 B=O_K residual 408/41 is conditional.
3. b=3 B=I value 9/41 is not actual under the natural alignment; it is only a
   conditional alternative if barGamma moves l.
4. b=273 B=O_K value 38883/41 and B=I value 38463/41 are both positive; the
   b=273 positivity is robust under the B branch, but both remain conditional
   on CFTH and on the corresponding full-barGamma behavior.

The label "B=O_K under natural alignment" for the full image is withdrawn;
the correct label is B_H=O_K for the subgroup H, full barGamma undetermined.

## 6. b=3 and b=273 evaluation

Uniform rho=1, e=41, m0=20, p=12301, T_p=1/2.

| b | d_p | H_p^Sp/log p (B_H=O_K) | Q_p/log p | Q_p-H_p^Sp (log p) | B=I Q-h_B |
|---:|---:|---:|---:|---:|---:|
| 3 | 408/41 | -411/41 | -3/41 | 408/41 | -12/41 (h_B=9/41) |
| 273 | 38883/41 | -39156/41 | -273/41 | 38883/41 | 38463/41 (h_B=-38736/41) |

The table entries are dimensionless log-p values. The natural-log finite
deficits are obtained by multiplying by log p.

For b=3, the B_H=O_K natural-log deficit is
(408/41)log 12301=93.714971...; the B=I value would be -12/41 and is not a
deficit. Under the full barGamma, if l moves, b=3 B=I is selected; that branch
is not actual in the frozen sources and is not used for closure.

For b=273, both B branches give positive residual:
- B_H=O_K: (38883/41)log p=8931.174578...;
- B=I: (38463/41)log p=8834.703284644... .
The b=273 conclusion "positive residual" is therefore robust under the B
branch, but it is still conditional on CFTH/TC and on the actual full image
being one of these two branches.

Exact b=273 B=I natural log:

    (38463/41) log 12301 = 8834.703284644...

The file reports both exact fractions and decimal natural-log values; the
log-p table entries remain dimensionless d_p, not natural logs.

## 7. Corrected radii

For F=Q, radial, shell-pi normalization,

    h_inf=log(r_inf/pi),  compensation h_inf>=D_C^Sp
    => r_inf >= pi * exp(D_C^Sp).                                    (D1)

Since D_C^Sp=d_p log p,

    r_inf >= pi * p^{d_p},   p=12301.                                (D2)

b=3:

    d_3=408/41,
    log10(p^{d_3})=(408/41)log10(12301)=40.6998948963,
    log10 r_inf=41.1970447690,
    r_inf=1.5741451259e41.                                           (D3)

b=273:

    d_273=38883/41,
    log10(p^{d_273})=(38883/41)log10(12301)=3878.7598364020,
    log10 r_inf=3879.2569862747,
    r_inf=1.8071170136e3879.                                         (D4)

These supersede:

- task-156 A18/A19 (pi*exp(d_p), omitted log p);
- task-162/v1 D1/D2 (pi*41^{d_p}, base e=41);
- any "log10 ~1530" or "3.51816e16" figure.

The corrected base is the rational prime p=12301. The number 41 is e and
appears in d_p and Q_p=-b/e log p, not in the exponential base.

If one uses the B=I b=273 value 38463/41, the radius is pi*12301^{38463/41}
with log10 exponent 3837.36...; it is not the selected branch in the frozen
sources.

## 8. Product formula and shell branch

Product formula (F=Q):

    sum_{v|infty} alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0.  (E1)

For x in the radial hull, log r_inf>=log|x|_infty, so

    h_inf >= -sum_p alpha_p v_p(x) log p - log pi.                    (E2)

This is a point-modulus constraint, not a hull-volume lower bound. It does
not force positive h_inf and does not exclude the positive-radius branch.

Shell branch: if r_v<=pi for all v, then under shell-pi normalization
h_inf<=0; then (B4) is impossible for D_C^Sp>0. This branch is not proved for
a complete C; the source shell I_v is not the tensor container pi^{j+1}B_I.

## 9. Proved, conditional, withdrawn

Proved/source-level:

- IUT III shell radius pi; angular/radial log-volumes; product formula and
  degree weights; Ind1 is procession automorphisms; target hull subject to
  Ind1/Ind2/Ind3.
- Kondo continuity/closedness of Phi, basis, Sp containment, JW presentation,
  mapping-class rho, trace kernel with basis caveat.
- Log-domain arithmetic of task-170: log on U^1; strict exp threshold;
  restricted J=m; volume (n f/e)log p.

Conditional:

- CFTH and TC-A..TC-H/TC-S;
- residual formula (B1)-(B3), max-container A3, radii D1-D4;
- B_H=O_K under natural alignment; full B branch undetermined;
- b=3/b=273 residuals and their B labels.

Withdrawn/invalid:

- any unconditional h_C>=Q_C or global counterexample;
- v1 D1/D2 base-41 radii;
- full-B=O_K label from natural alignment alone;
- b=3 B=I 9/41 as actual/selected;
- shell containment r_v<=pi as a source theorem;
- TAME (11)-(14) as target proof;
- task-156 A18/A19 and their numerical radii.

Unproved:

- actual complete C archimedean hull/radii and angular terms;
- actual full barGamma action on l (v/coordinates);
- TC/CFTH for a complete C;
- global finite good/bad sums and fixed q/Theta/target-column class;
- global h_C>=Q_C or a genuine counterexample.

## 10. Verdict

Under CFTH, the exact conditional residual is

    Q_C - h_C <= D_C^Sp - h_inf(C),
    D_C^Sp=sum_{p in S_bad} alpha_p d_p log p,
    d_p=b(e+1)/12-(b-1)/e-T_p.

For F=Q uniform one bad p=12301, e=41:

- b=3 B_H=O_K: D=(408/41)log p=93.714971..., above A_arc=13.164394; radius
  pi*12301^{408/41}=1.574145e41.
- b=273: B_H=O_K D=(38883/41)log p=8931.174579..., B=I D=(38463/41)log p;
  both positive; radius (B_H=O_K) pi*12301^{38883/41}, log10 3879.256986.
- B=O_K is only B_H=O_K under natural alignment; full barGamma remains
  undetermined. b=3 B=I 9/41 is not actual.

The archimedean max-container bound excludes archimedean-only compensation for
these conditional profiles, but does not prove global closure. No global
h_C>=Q_C and no complete counterexample is claimed.

target_accepted=false.