# C9 dependency/error audit (task-157)

Task: task-157, C9 dependency/error audit of completed records.
Date: 2026-10-25. Owner: kummer. Stage: natural-language audit only.
Deliverable: this file. No Lean/Project/target edits. target_accepted=false.

Audit inputs (current bytes; SHA256):

| file | lines | SHA256 |
|---|---:|---|
| C9-TAME-LOG-DOMAIN-20261025.md | 251 | 23b3514b94972de511f1b17e23ab3da832ed5bc63e89daca3875adeb07961f06 |
| C9-ERRATA-SYMPLECTIC-20261025.md | 14 | a189fc87d9f633916a097c2b8d9c5bda7407825920765c1ceca36335be5024c7 |
| C9-LOG-DOMAIN-EXTEND-20261025.md | 200 | cc52a8cf0d5fb56172a7af2f6fb0c5c57eb726a5a459d3ccde42fddd3daf2dfa |
| C9-UNIFORM-HULL-20261025.md | 255 | 99539b279b008cbee367c14bc48ac11114460b0c0b706a71546ffddc245a7d5b |
| C9-GLOBAL-ASSEMBLY-20261025.md | 253 | 6ab115790d8cdfd9e261985f7f209e4817c572af6aaf4a48eb0efdc2de52ccf2 |
| C9-SYMPLECTIC-SOURCE-20261025.md | 314 | 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70 |
| C9-IND1-GLOBAL-20261025.md | 532 | 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8 |
| C9-MODP-CERTIFICATE-20261025.md | 250 | e5056d524da94683e5b6ba765ea0aeaf8b23c03d96814f02b49cb47496cc9e95 |
| C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md | 230 | (task-151 follow-up; radius error corrected below) |

Correction sources read: C9-IND1-GLOBAL (task-149/155) and
C9-MODP-CERTIFICATE (task-155), as instructed by lead. The archimedean
radius correction from lead task-162/156 is audited in Section 5.

Verdict classes:

- VALID: exact local arithmetic/linear algebra or paper-level statement,
  independent of the withdrawn target step.
- CONDITIONAL: correct only with the listed corrected-donor / basis /
  low-ramification / TC conditions; not a target proof.
- INVALID: false or unjustified as written, or relies on withdrawn steps.
- WITHDRAWN: explicitly retracted by a later C9 record.

## 1. Executive verdict

1. Exact arithmetic for b=3, b=273, and b=1347 in
   C9-UNIFORM-HULL-20261025.md is correct. The s_j sums, h_A/h_B values,
   half-profile values, and gaps all reproduce exactly.
2. The global assembly algebra (G1), (G4), (G6) is correct, but it does not
   determine the global sign. Positive local D_p does not imply a global
   deficit; the archimedean term h_inf is unknown and enters with the opposite
   sign. No h_C >= Q_C, no global counterexample, and no global sign
   conclusion is established.
3. The original TAME Section 2 boundary-word symplectic donor is INVALID as an
   actual source construction. The corrected donor is
   H = Phi^{-1}(Sp_{2g}(Z_p)) inside Out(G_K), with
   Phi(H) = Sp_{2g}(Z_p). rho is not a homomorphism; there is no splitting.
4. TAME Section 5 equations (11)-(14) are not a target proof. Equation (13)
   does not follow from a Q_p-algebra isomorphism alone; it needs TC-B. (14)
   needs TC-C. TC-A..TC-H and TC-S are open.
5. MODP certificate is valid exact local arithmetic conditional on the inferred
   2025/2026 basis alignment. Under that alignment B=O_K, so the b=3 B=I
   surplus 9/41 is not actual. If alignment fails, the exact gap is the unknown
   W-coordinate v of O_K/J; v=0 gives B=O_K, v!=0 gives B=I.
6. MAJOR NUMERICAL ERROR in the archimedean radius record:
   C9-GLOBAL-ASSEMBLY-CORRECTED D1/D2 used base e=41 instead of p=12301.
   C7 requires r_inf >= pi * p^{d_p}, not pi * 41^{d_p}. The corrected b=3
   radius is about 1.574e41 (old value about 3.518e16); for b=273,
   log10(p^{d_p}) is about 3878.760 (old claim about 1530.0), so the necessary
   radius is astronomically larger. See Section 5.
7. Exact local numerical values are retained, but any statement calling them
   actual target hull values or using them to bound H_C is conditional or
   withdrawn.

## 2. Dependency ledger

### 2.1 TAME package

| claim | status | depends on | audit note |
|---|---|---|---|
| TAME §1: log on O_K^x, log(O_K^x)=m, I=p^{-1}m for e<p-1 | VALID conditional on e<p-1 and the source Teichmuller convention | standard p-adic analysis | Local statement; no target containment. e=p-1 is treated in EXTEND. |
| TAME §2: explicit boundary-word free-group substitutions as actual Galois automorphisms | INVALID | none / withdrawn | Retracted by ERRATA and SYMPLECTIC-SOURCE. Actual source is mapping-class/Dehn-twist rho. |
| TAME §2: Sp_{2g}(Z_p) subset Phi(Out(G_K)) | VALID paper-level | Kondo 2026 Lemma 1.6, Def 3.2, Lemma 3.3 | Containment, not equality, not splitting. |
| TAME §2: H=Phi^{-1}(Sp), Phi(H)=Sp | CONDITIONAL/VALID inference | paper containment + continuity | Valid as immediate subgroup construction; "actual paper-level donor" wording should be read with the inference. |
| TAME §2: G|U=id, G|W=Sp | CONDITIONAL | 2025 trace basis = 2026 symplectic basis; Tr_{K/K^{d=1}}; total ramification for Q_p | Basis alignment is an inferred convention. |
| TAME §3: J=m, I=p^{-1}m | CONDITIONAL | low-ramification e<p-1; correct log domain | Local input, not Kondo group theory. |
| TAME §3 (7): closed Z_p-span of actual Aut(G_K) orbit of pi^n O_K is p^s m_K | CONDITIONAL | corrected H; basis alignment; trace formula; standard Sp-stable lattice lemma; local unit/log naturality | Inferred consequence, not a Kondo theorem. |
| TAME §3 (8): volume gain ((t-1)/e) log p | CONDITIONAL | (7) and normalization | Local conditional. |
| TAME §4: finite witness and Hull(gamma(A_t))=m | CONDITIONAL | corrected source lift through H; two-transvection matrix certificate | Matrix part exact; actual source lift not established by matrices alone. |
| TAME §5 (11): T beta_+ = F | CONDITIONAL | Kummer/poly representatives; TC-A; beta in Ind1_src | Definition/composition once these are fixed; not automatic from Prop1.2(vi)/3.2(i). |
| TAME §5 (12): R = T beta_+ gamma_+(A(S)) = F gamma_+(A(S)) | CONDITIONAL | (11); beta,gamma in full source Ind1; actual source region; same target container | Algebraic identity does not repair a flawed source. |
| TAME §5 (13): F(Hull(...)) subset H_C because F is ring isomorphism | INVALID as written / WITHDRAWN | TC-B | Ring isomorphism alone does not imply target containment. |
| TAME §5 (14): nu(H_{C,j,p})/log p >= -s_j - 1/e | INVALID as target bound / CONDITIONAL | (13) + TC-C | Set inclusion alone does not give the volume bound. |
| TAME §5 target-hull derivation | WITHDRAWN | none | IND1 explicitly withdraws (11)-(14) as a target proof. |
| TAME §6: B=O_K or B=I classification | CONDITIONAL | corrected H action; basis alignment; irreducibility of standard Sp representation | Algebra clean; premise corrected donor; B=I not actual under inferred alignment. |
| TAME §6 (17b): B=I values | CONDITIONAL, currently unavailable | actual mod-p line v; TC-S | MODP inferred alignment gives B=O_K; B=I only if alignment fails with v!=0. |
| TAME §7: exact b=3, b=273, b=1347 values | VALID arithmetic, CONDITIONAL interpretation | TAME (15)/(17) local formulas | Numbers correct; "actual hull" interpretation conditional/withdrawn. |
| TAME §8: completed target hull and exact lower bound | INVALID/OVERCLAIM | none / withdrawn | Only conditional local expressions survive. |

### 2.2 ERRATA / EXTEND

| claim | status | depends on | audit note |
|---|---|---|---|
| ERRATA items 1-5 (rho not hom; boundary words; basis alignment; trace target; J/orbit inferred) | VALID corrections | Kondo 2026/2025 reading | Binding for all follow-up C9 records. |
| EXTEND §1: n0=ceil(e/(p-1)), convergence of log/exp | VALID local mathematics | standard p-adic analysis | e=p-1 boundary correctly included. |
| EXTEND §2: J=m^{n0}, I=m^{n0-e}, volume formula | CONDITIONAL | source Teichmuller convention (b) vs pure analytic domain (a) | Two domains must not be mixed; under (b) local formulas; under (a) Teichmuller roots are not in the power-series domain. |
| EXTEND: second iteration empty / integer lattice | CONDITIONAL | same source branch; low-ramification context | Local only; no target closure. |
| EXTEND global applicability | NOT ESTABLISHED | wild ramification and archimedean data absent | File itself states the gap. |

### 2.3 Uniform hull

| claim | status | depends on | audit note |
|---|---|---|---|
| b=3: h_A=-411/41, h_B=9/41, Q=-3/41, gaps 408/41, -12/41 | VALID arithmetic | TAME (15)/(17) formulas, conditional | Rechecked exactly. |
| b=273: h_A=-39156/41, h_B=-38736/41, Q=-273/41, gaps 38883/41, 38463/41 | VALID arithmetic | same | Rechecked exactly. |
| b=1347 half-profile values and gaps | VALID arithmetic | TAME (15)/(17) | Rechecked exactly; first-success reproduced. |
| "Branch A is actual (source-symplectic/aligned hull)" | CONDITIONAL/OVERCLAIM wording | corrected donor; TC-S; TC-A..H | Current version partly withdraws; retain only conditional local arithmetic. |
| "Branch B is the larger possible subfamily" | CONDITIONAL | B=I; MODP alignment | Under inferred alignment B=I is not actual; if alignment fails v!=0 would give it, but v is unknown. |
| p=12301 local realization | VALID local exact checks, CONDITIONAL source realization | IUT local data | Does not construct a complete global C; no global Galois image. |

### 2.4 Global assembly

| claim | status | depends on | audit note |
|---|---|---|---|
| (W1) place weights alpha_v | CONDITIONAL/INFERRED | paper III Rmk3.1.1(ii), IV Rmk1.7.1 | Not independently audited against page text; assembly input. |
| (W2)/(W3) global template | CONDITIONAL/INFERRED | complete C, weights, h_inf | Not constructed. |
| (G1) h_C >= sum alpha H_p log p + h_inf | CONDITIONAL | TAME (15b) and its withdrawn target interpretation | Conditional local lower-bound assembly, not target containment. |
| (G3)/(G4) local deficit formula | VALID ALGEBRA | H_p formula | Rechecked; exact for b=3,273. |
| (G5) D^Sp = D^old - G_p | CONDITIONAL/ALGEBRA | T16 improvement | Consistent; both sides conditional. |
| (G6) Q_C-h_C <= sum alpha D_p log p - h_inf | VALID ALGEBRA, CONDITIONAL PREMISE | (G1) | Correct inequality; sign not determined because h_inf unknown. |
| (G8)/(G9) b=3,b=273 local bounds | CONDITIONAL arithmetic | single bad p and h_inf assumptions | Arithmetic correct; no global counterexample. |
| (G10) with unknown h_inf | CONDITIONAL/OPEN | actual archimedean readout | No sign conclusion; no target closure. |
| b=3 B=I local value 9/41 treated as possible actual branch | CONDITIONAL, currently unavailable | MODP alignment | Under inferred alignment B=O_K; surplus not actual. |
| Global conclusion h_C >= Q_C | NOT PROVED/INVALID as completed | all above | No global sign, no counterexample. |

### 2.5 Symplectic / IND1 / MODP

| claim | status | depends on | audit note |
|---|---|---|---|
| SYMPLECTIC-SOURCE: Phi closed, Sp containment, rho set map, trace/basis caveats | VALID with stated caveats | Kondo 2026/2025 | No arithmetic; corrections binding. |
| SYMPLECTIC-SOURCE: H, basis alignment, J=m, lattice/orbit/volume inferred | CONDITIONAL | paper containment + alignment + low ramification + naturality | Correctly labeled inferences; not release of TAME §5. |
| IND1-GLOBAL: (11)-(14) withdrawn; full Ind1 >= H; TC-A..TC-H, TC-S | VALID correction | IUT I Def4.10, IUT III Thm3.11/Cor3.12; symplectic source | No target containment. |
| IND1-GLOBAL: Q1 conditional, Q2 not established | VALID status assessment | none | Matches dependencies. |
| MODP: p=12301 prime, trace table, I/J basis, W0=ker Tr | VALID exact local computation | tame totally ramified theory | Trace line l exact. |
| MODP: H=Phi^{-1}(Sp_40), H|U=id, H|W=Sp_40 | CONDITIONAL/INFERRED | symplectic source, basis alignment | H construction inferred; no splitting. |
| MODP: alignment => U=l, v=0, B=O_K; B=I unavailable | CONDITIONAL | inferred 2025/2026 alignment | If alignment fails, v unknown; v=0/v!=0 exact criterion. |
| MODP: matrix transvection certificate | VALID finite computation | exact arithmetic | Reproduced with Python: p prime, A symplectic, A l=l, exit0. |

## 3. Exact arithmetic recheck

### 3.1 Uniform rho=1, e=41, m=20

Definitions: s_j=floor(b j^2/41), t_j=b j^2-41 s_j;
h_A=-(41 sum s_j+20)/820; h_B=(-41 sum s_j+8380)/820;
Q_p/log p=-b/41.

- b=3: sum s_j=200; h_A=-8220/820=-411/41; h_B=180/820=9/41;
  Q=-3/41; Q-h_A=408/41; Q-h_B=-12/41. Correct.
- b=273: sum s_j=19100; h_A=-783120/820=-39156/41;
  h_B=-774720/820=-38736/41; Q=-273/41;
  Q-h_A=38883/41; Q-h_B=38463/41. Correct.
- b=1347, rho=1/2 half-profile:
  h_{1/2}=-51496081/10485760;
  h_direct=h_{1/2}-23/2=-172082321/10485760;
  Q=-1347/82;
  Q-h_{1/2}=-4950820039/429916160 (bound above Q);
  Q-h_direct=-6784199/429916160 (bound above Q; success).
  For b=3: h_{1/2}=-56311/10485760;
  h_direct=-120642551/10485760; Q=-3/82;
  gaps -13419889/429916160 and 4930615951/429916160. Correct.
- Independent exact scan of 82 h_direct + b >= 0 for admissible b<=6000,
  3|b, 41 not divide b: first success b=1347. This reproduces the finite
  first-success claim. The infinite tail b -> b+41 is not re-derived here;
  it remains a separate affine-period claim.

The s_j tables for b=3 and b=273 in UNIFORM-HULL §3.1/§3.2 match exact
floors; b=1347 sum s_j=94280, consistent with the half-profile formula.

### 3.2 Global assembly signs

Paper target: h_C >= Q_C, equivalently Q_C - h_C <= 0.

With D_p^Sp := Q_p - H_p^Sp log p and
Q_C - h_C <= sum_p alpha_p D_p^Sp log p - h_inf:

- D_p^Sp/log p = b(e+1)/12 - (b-1)/e - T_p,
  T_p=(1/(e m)) sum t_j. For b=3 and b=273, sum t_j=410,
  T_p=410/820=1/2, giving D_p/log p=408/41 and 38883/41. Correct.
- Positive D_p are local deficits, not a global sign. If
  h_inf^actual >= sum alpha D_p log p, G0 follows; if
  h_inf^actual < ..., a deficit is possible. Since h_inf is unconstructed,
  neither branch is proved.
- The statement "b=3/b=273 still have 408/41 or 38883/41 deficit" is a local
  bound statement, not the full global comparison.
- The b=3 B=I value 9/41 has Q-9/41=-12/41<0 arithmetically, but under MODP
  inferred alignment B=O_K; no actual b=3 local surplus is available. If
  alignment fails and v!=0, B=I would be the branch, but v is not computed.

## 4. Error ledger

| id | record | error / overclaim | verdict | correction |
|---|---|---|---|---|
| E1 | TAME §2 | Boundary-word free-group substitutions treated as actual Galois automorphisms. | INVALID | Use H=Phi^{-1}(Sp) and mapping-class/Dehn-twist source; see ERRATA/SYMPLECTIC-SOURCE. |
| E2 | TAME §2/§3 | "Image of rho = Sp" / G|W=Sp as explicit subgroup. | INVALID/OVERCLAIM | rho not homomorphism; use closed preimage H; Phi(H)=Sp. |
| E3 | TAME §3 | Tr_{K/Q_p} trace formula without basis alignment. | CONDITIONAL | Use Tr_{K/K^{d=1}}; equality to Q_p only totally ramified; alignment inferred. |
| E4 | TAME §4 | "source lift from §2" for finite transvections. | CONDITIONAL/INVALID source | Matrix certificate valid; source lift must use corrected H. |
| E5 | TAME §5 (11) | Treating T beta_+=F as automatic from paper isomorphisms. | CONDITIONAL | Needs Kummer representatives, beta in Ind1_src, TC-A. |
| E6 | TAME §5 (12) | Treating target possible image without source-group/target-container conditions. | CONDITIONAL | Needs beta,gamma in full source Ind1, actual source region, same target container. |
| E7 | TAME §5 (13) | "F(Hull) subset H_C because F is ring isomorphism." | INVALID/WITHDRAWN | Needs TC-B target saturation or actual target automorphism. |
| E8 | TAME §5 (14) | Target volume lower bound from set inclusion/ring isomorphism. | INVALID/WITHDRAWN | Needs TC-C normalized-volume compatibility. |
| E9 | TAME §8 | "completed target hull and exact lower bound". | OVERCLAIM | Only conditional local expressions; target step withdrawn. |
| E10 | UNIFORM-HULL | "Branch A is actual (aligned hull)" as target fact. | CONDITIONAL/OVERCLAIM wording | Current version partly withdraws; only conditional local arithmetic. |
| E11 | UNIFORM-HULL/GLOBAL | B=I b=3 9/41 as possible actual branch. | CONDITIONAL, currently unavailable | MODP inferred alignment gives B=O_K; B=I only if v!=0 under failed alignment. |
| E12 | GLOBAL-ASSEMBLY | (G1)/(G6)/(G10) as global inequalities without TC/h_inf. | CONDITIONAL | Exact assemblies under local premises; no global sign. |
| E13 | GLOBAL-ASSEMBLY | "B=I only b=3 local positive" as actual branch classification. | CONDITIONAL/OVERCLAIM | Arithmetic conditional; B=I unavailable under inferred alignment. |
| E14 | GLOBAL-ASSEMBLY | h_C>=Q_C or any completed global conclusion. | INVALID as proved | No global sign; no counterexample; h_inf/weights missing. |
| E15 | EXTEND | Global validity of e>=p-1 formulas. | CONDITIONAL | Local p-adic domain valid; wild/archimedean global and Teichmuller branch open. |
| E16 | any record | F(Hull) subset H_C from ring isomorphism alone. | INVALID | IND1 TC-B; no target containment without saturation/automorphism. |
| E17 | IND1-GLOBAL | Correction itself. | VALID | Correctly withdraws (11)-(14); TC-A..H/TC-S remain exact gaps. |
| E18 | MODP | B=O_K under inferred alignment. | VALID/CONDITIONAL | Exact local trace/matrix data; branch conclusion conditional. |
| E19 | MODP | B=I unavailable under alignment. | VALID conditional | If alignment fails, v unknown; exact criterion v=0?/v!=0?. |
| E20 | SYMPLECTIC-SOURCE | H/basis/J/orbit/volume labels as paper theorems. | MOSTLY VALID with inferred labels | Paper-level vs inferred labels explicit; no arithmetic error. |
| E21 | C9-GLOBAL-ASSEMBLY-CORRECTED D1/D2 (task-162/156) | Archimedean radius used base e=41 instead of p=12301; C7 requires r_inf >= pi p^{d_p}. | INVALID as written (major numerical error) | Correct radii below; old b=3 3.518e16 and b=273 log10 1530 are far too small. |

## 5. Archimedean radius correction (lead task-162/156 note)

The finite residual D_p^Sp is measured in log-p units:
d_p := D_p^Sp/log p. The archimedean radial readout is
h_inf = log(r_inf/pi) for F=Q. C7 requires h_inf >= D_p^Sp = d_p log p,
hence

    r_inf >= pi * p^{d_p},       NOT pi * 41^{d_p}.                 (R1)

Here e=41 but the local prime is p=12301. The exponent base must be p, not
the ramification degree e.

Exact values:

- b=3: d_p = 408/41 = 9.951219512195122.
  log10 p^{d_p} = 40.6998948963;
  log10(pi p^{d_p}) = 41.1970447690;
  pi p^{d_p} ~ 1.5741451259e41.
  The previous C9-GLOBAL-ASSEMBLY-CORRECTED value pi*41^{408/41} ~ 3.51816e16
  is too small by a factor of about 4.47e24.
- b=273: d_p = 38883/41 = 948.3658536585366.
  log10 p^{d_p} = 3878.7598364020;
  log10(pi p^{d_p}) = 3879.2569862747.
  The previous "log10 ~1530.0" is far too small; the necessary radius is
  roughly 10^{3879.257}, i.e. about 10^{2349} times the old value.

Thus the corrected C7 necessary radii are:

    b=3:   r_inf >= pi * 12301^{408/41}  ~ 1.574e41;
    b=273: r_inf >= pi * 12301^{38883/41}, log10 ~ 3879.257.

These are still only necessary radii under the conditional local residual;
they are not achieved values, not target containment, and not a global
counterexample. Any archimedean statement using base 41 must be replaced by
(R1). The old numbers 3.518e16 and 1530.0 are invalid as C7 radii.

## 6. Corrected donor / TC dependency

Any use of the symplectic donor in the audited records must carry:

- H = Phi^{-1}(Sp_{2g}(Z_p)) subset Out(G_K), Phi(H)=Sp_{2g}(Z_p);
  not image of rho, not a splitting, not a homomorphic section;
- mapping-class/Dehn-twist actual source, not arbitrary boundary-word
  free-group substitutions;
- inferred 2025/2026 basis alignment, or the explicit v computation;
- trace target Tr_{K/K^{d=1}}, equal to Tr_{K/Q_p} only in the totally
  ramified case;
- low-ramification e<p-1 for J=m;
- standard Sp-stable lattice lemma;
- local unit/log naturality interface (AbsTopIII/IUT III), not a Kondo
  theorem.

The target-container step additionally needs TC-A..TC-H:

- TC-A source procession/actual D^dag isomorphisms and beta in Ind1_src;
- TC-B target saturation or actual target automorphism;
- TC-C normalized-volume compatibility;
- TC-D row/place/profile preservation;
- TC-E Theta/gluing/target-column preservation;
- TC-F log branch/Ind3;
- TC-G fixed n and infinity branch;
- TC-H Ism/Ind2.

TC-S is the corrected symplectic donor condition above. None of TC-A..TC-H is
proved in the audited records.

## 7. What survives / what remains

Survives as exact conditional data:

- exact b=3, b=273, b=1347 arithmetic and the s_j/t_j computations;
- exact local trace table and mod-p line criterion from MODP, conditional on
  basis alignment;
- local p-adic log/exp threshold and domain statements from TAME/EXTEND,
  conditional on source convention;
- the corrected symplectic donor construction H and the paper-level Sp
  containment;
- the algebraic inequalities (G1), (G4), (G6) as conditional assemblies.

Remains:

1. Prove or compute the 2025/2026 basis alignment; equivalently decide v=0/v!=0
   for the W-coordinate of O_K/J in the actual 2026 symplectic basis.
2. If v=0, keep B=O_K and discard the b=3 B=I surplus. If v!=0, B=I is
   available under the corrected donor but still only local.
3. Supply TC-A..TC-H plus TC-S for any target-containment use.
4. Construct the actual archimedean readout h_inf^actual(C); compute the
   corrected radius pi p^{d_p} and its sign contribution.
5. Construct complete global row/place weights and a complete admissible C
   with its actual q/Theta/target-column class.
6. No global closure or global counterexample; no Lean kernel verification.

## 8. Acceptance record

- Audit type: natural-language dependency/error audit; no Lean/Project edits.
- Exact arithmetic: independently recomputed with exact rational arithmetic;
  all listed b=3, b=273, b=1347 values match.
- MODP finite check: reproduced with Python; p prime, A symplectic, A fixes l;
  exit0.
- Global sign: algebraic identity checked; no global sign conclusion.
- Archimedean radius: base error identified and corrected to pi p^{d_p};
  numerical values recomputed.
- statement_compiles=false, proof_body_checked=false, kernel_closed=false,
  target_accepted=false.
- No fabricated closure, no arbitrary assumptions added.
