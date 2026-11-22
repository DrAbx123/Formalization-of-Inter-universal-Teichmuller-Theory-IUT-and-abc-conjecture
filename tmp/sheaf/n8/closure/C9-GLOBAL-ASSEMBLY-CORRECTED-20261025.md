# C9 corrected global assembly after symplectic/Ind1 corrections

Task ID: task-162 / C9-GLOBAL-ASSEMBLY-CORRECTED-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language research only; no Lean/Project edits; no target changes; no new attack assumptions; no fabricated closure.
Deliverable: only this file.

## 0. Frozen inputs and binding errata

Inputs:

- C9-ERRATA-SYMPLECTIC-20261025.md, SHA256 a189fc87d9f633916a097c2b8d9c5bda7407825920765c1ceca36335be5024c7.
- C9-ERRATA-IND1-20261025.md, SHA256 ef63f916b4312a3e8562d16c2c122770bf7f188b75760989f958fda2f6a0f8c2.
- C9-GLOBAL-ASSEMBLY-20261025.md (task-151), SHA256 6ab115790d8cdfd9e261985f7f209e4817c572af6aaf4a48eb0efdc2de52ccf2.
- C9-IND1-GLOBAL-20261025.md (task-149), SHA256 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8.
- C9-MODP-CERTIFICATE-20261025.md (task-155), SHA256 e5056d524da94683e5b6ba765ea0aeaf8b23c03d96814f02b49cb47496cc9e95.
- C9-ARCH-GLOBAL-20261025.md (task-156), SHA256 524e078ad85c72067627f006d165a724436e1ba508e86475c5f991860586e489.
- C9-SYMPLECTIC-SOURCE-20261025.md (task-147), SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.

Binding corrections:

1. rho: Mod(S minus P) -> Out(G_K) is not known to be a homomorphism; no homomorphic section. The corrected donor is the closed preimage H = Phi^{-1}(Sp_{2g}(Z_p)), with Phi(H)=Sp. It is not the image of rho.
2. Boundary-word-preserving free-group substitutions are not all actual Galois automorphisms. The actual source is the mapping-class/Dehn-twist construction.
3. The 2025 trace basis and 2026 symplectic basis alignment is inferred, not a cross-paper theorem. The trace theorem is Tr_{k/k^{(d=1)}}; it equals Tr_{K/Q_p} only in the totally ramified C9 local type.
4. J=m, the standard-lattice classification, orbit generation T7, volume gain T8, and finite lower bounds T14/T15 are inferred consequences, not Kondo theorems.
5. TAME (11)-(14) are NOT a target proof. Full Ind1 is the procession automorphism group, not finite label translation. A ring isomorphism F alone does not imply F(Hull(...)) subset H_C. Target containment needs TC-A to TC-H and TC-S.
6. Under the inferred natural trace alignment, B=O_K and the conditional b=3 B=I surplus 9/41 is not actual. If alignment fails, the W-coordinate v of the line O_K/J is the exact finite mod-p gap and is not computed in current sources.

Consequently this file supersedes the unconditional reading of task-151. Every global statement below is conditional, and the old global closure claim is withdrawn.

## 1. Actual archimedean readout

Let F=F_mod, n=[F:Q]. For v|infty let F_v be R or C and d_v=[F_v:R] (1 or 2). IUT III Remark1.2.2(ii) gives the complex archimedean log-shell

    I_v = { a in F_v : |a|_v <= pi }.                         (A1)

IUT III Def1.1(ii)/(vii) and Prop1.2(iii),(v) supply angular and radial log-volumes; AbsTopIII Prop5.7(ii)/Cor5.10(ii) supply the actual archimedean normalization. For a radial ball B_v(r)={|a|_v<=r}, with I_v as reference,

    h_v^rad(B_v(r)) = d_v log(r/pi).                         (A2)

For all infinite places, for a radial hull with radius r_v=sup |x|_v over the archimedean hull,

    h_inf(C) = sum_{v|infty} alpha_v log(r_v/pi),            (A3)
    alpha_v = d_v/[F:Q],  sum_v alpha_v = 1.                 (A4)

F=Q has one real place and gives

    h_inf(C) = log(r_inf/pi).                                (A5)

If the hull is not radial, the actual readout is

    h_inf(C) = sum_{v|infty} alpha_v [h_v^ang(A_v)+h_v^rad(R_v)],   (A6)

and the angular term cannot be dropped. The value r_v comes from the actual complete C; it is not constructed here. The file does not set h_inf=0 and does not use r_v=pi unless the actual hull is proved to lie in the shell.

## 2. Global h_C, Q_C and weights

With alpha_p=[(F_mod)_p:Q_p]/[F_mod:Q], sum_{p|p0} alpha_p=1,

    h_C = sum_{p in S_bad} alpha_p h_p + sum_{p in S_good} alpha_p h_p + h_inf(C),   (B1)
    Q_C = sum_{p in S_bad} alpha_p Q_p.                                            (B2)

For F_mod=Q, alpha_p=1. For a uniform bad profile Q_p=-b_p/e_p log p. Native q has no archimedean Q-term, so h_inf enters h_C only. Good finite profiles have zero normalized contribution relative to the reference. Q_C cannot cancel h_inf separately; only the sum in h_C is meaningful.

## 3. Finite local data and their corrected status

The tame local type: e=ell prime, p>e+1, pi^e=p u, m=(pi), J=m, I=p^{-1}J, b j^2=s_j e+t_j, 1<=t_j<e, m0=(e-1)/2. Under the corrected donor plus basis alignment, low-ramification input, and naturality interface, the inferred aligned lower bound is

    H_p^Sp/log p := -(1/m0) sum_{j=1}^{m0}(s_j+1/e).          (B3)

and the inferred finite residual is

    d_p := D_p^Sp/log p = b(e+1)/12 - (b-1)/e - T_p,          (B4)
    T_p = (1/(e m0)) sum_{j=1}^{m0} t_j,   0<=T_p<1.

B3/B4 are not Kondo theorems. They are conditional on the corrected H donor, the inferred basis alignment, the standard-lattice lemma, the trace target, and the local naturality interface. If any of these fail, B3/B4 are not actual finite lower bounds.

The finite B-branch decision is the exact mod-p question from task-155: write O_K/J in the adapted U direct-sum W basis as span(1,v), v in F_p^{2g}. Then v=0 gives B=O_K; v nonzero gives B=I. Under the natural trace alignment U=trace line, v=0 and B=O_K. The b=3 B=I value 9/41 is therefore not actual under that alignment; if the alignment fails, v is not computed and no branch is assumed.

The B=O_K values are

    h_A/log p = -(1/m0) sum_j (s_j+1/e),                     (B5)
and the conditional B=I values (not selected) are

    h_B/log p = (1/m0) sum_j [-s_j + j - (j+1)/e].           (B6)

## 4. Corrected conditional global residual

Define the corrected finite-target hypothesis CFTH as the conjunction of:

- corrected donor H=Phi^{-1}(Sp), mapping-class source, basis alignment, trace target, low-ramification input, standard-lattice and local naturality (TC-S);
- TC-A through TC-H for the actual target container: source procession isomorphisms and beta in Ind1; target saturation or target automorphism; normalized-volume preservation; row/place/profile; Theta/gluing/q-class; log branch/Ind3; n/infinity; Ism/Ind2.

Under CFTH, and for a uniform bad profile whose bad places all lie in the above local type, the conditional finite bound is

    h_C >= sum_{p in S_bad} alpha_p H_p^Sp log p + h_inf(C).  (C1)

Equivalently,

    D_C^Sp := sum_{p in S_bad} alpha_p d_p log p,             (C2)
    Q_C - h_C <= D_C^Sp - h_inf(C).                          (C3)

(C3) is the exact conditional residual. It becomes a closure only if the right side is <=0:

    h_inf(C) >= D_C^Sp.                                      (C4)

If CFTH is not established, (C1)-(C4) are conditional formulas, not actual global inequalities. TAME (11)-(14) cannot be used to replace CFTH.

## 5. Archimedean branches and compensation

(i) Shell branch. If the actual archimedean hull lies in the source log-shell, r_v<=pi for all v|infty, then h_inf<=0. In that case C4 impossible for D_C^Sp>0 and C3 gives

    Q_C - h_C <= D_C^Sp.                                     (C5)

so the finite deficit cannot be compensated by archimedean terms. This branch is not proved for a complete C; it is a source-level condition, not an assumption.

(ii) Positive-radius branch. If r_v>pi, then h_inf can be positive. The exact conditional compensation criterion is C4. For F=Q (one real place) it is

    log(r_inf/pi) >= D_C^Sp,  i.e. r_inf >= pi exp(D_C^Sp).  (C6)

For a single bad p with d_p in log-p units, D_C^Sp=d_p log p, hence the exact radius is

    r_inf >= pi p^{d_p}.                                     (C7)

(iii) Product-formula bound. For x in F^×,

    sum_{v|infty} alpha_v log|x|_v + sum_p alpha_p v_p(x) log p = 0.   (C8)

If x lies in the radial hull, log r_v>=log|x|_v, hence

    h_inf(C) >= -sum_p alpha_p v_p(x) log p - log pi.         (C9)

For F=Q and finite-integral x (all v_p(x)>=0), the right side is <=-log pi<0. Thus product formula alone cannot force positive archimedean compensation; it also cannot exclude the positive-radius branch. It is a point-modulus constraint, not a hull-volume lower bound.

## 6. b=3 and b=273 evaluation

Take e=41, m0=20, p=12301, rho=1, and the B=O_K branch under the natural trace alignment. Then d_p values and H_p^Sp are exact rationals in units log p:

| b | d_p=D_p^Sp/log p | H_p^Sp/log p | Q_p/log p | Q_p-H_p^Sp (log p) |
|---:|---:|---:|---:|---:|
| 3 | 408/41 | -411/41 | -3/41 | 408/41 |
| 273 | 38883/41 | -39156/41 | -273/41 | 38883/41 |

Thus for b=3 the conditional residual is (408/41)log 41. For one bad p and F=Q, C7 requires

    r_inf >= pi * 41^{408/41} = pi * exp((408/41)log 41) approx 3.51816e16.   (D1)

For b=273 the required radius is

    r_inf >= pi * 41^{38883/41},                              (D2)

which has log10 approximately 1530.0; clearly enormous. These are exact necessary radii under CFTH, not achieved values.

Correction to C9-ARCH-GLOBAL A18/A19: those lines quoted pi*exp(d_p) and omitted the log p factor. Since D_C^Sp=d_p log p in log-p units, the exact radius is pi*p^{d_p}; the versions in (D1)/(D2) supersede the earlier numerical radii.

For comparison, the B=I values are not actual under the natural alignment: b=3 gives 9/41 and would locally exceed Q_p by 12/41; b=273 gives -38736/41 and remains below Q_p by 38463/41. If the basis alignment fails, B=I is not selected; the exact gap is the uncomputed v in F_p^{40}. No B=I surplus is claimed.

## 7. TC-A to TC-H and TC-S checklist

TC-A: Phi/Psi are actual D^dag-procession isomorphisms of the same source/target with core eta; components preserve log-shell, integral structures and Kummer labels; beta is in full source Ind1.

TC-B: either H_C is the target hull of the full target possible-image union for the full source Ind1 orbit, or F is an allowed target automorphism of H_C. A ring isomorphism alone is insufficient.

TC-C: F preserves the target integral closure/hull and the normalized log-volume, or its positive determinant factor is computed and tracked. Without this, F(Hull(...)) subset H_C is only a set inclusion, not the volume bound.

TC-D: F preserves row j, place vQ and bad/good profile; if it permutes capsule constituents, the target must be the full Ind1 union, not a fixed component.

TC-E: F preserves the fixed Theta-pilot, its Theta-times-mu gluing, and the q/BPS/target-column class. Core/gluing eta preservation alone does not prove this.

TC-F: F lies on the allowed log-Kummer branch and is compatible with Ind3. A field-copy construction is not a log-link construction.

TC-G: Ind1 is attached to a fixed n; n-permutations, target-column shifts, the +infinity branch and archimedean places are separate. TAME (14)/(15) do not cover them.

TC-H: F may differ by an Ism/order-2 indeterminacy; the integer lattice may be unchanged while the target hull/log-volume branch moves.

TC-S: any symplectic beta/gamma uses H=Phi^{-1}(Sp), mapping-class/Dehn-twist representatives, explicit basis alignment, trace target Tr_{K/K^{d=1}} (K^{d=1}=Q_p only in the tame totally ramified case), low-ramification J=m, standard-lattice lemma, and local naturality. The original boundary-word construction and rho-as-image-Sp are withdrawn.

None of TC-A to TC-H or TC-S is proved for a complete C in the frozen files.

## 8. Proved, inferred, conditional, withdrawn, unproved

Proved at paper/source level:

1. IUT III archimedean log-shell radius pi (Remark1.2.2(ii)); angular/radial log-volumes and log-link compatibility (Def1.1(ii)/(vii), Prop1.2(iii),(v)); IV/AbsTopIII normalization interface.
2. Standard product formula and degree weights; radial volume formula (A2).
3. IUT III Ind1 is the procession automorphism group; Cor3.12 target hull is subject to Ind1/Ind2/Ind3; ring isomorphism alone is insufficient.
4. Kondo paper-level: Phi continuous closed; basis; embedded Sp containment; JW presentation; trace kernel with basis caveat; mapping-class rho; unit/log compatibility.

Inferred (C9 context, not paper theorems):

5. H=Phi^{-1}(Sp) donor and its additive action; basis alignment; J=m; standard-lattice classification; orbit generation T7; volume gain T8; T14/T15; finite B=O_K under natural alignment.

Conditional:

6. CFTH and its consequences C1-C6; D_C^Sp and the b=3/b=273 residuals; archimedean compensation; B branch selection.

Withdrawn / not actual:

7. Any unconditional statement h_C>=Q_C, any actual global closure, or any complete counterexample.
8. The TAME (11)-(14) target-containment proof, including F(Hull(...)) subset H_C from F being a ring isomorphism and nu(F(E))=nu(E) without TC-C.
9. The b=3 B=I 9/41 surplus as an actual source value under the natural trace alignment; the original rho-image/boundary-word symplectic construction; T7/T8 as Kondo theorems.

Unproved:

10. Actual complete C archimedean hull/radii r_v (including angular terms); shell containment r_v<=pi or a positive radius lower bound.
11. Full bad set and row-Theta weights; CFTH and TC-A to TC-H/TC-S.
12. The finite mod-p coordinate v when the basis alignment fails; B=O_K vs B=I in that case.
13. Global h_C>=Q_C or a complete global counterexample.

## 9. Verdict and exact remaining gap

Under the corrected donor and TC-A to TC-H/TC-S, the exact conditional residual is

    Q_C - h_C <= D_C^Sp - h_inf(C),
    D_C^Sp = sum_{p in S_bad} alpha_p d_p log p,
    d_p = b(e+1)/12 - (b-1)/e - T_p.

For F_mod=Q uniform and one bad p this is exact. At b=3, B=O_K, d=408/41: the finite residual is (408/41)log 41, and archimedean compensation requires r_inf>=pi*41^{408/41} approx 3.51816e16. At b=273 it requires pi*41^{38883/41}, with log10 approximately 1530. Under shell containment r_inf<=pi, h_inf<=0, so archimedean compensation is impossible and the finite residual remains; that branch is not proved. Product formula does not force positive h_inf and cannot replace the actual radius computation.

Therefore the corrected assembly does NOT prove h_C>=Q_C for complete C. It proves only the conditional inequality C1/C3 and the exact radius criterion C4/C7, together with the explicit TC/B/archimedean gaps. The earlier unconditional global closure is withdrawn.

Next executable steps:

1. Construct the actual complete-C archimedean hull and radii r_v (including angular terms); decide shell containment or positive radius.
2. Complete CFTH: corrected donor, basis alignment, trace target, low-ramification, standard-lattice and local naturality; then TC-A to TC-H/TC-S.
3. Compute the finite coordinate v when the basis alignment fails, thereby deciding B=O_K versus B=I without assuming the branch.
4. Only after 1-3, substitute into C3/C4 and report a genuine global inequality or a genuine counterexample.

Status: stage1 natural-language/exact-evaluation only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete P6/ABC not proved.
