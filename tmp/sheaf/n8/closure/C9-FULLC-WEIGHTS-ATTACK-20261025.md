# C9 attack: full-C weights and other finite branches

Task ID: task-169 / C9-FULLC-WEIGHTS-ATTACK-20261025. Owner: primespine. Date: 2026-10-25.
Consumer: n8-c9-output-region-source-route P6; SHEAF stage1.
Nature: natural-language/exact-arithmetic research only; no Lean/Project edits; no target changes; no new arbitrary assumptions; only this file written.

## 0. Inputs and binding corrections

- C9-ERROR-LEDGER-20261025.md (task-164), SHA256 06f8e743c35d2212f81db34bcd8f17483054b1aa82297772b55cae65fcd313b6.
- C9-GLOBAL-ASSEMBLY-CORRECTED-20261025.md (task-162), SHA256 8e7ef66a737bbfe73ed13ea568875a4d1305f48d814de4b3773bebb3db2f3548.
- C9-RADIUS-CORRECTION-20261025.md (task-167), SHA256 d563226d8fcde7e01f06bcddd5195f19530182f828c3b419997f78ab3188405d.
- C9-ARCH-GLOBAL-20261025.md (task-156), SHA256 524e078ad85c72067627f006d165a724436e1ba508e86475c5f991860586e489.
- C9-AUDIT-ARITH-20261025.md (task-158), SHA256 84b3151f87d5414cfa481893577e0497a776b8fa6d50ac12b87c8b24e47ae61e.
- C9-IND1-GLOBAL-20261025.md (task-149), SHA256 94785726ee890f6bc672861c570238f040636a6273a7722b2621949c48af9ab8.
- C9-SYMPLECTIC-SOURCE-20261025.md (task-147), SHA256 3f98f68a5e143dcd51ed6790b1c839ae7b8811e4e418d48b02e37e7c4d5b9c70.

Binding status: the error ledger confirms (E1)-(E6) and classifies the surviving statements. This attack does not reinstate any withdrawn target claim. In particular:

- corrected donor H=Phi^{-1}(Sp_{2g}(Z_p)), not rho image; rho is not known to be a homomorphism; mapping-class/Dehn-twist source; basis alignment inferred; trace target Tr_{K/K^{d=1}};
- TAME (11)-(14) are not a target proof; full Ind1 is the procession automorphism group; ring isomorphism F alone does not give F(Hull(...)) subset H_C;
- TC-A through TC-H and TC-S are required; B=O_K versus B=I is not decided for the full finite image barGamma;
- b=3 B=I value 9/41 is conditional, not actual; B=O_K holds only under the inferred natural trace alignment or the extra hypothesis barGamma(l)=l;
- archimedean h_inf has only the formula and paper-level upper bound; actual r_inf/angular terms are missing.

## 1. Actual bad set for F_mod=Q: what the source fixes and what it does not

IUT I Definition 3.1(b): Vbad_mod is a nonempty set of nonarchimedean valuations of F_mod of odd residue characteristic at which X_F has bad multiplicative reduction. For F_mod=Q, the finite places are the rational primes; a section V -> V(F_mod) selects one place over each rational prime. Uniform profile means rho_p=1 at each selected bad p; it does not mean all rational primes are bad.

Standard arithmetic gives: an elliptic curve over a number field has bad reduction at only finitely many finite places. Since Vbad_mod consists of bad-reduction places of X_F, the actual set S_bad(C) is finite and nonempty. The corpus SourceInitialThetaData records only bad_nonempty and the local bad-reduction q-parameter clauses; it does not enumerate S_bad(C), does not fix the rational primes, and does not prove the global finiteness as a field. The finiteness is an arithmetic consequence, not a constructed list.

For F_mod=Q the degree weight is alpha_p=1. For each bad p the source data give an actual q-parameter and, in the tame local type used below, e_p=ell, p>e+1, qhat valuation b_p/e_p. The row/Theta weight is rho_p^{j+1}; for uniform rho_p=1 it is 1. Therefore the full-C templates are

    h_C = sum_{p in S_bad} h_p + sum_{p in S_good} h_p + h_inf(C),   (F1)
    Q_C = sum_{p in S_bad} Q_p,                                     (F2)
    Q_p = -b_p/e_p log p,                                           (F3)

with alpha_p=1. This is a template using actual objects; it is not an enumerated complete C.

Important weight gaps:

1. S_bad(C) is finite but not explicitly constructed; its cardinality/prime set is not fixed by the source templates. A single bad p=12301 test is not the full C.
2. The tame local type e_p=ell with p>e_p+1 is an extra local-type assumption. For bad p outside that type (e_p not equal to ell, wild ramification, e_p>=p-1, or different residue degree), the formulas T9/T14/T15 and the B-branch classification do not apply; C9-LOG-DOMAIN-EXTEND records J=m^{n0}, I=m^{n0-e}, and O_K/J no longer a line. These places are actual source places but have no proved positive contribution formula here.
3. The actual b_p may vary with p. b=3 and b=273 are two test values, not a uniform range forced by the source. The sum F2 is not evaluated for a complete C.
4. Row/Theta weights rho_p^{j+1} are normalized per bad p; summing over p with alpha_p=1 is not a new arbitrary weight, but the actual set and per-p b_p are not constructed.

## 2. Exact baseline and archimedean upper bound

For a single bad p=12301, e=41, B=O_K aligned conditional branch, task-148/task-151/task-167 give:

- b=3: D_p^Sp/log p = 408/41; the residual is (408/41)log 12301 = 93.71497127459669... natural;
- b=273: D_p^Sp/log p = 38883/41; residual = 8931.17457860329... natural.

The paper-level archimedean upper bound from IV Prop1.5(iii),(iv) and Thm1.10(vii), recorded in the ledger A4, is

    h_inf(C) <= ((ell+5)/4) log pi.                            (F4)

For ell=41: (46/4) log pi = 13.164394... natural. At p=12301 this is 1.397875... in log-p units. This is an upper bound, not an actual archimedean image and not a lower bound.

Comparison with the b=3 residual:

    93.71497127459669 - 13.164394 = 80.55057727459669 natural.   (F5)

In log-p units: 408/41 - 1.397875 = 8.55334495, positive. Thus even the maximal paper-level archimedean bound cannot cover the b=3 finite residual (conditional finite side), and it is vastly smaller than the b=273 residual: 38883/41 is about 948.366 log-p units versus at most 1.397875. Archimedean compensation is impossible under the paper-level upper bound, not merely unproved.

Caveat: the finite residual itself is conditional on CFTH/TC conditions. The archimedean upper bound is paper-level and donor-independent, so F5 is a valid upper-bound comparison, but it is not a global inequality proof until the finite side is actual and the target-container conditions are met.

## 3. Other finite branches: exact contributions and status

List all finite source branches that could change the residual, and classify them.

### 3.1 Good finite places

At a good selected place the Gaussian profile is the unit and the tensor hull is the reference O_E; its normalized contribution relative to the reference is zero. No positive compensation comes from good finite places. If a tuple contains a good factor, the permutation can move the Gaussian mark to it and the hull is O_E: contribution 0, not positive.

### 3.2 Kummer zero path / unit small domain

The Kummer zero path carries the integer lattice O_K; the small unit domain exp(pz) gives pO_K, and its normalized hull is O_K (log-volume 0 relative to reference). TAME/LOG-DOMAIN and task-148 record no positive normalized volume from these paths. They can reduce the local region, not increase it beyond the reference.

### 3.3 Tensor order and integral closure

The tensor order D_r differs from the integral closure O_{E_r} by a nonnegative length; the normalized log-volume loss is delta_r=(r-1)(e-1)/(2e), which is nonnegative. Full Ind1 alignment removes this loss in the conditional target formula T14, but it does not create a positive contribution beyond T14. Without the Ind1/target conditions, the tensor-order term is negative, not compensatory.

### 3.4 B=O_K bad places

Under the aligned/conditional B=O_K branch the local value is h_A, and d_p=Q_p-h_A is positive for every b>0 in the uniform profile. Task-148/A2 proves h_A never reaches Q_p for any positive b:

    h_A >= Q_p  iff  41 sum_j s_j + 20 <= 20 b,
    41 sum_j s_j >= 2870 b - 800 > 20 b - 20  for b>=1.       (F6)

Therefore adding another B=O_K bad place adds another positive deficit with weight 1; it cannot compensate a previous deficit. In particular, if the complete bad set contains p=12301,b=3, all other B=O_K bad places worsen the residual.

### 3.5 B=I bad places (conditional only)

Under the conditional B=I branch the local value is h_B. For b=3, h_B=9/41 and the local surplus is Q_p-h_B=-12/41; for b=273, h_B=-38736/41 and the deficit is 38463/41. The B=I branch is not actual under the inferred natural trace alignment; it is available only if the basis alignment fails and the actual finite coordinate v is nonzero, or if full barGamma(l) is not l. The exact mod-p criterion is: write l=span(1,v) in U direct-sum W; v=0 gives B=O_K, v nonzero gives B=I. The current sources do not compute v or the full barGamma.

Thus B=I is the only finite branch with a local positive value (b=3, 12/41 log p). It is not an actual finite branch. If one nevertheless asks for a conditional aggregate bound: many B=I bad primes with b=3 could in principle accumulate surpluses 12/41 log p and offset a b=273 deficit, but the bad set is not constructed, no bound on its size is available, and v/B is undetermined. This is a precise conditional gap, not an actual compensation.

### 3.6 Other bad local types

Bad p with e_p different from ell, wild ramification e_p>=p-1, or nontrivial residue degree are actual source places but are outside the tame totally ramified formulas. LOG-DOMAIN-EXTEND gives J=m^{n0}, I=m^{n0-e}; O_K/J is no longer one line, and the B-branch classification and volume formulas do not extend. No positive normalized volume formula is available; these branches are unknown, not compensation. They cannot be used to close the residual.

### 3.7 Ind1 factor permutations, Ind2 Ism, Ind3 log branches

- Full Ind1 is the procession automorphism group. Pure factor permutations change the tuple/min threshold; PROC proves the permutation hull is bounded by the original average and for uniform X=a gives -[ell(ell+1)/12]a log p < -a log p=Q_p. It does not create a positive compensation.
- Ind2 Ism/order-2 preserves the integer lattice; it can move the target hull branch but no positive normalized volume is proved. TC-H is missing.
- Ind3 log-link indeterminacy is upper semi-compatible; it does not add a positive volume beyond the allowed branch. The second log-link on the same path is empty for all e (LOG-DOMAIN).
- Factor swaps and full Ind1 cannot be used as actual target compensation without TC-A through TC-H/TC-S; ring isomorphism alone is not enough.

### 3.8 +infinity branch

The +infinity branch of Cor3.12 and n-permutations are separate from the finite all-bad formulas; they are not finite branches and are not covered by F1-F3. They do not supply a finite compensation.

## 4. Full-C residual with all finite branches

Under the corrected donor and CFTH, for a complete C whose bad places all lie in the tame e=ell type and B=O_K, the finite residual is

    Q_C - h_C <= sum_{p in S_bad} d_p log p - h_inf(C),       (F7)
    d_p = b_p(e+1)/12 - (b_p-1)/e - T_p,

with T_p=(1/(e m)) sum_j t_{p,j}. Every term d_p log p is positive for b_p>0 (F6); h_inf is bounded above by F4. Therefore

    Q_C - h_C <= sum_{p in S_bad} d_p log p - ((ell+5)/4) log pi.   (F8)

If the bad set contains a b=3 p=12301 place, the right side is at least

    408/41 log p - 13.164394... = 80.550577... natural.          (F9)

so this C cannot have Q_C <= h_C from the archimedean and B=O_K branches. Adding other B=O_K bad places only increases the right side. The only possible finite escape is a B=I contribution at some bad places (conditional, not actual), or an other-local-type contribution (unknown, no formula).

For b=273 the corresponding lower bound on the residual is 38883/41 log p minus the arch bound, enormous; no finite B=O_K place can cancel it, and the conditional B=I b=273 value still has deficit 38463/41. Only many conditional B=I b=3 places could in principle offset such a deficit, but that is not an actual source branch under the natural alignment and the bad set is not constructed.

## 5. Conclusion on actual compensation

Question: beyond the archimedean branch, is there any actual finite branch that compensates the b=3/b=273 residual?

Answer under the current corrected corpus: no actual finite branch supplies the needed positive compensation.

- Good finite, Kummer zero/unit small domain, tensor order: zero or negative; they cannot add positive volume.
- B=O_K bad places: positive residual for every b>0; they worsen the deficit.
- B=I bad places: conditional only; b=3 surplus 12/41 but B=O_K under the natural trace alignment, so B=I is not actual; v/B undetermined if alignment fails.
- Other bad local types: no proved formula; unknown, not compensation.
- Ind1/Ind2/Ind3, factor permutations, +infinity: no actual positive normalized volume without TC-A..H/TC-S; the withdrawn target-container step cannot be used.
- Archimedean: paper-level upper bound 13.164394 natural is smaller than the b=3 residual 93.7149712746 and vastly smaller than b=273; archimedean alone cannot compensate.

The residual is therefore not closed, but the open direction is precise: construct the actual complete bad set S_bad(C) and per-p local types/b_p; compute the finite mod-p v/full barGamma; and complete CFTH/TC-A..H/TC-S. A conditional aggregate B=I or an other-local-type branch could in principle change the sign, but no such actual branch is proved; the current sources do not supply one.

## 6. Proved, inferred, conditional, unknown

Proved / arithmetic-valid (not target closure):

1. Actual bad set is finite and nonempty by bad reduction; F_mod=Q gives alpha_p=1; the source supplies actual q-parameters but does not enumerate S_bad.
2. Exact b=3/b=273 residuals and F4 archimedean upper bound; F5/F9 shortfalls.
3. All B=O_K bad places have positive residual; A2/F6; uniform branch A never reaches Q_p.
4. B=I values and the exact v=0/v nonzero criterion; the conditional b=3 surplus 12/41.
5. PROC permutation bound and LOG-DOMAIN second-log emptiness.

Inferred / conditional:

6. F1-F3 full-C templates and F7-F8 assembly; CFTH and TC-A..TC-H/TC-S.
7. B=O_K under natural trace alignment; B=I conditional; d_p values for test p.
8. Actual archimedean h_inf and r_inf; only upper bound F4 is paper-level.

Unknown / missing:

9. Actual complete bad set, per-p e_p/b_p, and other local types.
10. Full finite image barGamma and the coordinate v when alignment fails.
11. Actual h_inf/angular terms and shell containment or positive radius.
12. Complete C, fixed q-volume class, row/Theta weights summed, target container TC-A..H/TC-S.
13. Any actual global h_C>=Q_C or complete global counterexample.

## 7. Next steps

1. Fix one complete C and enumerate S_bad(C) from the actual elliptic curve bad reduction; record each p, e_p, b_p, local type. This is the missing actual bad set, not a template.
2. For each tame p compute T_p and d_p; for non-tame p record the exact missing J=m^{n0} branch and do not apply T14/T15.
3. Compute the actual finite coordinate v (or full barGamma) to decide B=O_K versus B=I; do not assume v=0.
4. Compute the actual archimedean region/radii and angular terms; compare h_inf to the finite sum; use F4 only as an upper bound.
5. Complete TC-A..H/TC-S; only then use F7/F8 as a global residual.

Status: stage1 natural-language/exact arithmetic only. Lean/Project/kernel/comparator/independent review not run. target_accepted=false; complete C9/P6/ABC not proved.
