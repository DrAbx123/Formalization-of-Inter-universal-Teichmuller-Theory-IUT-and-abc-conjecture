# C9 stage1: uniform bad-profile hull lower bounds

Task: task-148 (C9 stage1: uniform bad-profile hull lower bounds). Owner: volumedet.
Date: 2026-10-25. Natural-language stage1 research only. No Lean/Project/kernel edits;
no target changes; no fabricated closure. Deliverable written: only this file.

## 0. Status

This file records exact finite calculations from the formulas of
`C9-TAME-LOG-DOMAIN-20261025.md` §3–§7: equations (10), (14), (15), (17).
It does not close P6 and does not bound the whole output family C.
Only the specified profiles/subfamilies below are covered. `target_accepted=false`.

### 0.1 Correction 2 (task-149 / C9-IND1-GLOBAL)

Read after this file was written: `C9-IND1-GLOBAL-20261025.md` withdraws the
reading of `C9-TAME` §5 equations (11)-(14) as a target proof. Full Ind1 is the
procession automorphism group, not a finite label-translation group. Target
containment `F(Hull(...)) subset H_C` needs the target-container conditions
TC-A..TC-H and, for any symplectic-source use, TC-S (corrected
`H=Phi^{-1}(Sp)`, inferred trace/symplectic basis alignment, trace target
`Tr_{K/K^{d=1}}`, low-ramification `J=m`, standard-lattice lemma).

Consequently every claim below about the aligned hull `h_A`/`h_B` is a
**local profile calculation conditional on those source/target conditions**, not
an actual target-containment theorem. The numerical identities remain exact
for the displayed formulas; the words "actual" for target hull and any
downstream `h_C <= Q_C` inference are withdrawn. In particular b=3/B=O_K is a
conditional local value, not a target closure.


## 1. Setup

Take the tame bad local type of the context: K/Q_p finite, p odd, absolute
ramification e=ell prime, p>e+1, μ_e⊂Q_p, π^e=p u with u∈Z_p^×, m=πO_K,
J=log(O_K^×)=m. Use e=41, m=(e−1)/2=20, and the bad-profile index j=1..20
with r=j+1. For a bad qhat assignment b write

    b j² = s_j e + t_j,   s_j = floor(b j²/e),   1 ≤ t_j < e.

For e=41 this is b j² = 41 s_j + t_j. Admissible b in the context: b>0,
3|b, 41∤b (the cases checked in §7); b=3 and b=273 are the uniform examples.

Notation: h_p is the bad-profile contribution to the normalized hull log-volume;
all displayed lower bounds are in units of log p. Q_p/log p = −b/e for the
uniform (ρ=1) profile; for a general all-bad profile with bad mass ρ,
Q_p/log p = −ρ b/e.

## 2. Formulas used

(10) per-layer source-symplectic interior bound (general ρ):

    ell_j^Sp(ρ,b) = −c[(j+1)ρ − 1 + (1−ρ)^(j+1)]
                    − ρ^(j+1)[s_j + e^(−j−1)],   c=(e−1)/(2e).

For e=41, c=20/41; at ρ=1:

    ell_j^Sp(1,b) = −(20/41) j − s_j − 41^(−j−1).        (10-u)

This is a per-layer exact rational; it keeps the tensor-order/interior loss.

(14) single all-bad tuple, field hull:

    ν(H_{C,j,p})/log p ≥ −s_j − 1/e = −s_j − 1/41.       (14-u)

(15) aligned full-Ind1 actual hull, same profile:

    ell_j^aligned ≥ −ρ^(j+1)(s_j + 1/e),
    h_p^aligned/log p ≥ −(1/m) Σ_{j=1}^m ρ^(j+1)(s_j+1/e),  m=20.

At ρ=1:

    h_A(1,b) = −(1/20) Σ_{j=1}^{20} (s_j + 1/41)
             = −(41 Σ s_j + 20)/820.                    (15-u)

Using only the directly traceable principal-unit small domain subtracts the
per-layer loss j+1:

    h_direct(1,b) = h_A(1,b) − (1/20)Σ_{j=1}^{20}(j+1) = h_A(1,b) − 23/2.

(17) the two possible results for the finite integer-ring subfamily:

    branch B=O_K:  ν_A/log p = −s_j − 1/41;
    branch B=I:    ν_B/log p = −s_j + (r−1) − r/41
                              = −s_j + j − (j+1)/41.

For uniform ρ=1 weighting, branch A gives (15-u); branch B gives

    h_B(1,b) = (1/20) Σ_{j=1}^{20} [−s_j + j − (j+1)/41]
             = (−41 Σ s_j + 8380)/820.                  (17-u)

## 3. Uniform bad profile ρ=1: exact values

### 3.1 b=3

The s_j table (j: s_j / t_j) for b=3 is

    1:0/3  2:0/12  3:0/27  4:1/7  5:1/34  6:2/26  7:3/24
    8:4/28  9:5/38 10:7/13 11:8/35 12:10/22 13:12/15 14:14/14
    15:16/19 16:18/30 17:21/6 18:23/29 19:26/17 20:29/11.

Thus Σ s_j = 200 and

    h_A(1,3) = −(41·200+20)/820 = −8220/820 = −411/41,
    h_B(1,3) = (−41·200+8380)/820 = 180/820 = 9/41,
    Q_p/log p = −3/41.

Branch A is actual (source-symplectic/aligned hull) and leaves gap

    Q_p − h_A = −3/41 + 411/41 = 408/41.

Branch B is not proved to occur for the actual source; it is the larger
possible subfamily from (16). If B=I occurred, h_B=9/41 would exceed Q_p
by 12/41 for b=3, but the present source data do not select B=I.

Per-layer (10-u) for b=3: for example

    j=1:  −(20/41) − 0 − 1/41² = −(20/41) − 1/1681,
    j=20: −(400/41) − 29 − 1/41²¹.

and (14-u) gives ν_j/log p ≥ −s_j − 1/41 at each j.

### 3.2 b=273

Σ s_j = 19100 for b=273 (the s_j sequence is
6,26,59,106,166,239,326,426,539,665,805,958,1125,1305,1498,1704,1924,2157,2403,2663).
Then

    h_A(1,273) = −(41·19100+20)/820 = −783120/820 = −39156/41,
    h_B(1,273) = (−41·19100+8380)/820 = −774720/820 = −38736/41,
    Q_p/log p = −273/41.

Even the larger (unproved) B branch leaves

    Q_p − h_B = −273/41 + 38736/41 = 38463/41

and branch A leaves 38883/41. Thus b=273 is far from closure in this
uniform subfamily; this is not a statement about the full output family C.

### 3.3 All admissible b: exact success criteria

For ρ=1, branch A, h_A ≥ Q_p iff

    41 Σ s_j + 20 ≤ 20 b.

Since s_j ≥ (b j² − 40)/41 and Σ j²=2870, we have 41Σs_j ≥ 2870b−800.
Then 41Σs_j+20 ≥ 2870b−780 >20b for every b≥1; branch A never reaches
Q_p for positive b. (This is an exact inequality, not a numerical sample.)

Branch B, h_B ≥ Q_p iff

    41 Σ s_j ≤ 20 b + 8380.

Using 41Σs_j ≥ 2870b−800, the left side exceeds the right side for b≥4:
2870b−800 > 20b+8380 iff 2850b>9180, i.e. b≥4. For admissible 3|b the
only candidate is b=3, and direct exact evaluation gives 9/41 ≥ −3/41.
So in the uniform all-bad family, only b=3 and only the unproved B=I branch
could close; no positive b closes in the proven A branch.

## 4. General all-bad profile: exact ρ formula and ρ=1/2

Eq. (15) at general ρ is exact:

    h(ρ,b) = −(1/20) Σ_{j=1}^{20} ρ^(j+1)(s_j+1/41).

For the concrete general all-bad profile used in the context, ρ=1/2:

    h_{1/2}(b) = −(1/20) Σ_{j=1}^{20} 2^(−j−1)(s_j+1/41),
    h_direct,1/2(b) = h_{1/2}(b) − 23/2,
    Q_p/log p = −b/82.

Exact evaluations:

| b | h_{1/2} (zero Kummer integer domain) | h_direct,1/2 (unit-log small domain) | Q_p |
|---:|---|---|---:|
| 3 | −56311/10485760 ≈ −0.0053702354 | −120642551/10485760 ≈ −11.50537 | −3/82 |
| 1347 | −51496081/10485760 ≈ −4.91105 | −172082321/10485760 ≈ −16.41105 | −1347/82 |

Exact gaps Q_p−h (positive means the lower bound is still below Q_p):

| b | zero-Kummer gap | direct-domain gap |
|---:|---|---|
| 3 | −13419889/429916160 (bound above Q_p) | 4930615951/429916160 (fails) |
| 1347 | −4950820039/429916160 (bound above Q_p) | −6784199/429916160 (succeeds) |

The zero-Kummer integer-domain bound is already above Q_p for these b.
The direct principal-unit small domain has the exact success condition
82·h_direct,1/2(b)+b ≥ 0; exact finite evaluation over admissible b (3|b, 41∤b) in the checked range
b≤6000 gives failure through b=1344 and success from b=1347. The infinite tail
b↦b+41 is supplied by the affine-period formula recorded in the context §7;
this file does not re-derive that tail.

For comparison, the context's first-success table is reproduced exactly:
b=1347 is the first direct-domain success, and its gap is only −6784199/429916160.

## 5. Which hull/subfamily the bounds apply to

- (10-u) is the per-layer source-symplectic interior bound on the bad
  tensor order; it retains the tensor-order/integral-closure loss.
- (14-u) is the single all-bad field-tuple lower bound on the target
  holomorphic hull H_{C,j,p}; it is the strongest per-layer field form.
- (15-u) is a **conditional** aligned full-Ind1 formula for the specified
  all-bad tuple (same profile). It is not a target proof: full Ind1 is the
  procession automorphism group, and target containment requires TC-A..TC-H
  plus TC-S. The phrase "actual target hull" is withdrawn; only the exact
  numerical lower expression is retained.
- (17-u) concerns only the finite integer-ring subfamily: branch A=O_K is the
  source-side conditional branch; branch B=I is a possible larger subfamily
  whose occurrence is the finite mod-p question (16). Neither branch is a
  target-container theorem; TC-A..TC-H/TC-S remain required.

None of these is a bound for the entire output family C, and none includes
the archimedean place or other finite places. The uniform bad profile is the
specified local profile only.

## 6. p=12301 local realization

p=12301 is prime and p−1=12300=5·2460=5·60·41, so p−1 is divisible by 60·41.
The context §7 realization uses Tate q=p^3240 (full 30-torsion), qhat=π^1620,
K=Q_p(π), π^41=p, and the alternative q=p^2694 (full 6-torsion), qhat=π^1347;
2694 mod 41 = 29 and gcd(29,41)=1, so K=Q_p(E[41]) is unchanged. This supplies the bad local source realization; it does not
construct a complete global C with a good place and global Galois image.

## 7. Remaining gap / no fabricated closure

1. Uniform ρ=1, b=3: proven aligned branch gives h_A=−411/41 vs Q_p=−3/41,
   gap 408/41. The only possible closure is b=3 with the unproved B=I branch.
2. Uniform ρ=1, b=273: both A and B subfamilies are below Q_p; gaps
   38883/41 and 38463/41. No closure.
3. General ρ=1/2: zero-Kummer integer domain succeeds for b=3 and b=1347
   (and the context's checked range); direct unit-log domain first succeeds
   at b=1347. These are local profile results, not the full C comparison.
4. The full target h_C<Q_C for every complete C is still open: missing
   archimedean/other-finite weighted sum, global q volume-class identification,
   (for the B branch) the actual mod-p action on O_K/J, and the target-container
   conditions TC-A..TC-H plus TC-S. Equations (11)-(14) of TAME §5 are not a
   target proof and are not used as one here.
5. No inequality here is inserted as an assumption; the A/branch and B/branch
   are conditional local formulas, not target-containment facts. No full source
   comparison and no `F(Hull(...)) subset H_C` claim is made.

## 8. Source citations and status

Formulas and source claims are as recorded in
`C9-TAME-LOG-DOMAIN-20261025.md` §3–§7, citing IUT III Def1.1, Prop1.2,
Rmk1.1.1/1.2.2, Prop3.4/3.5, Thm3.11; Kondo, arXiv:2605.25428v2,
Theorem1.2/Lemma1.3/Definition3.2/Lemma3.3; Kondo, arXiv:2512.09231v1,
Theorem1.3. The external papers are cited through that context; this file
does not add new external claims.

Computation status: exact rational arithmetic only; no floating-point
assertion. Lean/Project/kernel/comparator/independent review not run.
statement_compiles=false, proof_body_checked=false, kernel_closed=false,
target_accepted=false.
