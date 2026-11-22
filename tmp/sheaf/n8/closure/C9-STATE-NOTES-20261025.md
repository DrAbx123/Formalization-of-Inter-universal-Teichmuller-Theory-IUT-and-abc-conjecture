# C9 P6 STATE NOTES (authoritative, 2026-10-25)

Purpose: durable notes for the P6 route so results/retractions are not lost.
Scope: fixed F_mod=Q uniform target only. Mixed profiles are E3 and EXCLUDED.

## 1. Sign convention (fixed)

F(C) := Q_C - h_C.
P6: h_C >= Q_C  <=>  F(C) <= 0.
F>0 is a P6 counterexample; F<0 means P6 holds for C.
C1 is h_C >= sum alpha_p H_p^Sp logp + h_inf, hence
C3: F <= D_C^Sp - h_inf  (UPPER bound on F).
C1 NEVER gives F >= ... .
The old task-245/254/256 "F>=80.55 / F>=8821" claims are RETRACTED (E48).

## 2. Local arithmetic (valid)

p=12301, e=41.
b=3: Q_p=-3/41 logp, H_A=-411/41 logp, H_B=9/41 logp,
     D3=408/41 logp=93.7149712746.
b=273: Q_p=-273/41 logp, H_A=-39156/41 logp, H_B=-38736/41 logp,
       D_A=38883/41 logp=8931.174578603, D_B=38463/41 logp=8834.703284644.

## 3. P6-TRUE route (user priority)

Need both:
(A) E1: no admissible complete C with b=273.
(B) b=3: H1 actual B=I, H2 R_B subset H_C, H3 h_C>=h_B+h_inf,
    H4 h_inf>=-S3=-(12/41)log12301=-2.7563226845
    => h_C>=Q_p, so b=3 P6.

Status:
E1: NOT PROVED. E_546 skeleton passes Def3.1(a)-(f), q-order 273 coprime 41,
mod41 G=H=GL2, F 2,3-smooth/41-free; M-prime III* additive becomes good
after F_sem; 2/3 semistabilize; no source bound b<273. Non-construction is
not impossibility.
H1: NOT PROVED. Kappa>=0 proved; kappa<=40 not proved. Model
y1=p^2+pi gives A=2, kappa=81, consistent with recorded structure.
H2: conditional/definitional under TC-B; actual B=I and TC-B/H_C missing.
H3: conditional on H2.
H4: NOT PROVED. IV gives only h_inf<=A_proc=11.5 log pi=13.164393687.

## 4. P6-FALSE / counterexample route (conditional)

E_546 has single multiplicative bad p, I_546, b=273, e=41,f=1.
M-prime III* and 2/3 become good after F_sem, volume 0.

Conditional chain:
JP: D^dag action preserves J=piO_K
G1: every possible image is a TAME row image
U/NPC: h_C <= H_B+h_inf
complete C + CFTH/TC/arch
=> b=273 F >= D_B-A_proc = 8821.538890956 > 0
=> P6 false.

Status:
JP: NOT a source theorem. IUT I Def4.1/4.10/Prop4.11 give categories up to
equivalence / outer G_K, not a chosen J action. H_A-lite only covers
H=Phi^-1(Sp), full Ind1 larger. JP is an extra hypothesis.
G1: NOT proved. TAME §6 classifies only the actual all-bad row subfamily,
not the whole C log/Theta/infinity possible-image family.
U/NPC: conditional on JP+G1+good/arch+TC.
Complete C: NOT constructed. Global BPS/F-prime-strip label/gluing to
Theta-pilot 0-column, arch theta/BPS, target column/q-volume, explicit
C_F/C_K/V/epsilon, CFTH/TC/arch are missing.

## 5. Retractions / scope errors (do not revive)

- Mixed bad/good profiles (0<rho<1): E3 profile change, NOT possible images
  of fixed F_mod=Q uniform target. Mixed P6 rescue/counterexample/U refutation
  are RETRACTED.
- Row max/sup: target readout is weighted average H_B, not max row. Using max
  changes normalization/object; not permitted.
- M-prime III* as selected bad: additive, not in admissible V_bad; after
  F_sem good, volume 0.
- b=273 no-go F>=8821/8918: RETRACTED (C1 gives upper bound on F only).
- b=3 B=OK F>=80.55 counterexample: RETRACTED.
- JP/G1/U/NPC as source theorems: NOT proved; conditional only.
- Kondo 2026: local p-adic only; no global BPS/0-column/complete C, no
  explicit y1/Tr/kappa.

## 6. Exact missing inputs (what to fill)

For P6-true:
1. E1: source theorem no admissible b=273 complete C.
2. Actual B=I: actual Kondo F(x0)/y1/Tr(y1), A=v_p(Tr y1)=1,
   kappa in [1,40].
3. R_B subset H_C: actual B=I + actual TC-B/target saturation.
4. h_inf>=-S3: B_I subset H_C,inf or global unit/point in H_C,inf.

For P6-false:
1. JP: full Ind1/Ind2/Ind3 D-prime-strip action preserves J.
2. G1: row exhaustion for full possible-image family.
3. U/NPC + complete C + CFTH/TC/arch.

## 7. Current verdict

P6: OPEN. No accepted proof, no accepted counterexample.
Lean: paused. target_accepted=false.

Key files:
C9-MASTER-V5-SCOPE-20261025.md
C9-P6TRUE-MASTER-20261025.md
C9-UNIFORM-B3-P6-20261025.md
C9-NPC-VERIFY-20261025.md
C9-JP-AUDIT-20261025.md
C9-KONDO-2026-Y1-20261025.md

## 8. Kondo 2026 source mining (task-354/356/358/360)

Files:
C9-KONDO-2026-Y1-20261025.md
C9-KONDO-2026-INTEGRAL-20261025.md
C9-KONDO-2026-BPS-20261025.md
C9-KONDO-2026-E1-20261025.md

Findings:
- Kondo 2026 (arXiv:2605.25428v2) is LOCAL p-adic anabelian/Hodge-Tate.
  It gives Phi, alpha_+, unit/log compatibility, local Sp donor, Q_p-basis
  y_i of k_+(G), JW presentation, local Hodge-Tate facts.
- It does NOT give: global BPS/Theta-pilot 0-column, global initial Theta
  data, arch theta/BPS, target column/q-volume, CFTH/TC, complete C, E1,
  explicit y1=F(x1), Tr(y1), Z_p-basis of J, primitivity, A=v_p(Tr y1)=1,
  or kappa.
- Kondo 2025 Theorem E only gives W=ker Tr, Tr(y1) in pZ_p nonzero, hence
  A>=1; no A=1 and no kappa range.
- Therefore Kondo cannot fill E1 or actual B=I. Local unit/log input remains
  usable for the JP k=0 local argument only.

Exact remaining gaps after Kondo:
E1: global BPS/Theta-pilot/0-column/target/arch/CFTH/TC/complete-C
    existence or nonexistence theorem.
b=3: actual y1/Tr(y1) or integral basis (A=1, y1 primitive, kappa in
    [1,40]); actual B=I; R_B subset H_C/TC-B; h_inf>=-S3.
Counterexample: JP (full Ind1 J-action) + G1 (row exhaustion) + U/NPC +
    complete C + CFTH/TC/arch.

Decision request from user: do E1 or b=3 R_B+h_inf; missing items are exactly
the source-global data above, not more local arithmetic. P6 still OPEN.

## 9. Lean formalization cross-check (BPS/ThetaPilot)

The existing Lean tree already has:
- Iut/Wall/BPS.lean: BPS (basic prime strips) definitions and isomorphism theory;
- IUTII/Kummer/SourceThetaPilotIQContainment.lean: Theta-pilot possibleImage orbit containment;
- IUTIII/.../SourceArithmeticThetaPilotBridge.lean: source-arithmetic Theta-pilot bridge.

But the bridge file explicitly records the same gap as the natural-language route:
- no constructed map from OriginalInput/ThetaPilotObject to the actual integral
  log-shell tensor over ArithmeticTensorTupleBlock;
- no proof theta-pilot generator lies in its image;
- no source-to-integral-tensor map; N4-N7 open;
- no non-degree-faithful comparison; full-hull degree-faithful bridge is
  impossible (negative calibration).

So the Lean side does not hide a ready-made global BPS/0-column/arch bridge.
It confirms the missing source-global comparison is real, not a note-taking gap.
P6: OPEN.

## 10. Branch/arch audits (task-362/363)

Q1: Is H_C the hull of ALL abstract B branches, or only the actual branch?
ANSWER: only the ACTUAL source/Ind1 possible images. TAME §6 defines
B = closed Z_p-span over the actual Gamma; B=O_K if barGamma preserves
l=O_K/J, B=I if some actual gamma moves l. Only one actual branch.
IUT I Def4.10/Prop4.11 + III Cor3.12 possible images are the actual
Theta-pilot orbit, not an independent union of B choices.
Consequence: R_B subset H_C requires actual B=I + TC-B. If actual B=O_K,
R_B is not available. Treating both branches as possible is a profile change.
So b=3 P6 is NOT independent of kappa.

Q2: Is B_I an actual arch possible image, giving B_I subset H_C,inf and
h_inf>=0?
ANSWER: NOT proved. IV gives only H_C,inf subset pi^(j+1)B_I and
logvol(B_I)=0, logvol(pi^(j+1)B_I)=(j+1)logpi; B_I subset pi^(j+1)B_I,
so IV is compatible with B_I subset H_C,inf but does not imply it.
B_I-zero is normalization only. No actual r_v/angular/unit-ball image.
Conditional only: if B_I subset H_C,inf then h_inf>=0, and with R_B
b=3 B=I P6 follows strongly.

Current exact b=3 requirements: actual B=I (+TC-B/R_B) AND
(h_inf>=-S3 or B_I subset H_C,inf). Both unproved.
P6: OPEN.

## 11. P6 true is exactly IUT III Corollary 3.12

IUT III (text: sources/IUT-III.txt, 199 pages, extracted from IUT-III.pdf)
states Corollary 3.12 / Theorem B:

  -|log(Theta)| in R and
  -|log(Theta)| >= -|log(q)|,
  equivalently C_Theta >= -1 for any C_Theta in R with
  -|log(Theta)| <= C_Theta * |log(q)|.

Here:
  -|log(Theta)| = procession-normalized mono-analytic log-volume
                   of the holomorphic hull of the union of possible
                   images of the Theta-pilot object (Ind1/Ind2/Ind3);
  -|log(q)|    = log-volume of the q-pilot object.
In C9 notation this is exactly h_C >= Q_C (up to sign/normalization), i.e.
P6 true for the covered profile.

Therefore P6 true is not an independent C9 conjecture: it is a special
case of IUT III Cor 3.12. The C9 route is an alternative attempted
reconstruction; it is blocked at the same global BPS/0-column/target/
arch input as Cor 3.12.

Lean status of Cor 3.12 (read-only):
LeanFormal/IUT/IUTIII/Corollary312/ has 90 modules. It contains:
- Obligations.lean: IPL, SHE, APT status = pending;
- StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction.lean:
  cor312CThetaLowerBound is proved from Cor312ComparisonData CARD data;
  the paper's source-side carrier/hull/log-volume content is frozen as named
  cards, not proved; O1 degree-faithful hull volume = top; IQHull interface
  is an interface, not actual carrier.
So Lean does not currently give a black-box-free proof of IUT III Cor 3.12.

Consequence: P6 true requires either
  (a) formalizing/filling IUT III Cor 3.12 proof (IPL/SHE/APT + StepXI
      holomorphic-hull/source-arithmetic bridge), or
  (b) completing the C9 alternative (E1 + b=3 H1-H4),
  or (c) accepting Cor 3.12 as source theorem, which the user forbids as
      black box.
P6: OPEN.

## 12. Cor 3.12 natural-language proof skeleton (not black box)

Source: IUT-III.txt lines 1155-1184 (Theorem B/Cor 3.12 statement),
10157-10240 (proof setup), 10570-10720 (Steps xi-a..g),
7529-7868 (Remark 3.9.5 Ob1-Ob9).

Steps:
xi-a IPL: multiradial output possibilities are linked by full
  F^{value x mu}-prime-strip poly-isomorphisms to the fixed q-pilot input;
  F^value part full polyisomorphism, F^{unit x mu} part subject Ind1/2/3.
xi-b SHE: all operations are expressible relative to the fixed 1-column
  arithmetic holomorphic structure and fixed q-pilot log-volume.
xi-c APT: the Theorem 3.11 construction algorithm is not a set-theoretic
  region map; it is simultaneously valid/executable in domain/codomain,
  with theta functions/values hidden (HIS).
xi-d: take holomorphic hull of the union of possible images in 1,circ U;
  express via rank>1 localizations of arithmetic vector bundles;
  det^{tensor M} gives an arithmetic line bundle comparable to q-pilot;
  procession-normalized log-volume gives -|logTheta| for hull and
  -|log q| for q-pilot image; Ob3-3 allows omitting determinant for
  log-volume; log-Kummer 1-column rectifies vertical shift.
xi-e: SHE means output possible log-volumes are linked to the fixed
  q-pilot value -|log q|.
xi-f: hence -|log q| lies in R_{<= -|logTheta|}; so
  -|log q| <= -|logTheta|; CTheta>=-1. WLOG -|logTheta|<0; if >=0 trivial.
xi-g: two tautologically equivalent computations of q-pilot log-volume
  (Fig. I.8); first tensor power only (xi-h scope).

Exact source inputs/gaps:
G1 Theorem 3.11 (Ind1-3/IPL/SHE/APT) used as theorem.
G2 Remark 3.9.5 Ob1-Ob9 determinant weights/normalization left to reader.
G3 -|log q| in R follows from SHE, not independent computation.
G4 hull existence/compactness/log-volume finiteness from Prop 3.9.
G5 vertical log-Kummer rectification cited, not expanded.
G6 |log q|>0 / -|logTheta|<0 WLOG.
G7 first tensor power only.

This is a universal proof schema: it does NOT require constructing an
explicit complete C. To make P6 true black-box-free, the named source
inputs G1-G7 must be proved/formalized, not assumed. Natural-language
proof is possible by expanding G1-G7; encoding in Lean requires the same
infrastructure (global BPS/0-column/hull/log-volume).
P6: OPEN (but P6 true is exactly this Cor 3.12 schema).

## 13. Cor3.12 A1-A3 schema (no explicit C)

A1 q-pilot input/representation:
  q-pilot at (1,0) represented on 1,circ U_Q via Kummer/log-shells;
  log-volume fixed -|log q|, not subject to Ind1-3;
  multiradial algorithm gives possible output data in 1,circ U
  with IPL/SHE. Source IUT III 10166-10180, 10582-10626.

A2 determinant/log-volume comparison:
  output hull data are rank>1 arithmetic vector-bundle localizations;
  det^{tensor M} (Remark3.9.5 Ob3; weighted powers/O(-); Ob3-3 allows
  omitting determinant for log-volume) makes them comparable to the
  q-pilot line bundle; procession-normalized log-volumes are
  -|logTheta| and -|log q|, both in R_{<= -|logTheta|};
  log-Kummer 1-column rectifies vertical shift.
  Source 10641-10681, 7735-7868.

A3 fixed q-pilot value => inclusion:
  by SHE construction valid under fixed input pilot log-volume -|log q|;
  hence -|log q| in R_{<= -|logTheta|} => -|log q| <= -|logTheta|
  => CTheta>=-1. Source 10682-10715.

A1+A2+A3 => Cor3.12/Thm B. This is a tautological construction-computation
comparing two representations of the same q-pilot log-volume, universal
over admissible Theta/C data. It does NOT require an explicit complete C.
P6 true does not need explicit C; it needs this universal schema plus the
C9 target translation.

Remaining C9-specific step: identify C9 h_C with -|logTheta| and Q_C with
-|log q|, including canonical/normalized factor d, B_I-zero, procession
average, C6 alignment (tasks 380/381). If exact, P6 true follows from
A1-A3 without constructing explicit C.
P6: OPEN pending A1-A3 proof + C9 translation.

## 14. Canonical target decision and arch factor (task-395/400)

CANONICAL IS THE PAPER TARGET. Do not replace P6 by a normalized object.

P6_can:
  for every admissible C, Q_can <= h_can,
  Q_can=-|log q|, h_can=-|logTheta|.

P6_norm is only an auxiliary C6/Lean surrogate:
  Q_norm=Q_can/d, h_C=h_bad_can/d+h_inf, d=41.

Exact arch relation (arbitrated from Lean C6 definitions):
  C6 normalizedLogVolume is defined on the FINITE ArithmeticTensorTupleBlock
  with 1/D factor, D=d=41; no arch component.
  C9 global h_C adds B_I-zero h_inf undivided.
  h_C = h_bad_can/d + h_inf.
  h_can = h_bad_can + h_inf = d*h_C - (d-1)*h_inf.
  Q_can = d*Q_norm.
  Cor3.12 Q_can<=h_can gives
    Q_norm <= h_C - ((d-1)/d)*h_inf.
  P6_norm follows only if h_inf>=0; not implied otherwise.
  Mixed target Q_can<=h_C is invalid.

The existing Lean candidate PaperP6C6AlignedTarget uses normalized quantities;
if it is to be identified with paper P6_can, a comparator/normalization
theorem is required. It cannot be assumed.

## 15. Natural-language A1/A2/A3 status (P6_can)

A1: smooth source-input.
  full poly-isomorphism class of F^value x mu prime-strips,
  Q_pilot object determined by generators up to torsion,
  -|log q| well-defined. No canonical scalar q needed.

A2: exact identity stated, source gaps remain.
  deg(det^tensor M(E_H))/M = deg(det E_H) = mu_log(H) = -|logTheta|.
  Need: E_H/det construction, O(-) degree, M formula, N_v exponents,
  hull approximant, vertical shift, tensor-twist/upper-semi compatibility.

A3: exact membership route, source approximation gap.
  -|log q| in R_{<=-|logTheta|} via L1 full-poly invariance,
  L2 SHE-to-membership, L3 hull/log-volume monotonicity.
  IUT III says "perhaps only up to some sort of approximation";
  exact membership or signed error is not yet derived.

T_can: C9Hull=IIIHull, C9QPilot=IIIQPilot; object identity, open/conditional.

P6_can: conditional on A2/A3/T_can; P6 OPEN.

## 16. A2 scale-invariance insight (task-401)

Canonical ABSOLUTE -|logTheta| is not fixed by Prop3.9; only a common
packet/procession normalization nu is fixed. But the exact A2 result is a
ratio identity in a common normalization:

  deg_nu(L_H)/M = deg_nu(det E_H) = mu_log_nu(H) = -|logTheta|_nu,
  deg_nu(L_q) = -|log q|_nu.

Under a change nu' = c*nu, BOTH sides scale by c. Therefore the inequality
  -|log q|_nu <= -|log Theta|_nu
is invariant under the common normalization c. P6 does not require a
canonical absolute c; it requires that h_can and Q_can use the SAME c.

Consequence for A2 smoothness:
- A2 ratio identity is sufficient for the P6 inequality.
- The missing G1-G7 are source details for the absolute identity; they do
  not block the scale-invariant inequality if both sides use the same
  normalization.
- The remaining substantive A3 gap is exact membership up to the source's
  "perhaps only up to some sort of approximation".
- T_can is the statement that C9/paper h,Q use the same source normalization;
  if paper target, definitional; if Lean normalized target, comparator.

So A2 can be treated as smooth at the inequality level; A3 is the remaining
hard node. P6: OPEN.

## 17. A3 approximation closeout (C9-CAN-A3-CLOSEOUT)

IUT III xi-f says the construction is a construction of the input q-pilot
log-volume "perhaps only up to some sort of approximation, as a result of
various indeterminacies", and then says the inclusion
-|log(q)| in R_{<=-|logTheta|} "follows formally".

Remark 3.12.2(fitw), lines 10977-11022, gives the logical relation:
  (q-itw) => (q-itw) AND (Theta-itw/indets) => (Theta-itw/indets),
where "/indets." means up to (Ind1),(Ind2),(Ind3); the second arrow is purely
formal; the AND follows from the AND of (citw) via the subquotient operations
of Remark 3.9.5(viii).

Therefore "approximation" is the indeterminacy quotient, not an unknown
numerical epsilon. R_{<=h_can} is the set of possible output log-volumes up
to Ind1/2/3; exact membership means Q_can is a special case of the Theta-pilot
output log-volume under that quotient.

A3 closeout schema:
  A3.1 q-pilot coric input (A1)
  A3.2 multiradial algorithm constructs Theta-intertwining simultaneously
       with/without invalidating q-intertwining
  A3.3 formal AND via subquotient operations
  A3.4 log-volume of Theta-intertwining gives h_can and R_{<=h_can}
  A3.5 Q_can is the q-pilot special case; Q_can in R_{<=h_can}
  A3.6 Q_can <= h_can.

Residual formalization gap: the subquotient operations/AND of Remark3.9.5(viii)
are cited, not expanded. No arbitrary epsilon; no target/normalization change.

A-chain status:
  A1 source-input smooth.
  A2 ratio identity sufficient; absolute canonical identity open but not needed.
  A3 closeout via fitw logical relation; residual subquotient formalization.
  T_can definitional for paper target; comparator for Lean normalized target.

P6_can: A1+A2 ratio+A3 fitw+T_can => Cor3.12 => P6_can.
P6: OPEN pending fitw/subquotient expansion and T_can.

## 18. A3 closed-loop expansion (C9-CAN-A3-CLOSED-LOOP)

Source expanded: Remark3.9.5(viii),(ix), lines 8383-8431; (citw) 10913-10943;
(fitw) 10977-10998.

Closed loop:
  q-pilot codomain -> LGP-link to domain -> (sQ1),(sQ2) polyisomorphisms
  -> (sQ3),(sQ4) compatible with log-Kummer -> back to q-pilot.

Only a closed loop completes the projection of Theta-intertwining onto
q-intertwining; skipping sQ3/sQ4 breaks the loop. This realizes the AND:
  (q-itw) AND (Theta-itw/indets).
Then log-volume gives Q_can in R_{<=h_can}.

Residual A3 gaps:
  CL1 formal quotient indeterminacies (cQ3),(cQ4),(Ob9-1)
  CL2 log-Kummer compatibility of sQ3/sQ4
  CL3 subquotient AND identification with (citw) AND.
These are source-internal expansions, not epsilon/normalization/target changes.

Source ledger: C9-CAN-A-SOURCE-LEDGER-20261025.md
Wrong-route ledger: C9-CAN-A3-WRONG-ROUTES-20261025.md
P6_can conditional on CL1-CL3 + T_can. P6 OPEN.

## 19. CL1-CL3 expanded (C9-CAN-A3-SUBQUOTIENT-EXPANDED)

CL1 formal quotient indeterminacies:
  Ob9-1 lines 8145-8161: tensor-power-twist, ⊼-formalism, log-link iterates
  have no effect on comparability; they are compatibility conditions for
  coarse invariants such as log-volume. Ob9 realified semi-simplification
  induces a natural bijection between hull log-volumes in domain/codomain.
  Expanded: formal quotient compatible with log-volume; no numerical epsilon.

CL2 sQ3/sQ4 log-Kummer compatibility:
  sQ3 lines 8183-8186: positive tensor powers of determinants of hulls plus
  ⊼-formalism.
  sQ4 lines 8187-8191: vertical-shift adjustment via log-Kummer.
  cQ3 lines 8264-8345: det^tensor M(phi(PB)) objects with G_v/O^×μ_Fv actions
  and ⊼-category quotient.
  cQ4 lines 8346-8366: log-Kummer vertical shift compatible with F^⊣×μ data
  up to log-link iterates.
  Expanded: sQ3/sQ4 compatibility is exactly (cQ3),(cQ4), not approximation.

CL3 subquotient AND:
  closed loop through sQ1-sQ4 (lines 8373-8431); skipping sQ3/sQ4 breaks loop.
  citw lines 10913-10943: simultaneous q-intertwining and Θ-intertwining.
  fitw lines 10977-11022: (q-itw)=>(q-itw)AND(Θ-itw/indets)=>(Θ-itw/indets),
  second arrow purely formal.
  Expanded: closed loop realizes subquotient AND; q-pilot log-volume is
  projection/special case of Θ-pilot output log-volume; Q_can in R_{<=h_can}.

Residual: formal encoding of subquotient/realified-semi-simplification
operations; no epsilon/normalization/target change.

A3 wrong-route exclusion ledger:
  C9-CAN-A3-WRONG-ROUTES-20261025.md
  Excluded: numerical epsilon, d-normalization/P6_norm, mixed target,
  h_inf>=0/B_I rescue, mixed profiles/row max, q_v/full q factor82,
  canonical 0-column equality, geometric max, C1 sign, b273 no-go,
  global unit/product formula, epsilon->0 closure, canonical absolute A2,
  Lean normalized target. Only surviving route: fitw logical relation +
  Remark3.9.5(viii) subquotient AND.

## 20. cQ3/cQ4 derivation and correction

C9-CAN-A3-COMPATIBILITY-DERIVATION-20261025.md.

CORRECTION: 'sQ3/sQ4 = cQ3/cQ4' was wrong. cQ3 is compatibility of sQ3;
cQ4 is compatibility of sQ4. cQ3+cQ4 do NOT imply the composite closed loop.

cQ3 derived:
  hull stabilized by O_K^× (Ob1/Ob2)
  ⇒ O_K^× action on E_H
  ⇒ functorial det^tensor M inherits action
  ⇒ localization trivial for M sufficiently divisible
  ⇒ O^×mu_Fv root-of-unity action
  Frobenioid supplies G_v action; ⊼ quotient preserves actions.
  = cQ3.

cQ4 derived:
  log-link O^×→log-shell m
  vertical shift adds log(O_K^×)=m
  F^⊣×mu data records log modulo m
  Kummer iso aligns log-shell/value group up to log-link iterate
  log-link/Kummer G_v-equivariant.
  = cQ4.

Not derived:
  closed loop is a separate source assertion (Remark3.9.5(ix)).
  sQ5 is incompatible with F^units×mu (iQ5), final coarse quotient.
  xi-f exact membership is source formal conclusion.
P6_can conditional on closed loop+xi-f; P6 OPEN.

## 21. Closed loop and xi-f membership derived

C9-CAN-A3-CLOSED-LOOP-DERIVED-20261025.md.

Key: F^value×mu data determine the full-poly-isomorphism class
(Def2.4/Def3.8). Then:
  LGP-link + sQ1/sQ2 polyisomorphisms + cQ3/cQ4-compatible sQ3/sQ4
  produce an F^⊩▶×mu-prime-strip with the same F^value×mu data as the q-pilot S_q.
Hence composite is a full poly-isomorphism S_q -> S_q: closed loop.
Then S_q is a possible output; Q_can in R_poss subset R_{<=h_can}; Q_can<=h_can.

Residual assumptions CL-A..CL-D:
  CL-A F^value×mu data determine full-poly class;
  CL-B sQ1/sQ2 compose with LGP-link;
  CL-C sQ3/sQ4 produce same F^value×mu data (cQ3/cQ4);
  CL-D Ob9-1 formal indeterminacies no effect on comparability; R_poss defined up to them.
These are structural, not epsilon/normalization/target changes.
P6_can conditional on CL-A..CL-D. P6 OPEN.

## 22. Cor3.12 unconditional NL review result

C9-COR312-UNCONDITIONAL-NL reviewed by 8 agents.
VERDICT: Cor3.12 statement/source theorem ACCEPTED.
Self-contained unconditional NL proof REJECTED.

Decisive gaps:
- xi-f exact membership vs source's "perhaps only up to some sort of approximation";
  no signed epsilon/bound, no exact output element.
- q-pilot value is fixed INPUT, not subject to Ind; R is OUTPUT values.
  IPL/SHE link prime-strips/constructions, not numerical value membership.
- closed loop is a source assertion (Remark3.9.5(ix)); cQ3/cQ4 give individual
  compatibility only, not composite loop.
- Ob9-1 says formal indeterminacies no effect on comparability; does not give
  natural bijection between domain/codomain log-volume sets.
- Ind1/Ind2 descriptions incomplete/wrong; finiteness/compactness under-expanded.
- WLOG -|logTheta|<0 branch omitted.

Conclusion:
  Cor3.12 paper source theorem: ACCEPT.
  Our unconditional NL proof: REJECT as self-contained.
  P6_can: conditional on Cor3.12/source xi-f.
  P6 OPEN. No Lean.

## 23. Paper-level Cor3.12 review split

C9-COR312-PAPER-PROOF reviewed.
- kummer: ACCEPT paper-level proof; reject only as first-principles.
- qside: ACCEPT source theorem/paper-level under Theorem3.11 hypotheses; reject
  hypothesis-free 'unconditional' and C9 target claims.
- transport: REJECT as paper-level proof: xi-f 'constitutes a construction'
  does not imply membership; source separately asserts inclusion. Correctly
  quoted but not derived; determinant/xi-d omitted; Ind1/2/3 identification
  unsupported.
- iplsheapt: pending.

Net:
  Cor3.12 source theorem: ACCEPT (paper-level, under Theorem3.11 hypotheses).
  Our NL proof as independent/paper-level proof: split; transport rejects.
  xi-f exact membership: source assertion, not derived.
  Lean unconditional Cor3.12: not available; Lean has StepXIContract fields,
  no construction of the contract from source.
  P6 OPEN. No black box claimed.

## 24. Final review sweep (paper-level Cor3.12)

kummer: ACCEPT paper-level; reject first-principles.
qside: ACCEPT source theorem under Thm3.11 hypotheses; reject hypothesis-free
        and C9 target claims.
transport: REJECT paper-level proof; xi-f is source assertion/paraphrase.
iplsheapt: REJECT Section2 hull/finiteness: VQ index infinite; compact containers
           do not imply H compact; Prop3.9 finiteness cited not derived.

Net:
  Cor3.12 source theorem: ACCEPT (paper-level, source hypotheses).
  Our natural-language proof: NOT accepted as self-contained/paper-level proof
  (only a source-faithful exposition).
  Lean: StepXIContract conditional theorem zero-sorry; construction of the
  contract from source is pending; unconditional Lean would require axiom/sorry.
  xi-f exact membership and finiteness/hull compactness remain source gaps.

BLOCKED: unconditional natural-language Cor3.12 and unconditional Lean 3.12
cannot be closed from the current corpus without accepting IUT III Theorem3.11/
Prop3.9/Remark3.9.5/xi-f as source theorems or proving them first.

## 25. 'inclusion follows formally' = named sorry at our level

Source xi-f ends:
  'The inclusion -|log(q)| in R_{<=-|log(Theta)|}, hence also the inequality
   -|log(q)| <= -|log(Theta)| ... then follows formally.'
At our level, using this sentence without an independent derivation is
equivalent to:
  sorry xi_f : -|log q| ∈ R_{<=h_can}.
It is not a proof step we have expanded. The source may regard it as formal,
but we have not produced:
  - an exact output possibility D with logVol(D) = -|log q|;
  - or a signed epsilon with sign/bound;
  - or a definitional identification of 'constitutes a construction' with
    membership in R.
Therefore our natural-language proof contains a named sorry at xi-f.
Cor3.12 remains accepted only as the paper's source theorem, not as our proof.
P6/Lean remain blocked until xi-f is derived or explicitly accepted as source.

## 26. Tautology audit

C9-TAUTOLOGY-AUDIT-20261025.md.

YES: the final implication is tautological.
Define R_{<=h} := {x in R | x <= h}. Then
  q in R_{<=h} => q <= h
is true by definition, not a theorem.
Lean StepXIContract has fields q_le_target,target_le_theta; cor312 is le_trans.
C9P6CanFormal.lean p6_can is Rposs_upper Qcan Sq_possible; same wrapper.

The only real content is xi-f: Qcan in R (q-pilot is a possible output
log-volume). Source asserts it formally; we only have it as named sorry.

Non-tautological options not yet proved:
N1 explicit output U with logVol=Qcan (or local exact equality summing to Qcan);
N2 exact deg(L_H)=deg(L_q) in fixed normalization;
N3 R closed + Qcan limit of output values with compactness/continuity.
Current local/closed-loop/determinant attempts did not establish N1-N3.

Conclusion: Stage1 contract is an honest named-sorry boundary, but it does
NOT reduce the theorem; it names the content xi-f.
P6/Cor3.12 unconditional proof: not achieved. No Lean.

## 27. C1 independence result (8 agents)

C1:
  exists possible output D0 (mod Ind1/2/3) with logVol(D0)=Q=-|log q|.

A1=Theorem3.11, A2=Prop3.9, A3=Remark3.9.5 assumed.

Five independent routes + adversarial review agree:
  A1+A2+A3 do NOT imply C1.

Reasons:
- APT not set-theoretic transport; no evaluation map.
- HIS forgets theta values; no numerical Q.
- SHE is expressibility, not existence at fixed value.
- Ind1/2 preserve log-volume; Ind3 only upper-semi.
- closed loop returns q-pilot INPUT; not output membership.
- cQ3/cQ4 compatibility only; cQ3+cQ4 do not imply loop.
- Ob9-1 comparability, not attainment.
- determinant degree functional equality, no output-to-q-pilot identification.
- additivity conditional on already assembled object; no surjectivity.
Abstract models satisfy A1-A3 but fail C1 (non-implication), no source-valid
counterexample.

Conclusion:
  A1+A2+A3+C1 => Cor3.12.
  A1+A2+A3 => Cor3.12: FALSE/not derivable.
  C1 is an independent source compatibility/existence lemma (xi-e/xi-f).
  To prove 3.12 unconditionally, need C1 from deeper IUT or accept it as
  source assumption. No Lean. P6 OPEN.

## 28. C1 master synthesis (task-434)

C9-C1-MASTER-20261025.md, 264 lines.

Exact C1: exists output D0 in O (multiradial possible output data mod Ind1/2/3)
with logVol(D0)=Q=-|log q|; equivalently Q in R_possible=logVol(O).
Separated:
  C1_xi (Q in R<=h formal/approx xi-f)
  C1_approx (signed epsilon)
  C1_scalar_weak (Q<=h)
P6_can needs C1 or exact xi-f membership.

A1/A2/A3 give only R_possible subset (-inf,h]; no evaluation/attainment map,
no surjectivity, no representative. C1 NOT derivable.
Strongest valid derivation:
  Hloc (local outputs with logVol=Q_v)
  + Hasm (source-allowed assembly preserving additivity)
  + Hcompat (assembled object compatible with Ind/q-pilot)
  => C1.
E1/E2/E3 (attainment/representative/approx-zero) => C1.
No source-valid counterexample; abstract O={0},logVol=id,Q=1 and local
no-assembly models show no formal implication, not source counterexamples.

Conclusion:
  A1+A2+A3+C1 => Cor3.12.
  A1+A2+A3 => Cor3.12: NOT derivable.
  C1 is independent open attainment/compatibility lemma.
No Lean. P6 OPEN.
