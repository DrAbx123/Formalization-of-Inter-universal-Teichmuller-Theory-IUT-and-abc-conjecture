# DECOMP-POSITIVE-TERMS — known provable nonnegative local terms

Status: READ-ONLY inventory, 2026-11-12. No compile, no Lean file written.
Scope: lana root Iut/ (C0 definitions) plus Mathlib volume facts and the model file
tmp/sheaf/xif/paper/Mzk1C0Ind2ArchActual.lean. The model file is explicitly separated
from actual lana theorems; it is not proof-grade evidence for Gap.lean.

## 1. Evidence classes

A. ACTUAL-LANA: theorem/lemma in Iut/ source with a real statement and proof term.
   All of these currently have NO oleans in .lake/build/lib/lean/Iut (only
   Iut/Concrete/LocalConstruct/Haar.olean exists), so they are green-by-source,
   not green-by-build in this checkout.
B. MATHLIB: volume/ball/area positivity already in Mathlib; importable independently
   of lana.
C. MODEL-ONLY: Mzk1C0Ind2ArchActual.lean structures Ind2Data/ArchDefectData with
   asserted fields frac_nonneg, logp_pos, formula. These are not the actual lana
   ind2Term/archDefect; use only as a target shape, never as proof of an actual
   nonnegativity theorem.
D. UNKNOWN: no sign theorem exists; a new estimate is required.

## 2. ACTUAL-LANA nonnegative terms

| term | Lean declaration (file:line) | sign | proof source |
|---|---|---|---|
| componentVol of admissible region | admissible_haar_pos / admissible_haar_lt_top (Volume.lean:?; used Gap.lean:134) | positive/finite | definition of admissible |
| gapTerm | Gap.lean:646 gapTerm_nonneg | >= 0 | componentVol_le_leastHull |
| gapAt | Gap.lean:657 gapAt_nonneg | >= 0 | Finset.sum_nonneg + weight_pos |
| gap | Gap.lean:514 gap_nonneg | >= 0 | logVol_lgp_vcI_le_rhs |
| gapNoHull | Gap.lean:579 gapNoHull_nonneg | >= 0 | gap_nonneg + gap_le_gapNoHull |
| ind2Term | Gap.lean:756 ind2Term_nonneg | >= 0 | componentVol_le_of_subset; lgpComp_subset_theta |
| shellDefect | Gap.lean:442 shellDefect_nonneg | >= 0 | componentVol_le_leastHull_self |
| archDefect | Gap.lean:463 archDefect_nonneg | >= 0 | componentVol_le_leastHull_self + archLogShell_admissible |
| defectPacket | VcI.lean:770 defectPacket_nonneg | >= 0 | shellDefect_nonneg + archDefect_nonneg |
| orderVol | VcI.lean:102 orderVol_nonpos | <= 0 (negative side) | componentVol_le_of_subset |
| shell excess upper bound | VcI.lean:251 shellExcess_le_neg_sum_ordp_scalB_mul_log | >= 0? it is an upper bound; RHS sign | lattice sandwich |
| defectPacket_tame_le | VcI.lean:870 | upper bound; sign of bound | defectPacket_tame |

Supporting positivity of measures:
- haar_order_pos (VcI.lean:95): 0 < haar (order p c);
- haar_tensorLogShell_pos (VcI.lean:145): 0 < haar (tensorLogShell);
- haar_logShell_pos (LogShell.lean:441): 0 < haar (logShell);
- haar_archLogShell_pos (ArchLogShell.lean:401): 0 < haar (archLogShell);
- haar_integralAt_pos (Volume.lean:182): 0 < haar (integralAt);
- haar_smul_integralAt_pos (Volume.lean:170);
- toReal_haar_integralAt_pos (Volume.lean:188);
- weight_pos (ThetaRegion.lean:352): 0 < tupleWeight w;
- finrank_tensor_infinite_pos (Volume.lean:224);
- finrank_tensor_finite_pos (Volume.lean:230);
- archHullRadius_pos (ArchLogShell.lean:366): 0 < sqrt2*pi;
- isUnit_archScalar (ArchLogShell.lean:368).

Strictly positive ACTUAL-LANA terms:
- archDefect_pos (Gap.lean:468): 0 < archDefect c, provided two distinct maximal
  spectrum components and all complex; proof uses componentVol_archLogShell_lt_leastHull.
- gapTerm_infinite_pos (Gap.lean:853), gapAt_infinite_pos (:861), gapNoHull_pos (:871).
- Note: ind2Term_nonneg is only nonnegative; strict positivity at bad primes is OPEN
  in lana. shellDefect strict positivity in the wild case is OPEN (only shellDefect_nonneg).

## 3. Equality/zero classification (sign-adjacent, already green)

| statement | declaration | content |
|---|---|---|
| ind2Term_eq_zero | Gap.lean:771 | p not in badChars => ind2Term = 0 |
| thetaComponent_finite_of_not_bad | Gap.lean:725 | theta component equals shell at nonbad |
| shellDefect_eq_zero | Gap.lean:447 | tame + odd + unramified => shellDefect=0 |
| gapTerm_eq_zero | Gap.lean:802 | same hypotheses => gapTerm=0 |
| gapAt_eq_zero | Gap.lean:814 | same => gapAt=0 |
| archDefect_nonneg/pos | Gap.lean:463/468 | arch sign |
| support_gapAt_subset | Gap.lean:822 | support only at infinity, 2, bad chars, ramified |

These are proven zero/nonnegative statements; they do not give exact values.

## 4. MATHLIB volume positivity and ball/polydisc formulas

Available in Mathlib (verified by source search):
- EuclideanSpace.volume_closedBall, EuclideanSpace.volume_ball:
  Mathlib/MeasureTheory/Measure/Lebesgue/VolumeOfBalls.lean:311/328; formula
  (.ofReal r)^card * .ofReal (sqrt pi^card / Gamma(card/2+1)).
- InnerProductSpace.volume_closedBall/volume_ball (:347/358).
- Complex.volume_ball / Complex.volume_closedBall (same file; complex plane).
- volume_pi / Measure.pi_pi for finite products.
- addHaar_closedBall_eq_addHaar_ball, Measure.addHaar_ball,
  Measure.addHaar_closedBall (Haar basic/volume files).
- addHaarMeasure_unique (Mathlib/MeasureTheory/Measure/Haar/Basic.lean) for uniqueness.
- measure_pos of nonempty open sets, IsCompact.measure_lt_top, ENNReal.toReal_pos.
These give: volume of a closed ball of radius r>0 is >0 and finite; volume of a finite
product of unit discs is pi^N; volume of closed nonempty sets is positive in the
Lebesgue/addHaar measure.

## 5. MODEL-ONLY terms (not actual theorems)

Mzk1C0Ind2ArchActual.lean:
- Ind2Data.frac_nonneg / frac_lt_one / logp_pos: fields, not theorems about lana;
- ind2Term_nonneg, ind2Term_lt_logp, ind2Term_eq_zero_iff, ind2Term_pos_iff:
  MODEL statements for fracPart*logp;
- ArchDefectData.formula: a field asserting value = log(2^(N-1)!)/2^N;
- archDefect_model_nonneg: proved from the model fields.
These establish the target formulas' consistency/nonnegativity, NOT that lana
ind2Term/archDefect satisfy them. Do not cite them as C0 evidence.

## 6. UNKNOWN sign / new estimate needed

1. logShellRadius (VcI.lean:464): defined as sSup of -ordp over nonzero logShell
   elements; exists_isGreatest_logShellRadius (:469) gives an element y with
   logShellRadius = -ordp y but NO sign theorem. Whether logShellRadius >= 0 or
   > 0 is not available; a new estimate from logShell's norm bound is needed.
2. ind2Term strict positivity at bad primes: only ind2Term_nonneg; the exact value
   frac(x)logp (and x>0) is the C0 missing lemma. If frac(x)>0 then positive;
   otherwise zero. Need leastHull_thetaComponent_eq_pow_floor and x>0.
3. shellDefect strict positivity in wild case: only nonneg; exact value/estimate
   requires shellExcess/orderVol estimates (VcI.md 140-146), not just sign.
4. archDefect exact value: only nonneg/pos; exact log(N!)/(2N) requires the C0
   arch lemmas (ball/polydisc volume, arch hull scalar, Haar-Lebesgue comparison).
5. hullPacket_tame signed expression: theorem hullPacket_tame gives an equality to
   sum_c w_c * sum_j (1 - 1/e) logp. The right side is >=0 because e>=1 and logp>0;
   this nonnegativity is not a named theorem yet and requires a small new lemma
   hullPacket_tame_nonneg (Finset.sum_nonneg + weight_pos + ramIdx_pos).
6. vcIPacket_tame (VcI.lean:830) contains orderVol (<=0); its total sign is not
   asserted and should not be listed as positive without a new estimate.

## 7. Consequence for C0-PROOF-PLAN

- The already-positive local terms cover the nonnegativity half of the route:
  ind2Term_nonneg, shellDefect_nonneg, archDefect_nonneg/pos, defectPacket_nonneg,
  gapTerm_nonneg, and all measure positivity.
- The exact C0 formulas do NOT follow from these; they need the missing exact-value
  lemmas (C0-PROOF-PLAN items 2, 3, 6) and the Haar/Lebesgue comparison (item 4).
- logShellRadius and strict wild shellExcess are the two sign-sensitive quantities
  that still require new estimates; do not assume their sign.
- Model file Mzk1C0Ind2ArchActual must remain labeled MODEL; it is not a Lean proof
  of lana ind2Term/archDefect.
