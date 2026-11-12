# DECOMP-EXISTING-LEMMAS — lana decomposition/inequality inventory

Status: READ-ONLY grep, 2026-11-12. No Lean file, no compile.
Scope: lana root Iut/. Goal: can existing lemmas prove M = A - R >= 0
(equivalently -A <= rhs, or V + gap >= (sF-1)A)?

Notation:
  A = D.qPilot.absLogQ; lhs = -A; rhs = (concreteVariantData D).rhsData.rhs;
  R = -rhs; M = A - R = A + rhs; gap = rhs + sFactor(nC)*A - V(hull VC).

## 1. Definitions and direction of the variant

- Corollary312Variant (Iut/Cor312/Statement.lean:89): X.qPilot.lhs <= X.rhsData.rhs.
- variant_iff_le_rhs (Iut/WallEquiv/Gap.lean:537):
    Corollary312Variant (concreteVariantData D) <-> -A <= rhs.
  Thus M >= 0 is EXACTLY the variant inequality; it is not a separate consequence.
- V + gap decomposition:
    gap_eq_rhs_add (Gap.lean:523):
      gap = rhs + sFactor(nC)*A - V(hull VC).
    Hence V + gap = rhs + sFactor(nC)*A, and
      V + gap >= (sF-1)*A  <->  rhs >= -A  <-> variant.
  (sFactor here is the lana sFactor; sF in the paper notation.)

## 2. Existing lemmas: names, lines, direction

Legend:
  G = proved source theorem (green-by-source; lana modules have no oleans in our tree);
  C = conditional theorem/implication with an unproved hypothesis;
  S = definition/statement only (no proof of the inequality).

| lemma | file:line | statement/direction | class | use for M>=0? |
|---|---|---|---|---|
| rhs_le | Iut/Implication/LogVolumeBound.lean:210 | rhs <= (1/proc.length) * sum_i (local bounds + capsule*log(sqrt2*pi)) | G+C (depends on inv/est) | NO: upper bound on rhs; M needs lower bound |
| globalVol_thetaHull_le | LogVolumeBound.lean:199 | globalVol(thetaHull i) <= sum local bounds + card*log(sqrt2*pi) | G+C | NO: upper bound |
| packetVol_hull_le | LogVolumeBound.lean:178 | packetVol(proj hull theta) <= placeBound | G+C | NO: upper bound |
| logVol_lgp_vcI_le_rhs | Gap.lean:510 | logVol(LGP*hull(VC)) <= rhs | G | Only gives rhs >= logVol; to get rhs >= -A needs logVol >= -A (SS) |
| logVol_le_rhs | Wall/Rss.lean:374 | logVol(U) <= rhs for adelic U in hull of a single theta image | G+C | NO: upper bound |
| rhs_le_rhsLit | Concrete/Literal.lean:84 | rhs <= rhsLit | G | Not a lower bound for rhs; literal is larger |
| variant_of_ss | WallEquiv/Basic.lean:168 | SSIneq D -> variant | C | Needs SSIneq; no proof of SS |
| variant_of_ss_gap | Gap.lean:543 | SSIneq D -> variant, via gap>=0 | C | Needs SSIneq |
| variant_of_wall | Wall/EtaAlg.lean:201 | Wall D A -> variant | C | Needs wall |
| variant_of_wall3 | Wall/MultiContainer.lean:418 | Wall3 -> variant | C | Needs Wall3 |
| variant_of_thm311 | LogLink/Thm311.lean:214 | Thm311 + XiPrinciple -> variant | C | Needs Thm311/Xi |
| variant_of_xi | WallEquiv/NonDerivable.lean:306 | Xi -> -a <= R | C | Needs Xi |
| ss_iff_le_rhs_sub_gap | Gap.lean:531 | SSIneq <-> -A <= rhs - gap | G | Equivalence; SS is hypothesis |
| variant_iff_le_rhs | Gap.lean:537 | variant <-> -A <= rhs | G | Target identity |
| variant_iff | Basic.lean:172 | variant <-> numerical wall <-> exists EtaAlg wall | G | Reformulation; no proof of wall |
| logVol_vcI_le_hull | VcI.lean:778 | V(vcI) <= V(hull vcI) | G | Lower bound for hull, not for rhs |
| logVol_hull_vcI_sub_eq | VcI.lean:762 | V(hullvcI)-V(vcI) = average defectPacket | G | Algebraic; uses defect >=0 |
| defectPacket_nonneg | VcI.lean:770 | 0 <= defectPacket | G | Nonneg local term; no rhs lower bound |
| ind2Term_nonneg | Gap.lean:756 | 0 <= ind2Term | G | Nonneg local term; no rhs lower bound |
| gapHullAt_eq | Gap.lean:919 | gapHullAt finite = sum ind2Term; infinite=0 | G | Rewrites gap; not an inequality for rhs |
| gap_eq_zero_of_ind2Term | Gap.lean:974 | all ind2Term=0 -> gap=0 | C (hypothesis all zero) | If gap=0, SS<->variant; still needs SS |
| ss_iff_variant_of_ind2Term | Gap.lean:986 | all ind2Term=0 -> SS<->variant | C | Needs SS |
| gap_nonneg | Gap.lean:514 | 0 <= gap | G | SS=>variant only, SS missing |
| gap_le_gapNoHull | Gap.lean:575 | gap <= gapNoHull | G | no direct lower rhs |
| gapNoHull_nonneg | Gap.lean:579 | 0 <= gapNoHull | G | no direct lower rhs |
| archPart_le_gapNoHull | Gap.lean:879 | arch part <= gapNoHull | G | upper bound |
| logVol_lgp_vcI_eq | Gap.lean:516 | logVol LGP hull = rhs - gap | G | Algebraic rewrite |
| ssIneq_of_noHull | Wall/MultiContainer.lean:99 | SSIneqNoHull -> SSIneq | G | Conditional on no-hull SS |

## 3. Can they be combined to prove M>=0?

No combination in the tree proves M>=0 unconditionally.

- The only existing inequalities with rhs on the correct side are:
  - logVol_lgp_vcI_le_rhs: logVol(LGP hull) <= rhs;
  - it does NOT give -A <= rhs unless one already has -A <= logVol(LGP hull), which is exactly SSIneq (or a stronger lower bound).
- rhs_le, globalVol_thetaHull_le, packetVol_hull_le, logVol_le_rhs all give UPPER bounds on volumes/rhs. An upper bound rhs <= B cannot imply the lower bound rhs >= -A.
- The implications variant_of_ss / variant_of_ss_gap / variant_of_wall / variant_of_wall3 / variant_of_thm311 all take SS/wall/Thm311 as hypotheses; those hypotheses are not proved in the audited source (Cor312VariantHolds is a def/hypothesis; see LANA-VARIANT-STATUS).
- gap_nonneg and ind2Term_nonneg/defectPacket_nonneg are positive local terms, but they only let SS imply variant (through gap) or rewrite the gap; they do not supply the missing lower bound on rhs.
- Equivalence ss_iff_le_rhs_sub_gap plus gap_nonneg gives:
    SSIneq => -A <= rhs - gap <= rhs => variant.
  This is variant_of_ss_gap; it still assumes SS.

## 4. Green source vs statement

- Green-by-source (proof present; no olean in current build):
  rhs_le (conditional on its inv/est), packetVol_hull_le, globalVol_thetaHull_le,
  logVol_lgp_vcI_le_rhs, logVol_le_rhs, logVol_vcI_le_hull,
  logVol_hull_vcI_sub_eq, defectPacket_nonneg, ind2Term_nonneg, gapHullAt_eq,
  gap_nonneg, gap_le_gapNoHull, gapNoHull_nonneg, archPart_le_gapNoHull,
  archDefect_nonneg, shellDefect_nonneg, rhs_le_rhsLit, ssIneq_of_noHull.
- Conditional theorems/implications (proof present but hypothesis unproved):
  variant_of_ss, variant_of_ss_gap, variant_of_wall, variant_of_wall3,
  variant_of_thm311, variant_of_xi, gap_eq_zero_of_ind2Term,
  ss_iff_variant_of_ind2Term, classicalABC_of_variant.
- Definitions/statements only (no proof of the desired inequality):
  Corollary312Variant, Cor312VariantHolds, Cor312LiteralHolds,
  RHSData.rhs, QPilotData.lhs, gap, gapNoHull, SSIneq (definition).
- No theorem in the audited tree proves:
    -A <= rhs, or
    V + gap >= (sF-1)A,
  without SS/wall/Thm311/other unproved hypothesis.

## 5. Verdict

1. Existing lana lemmas decompose rhs/volumes but the usable upper bounds
   (rhs_le, globalVol_thetaHull_le, packetVol_hull_le, logVol_le_rhs) point in
   the wrong direction for M>=0.
2. The only lower-bound bridge is logVol_lgp_vcI_le_rhs, which reduces
   M>=0 to SSIneq/lower bound on logVol(LGP hull); that hypothesis is not proved.
3. The conditional implications (variant_of_ss, variant_of_wall, variant_of_thm311)
   do not prove the variant; they only transport an unproved wall/SS/Thm311.
4. Therefore no combination yields rhs >= -A or V+gap >= (sF-1)A. The missing
   input is exactly a lower bound for rhs / an upper bound for R (SS or variant),
   not an additional algebraic manipulation.

Pointer: the variant status is in coord/LANA-VARIANT-STATUS.md; the no-hidden-bound
audit is there as well. No Lean file written; no compile claimed.
