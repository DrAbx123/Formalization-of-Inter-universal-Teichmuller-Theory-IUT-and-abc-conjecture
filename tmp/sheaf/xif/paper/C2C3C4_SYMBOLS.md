# C2/C3/C4 symbol reconciliation (kurt draft, 2026-11-17)

Route ruling (Lead): C2 q-side uses Q := actualQPilotMagnitudeClassical, M := Q/(2l),
q_P5 := -M. The v2 expression (qPilotMagnitudePaper_v2) is an AUDIT/ALTERNATIVE expression,
NOT the route Q; no v2-to-theta per-fibre bridge is required.

| symbol | meaning | exact declaration | file:line | status |
|---|---|---|---|---|
| Q | actual global normalized q-divisor degree (unrooted) | actualQPilotMagnitudeClassical | BadPlacePaperNormalizedTargetBridgeActual.lean:63 (rfl = s13QPilotCoefficientSum) | accepted |
| M | Q/(2l) | Mzk1URQNormalizationActual.urM_eq_half_qMagnitude | Mzk1URQNormalizationActual.lean:69 | accepted (local q-mass link) |
| q_P5 | -M | david URC2AssemblyActual.qP5 (currently -M_paper_v2; switch to -M per Lead) | Mzk1URC2AssemblyActual.lean:44 | needs david switch |
| theta | actual normalized root-hull log | actualThetaHullLogRoot | BadPlaceThetaHullCorrectionFormulaActual.lean:78 | accepted |
| theta_lam | K-side lambda/d_mod weighted readout | ksThetaHullLogRoot_lam | Mzk1URThetaKSideActual.lean (lambda batch) | accepted (unconditional) |
| H_pkt | packet weighted hull | ucWeightedHpkt (thetaLamWeight T) packetV | Mzk1UCC3ProducerActual + lambda adapter | accepted; actual V pending |
| C2 lower | -Q <= theta | p6SandwichChain_neg_M_le_HTheta : -actualQPilotMagnitudeClassical T <= actualThetaHullLogRoot T | Mzk1P6HCor312SandwichChain.lean:26 | PROVED |
| C2 upper theta | theta_lam <= H_pkt | ksThetaHullLogRoot_lam_le_ucWeightedHpkt_lam / paperThetaHullLogRoot_le_Hpkt | Mzk1URThetaKSideActual + Mzk1URThetaKLambdaAdapterActual | accepted |
| C3 upper | H_pkt <= kappa*(A - c_l*Q) - M | p6_sandwich_cancel gives cl*Q <= A from the upper sandwich | Mzk1P6HThetaUpperSandwichActual.lean:35 | C3 real gap |
| A | actual target signed magnitude | actualTargetSigned_actual (actualQPilotSignedLogClassical <= actualThetaHullLogRoot) | Mzk1ActualHullTargetMagnitudeActual.lean:60 | PROVED |

## Real missing links (only these)
1. C3 upper: assemble H_pkt <= kappa*(A - c_l*Q) - M from the StepV paperBound / lambda-weight
   work plus p6_sandwich_cancel (this is the U-C gap, not a C2 gap).
2. Actual packet V instantiation: per-b ksThetaHullLog b <= urPacketV_K b
   (Mzk1URPacketActualInstanceActual, in compile; uses StepVPaperBound:524 + hull containment).
3. URC2 q_P5 switch to -M with M = Q/(2l) using actualQPilotMagnitudeClassical (david lane).

## Not needed (recorded to avoid rework)
- v2-to-theta per-fibre bridge (Mzk1URThetaKHP5J1SameQActual / hbridge_of_fiberCoeff): audit only.
- KLambda J1 bridge with hvol: audit-only interface; do not treat as terminal condition.
- v2 stays as an alternative/audit expression; docstrings must mark it as non-route Q.
