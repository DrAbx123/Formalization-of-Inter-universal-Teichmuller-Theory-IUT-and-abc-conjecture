# O2 paper comparison: conditional actual closure

Date: 2026-10-25. Owner: logdescent. Lean: O2PaperComparisonConditionalActual.lean.
Compile: lake env lean -j1 -R D:/lean -> EXIT=0, zero sorry.

## Source conditions (fields, not arbitrary)

O2PaperSourceConditions W:
1. order_eq_one : W.q.order = 1 (Tate parameter is a uniformizer);
2. residuePowerCard : LogShellResiduePowerCardHypothesis (K:=FCompletion W) 1;
3. residueCard_eq_base : logShellResidueCard = residueNormBase at W.place.

## Proved

- thetaAnab_eq_log_residueCard: from logShellVolume_exact_residue_power,
  ThetaAnab = log(logShellResidueCard).
- thetaAnab_eq_thetaQ_of_sourceConditions: conditions (1)-(3) give
  ThetaAnab = ThetaQ (using NormalizedThetaQ = q.order * log residueNormBase).
- o2PaperComparison_of_sourceConditions: O2PaperComparison W.

## Exact extra condition

Condition 3 is the residue-cardinality base agreement.  Production has the
residue-power theorem but no theorem identifying the log-shell residue
cardinal logShellResidueCard with the q-normalization base residueNormBase;
this is carried as a source field.  No arbitrary q/place/readout is used.