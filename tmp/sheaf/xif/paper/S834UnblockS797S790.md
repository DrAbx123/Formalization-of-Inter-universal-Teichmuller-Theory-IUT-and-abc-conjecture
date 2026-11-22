# S834: unblock S797/S790

Date: 2026-10-30. RootHullClosedness remains broken; unused dependency removed.

## Bypass

S797PaperHullFirstAuditActual and S790StackToPaperQPilotThetaActual imported
S745PaperRootHullNonzeroCorrectionActual but did not use any S745 symbol.
S745 imports RootHullClosednessActual, which fails with:
* unknown namespace LeanFormal.IUT.Foundations.Theta;
* unknown identifiers hcRoot/hone;
* unfold rootMinimalRegion failure.

Action: removed the unused S745 import from S797 and S790. Both now compile
EXIT=0 against the existing actual definitions.

## S797 correction

Added paperHullFirstCarrierCorrected := S810.least hull.
* paperHullFirstCarrierCorrected_eq_least:
    corrected carrier = S793.paperLeastLambdaOHull.
* paperHullFirstCarrierCorrected_subset_old:
    corrected carrier subset old paperRootThetaHull.

The old paperHullFirstCarrier is retained only as the old union/closure audit.

## S790 least-hull link

Added:
* paperStackQPilotRegion_eq_corrected:
    qPilot region = S810.paperQPilotRegionCorrected.
* paperStackQPilotRegion_subset_leastHull:
    qPilot region subset corrected least hull.
* PaperStackTargetLeast: exact target qPilot log <= least-hull normalized log.

No fake hull equality; exact target remains.

## Compile

S797PaperHullFirstAuditActual EXIT=0.
S790StackToPaperQPilotThetaActual EXIT=0.
