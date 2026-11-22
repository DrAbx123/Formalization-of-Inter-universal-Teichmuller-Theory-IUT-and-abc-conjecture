# S810: least lambda-O paper hull carrier

Date: 2026-10-30. S797/S790 blocked; corrected carrier uses S793.

## Dependency status

S797PaperHullFirstAuditActual and S790StackToPaperQPilotThetaActual were not
compiled: both depend on S745PaperRootHullNonzeroCorrectionActual, which imports
RootHullClosednessActual.  RootHullClosednessActual fails locally with:
* unknown namespace LeanFormal.IUT.Foundations.Theta;
* unknown identifiers hcRoot/hone;
* unfold rootMinimalRegion failure.
Those errors are in the unqueued closure file, so S745/S797/S790 remain exact
blocked in the current tree.

## Corrected carrier (actual)

paperHullFirstCarrierCorrected := paperLeastLambdaOHull.

paperHullFirstCarrierCorrected_eq_lambdaORegion:
  corrected carrier = paperLambdaORegion paperRootCoefficientFamily.

paperHullFirstCarrierCorrected_subset_oldUnion:
  corrected carrier subset paperRootThetaHull (old closure-union carrier).

## Exact reverse gap

S810LeastEqualsOldUnion:
  paperRootThetaHull = paperHullFirstCarrierCorrected.
This is the exact condition under which the old union-closure hull agrees with
the least lambda-O hull; no inhabitant is provided.

## qPilot region

paperQPilotRegionCorrected := paperLambdaORegion paperRootCoefficientFamily.
paperQPilotRegionCorrected_eq_least: it equals the corrected least hull.
paperQPilotRegionCorrected_subset_least.

## Log bridge

S810HullLogDataRequired :=
  Nonempty (ArithmeticTuplePureFractionalScalingData ... paperRootCoefficientFamily).

paperHullFirstLogCorrected is defined as the actual normalized log-volume of the
corrected carrier; the formula needs the exact scaling data above.

No fake hull equality; old union is retained only as a superset.
