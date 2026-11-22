# Paper theta normalization status (authoritative)

## Correct objects

* q[1u] = q_v: single-underline q-parameter.  C3.q / qVFamily are q[1u].
* q[2u] = q[1u]^(1/(2l)): double-underline 2l-th root.
* paper theta value: q[2u]^(j^2) = q[1u]^(j^2/(2l)).
* Existing implementation:
  - BadPlacePaperConstantsActual.paperRootCoefficient = order(q_v)/(2l)
  - paperThetaCoefficient = qVFamPaperThetaTensorCoefficient = j^2*order/(2l)
  - classicalThetaCoefficient_eq_twoL_mul_paper:
      classical q^(j^2) coefficient = (2l)*paperThetaCoefficient
  - paperThetaValueRoot_is_root_power:
      qVFamPaperThetaValueRoot = (hodgeTwoLthRoot)^(j^2)

## INVALID / must not be used for paper theta

* realThetaValue q j = q^(j^2) when q = C3.q = q[1u] (missing 1/(2l)).
* C3GaussianThetaPacketActual / c3ThetaProcession / c3ThetaSignedProcession
  (classical q^(j^2) normalization).
* ConcreteSourceComparisonNumericActual
* ConcreteSourceComparisonInequalityActual
* S660ConcreteSourceComparisonObstacleActual
* S621/S624/S625 and any comparison built on classical theta average.
* BadPlaceHalfRootSupplyActual.HalfRootInCompletion (completion 2l-root;
  impossible by S342).  It is not the paper root.

## Consequence

Any q=1/5 'counterexample' from the classical normalization is a
normalization artifact.  Do not prove inequalities from it.

## Required fix

Replace C3 theta packet/procession by the existing paper root data:
  paperThetaCoefficient
  qVFamPaperThetaValueRoot = hodgeTwoLthRoot^(j^2)
Then rebuild procession/hull/comparison.  Do not create another
rpow-based duplicate normalization.
## Already-existing root-normalized construction (REUSE)

* BadPlacePaperRootThetaHullActual
  - paperRootThetaHull, paperRootThetaHullLog, paperRootThetaFormulaLog
  - PaperRootHullFormulaGap (exact remaining gap)
* CompletionValuedThetaHullMuLogActual
  - actual root-coefficient completion hull, positive finite Haar,
    normalized log.
* BadPlacePaperRootComparisonActual
  - S13 qPilot/Theta coefficient sums vs paper root constants;
    correction identities.
* RootCorrectedQPilotScalarActual
  - qVPilotRootLocalMagnitude = classical magnitude/(2l)
  - qVPilotRootNormalizedMagnitude/SignedLogVolume
  - native = (2l) * root scalar.
* S638PaperThetaNormalizationActual
  - paper theta = root^j^2, classical = 2l * paper coefficient.

## Remaining exact gap

  PaperRootHullFormulaGap T b
    = pure fractional scaling data for paperRootCoefficientFamily
      + hull equality to the fractional-lattice region.

Only after this gap, compare paperRootThetaFormulaLog with qPilot.
## Further existing layers (recursive audit)

* RootNormalizedThetaHullActual
  - rootThetaHullNormalizedLog
  - RootThetaHullNormalizationGap (scaling data at rootThetaCoefficient + hull_eq)
  - rootThetaHullNormalizedLog_eq_formula_of_gap
* RootQPilotContainmentActual
  - actual qPilotRootLog_le_rootThetaHullLog (rootNormCoefficient version)
* Remaining at paperRootCoefficient:
  - PaperRootHullFormulaGap (scaling data at paperRootCoefficientFamily + hull_eq)
  - QPilotRootScalingDataGap (q-pilot side paper-root scaling data)
  - correction transport: s13HalfCoefficient = paperRootCoefficient
      + normalizedOrderCorrection/(2l), only zero correction gives equality.
## PaperRootHullFormulaGap is a completion-root obstruction

BadPlacePaperRootThetaHullActual.PaperRootHullFormulaGap requires

  ArithmeticTuplePureFractionalScalingData
    (paperRootCoefficientFamily = order/(2l))

whose localGenerator has completion norm

  ||g|| = p^(-(order/(2l))).

Such a completion generator is equivalent to a completion 2l-th root of
q[1u].  S342 (qVFamily completion root impossible) contradicts this.

Therefore the gap CANNOT be filled in the completion carrier.  The paper
q[2u] lives in the extension/root stack (hodgeTwoLthRoot), not in the
completion.  Do not fabricate completion scaling data.

Consequences:
* PaperRootHullFormulaGap is an object-level carrier gap, not a missing
  arithmetic lemma.
* A completion-valued theta hull cannot be the paper theta hull.
* The theta hull/root data must be built on the root-stack/extension
  carrier using hodgeTwoLthRoot, or the final comparison must be stated
  directly on root values/log scalars.
