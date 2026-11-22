# S157: thetaPacket.scale / qVFamilyThetaValue usage audit

Date: 2026-10-29.

## Classification rule

* thetaPacket.scale j = realThetaValue q j = q^(j^2): a power of the
  q-parameter q_v (single underline).
* paper Theta values use the double-underlined 2l-th root q_v:
  paperRootThetaUnit / twoLthRootAt, in the algebraic closure.

No equality between thetaPacket.scale and the paper root theta is asserted.

## A. Correct q-parameter comparisons

These use q-parameter powers intentionally, not paper root theta:

| File | Object | Use |
|---|---|---|
| QVFamThetaImageActual | qVFamilyThetaValue, qVFamilyThetaPacket | q-parameter qVFamily comparison |
| QVFamThetaLatticeHullActual | qVFamilyThetaValue_log_eq_lattice | q-parameter lattice |
| QVThetaValueBridgeActual | sourceThetaValue vs qVFamilyThetaValue | exact q-parameter relation proposition |
| QVFamThetaScalingActual | qVFamilyScalingLambda | q-parameter scaling |
| QVFamNormalizedGeneratorSupplyActual | qVFamNormalizedGenerator | q-parameter generator |
| QPilotZeroLocusDivisorActual | qVFamily | q-parameter q_v |
| ConcreteThetaPacketIdentificationActual | thetaPacket.scale = realThetaValue (1/5) | q=1/5 q-parameter packet |
| C3TensorIndexBadSourceMapActual | c3SourceThetaValue = A.thetaPacket.scale | q-parameter source map |
| LogThetaLatticeActual | thetaPacket.scale node comparisons | q-parameter log-theta lattice |
| MultiradialProcessionActual | thetaPacket.scale at 0 0 | q-parameter procession |

## B. q-parameter power labeled as paper Theta (needs correction/annotation)

These call thetaPacket.scale or qVFamilyThetaValue the actual Theta value while
the source value is only q_parameter^(j^2):

| File | Mislabel | Required correction |
|---|---|---|
| GlobalThetaPilotKummerActual | 'actual theta value C3.thetaPacket.scale j' | q-parameter value; rename/annotate or use paperRootThetaUnit for root Theta |
| GlobalThetaPilotIQKummerActual | 'literalIQThetaValue = C3.thetaPacket.scale' | q-parameter value; not root theta |
| ConcreteGlobalPilotDataActual | 'actual theta scale' and theta-pilot log-volume from q=1/5 | q-parameter power; root theta needs paperRootThetaUnit |
| ProcessionThetaPacketAverageActual | Theta packet average values log scale | q-parameter procession; not root theta |
| PaperSignedHullSignedActual | signed hull values -log scale | q-parameter hull; not root theta |
| PaperProcessionEqSigned | procession equality log scale | q-parameter; not root theta |
| PaperThetaMagnitudeComparisonProof | magnitude comparison log scale | q-parameter; not root theta |
| SignedHullLogFromSourceActual | source local log degree of theta packet scale | q-parameter; root theta relation missing |
| SignedHullSupActual | signed hull sup from scale | q-parameter; root theta relation missing |
| SignedMagnitudeConditional | -log(scale) = gauss * log 5 | q-parameter value; not root theta |
| ThetaFunctionLineBundleActual | realThetaValue q | q-parameter power |
| CorrectedHullCounterexampleActual | -log(scale) | q-parameter counterexample |
| PaperC3ThetaUnitSourceActual | thetaUnit = qParameterUnit^(j^2) | q-parameter power in completion, not 2l-root |

Exact status: these are real q-parameter comparisons; they are not paper root
Theta values.  Where the paper target is the Theta-pilot root value, the correct
object is paperRootThetaUnit (PaperC3ThetaRootActual), which lives in the
algebraic closure, not in the completion.  No identification with thetaPacket.
scale is asserted.

## C. Actual root theta objects

paperRootThetaUnit, twoLthRootAt, paperRootThetaImagePoint,
paperRootThetaValue (PaperC3ThetaRootActual) are the root-side objects.

S157ThetaRootCorrectionActual adds paperRootThetaPower and proves the actual
2l-th power relation paperRootThetaPower_pow_twoL.

## Exact correction gap

A bridge from thetaPacket.scale (completion q-parameter power) to
paperRootThetaUnit (algebraic-closure root power) is not constructed: it would
require the 2l-th root and the mu_{2l} indeterminacy, and no norm/coercion of
the root extension to the completion is supplied.  This is an exact gap, not a
fake equality.

No fake root/parameter equality/sorry/axiom/True/PUnit.
