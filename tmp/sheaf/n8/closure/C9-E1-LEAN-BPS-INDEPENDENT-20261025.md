# C9 E1 via Lean BPS/Theta 0-column: exact obstruction

Task: task-370. Owner: kummer. Date: 2026-10-25.
Source/Lean audit; no Lean/Project edits; no arbitrary data; no mixed/E3.
Only this file written. target_accepted=false; P6 open.

## 0. Inputs (existing Lean modules)

- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceArithmeticThetaPilotBridge.lean
  (minimal source-arithmetic theta-pilot bridge; no bridge constructed;
  negative calibration for degree-faithful full hull).
- LeanFormal/IUT/Foundations/AlgebraicGeometry/SourceQlThetaLineBundleObstruction.lean
  (actual curve/divisor/product formula; exact six missing theta/line-bundle
  items).
- LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment.lean
  (orbit containment conditional on a map; no source-to-integral-tensor map).
- LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CertificateCThetaTransfer.lean
  (certificate transfer; no actual source certificate constructed).
- C9-B273-COMPLETE-BPS-20261025.md (task-288), 91 lines,
  SHA256 739757d99c6aa23cf67925e3272ea0b146066ab8a95c4486b288d1b3c906bd8b.
- C9-B273-GLOBAL-BPS-20261025.md (task-292), 155 lines,
  SHA256 1284a14a6844692f13ad8503cba10eba0526c5d0cafdae577664b251e77b6ec7.

## 1. Verdict

E1 (no admissible complete C with b=273) is NOT proved by the Lean
BPS/ThetaPilot modules. The modules establish missing source data and one
negative calibration, not an impossibility of every complete C.

The exact situation:

- the actual curve/divisor/product-formula layer is present;
- the global BPS/F-prime-strip label/gluing to the Theta-pilot 0-column is absent;
- the minimal ArithmeticThetaPilotBridge is not constructed;
- there is no map from OriginalInput/ThetaPilotObject to the actual integral
  log-shell tensor over ArithmeticTensorTupleBlock;
- six specific theta/line-bundle data are named as missing and not constructed;
- no actual StepXIFiniteCertificate for the source carrier is constructed;
- the only proved negative statement is that no degree-faithful full-hull
  ArithmeticThetaPilotBridge exists in the hdeg regime. That rules out one
  bridge design, not every possible non-degree-faithful comparison.

Therefore E1 cannot be concluded. The b=273 profile inherits the same missing
global data as b=3; no b=273-specific Lean contradiction is present.

## 2. Actual Lean content

### 2.1 Source arithmetic theta-pilot bridge

SourceArithmeticThetaPilotBridge.lean records a conditional bridge:

    toSource : A^times ->* I.ThetaPilotPoint v,
    degreeMap : Additive A^times ->+ Real,
    thetaLift : SourceVolumeIndex l -> A^times,
    hull_cover : sourceHolomorphicHull v R n subset toSource '' (H_A cap A^times),
    unit_bound : ...

It proves conditionally that the source hull volume is finite, and proves the
negative calibration:

    under pointwise degree faithfulness hdeg, no ArithmeticThetaPilotBridge
    exists (no_degreeFaithful_fullHull_arithmeticThetaPilotBridge,
    not_nonempty_arithmeticThetaPilotBridge_of_degreeFaithful).

The module explicitly states that no bridge is constructed and that closing
N5 needs a non-degree-faithful comparison or a different justified carrier
equivalence. This is an exact gap, not a proof that no complete C exists.

### 2.2 Theta line-bundle obstruction

SourceQlThetaLineBundleObstruction.lean constructs the actual punctured curve,
Weierstrass model, base change, full real principal divisor, product formula
degree zero, and integer theta divisor. It names exactly six missing items:

    curveLineBundle
    thetaObjectATheta
    geometricThetaDivisor
    unitComparisonMqMTheta
    muTwoLDeckRootAction
    conjugateSynchronization

and proves sourceThetaLineBundleObstructionMissing_length = 6. No theta
object/line bundle/unit comparison/deck action is constructed.

### 2.3 Theta-pilot IQ containment

SourceThetaPilotIQContainment.lean proves an abstract orbit lemma: a submodule
containing the Theta-pilot generator and stable under the splitting-monoid
action contains the whole possible image. But the module explicitly states
there is no declaration of a map from OriginalInput/ThetaPilotObject data to
the actual integral log-shell tensor over ArithmeticTensorTupleBlock, nor a
proof that the generator lies in the image of such a map. No such map is
postulated.

### 2.4 CTheta certificate

CertificateCThetaTransfer.lean proves transfers over a supplied
StepXIFiniteCertificate, but no certificate is constructed for the actual
source carrier. The carrier realization remains a separate source obligation.

## 3. Why this is not E1

A complete C with b=273 would require at minimum:

(C1) the global BPS/F-prime-strip labels and their full poly-isomorphism/gluing
     to the Theta-pilot 0-column;
(C2) the source arithmetic theta-pilot bridge or a justified non-degree-faithful
     replacement;
(C3) the six line-bundle/theta data above;
(C4) the source-to-integral-log-shell comparison;
(C5) an actual CTheta certificate for the source carrier;
(C6) CFTH/TC/arch and the complete-C target data.

The Lean modules show (C1)-(C5) are not constructed. They do not prove that
(C1)-(C5) are impossible. In particular:

- the negative degree-faithful calibration rules out only that bridge design;
- the six-missing-items theorem is a list, not an inconsistency;
- the orbit lemma is conditional on a generator/IQ comparison not constructed;
- the CTheta transfer is conditional on an unconstructed certificate.

Hence the implication

    Lean BPS/Theta modules => no complete C with b=273

does not hold. E1 remains open.

## 4. Exact gap

The exact missing source declarations are:

(G1) BPS label/0-column gluing: an actual F-prime-strip label set and full
     poly-isomorphism to the Theta-pilot 0-column, compatible with E_546
     local q/theta data;
(G2) source-to-arithmetic theta-pilot bridge: toSource, degreeMap, thetaLift,
     hull cover and unit bound, or a justified non-degree-faithful replacement;
(G3) the six theta/line-bundle items: curve line bundle, A_Theta, geometric
     theta divisor, unit comparison M_q/M_Theta, mu_2-l deck root action,
     conjugate synchronization;
(G4) source-to-integral-log-shell tensor map and generator-membership proof;
(G5) actual CTheta certificate/carrier realization;
(G6) b=273-specific CFTH/TC/arch/BPS target data.

None is a b=273 arithmetic defect; all are global and shared with b=3.

## 5. Classification

| item | status |
|---|---|
| actual curve/divisor/product formula in Lean | PRESENT |
| ArithmeticThetaPilotBridge | NOT CONSTRUCTED |
| degree-faithful full-hull bridge | PROVED IMPOSSIBLE (hdeg regime) |
| non-degree-faithful bridge | OPEN |
| six theta/line-bundle items | NAMED MISSING, NOT CONSTRUCTED |
| source-to-IQ/log-shell map | MISSING |
| actual CTheta certificate | NOT CONSTRUCTED |
| b=273 complete C | NOT CONSTRUCTED |
| E1 no admissible b=273 C | NOT PROVED |
| b=273 P6 counterexample | CONDITIONAL on complete C |
| P6 true via E1 | NOT ESTABLISHED |

## 6. Conclusion

The Lean BPS/ThetaPilot modules give a precise obstruction/gap list but not an
E1 impossibility proof. They show no global BPS 0-column gluing, no
ArithmeticThetaPilotBridge, six missing theta line-bundle data, no source-to-IQ
comparison, and no actual CTheta certificate. The only negative theorem is
against a degree-faithful full-hull bridge, not against all complete C.
Therefore b=273 E1 remains open; no complete C is constructed; P6 is not
established. No arbitrary BPS label or bridge is inserted; no mixed/E3 profile
is used.

No Lean/Project edits; target_accepted=false; P6 open.

## 7. Status

- Lean/source audit only; no Lean/Project edits.
- E1 not proved; exact six-item/bridge/label gap recorded.
- target_accepted=false.
