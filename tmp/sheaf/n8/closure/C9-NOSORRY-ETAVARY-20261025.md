# C9 no-sorry task: EtaComparisonVaryingTarget

Task: task-483. Owner: qside. Date: 2026-10-25.
Target: tmp/sheaf/n8/closure/EtaComparisonVaryingTarget.lean
Deliverable: this report only; target Lean edited to replace the one provable
sorry; two source-gap sorries retained and documented. No fake, axiom, toy.
No mixed/E3.

## 0. Status

Original target SHA256 before edit:
3E488B3EE603609FD12BED04976FC276276948BACD604617B4FC2FF209E50275

Edited target SHA256:
90E07DAA9EBAEEB92BF9E4E6C7D3481C9BBA535E46C59CA8E10DA727776AC94A

Edited target lines: 139.

Compile with the required central serial wrapper:

  cd D:/lean
  & 'D:/lean/tmp/n8-20261018/lead/lean-serial.ps1' env lean -j1 -R D:/lean       tmp/sheaf/n8/closure/EtaComparisonVaryingTarget.lean

Result: EXIT=0.

The compile log retains:
- duplicate-namespace linter warnings for the pre-existing
  EtaComparisonVaryingTarget structure;
- two sorry warnings at lines 126 and 136.

No new axiom, no fake proof, no toy carrier, no sorry replacement by axiom.

## 1. What was proved

Original sorry 1 (etaComparisonVaryingTarget_exists) is now proved.

Added declaration etaComparisonVaryingMap:
  Rval -> Rss (K := K) muK
which sends 1 to sourceOpenClass and every other element to
sourceClosedClass.

The proof of etaComparisonVaryingTarget_exists:
- constructs the structure with etaQ = etaAnabS = etaComparisonVaryingMap;
- comparison is rfl;
- nonconstant: assume a constant c; evaluate at 1 and at
  Multiplicative.ofAdd (1 : Real); the values are sourceOpenClass and
  sourceClosedClass; sourceClasses_ne makes them unequal; contradiction.

This uses only actual declarations:
- Rval = Multiplicative Real (EtaValueGroupLineActual);
- Rss = Quotient (SameVolume ...) (EtaRssNontrivialActual);
- sourceOpenClass, sourceClosedClass, sourceClasses_ne
  (EtaRssSourceRegionBridge);
- Multiplicative.ofAdd / toAdd arithmetic.

No toy field is introduced: the two values are the actual open/closed unit
region quotient classes already constructed in the project.

## 2. What remains sorry and why

Two sorries remain, both exact source gaps, not provable from the current
project declarations.

### 2.1 etaVaryingQCalibration_exists (line 126)

Statement:
  for every O : PaperC9Output X mu,
    EtaVaryingQCalibration K muK O
where
  EtaVaryingQCalibration O :=
    O.Q = logVolumeReadout (sourceOpenClass).

Exact obstruction:
- In C9PaperClosure.lean, O.Q = qPilotSignedLog X, which is fixed by X and
  independent of O (PaperC9Output.Q_eq_nativeScalar and QNamed).
- The right-hand side is the Rss log-volume readout of sourceOpenClass,
  an actual positive-measure quotient class from the local field K.
- No declaration in the project proves
    qPilotSignedLog X = logVolumeReadout (sourceOpenClass).
  This is the eta/Q calibration gap (the q-pilot value vs the varying-region
  open-class readout).
- The statement is universally quantified over every PaperC9Output O, but
  O.Q is X-fixed; proving it would require the missing equality for every X
  and K. There is no counterexample constructed here, but there is also no
  derivation; it is a named source comparison, not an algebraic consequence.
- Replacing it with an axiom or a toy equality would be fake; not done.

### 2.2 etaVaryingThetaCalibration_exists (line 136)

Statement:
  for every O,
    EtaVaryingThetaCalibration K muK O
where
  EtaVaryingThetaCalibration O :=
    O.Theta = logVolumeReadout (sourceClosedClass).

Exact obstruction:
- PaperC9Output.Theta = O.theta.ellOutValue, and P6L.P6Readout.ellOutValue is
  an arbitrary field value (P6Readout.value); ThetaSourceObject is data, not
  a fixed number.
- The right-hand side is the fixed Rss readout of sourceClosedClass.
- No project declaration identifies an arbitrary ThetaSourceObject value with
  the fixed closed-class readout.
- Thus the theorem is a source calibration obligation, not a formal
  consequence; retained as sorry with this exact obstruction.

## 3. Effect on downstream declarations

The pre-existing theorem etaVarying_Q_le_Theta is genuinely proved from
hypotheses hQ and hTheta: it rewrites both calibrations and applies
varyingReadout_open_lt_closed, which is already proved from actual open/closed
ball mass and Real.log strict monotonicity.

The pre-existing etaVarying_Q_le_Theta_of_gaps still compiles, but it consumes
the two calibration sorries; it is therefore a conditional theorem depending
on those named source gaps, not a closed proof of Q<=Theta for arbitrary O.
This report does not turn it into an axiom or a fake theorem.

## 4. Exact remaining gap list

G1 Q calibration:
   qPilotSignedLog X = logVolumeReadout sourceOpenClass.  Missing declaration
   and source identification.

G2 Theta calibration:
   O.theta.ellOutValue = logVolumeReadout sourceClosedClass for every Theta
   source object.  Missing declaration and source identification.

G3 The nonconstant comparison structure is now constructed, but the Q/Theta
   calibrations to the actual varying-region readouts remain G1/G2.

No other sorries were introduced.  No fake/axiom/toy.

## 5. Compile evidence

Command log: tmp/sheaf/n8/closure/eta_vary_compile3.log
Log SHA256: 527113EA342BB5FF013CB88E0635DF5271CF79F7D5C3158AF5C5407BCBB38C5E

Output:
  EXIT=0
  warnings: duplicate namespace in the pre-existing structure;
            declaration uses sorry at lines 126 and 136.

No errors.  The target module compiles with the two documented source-gap
sorries.

## 6. Classification

PROVED:
- etaComparisonVaryingTarget_exists, via actual source open/closed quotient
  classes and a nonconstant map.
- varyingReadout_open_lt_closed (pre-existing).
- etaVarying_Q_le_Theta (conditional on hQ/hTheta, pre-existing).

SORRY/EXACT GAP:
- etaVaryingQCalibration_exists (G1);
- etaVaryingThetaCalibration_exists (G2).

NOT USED:
- no axiom;
- no singleton/toy Rss;
- no arbitrary equality inserted as hypothesis inside the target;
- no mixed/E3.

target_accepted=false; the module is no-sorry except for the two documented
source calibrations, which are exact obstructions rather than provable
algebraic lemmas.
