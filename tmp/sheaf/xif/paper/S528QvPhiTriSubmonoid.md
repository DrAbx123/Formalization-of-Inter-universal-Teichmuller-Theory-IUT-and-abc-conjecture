# S528: Phi_Cv split submonoid from S516 model and qVFamilyK.order

Date: 2026-10-29. Conditional on QvRamificationIndexData.

## qOrder

qvTriQOrder T b N := N * (qVFamilyK T b).order
qvTriQOrder_pos: N>0 and qVFamilyK.order>0.

## Model

dvQvPhiModel E := qvPhiRamificationModel E
(S516 Qv-Phi ramification model on Example32SmallBase (T.arithmetic.K)).

## Split submonoid

qvTriSubmonoid qOrder : AddSubmonoid (ULift Nat)
  := closure {qOrder • ULift.up 1}.

## Candidate and pullback_mem

QvPhiTriCandidate N hN:
  ramification : QvRamificationIndexData
  qOrder, qOrder_eq
  split, split_eq
  pullback_mem: for f : X -> Y and n in split Y,
    model.pullback f n ∈ split X.

Proof: model.pullback f = uliftNatMulLeft (E.index f) = E.index f • -;
membership is closed under nsmul (AddSubmonoid.nsmul_mem), so pullback_mem.

qvPhiTriCandidate constructs it from explicit E.

Exact missing: QvRamificationIndexData (including index alignment).  No fake
ramification/qOrder; no tau; no completion/L.
