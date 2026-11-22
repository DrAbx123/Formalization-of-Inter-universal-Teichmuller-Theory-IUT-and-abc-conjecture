# S507: paper Phi_Cv candidate

Date: 2026-10-29. Candidate only; no tau, no fake q_v value.

## Actual DivisorialMonoidOn

phiCvCandidate : DivisorialMonoidOn (StageBase place) StageFSM
  := stageDivisorialMonoidOn place.

This is the actual stage divisor monoid with its ramification pullback
liftedStageDivisorPullback; carrier PhiCarrier = StageDivisor = ULift Nat.

## q_v constant section

qvConstantSection order X := ULift.up order, a constant section over StageBase.

qvConstantSection_apply is rfl.

## Split submonoid N log(q_v)

splitAddSubmonoid coefficient := AddSubmonoid.closure {ULift.up coefficient}.

qvConstantSection_mem_split: the constant section belongs to the split
submonoid.

## Candidate package

PaperPhiCvCandidate packages phi, phi_eq, qvOrder, split, and qv_constant_mem.

paperPhiCvCandidateOfOrder order constructs it for an externally supplied
q_v order.  No q_v value is fabricated; order is a parameter.

No characteristic splitting tau is constructed.  No fake q_v/Phi, no
completion/L, no inequality.
