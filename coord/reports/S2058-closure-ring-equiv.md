# S2058: actual closure ring equivalence and the exact norm gap

Date: 2026-11-02. Layer O. Canonical completion carrier remains
S2055CompletionIntegralUnits. No all-units/S2035 carrier is used for PaperO.

## Actual file

tmp/sheaf/xif/paper/S2058ClosureRingEquivActual.lean
Source SHA256 130ff4fb98d7de4e6bfb82d127e07de48848829d84f35de847f60444b2073ae4
olean SHA256 b2e3209d852faf91509516a7b29bf65188453433490525f32a4e0bc705ca83ed
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

Built:
S2058ClosureRingEquiv (v) :
  SourceAlgebraicClosure (QPlace v) ≃+* AlgebraicClosure Q_[v.1]
using IsAlgClosure.equivOfEquiv with the actual
(completionPadicEquiv v).symm.

Exact missing:
S2058NormPreservationRequired (v) :
  forall x, ||S2058ClosureRingEquiv v x|| = ||x||.

## Consequence

Given S2058NormPreservationRequired, the S2056 construction (already checked)
gives the Integers ring equivalence and the integral units equivalence
S2055CompletionIntegralUnits (QPlace v) ~= S2055QpIntegralUnits (QPlace v),
and S2057 gives the canonical S2046NormBridge with muCompatible.

## S2038 alignment

S2038 PaperOActual fields:
(a) CurvePiOneData: exact missing.
(b) ThetaMonoidActual: exact missing; S1973 is only the local-field model,
    not the cohomological Psi_cns assignment.
(c) OUnitsMuActor: exact missing algorithm; the carrier side is now represented
    by S2055/S2056/S2057, but the group-theoretic construction
    alg : ProfiniteGrp -> Type and its functoriality are not constructed.
(e) OperationKummerEvaluation: exact missing; consumes (b) and (c).
(d) q-pilot is S2038's actual construction; this file does not touch it.

No fake/reduced/Q_p carrier is claimed as PaperO.
