# Eta consumer dependency audit

Date: 2026-10-24
Files audited:
- tmp/sheaf/n8/closure/EtaComparisonConsumerNondegenerate.lean
- tmp/sheaf/n8/closure/EtaRouteInterface.lean
- tmp/sheaf/n8/closure/EtaConsumerIndependent.lean (new independent version)

## 1. What EtaRouteInterface.EtaComparison actually is

EtaRouteInterface defines

  Rval := NativeShell.preLogShell
  Rss  := NativeShell.logShell
  EtaQ a := pStar^{-1} * a
  EtaAnab b := pStar * b
  EtaComparison := LeftInverse EtaAnab EtaQ ∧ RightInverse EtaAnab EtaQ ∧
    qPilotSignedLog X < 0

All three conjuncts are proved outright by etaQ_leftInverse, etaQ_rightInverse,
and qPilotSignedLog_neg.  This is a negative-control tautology: it checks the
two scaling maps are inverse and q is negative.  It does NOT compare the source
maps eta^q and eta^anab_S.

## 2. Dependency of the old consumer

EtaComparisonConsumerNondegenerate.lean imports EtaRouteInterface and takes

  hEta : EtaComparison X.

Inside etaNormalizedQ_le_Theta_nondegenerate, hEta is used only to prove
O.Q < 0 after the exact identification O.Q = EtaNativeQ X.  The conclusion
O.Q ≤ O.Theta itself is obtained from
PaperQLeThetaReduction.paperQLeTheta and paperC9Comparison, i.e. the P6/Values
route, not from the Eta tautology.

Nevertheless the file's type mentions EtaComparison, so it must be labeled
conditional-on-negative-control, not a consumer of eta^q = eta^anab_S.

## 3. Independent replacement

EtaConsumerIndependent.lean defines

  structure EtaComparisonIndependent where
    etaQ : Real
    etaAnabS : Real
    comparison : etaQ = etaAnabS
    etaQ_eq_native : etaQ = qPilotSignedLog X
    etaQ_neg : etaQ < 0

Its inhabitant is the explicit named gap

  etaComparisonIndependent_exists : Nonempty (EtaComparisonIndependent X)

and the Q identification is the named gap

  etaQNormalizedIdentification_exists :
    EtaQNormalizedIdentification O.

The consumer etaNormalizedQ_le_Theta_independent takes the independent
interface, the exact Q identification, the audit guards

  Theta != 0, Values != {0}, reference != region,

and ValuesBounded, and derives O.Q <= O.Theta.  No direct scalar Q <= Theta
hypothesis is used.  The empty gap version
etaNormalizedQ_le_Theta_independent_of_gap consumes the named interface gap.

## 4. Correct usage

- Do not cite EtaRouteInterface.EtaComparison as eta^q = eta^anab_S.
- The old EtaComparisonConsumerNondegenerate is conditional-on-negative-control
  and is superseded by EtaConsumerIndependent.
- Downstream Q <= Theta consumers should use EtaConsumerIndependent with the
  independent named gap.  The P6/Values route remains the actual proof of the
  inequality; the Eta interface supplies only the q-side normalization.
- The audit guards are nondegeneracy only; they are not scalar bounds.

## 5. Status

- EtaRouteInterface.lean: compile EXIT=0 (pStar inverse proofs fixed; this is
  still the negative-control interface).
- EtaComparisonConsumerNondegenerate.lean: compile EXIT=0; dependency correctly
  described as conditional-on-negative-control.
- EtaConsumerIndependent.lean: compile EXIT=0; two named gaps
  (independent eta comparison, normalized Q identification); no direct scalar
  Q <= Theta assumption.
