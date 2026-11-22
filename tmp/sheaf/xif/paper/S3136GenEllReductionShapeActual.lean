/-! # Stage-4 host: abstract shape of the [GenEll] Theorem 2.1 equivalence

TEXT: papers/motizuki_corpus/text/Arithmetic Elliptic Curves in General Position.txt,
Theorem 2.1 (p.615-687): (i) Effective Mordell/ABC/Vojta (general hyperbolic
curves) <=> (ii) ABC for Sigma-supported compactly bounded subsets.
The implication (ii) => (i) is the reduction (via [Mzk1] noncritical Belyi maps
and Props 1.4/1.7); (i) => (ii) is immediate.

CONSUMER: mainline's paper-input statement skeleton. This file records the
abstract equivalence/reduction shape as a reusable statement hook (class A).
No analytic content is asserted.

LABEL: statement-shape hook (class A). Registry frozen; new file only. -/

namespace LeanFormal.IUT.XiFPaper.S3136GenEllReductionShapeActual

/-- The shape of the [GenEll] Theorem 2.1 equivalence between the general
hyperbolic-curve statement and the compactly bounded subset statement. -/
def LGPGenEllEquivalence (generalStatement compactlyBoundedStatement : Prop) : Prop :=
  generalStatement ↔ compactlyBoundedStatement

/-- The reduction direction: a proof of the compactly bounded statement plus the
equivalence yields the general statement. -/
theorem lgpGenEll_reduction {generalStatement compactlyBoundedStatement : Prop}
    (h : LGPGenEllEquivalence generalStatement compactlyBoundedStatement)
    (hb : compactlyBoundedStatement) :
    generalStatement :=
  h.mpr hb

/-- The immediate direction. -/
theorem lgpGenEll_immediate {generalStatement compactlyBoundedStatement : Prop}
    (h : LGPGenEllEquivalence generalStatement compactlyBoundedStatement)
    (ha : generalStatement) :
    compactlyBoundedStatement :=
  h.mp ha

#check LGPGenEllEquivalence
#check lgpGenEll_reduction
#check lgpGenEll_immediate

end LeanFormal.IUT.XiFPaper.S3136GenEllReductionShapeActual