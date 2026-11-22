# S436: paper K-side q_v exact missing spec

Date: 2026-10-29. No fake q, no arbitrary badPlaceQCandidate.

## Setup

kSidePlace = sectionFiniteLift (nativePlaceSelection T) b.1, the section-chosen
K-place over the bad moduli place b.1.

kSideCurve = T.arithmetic.curve.baseChange T.arithmetic.K, the base-changed
curve over K.

F-side reference: qVFamily T b at (nativeBadLift T).lift b; shadow is
fkDescentShadow (nativePlaceSelection T) b.1.

## Exact missing K-side q_v data

KSideQVFamilySpec:
* kPlace : FinitePlace T.arithmetic.K with kPlace = kSidePlace;
* kCurve : PuncturedEllipticCurve T.arithmetic.K with kCurve = kSideCurve;
* q : FinitePlaceQCandidate kPlace;
* uniformization : TateCurveComparison kCurve kPlace q;
* fPlace : FinitePlace T.arithmetic.F with fPlace = (nativeBadLift T).lift b;
* shadow_compatible : fkDescentShadow (nativePlaceSelection T) b.1 = fPlace;
* fOrder : Nat with fOrder = (qVFamily T b).order;
* order_eq : q.order =
    fkDescentSectionRamificationIndex (nativePlaceSelection T) b.1 * fOrder.

KSideQVFamilyRequired := Nonempty spec; no inhabitant.

MissingKSideQVFields packages the three exact fields:
qObject, uniformization, orderEquality, plus fPlace/shadowEq.
MissingKSideQVFieldsRequired := Nonempty package; no inhabitant.

## Why exact missing

Repo has:
* F-side qVFamily/Tate comparison (F-place);
* sectionFiniteLift K-place and fkDescentShadow;
* frozen TateQIdentificationStatement and FKDescent statements;
* badPlaceQCandidate as an arbitrary Classical.choice q-candidate.

No actual K-side q object tied to E/K_v Tate uniformization exists.  The spec
deliberately does not use badPlaceQCandidate; it requires an actual q and a
TateCurveComparison at the K-place, plus the F-to-K order equality under the
ramification index.

No fake q/uniformization/order equality; no completion/L.
