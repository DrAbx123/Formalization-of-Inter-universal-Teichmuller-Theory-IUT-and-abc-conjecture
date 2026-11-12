# S2047: component (a) completion model — prerequisite actual, first missing

Layer: O (IUT II Cor 4.10(ii) operation Kummer/evaluation; A/F source-object base).
Source object: actual local field Base(QPlace v) = Completion(QPlace v) and Q_p completion; LocalAbsoluteGalois v.1/Gv v.
Domain: actual rational completion model and local absolute Galois groups.
Direction: actual comap equality proved; completion Algebra-instance bridge and Galois equivalence exact missing.

BUILT/PROVED:
- S2047ComapQPlace: comap(k=Q) (QPlace v) = QPlace v, actual (via maximal ideal/height-one ext).
- Axioms: propext, Classical.choice, Quot.sound.

MISSING exact:
- S2047BaseModelEquivRequired: Base(QPlace v) ≃+* Q_[v.1] (completion model bridge). The Mathlib rational completion equivalence exists between Completion(comap QPlace) and PadicScalarField, but the Algebra instance on Base/adicCompletion is not definitionally the PadicScalarField instance; this instance mismatch is the exact first missing conversion.
- S2047RationalCompletionModelEquiv: Completion(comap QPlace) ≃A[Q] PadicScalarField(QPlace v), recorded as type (no fake inhabitant).
- S2047GaloisEquivOfBaseData: base ring equivalence + closure ring equivalence + compatibility; from it one could conjugate to LocalAbsoluteGalois v.1 ≃* Gv v. No inhabitant.
- S2047GaloisEquivRequired (S2046) remains missing.

Consumer: S2046OperationComponentsActual (a), then (b)/(c) S2039 actual PsiCns once local CFT port is ready.

Reports read: S2045/S2046 reports and sources; S1949 rational completion lemmas; FreyTateAnalyticInput rationalFinitePlacePadicEquiv; FinitePlacePadicScalarStructure.

Lean: tmp/sheaf/xif/paper/S2047GaloisCompletionActual.lean
EXIT=0; SHA256 2C738B20742E0E7704E21BEAC81FA7A18D962B57C7F451D59258099236B30846
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2047GaloisCompletionActual.olean
axioms: propext, Classical.choice, Quot.sound (no sorryAx).
No fake module equivalence or Q_p model substitution.
## Additional S2047 follow-up

Direct `RingEquiv`/`AlgEquiv` construction from `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` fails at elaboration because the Algebra instance on Base(QPlace v)/adicCompletion is not definitionally equal to the instance inferred for Q_[p]/PadicScalarField.  This is not a proof gap in comap (S2047ComapQPlace is actual); the first missing is the explicit Algebra-instance bridge or a casted ring equivalence of the two completion models.  No fake instance, Q_p substitution, or inhabitant was inserted.

## S2047 update: underlyingPrime aligned

Added actual S2047UnderlyingPrimeQPlace:
  underlyingPrime (QPlace v) = rationalHeightOneSpectrum v.1.

Together with S2047ComapQPlace this aligns the Base model source with Mathlib's rational adicCompletion.  The remaining blocker is still not the ring bijection but the Algebra-instance/type transport: after dsimp to adicCompletion, rewriting the height-one prime in the RingEquiv goal or casting the padic equivalence target still triggers the non-defeq DivisionRing.toRatAlgebra vs instAlgebraAdicCompletion instance error.  Exact missing remains S2047BaseModelEquivRequired / S2047GaloisEquivOfBaseData / S2047GaloisEquivRequired.  No fake instance or inhabitant.

Updated Lean SHA256 F00F67D915DDEFBCF9E71576791138621DBE559DBCD4E6F3DDE76A7C7FE89D46; EXIT=0; olean present; axioms propext/Classical.choice/Quot.sound.

## Resolution (2026-11-02)

The four exact missing objects are now inhabited by
tmp/sheaf/xif/paper/S2061BaseCompletionGaloisActual.lean
(SHA256 412CE88A68EAA291266E9DDB91AE476166D40EB9D2F4815CC7687062748EB9F5):
S2061BaseCompletionRingEquiv, S2061RationalCompletionModelEquiv,
S2061S2047GaloisEquivOfBaseData, S2061S2047GaloisEquivRequired /
S2061S2046GaloisEquivRequired.  Independent constructions also appear in
S2063BaseAlgebraBridgeActual and S2064GaloisEquivActual.  The earlier
instance obstruction is bypassed by explicit terms and
Algebra.rat_algebra_subsingleton, not by a fake instance or Q_p substitution.
See coord/reports/S2061-base-completion-galois.md.
