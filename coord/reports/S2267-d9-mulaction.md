# S2267: point-type MulAction bypassed; P_T/Q_T and pointwise f,g actual

Date: 2026-11-02. Status: the typeclass blocker is bypassed by an explicit
action instance. P_T, Q_T and the pointwise f,g are constructed. Naturality and
the ULift equalizer iso remain missing. No fake, no IsStack claim.

## 1. Explicit action

File: tmp/sheaf/xif/paper/S2267QHomEqualizerMulActionActual.lean

S2267Point S T :=
  Opposite.unop (LocallyDiscrete.mk (Opposite.op T.unop.left)).as
    ⟶ S1726AffineOver.

S2267smul g P := P ≫ S1971SchemeAut g.

instance S2267PointMulAction T : MulAction SignGroup (S2267Point S T),
with one_smul and mul_smul proved from S1971SchemeAut_one / _mul.

S2267smul_eq: g • P = P ≫ S1971SchemeAut g (rfl).

This bypasses the failed typeclass synthesis.

## 2. P_T/Q_T actual

S2267PT S M T :=
  ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj M).back.

S2267QT S N T :=
  ((S2152Q.map (T.unop.hom.op).toLoc).toFunctor.obj N).back.

S2267PT_back / S2267QT_back: definitional back formulas.

## 3. Pointwise f,g actual

S2267fPoint M T g := g • S2267PT S M T.
S2267gPoint N T g := S2267QT S N T.

These are actual pointwise functions.

## 4. Remaining first missing

- naturality of f,g as natural transformations P ⟶ R;
- ULift(Q.presheafHom M N) ≅ Limits.equalizer f g, using
  S1971PointwiseQuotient_hom.

Both are not constructed.

## 5. Status

| Item | Status |
|---|---|
| explicit smul/MulAction | PROVED |
| P_T/Q_T | BUILT |
| pointwise f,g | BUILT |
| naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 40843087a79aacda3793a0097f9c060c4e0a50f833503bd701d690b387dcdae9
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2267QHomEqualizerMulActionActual.olean, size 60544
- axioms: propext, Classical.choice, Quot.sound.
