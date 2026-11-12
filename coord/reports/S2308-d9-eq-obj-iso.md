# S2308: pointwise equalizer object iso actual; subtype Equiv missing

Date: 2026-11-02. Status: the pointwise equalizer object iso is proved from
S2303 plus limitObjIsoLimitCompEvaluation. The subtype Equiv and final NatIso
are not constructed. No fake, no IsStack claim.

## 1. Actual

S2308EqualizerObjIso:

  (Limits.equalizer (S2285f S M) (S2285g S N)).obj T
    ≅ Limits.equalizer ((S2285f S M).app T) ((S2285g S N).app T)

Proof: e₁ := limitObjIsoLimitCompEvaluation (parallelPair f g) T;
e₂ := HasLimit.isoOfNatIso (S2303EvalDiagramIso S M N T);
exact e₁ ≪≫ e₂.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Missing subtype Equiv

The attempted Equiv

  Limits.equalizer (f.app T) (g.app T)
    ≃ {h : SignGroup // S2267fPoint S M T h = S2267gPoint S N T h}

was not completed. Concrete blocker: converting the equalizer.condition
equality of Type-morphisms to the pointwise equality needed for the subtype,
and the inverse lift through equalizer.lift, require careful coercion handling
for Type-category morphisms. The exact failing goal is:

  (equalizer.ι (f.app T) (g.app T)) x
    with x : equalizer (f.app T) (g.app T),
  needing
  S2267fPoint S M T (equalizer.ι ... x)
    = S2267gPoint S N T (equalizer.ι ... x).

## 3. Remaining

- subtype Equiv;
- combine S2271QHomObj_eq_subtype;
- final NatIso (and possibly ULift version).

## Verification

- EXIT=0
- SHA256: c63d4122cff404cdd1bbde2a06b577f806df02026476b28ff27f7d41dd055f8c
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2308EqualizerIsoFinalActual.olean, size 37424
- axioms: propext, Classical.choice, Quot.sound.
