# S2295: equalizer pointwise-limit comparison — not completed

Date: 2026-11-02. Status: the pointwise limit comparison for the functor-category
equalizer is not proved. S2285 R.map formula and f/g natural transformations
remain actual. No fake, no IsStack claim.

## 1. Exact attempt and failure

The intended comparison was

  S2295EqualizerObjIso M N T :
    (Limits.equalizer (S2285f S M) (S2285g S N)).obj T
      ≅ Limits.equalizer ((S2285f S M).app T) ((S2285g S N).app T)

using limitObjIsoLimitCompEvaluation.

The term

  limitObjIsoLimitCompEvaluation
    (parallelPair (S2285f S M) (S2285g S N)) T

has codomain

  limit ((parallelPair f g) ⋙ (evaluation (Over S)^op Type).obj T),

not

  limit (parallelPair (f.app T) (g.app T)).

Thus the required diagram comparison

  (parallelPair f g) ⋙ evaluation T ≅ parallelPair (f.app T) (g.app T)

is missing.  After unfolding Limits.equalizer/parallelPair the two limit
diagrams are still not definitionally equal.

## 2. Actual inputs

From S2285:
- R.map p h = p.unop.left ≫ h;
- f/g naturality;
- f,g : S2206P0 S ⟶ S2192R S.

These are available and actual.

## 3. Remaining first missing

- pointwise diagram comparison above;
- then Equiv between equalizer object and
  {h // S2267fPoint S M T h = S2267gPoint S N T h};
- then NatIso with S2271QHomObj_eq_subtype.

## 4. Status

| Item | Status |
|---|---|
| R.map formula | PROVED (S2285) |
| f/g natural transformations | BUILT (S2285) |
| equalizer pointwise diagram comparison | MISSING |
| equalizer object Equiv | MISSING |
| equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: ac19bac939e054da118cd3999bbc2912df1485923f0fd5b3918d8caa296004bd
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2295EqualizerIsoFinalActual.olean, size 2344
- axioms: propext, Classical.choice, Quot.sound.
