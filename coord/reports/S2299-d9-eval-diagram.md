# S2299: evaluated diagram comparison — not completed

Date: 2026-11-02. Status: the evaluated parallel-pair diagram comparison is not
proved. S2285 R.map formula and f/g natural transformations remain actual.
No fake, no IsStack claim.

## 1. Failure

Target:

  (parallelPair (S2285f S M) (S2285g S N)) ⋙ (evaluation T)
    ≅ parallelPair ((S2285f S M).app T) ((S2285g S N).app T)

eqToIso rfl fails: the two functors are not definitionally equal.

NatIso.ofComponents with Iso.refl fails at the component type: the evaluated
parallelPair object at a component x is

  ((parallelPair f g) ⋙ evaluation T).obj x

which is not definitionally equal to

  (parallelPair (f.app T) (g.app T)).obj x.

The naturality square then also fails without the object equality.

## 2. Exact first missing

Prove the evaluated diagram comparison, e.g. by providing object equalities at
zero/one and the map equalities:

  ((parallelPair f g) ⋙ evaluation T).obj zero = (P0 S).obj T
  ((parallelPair f g) ⋙ evaluation T).obj one = (R S).obj T
  ((parallelPair f g) ⋙ evaluation T).map left = (f.app T)
  ((parallelPair f g) ⋙ evaluation T).map right = (g.app T)

using parallelPair_obj_zero/one and parallelPair_map_left/right after unfolding
evaluation. Then parallelPair.ext or NatIso.ofComponents gives the iso.

## 3. Actual inputs

S2285: R.map formula, f/g naturality, f,g natural transformations.

## 4. Status

| Item | Status |
|---|---|
| R.map formula | PROVED (S2285) |
| f/g natural transformations | BUILT (S2285) |
| evaluated diagram comparison | MISSING |
| equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: b3dc81366dbee389413f2e296b0c4a813b208d0d8777265b6319cb36b7de7754
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2299EvalDiagramIsoActual.olean, size 2344
- axioms: propext, Classical.choice, Quot.sound.
