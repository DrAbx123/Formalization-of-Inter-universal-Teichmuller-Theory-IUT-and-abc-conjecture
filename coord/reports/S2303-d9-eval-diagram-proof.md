# S2303: evaluated diagram equalities and diagram iso actual

Date: 2026-11-02. Status: all four evaluation equalities and the evaluated
diagram iso are proved. Next: limitObjIsoLimitCompEvaluation, equalizer subtype
Equiv, S2271 iso. No IsStack claim.

## 1. Actual equalities

File: tmp/sheaf/xif/paper/S2303EvalDiagramProofActual.lean

With S2303F := parallelPair (S2285f S M) (S2285g S N), T : (Over S)^op:

- S2303_obj_zero:
    (S2303F ⋙ evaluation T).obj zero = (S2206P0 S).obj T
- S2303_obj_one:
    (S2303F ⋙ evaluation T).obj one = (S2192R S).obj T
- S2303_map_left:
    (S2303F ⋙ evaluation T).map left = (S2285f S M).app T
- S2303_map_right:
    (S2303F ⋙ evaluation T).map right = (S2285g S N).app T

All by rfl, axioms propext/Classical.choice/Quot.sound.

## 2. Actual diagram iso

S2303EvalDiagramIso:
  S2303F ⋙ evaluation T ≅ S2303G T
with components eqToIso of obj_zero/obj_one; naturality discharged by simp
using map_left/map_right and eqToIso.

Axioms: propext, Classical.choice, Quot.sound.

## 3. Remaining

- compose with limitObjIsoLimitCompEvaluation to get the pointwise equalizer iso;
- build Equiv to {h // f_T h = g_T h};
- combine with S2271QHomObj_eq_subtype and NatIso.ofComponents for the final iso.

## Verification

- EXIT=0
- SHA256: de871109aed8dc7d8c67c296004c14dbf8a6af70469d8a37dfd91996f6209dc2
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2303EvalDiagramProofActual.olean, size 47984
- axioms: propext, Classical.choice, Quot.sound.
