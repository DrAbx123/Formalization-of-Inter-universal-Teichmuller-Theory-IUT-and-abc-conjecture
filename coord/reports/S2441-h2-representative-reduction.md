# S2441: actual levelwise H^2 representatives and the exact compatibility gap

Date: 2026-11-03. Layer O. Consumer: S2440/S2427/S2114/S2112.

## Build recovery

lake exe cache get succeeded (EXIT=0, 53290 ms); restored Mathlib/Tactic/Widget/LibraryRewrite and Mathlib/MeasureTheory/Integral/Bochner/Set (+.private), UniformField.
Minimal gate lake env lean -j1 tmp/sheaf/xif/paper/_BuildGateMinimal.lean EXIT=0. Lock tmp/xif_build.lock released; status in tmp/xif_build_status.md.

## File

tmp/sheaf/xif/paper/S2441H2RepresentativeActual.lean
Source SHA256 2c6b5470181916b857a1d6b1509a504cc9630b91a50c18a58e1334a2c7e87a1b
olean SHA256 52df45d1d745ef5634e95635699c2bdf50aadb84f17a2e8fcce67e64dcbba54f
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

## Built

S2441LevelRep: actual choice, for every compatible family y of level H^2 classes, of a continuous 2-cocycle representative at each level.
S2441LevelRep_spec: its image in level H^2 is y n.
S2441CompatibleLevelRep: adds exact compatibility
  twoCocycleProj n (rep (n+1)) = rep n.
S2441CocycleOfCompatibleLevelRep: from compatible levelwise family, builds the limit continuous 2-cocycle via twoCocycleExchange.
S2441CocycleOfCompatibleLevelRep_spec: its z2ToLimH2 is exactly y.
S2441LiftOfCompatibleLevelRep: hence a compatible levelwise family gives an actual S2114CompatibleRepresentativeLift.
S2441ActualRepresentativeLiftRequired_of_compatible: hence the actual representative lift.

## Exact first missing

An inhabitant of S2441CompatibleLevelRepRequired:
  forall y : LimH2, Nonempty (S2441CompatibleLevelRep p y),
i.e. a levelwise choice of 2-cocycle representatives whose projections match on the nose. Levelwise representatives alone are actual; only compatibility/projection matching is missing. Once supplied, actual S2114 lift and Surjective h2Comparison follow kernel-checked from S2441.
No unconditional representative lift or h2Comparison surjectivity is claimed.
