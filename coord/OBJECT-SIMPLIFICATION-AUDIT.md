# Object simplification audit (2026-10-24)

Question: can we guarantee current N8/C9 objects are not simplified?
Answer: NO. This file lists known simplifications; they are not closure evidence.

| paper object | current Lean object | simplification status |
|---|---|---|
| full log-theta-lattice L | NativeLattice: family + arithmetic_alignment; no full L type | simplified / missing |
| complete source choice alpha | C4 Choice = SignedLabel; eval/Choice independent of x | simplified |
| R_alpha region family | C4 U finite point set; no admissible regions | simplified/missing |
| q-pilot full region/log-volume | C9QPilotRegion q region = singleton completion q; scalar localSignedLog | simplified |
| Theta hull target | ThetaPaper thetaHull = sourceHolomorphicHull; thetaToC6 free | simplified |
| Values output log-volumes | finite point image / arbitrary subsets | simplified |
| global L/ell_out | C6.normalizedLogVolume single tensor block | simplified; no global weights/procession |
| arithmetic degree | C8 profileArithmeticDegree; no determinant line bundle | partial |
| C4 output to IQ | named donor only; no actual map | missing |
| C2 Gv/Kummer/K1K2/arch | local log shell only | simplified/missing |
| C10 native bridge | named donor only | missing |
| +inf/archimedean | WithTop in some targets; no source branch | simplified |

## Policy

1. A file is not closure evidence if its target object is simplified unless an explicit projection/embedding theorem from the paper object is present.
2. Named sorries may record the missing identification; they cannot replace it.
3. C10 must not consume simplified objects as if they were paper objects.

## Immediate consequence

Current P6ChainA/B/P6Comparison tasks must state, per arrow, whether the object is the paper object or a simplification, and which named sorry identifies it.

No guarantee of non-simplification is made.