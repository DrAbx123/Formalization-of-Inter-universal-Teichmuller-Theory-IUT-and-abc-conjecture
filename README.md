# Unfinished 100% AI LeanFormal IUT audit project

## Where to resume (2026-11-22)

> **With limited time or compute, follow one point.** In the fixed example for IUT III, Corollary 3.12, use the paper's evaluation map to construct $z=E_\tau(1)$ and prove that it belongs to $U_{2,3}$, the region of allowed images in row 2 at the prime 3.

**What the model already shows.** Fix $p=3$, $\ell=5$, and $d=3$. The labels `G` and `B` denote good and bad places. In the target tuple `(G,B,B)`, the default mark is at slot 2, where the projection of the reference point has absolute value $3^{-6/5}$. Swapping slots 2 and 0 carries the reference point `1` and its mark from good slot 2 of `(B,B,G)` to good slot 0 of `(G,B,B)`. Every designated projection of the transported point equals `1`. The open step is to show that the paper permits this marked output for the same input. [Reindexing theorem](Iut/Concrete/Ind1Invariance.lean#L592) · [Handoff, section 19.3](coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#193-%E5%8E%9F%E6%96%87%E6%9D%A5%E6%BA%90%E6%A1%A5%E7%9A%84%E7%B2%BE%E7%A1%AE%E5%BD%A2%E7%8A%B6)

1. **Start at the diagram in IUT III, Remark 3.10.2.** Its bottom arrow `env → gau` is the evaluation from IUT II, Corollary 4.10(ii). For a compatible choice of representatives, the six arrows of the cross-column identification (IPL) reduce at the prime-strip level to two. Follow the bottom arrow `LGP → lgp`, then the vertical Kummer arrow at `lgp`. Trace the point `1` of `(B,B,G)` and its mark at slot 2 through both arrows into column 1. [Diagram in the paper](coord/IUT-TEXT/III.txt#L9069) · [Derivation of identity (15.1a)](coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#152-%E5%9B%BA%E5%AE%9A-293%E5%B0%86%E6%88%90%E5%8A%9F%E8%AF%81%E4%B9%A6%E5%8E%8B%E5%88%B0%E4%B8%80%E4%B8%AA%E5%8D%95%E4%BD%8D%E6%88%96%E5%8E%9F%E8%BE%93%E5%87%BA%E7%9A%84%E4%B8%A4%E4%B8%AA%E6%95%B0)
2. **Prove membership.** Exhibit an allowed output $D_\tau$ in the target column for this fixed input. Identify $z$ in that output and its projection at slot 0, then prove $z\in U_{2,3}$. If multiplication by $z$ preserves a full $\mathbf Z_3$-lattice $L$ in the specified tensor block, a nonzero determinant on $L/3L$ certifies that every designated projection of this same point is a unit. [Definition of the allowed images](coord/IUT-TEXT/III.txt#L10376) · [Mod 3 test and its hypotheses](coord/GRH-METHODS-FOR-IUT-20261122.md#iii312-%E5%9B%BA%E5%AE%9A%E8%BE%93%E5%85%A5%E4%B8%8A%E7%9A%84%E5%88%A4%E6%8D%AE)
3. **Stop at this tuple.** Once membership is proved, record the proof and stop. If an arrow gives only an unmarked scalar or a formal permutation, record the last object that still carries the mark, the domain and codomain of the missing map, and the statement needed from the paper. That is the stopping point for this attempt.

**After membership is proved.** Use compatibility of the same evaluation with reindexing to handle the transposition `(2,1)` and the other affected tuples. Check the rank normalization and weights in the paper's readout to obtain the comparison for this fixed input. The comparison for general inputs and finiteness of the hull's log-volume remain open on the route to the height estimates in IUT IV and the integer ABC conjecture. [Handoff, section 19.5](coord/R0-R7-THETA-COMPARISON-HANDOFF-20261118.md#195-%E6%9A%82%E5%81%9C%E7%82%B9%E9%AA%8C%E6%94%B6%E5%92%8C%E4%B8%8B%E4%B8%80%E5%8A%A8%E4%BD%9C) · [Project goals](GOAL.md)

[Project notes](./%E5%BF%83%E5%BE%97.md)

This repository is a source-oriented, auditable Lean 4 project for the
bottom-up study of Mochizuki's IUT I--IV papers and the ABC bridge.  The
production entry point is `LeanFormal/IUT/Project.lean`; the root library
`LeanFormal.lean` imports that entry point only.

The ordinary arithmetic, theta-kernel, labelled-coordinate, and weighted-volume
foundations use Mathlib directly.  IUT-specific constructions are separated
from interfaces and marked obligations.  The Theorem 3.11 -> Corollary 3.12
Step XI contract remains open.  The repository has no accepted proof of IUT or ABC.

The source corpus and citation/dependency map are under
`papers/motizuki_corpus/`.  The per-module status and exact verification
history are maintained in `AUDIT_LEDGER.md`.

The previous independent real-analysis exercise is retained, but quarantined
at `LeanFormal/Archive/AnalysisExercise/Basic.lean` and is not part of the IUT
production entry point.

## Versions

- Lean: `v4.32.2`
- Mathlib: `v4.32.2`

## Verify

Run Lean verification through the watchdog. Add the affected `.lean` path to
[extra-targets.txt](dag/watchdog/extra-targets.txt) and read its `DONE` or `FAIL`
entry in `dag/watchdog/watchdog.log`. [Watchdog instructions](coord/LEAN-INDEX.md)

# If it've benefited your project, I'll more than excited.
# It's paused cause the ability of the AI is far more than enough to achieve the goal
