# FACE2-VERDICT — tame-everywhere arithmetic (A899)

Status: minimal arithmetic verdict only. Not an IUT theorem, not Lean evidence.

## 1. Tame-everywhere computation

At a tame place with e = 1:
- hullPacket_tame term = (1 - 1/1) log p = 0.
- logMuPaper = (1 - 1/e - r/n) log p = (1 - 1 - r/n) log p = -(r/n) log p <= 0.
- different = -order log p - r/n + arch (arch only at infinity; finite tame place no arch).

Thus on the hull side every tame finite place contributes 0 (or negative via -r/n).
The q side contributes (sF-1)*A with A = |log q| > 0 and sF = sFactor(nC) > 1,
strictly positive for nontrivial q.

## 2. Verdict

In the tame-everywhere model with no wild places and no arch contributions:
    LHS = (sF-1) A > 0,   RHS = V_hull = 0 (finite tame) [+ arch],
so the inequality
    (sF-1) A <= V_hull
**FAILS** (strictly).  It can only hold if some positive RHS source exists:
wild different/shell buffer (e > 1 gives 1 - 1/e > 0), or arch/infinity terms.

Therefore attack face 2 (tame-everywhere) is **not provable from the object
definitions**: it requires either a wild-place positive buffer or an additional
hypothesis D_exact >= c*A, which is exactly the target inequality.
**Not feasible as an unconditional route**; tame-everywhere is a counterexample
direction (RHS zero), not a proof direction.

## 3. Consequence

- Do not claim tame-everywhere; the L7 tame chain assumed e >= l, which excludes e = 1.
  L7 must be read with e >= l (wild/tame split).
- Wild places (e > 1) with 1 - 1/e > 0 plus arch are the only possible RHS buffer;
  a lower bound D_exact >= c*A is still needed and is the target.
