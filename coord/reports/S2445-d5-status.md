# S2445 D5 status: clean rootPerm alignment; final S2217 application missing

Date: 2026-11-03.

## CLEAN / EXIT=0

1. tmp/sheaf/xif/paper/S2440RootPermCycleCleanActual.lean
   SHA256 88E6A0C79E2CD7FFADEAB936C157DC7CC6F887261986A3FABD95EDC2D00F53CC
   olean SHA256 34F87BFF37C5586CDA751107C7D6F70B544D6DF312A3AEBF1B074643A2F330B9
   size 269680
   axioms propext, Classical.choice, Quot.sound; no sorryAx.
   key theorems:
   - s2440_cycleType_permCongr;
   - s2440RootSetEquiv (codomain = (f.map algebraMap O_K K).rootSet L);
   - s2440RootPermBar_agrees_rootPerm;
   - s2440RootPermBar_eq_permCongr_rootPerm;
   - s2440RootPermBar_cycleType_rootCycleType;
   - s2440_permBar_cycleType_eq_rootCycleType.

2. tmp/sheaf/xif/paper/S2428FilterBridgeActual.lean
   SHA256 487D12CE98D6186F8FB8CF212B9888C476FD715685415F18EAFA780135A1D311
   olean SHA256 0DE405A566CEB875A110D0F24BEB37E30112F7FA0717DEF6547687820A49DA7B
   size 127608
   s2428_filter_two_le_map, s2428_filter_fiberSizes_eq_factorDegrees_filter
   axioms trio; no sorryAx.

3. S2420 and S2425 also clean (see S2432 audit).

## BROKEN (not used)

S2427RootPermCycleActual.lean contains sorryAx in four rootPerm/cycle
theorems; not imported by S2440 and not used.

## Exact first missing for final S2217Missing

A clean application of S2217 cycleType_eq_fiber_sizes to
permBar and s2425RootFactor.  The remaining formal gap is the fibre-card
conversion:

- cycleType_eq_fiber_sizes needs, for every normalized factor b,
  Fintype.card {x : (fbar f p).rootSet E // s2425RootFactor x = b} = b.1.natDegree.
- S2408FiberSet_ncard gives
  (s2408FiberSet b.1).ncard = b.1.natDegree.
- Need an actual equivalence between the fibre subtype and the subtype
  {y : O_L/P // minpoly F y = b.1}; forward x |-> x.1, backward needs
  root membership of y from b.1 | fbar and minpoly.aeval.
- Then transitivity on each fibre is S2339FrobTransitive; S2428 converts the
  filtered multiset to factorDegrees.filter (· != 1); S2440 transfers
  permBar cycle type to rootCycleType.

Until this fibre-card equivalence is written, no inhabitant of S2217Missing
or of the corrected Dedekind-Frobenius theorem is claimed.  The final
integration subagent did not produce a clean file in this session.

## Conclusion

- CLEAN: S2440, S2428, S2420, S2425.
- BROKEN: S2427 (sorryAx), disabled.
- MISSING: fibre-card equivalence and final cycleType_eq_fiber_sizes
  application.
- no fake; D5 not announced complete.
