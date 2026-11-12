# S2452: clean fibre equivalence and card

Date: 2026-11-03. LOCK released; serial S2446 compile.

## Actual

Lean:
  tmp/sheaf/xif/paper/S2446D5FinalActual.lean
  SHA256 4B4F9FACEC6015988BF08BB8CD77DAC5641E87533F92B67F7F84D2F7844ECB19
  EXIT=0
  olean SHA256 6EB578AF92C0DF055C7DEE98DEF010097B88CB7EE4D0650934B2AFE0E9DC3E23
  size 209416
  axioms propext, Classical.choice, Quot.sound; no sorryAx.

Theorems:
- s2446FiberEquiv:
    {x : (fbar f p).rootSet E // s2425RootFactor ... x = b}
    ~= {y : E // minpoly F y = b.1};
- s2446Fiber_card:
    Fintype.card fibre = b.1.natDegree.

right_inv corrected to rfl; inverse-property uses y.2.

## Exact remaining for S2217Missing

1. Fintype instance for beta = {g // g in normalizedFactors}; construct
   Set.Finite of the membership set from normalizedFactors.toFinset and use
   Set.Finite.fintype.
2. htrans: for b,x,y with rootFactor x=b, rootFactor y=b,
   - b.2 -> b.1 monic, irreducible, divides fbar;
   - minpoly.aeval -> x.1 and y.1 are roots of b.1;
   - S2339FrobTransitive -> exists n, frobBar^n x.1 = y.1;
   - convert to permBar.SameCycle using a lemma
       ((permBar ^ n) x).1 = (frobBar)^[n] x.1
     and zpow_natCast.
3. apply cycleType_eq_fiber_sizes with beta/p=rootFactor/d=natDegree;
   need normalize the Finset.univ RHS to
   ((normalizedFactors).map natDegree).filter (2 <= .).
4. S2428 filter -> factorDegrees.filter (· != 1).
5. S2440 -> rootCycleType = factorDegrees.filter (· != 1).
6. sigma = arithFrobAt -> corrected cycle-type/orbit-size theorem.

## Status

- CLEAN: S2446 fibre equivalence/card.
- S2427 sorryAx remains forbidden.
- D5 corrected theorem NOT accepted yet; no fake.
