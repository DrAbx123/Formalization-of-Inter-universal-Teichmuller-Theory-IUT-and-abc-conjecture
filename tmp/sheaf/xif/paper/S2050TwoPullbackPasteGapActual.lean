import tmp.sheaf.xif.paper.S2048FiniteEtaleCompSchemeActual

/-! # S2050: TwoPullbackWitness.paste gap: exact statement and coherence list

The D6(c) composition API needs the pasting of two bicategorical pullback
squares.  This file states the exact pasting problem and the required output as
Type-valued data; it does not fabricate a witness.

Geometry:
  square_1 = (P1 -> W, P1 -> S, W -> Y, S -> Y)
  square_2 = (P2 -> W, P2 -> P1, W -> Y, P1 -> Y)
and the composite square is
  (P2 -> W, P2 -> S, W -> Z, S -> Z)
with the composite commutes 2-isomorphism obtained from the two squares and
the associator/whiskering composites.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2050TwoPullbackPasteGapActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT

universe u
variable {F : Type u} [Field F]

/-- Data of two composable bicategorical pullback squares and the candidate
composite square. -/
structure S2050PasteProblem where
  W : EtaleStackPseudofunctor F
  S : EtaleStackPseudofunctor F
  Y : EtaleStackPseudofunctor F
  Z : EtaleStackPseudofunctor F
  P1 : EtaleStackPseudofunctor F
  P2 : EtaleStackPseudofunctor F
  sq1 : EtalePseudofunctorSquare P1 W S Y
  sq2 : EtalePseudofunctorSquare P2 W P1 Y
  composite : EtalePseudofunctorSquare P2 W S Z
  w1 : EtalePseudofunctorSquare.TwoPullbackWitness sq1
  w2 : EtalePseudofunctorSquare.TwoPullbackWitness sq2

/-- Exact missing pasting theorem: two composable full 2-pullback witnesses
give the full 2-pullback witness of the composite square. -/
def S2050PasteStatement : Type _ :=
  ∀ (problem : S2050PasteProblem (F := F)),
    EtalePseudofunctorSquare.TwoPullbackWitness problem.composite

/-- Required coherence inputs for the paste (documented as a list, not
asserted).

1. lift: from a cone over the composite square, build a cone over `sq1`
   (`W' -> W` and `W' -> S`, the second from the composite cone; the first
   `W' -> Y` is `W' -> W -> Y` via `sq1.xToBase`); apply `w1.lift` to get
   `W' -> P1`.  Then build a cone over `sq2` using `W' -> W` and `W' -> P1`;
   apply `w2.lift` to get `W' -> P2`.
2. liftToX: `vcomp (lift composite cone) composite.toX` is computed from
   `w2.liftToX` and `w1.liftToX` plus the associator; liftToY likewise from
   `w1.liftToY` and the second-leg comparison.
3. liftTwoCell: apply `w1.liftTwoCell` to the induced cone morphism between
   `sq1` cones, then `w2.liftTwoCell`; the two `_toX`/`_toY` equations use
   `whiskerRight_comp`, `comp_whiskerRight`, `whisker_exchange`.
4. twoCell_ext: reduce by `w2.twoCell_ext`, then by `w1.twoCell_ext`, using
   joint faithfulness of the two projections of both squares.

Items 1-4 are exactly the missing content; no `TwoPullbackWitness` is
constructed here. -/
def S2050PasteCoherenceList : List String :=
  [ "lift: two-step dependent cone lift via w1.lift and w2.lift",
    "liftToX/liftToY: associator + whisker composites of w1/w2 comparisons",
    "liftTwoCell: induced cone morphisms + w1/w2 liftTwoCell",
    "_toX/_toY: whiskerRight_comp, comp_whiskerRight, whisker_exchange",
    "twoCell_ext: w2.twoCell_ext then w1.twoCell_ext" ]

#check S2050PasteStatement

end LeanFormal.IUT.XiFPaper.S2050TwoPullbackPasteGapActual

end
