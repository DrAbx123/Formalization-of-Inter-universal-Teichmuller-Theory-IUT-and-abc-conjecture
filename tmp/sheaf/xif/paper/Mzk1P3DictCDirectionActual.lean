import tmp.sheaf.xif.paper.Mzk1P3DictionaryActual
import tmp.sheaf.xif.paper.Mzk1DExactLowerActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import Mathlib.Tactic

/-!
# Mzk1P3DictCDirectionActual

DICT-C direction analysis.

Paper box: 0 <= boxSlack l D Q S Tstar
L6:        L6ReducedInequality C l D_exact

Proved:
* L6 + S>=0 + Tstar>=0 + l>=5 => 0 <= boxSlack l D Q S Tstar
  (L6 gives D>=0 because T(l)>0 and e log p>=0).
* The reverse implication boxSlack>=0 => L6 is FALSE in general:
  for C with p=2,e=1, l=5,D=0,S=T=0,Q=0, boxSlack=0 but L6 fails.

Therefore DICT-C is not a two-way algebraic equivalence: it needs an additional
D=D_exact + lower-bound source, not present in the tree.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictCDirectionActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual
open LeanFormal.IUT.XiFPaper.Mzk1DExactLowerActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.Mzk1ThetaDataLegalityActual

/-- One direction: L6 plus nonnegative S,T and l>=5 implies the paper box. -/
theorem boxSlack_nonneg_of_L6
    (C : PrimeConductorCurve) (l D Q S Tstar : Real)
    (hl : 5 <= l) (hS : 0 <= S) (hT : 0 <= Tstar)
    (hL6 : L6ReducedInequality C l D) :
    0 <= boxSlack l D Q S Tstar := by
  have hlpos : 0 < l := by linarith
  have hTpos : 0 < T l := T_pos_of_five_le hl
  have hlogp : 0 <= Real.log (C.p : Real) := by
    have hp1 : (1 : Real) <= (C.p : Real) := by exact_mod_cast C.hp.one_lt.le
    exact Real.log_nonneg hp1
  have he : 0 <= (C.e : Real) * Real.log (C.p : Real) :=
    mul_nonneg (by positivity) hlogp
  have hTD : 0 <= T l * D := le_trans he hL6
  have hD : 0 <= D := (mul_nonneg_iff_of_pos_left hTpos).mp hTD
  rw [boxSlack_eq l D Q S Tstar (ne_of_gt hlpos)]
  have h1 : 0 <= (1 / l) * D :=
    mul_nonneg (one_div_nonneg.mpr hlpos.le) hD
  have h2 : 0 <= (1 / l) * S :=
    mul_nonneg (one_div_nonneg.mpr hlpos.le) hS
  have hcoef : 0 <= (2 * l - 10) / 3 := by nlinarith
  have h3 : 0 <= ((2 * l - 10) / 3) * Tstar := mul_nonneg hcoef hT
  linarith

/-- Prime-conductor carrier p=2,e=1 (pure test object for the reverse failure). -/
def Ctwo : PrimeConductorCurve where
  p := 2
  hp := by norm_num
  e := 1

/-- Reverse implication fails: boxSlack=0 does not imply L6. -/
theorem boxSlack_nonneg_not_implies_L6 :
    exists C : PrimeConductorCurve, exists D Q S Tstar l : Real,
      0 <= boxSlack l D Q S Tstar ∧ ¬ L6ReducedInequality C l D := by
  refine Exists.intro Ctwo (Exists.intro 0 (Exists.intro 0 (Exists.intro 0
    (Exists.intro 0 (Exists.intro 5 ?_)))))
  constructor
  · unfold boxSlack paperLHS paperRHS
    norm_num
  · unfold L6ReducedInequality T
    norm_num [Ctwo]
    have hlog : 0 < Real.log (2 : Real) := Real.log_pos (by norm_num)
    linarith

#check boxSlack_nonneg_of_L6
#check Ctwo

/-- If D = D_exact and L7 (DExactLowerTarget) holds, then L6 follows via the
green l6Reduced_of_dExactLower (Mestre-Oesterle + ThetaDataLegality + logp>=0).
Note: boxSlack is kept as an explicit hypothesis to match the proposed DICT-C
conditional, but the proof shows it is not needed: L7 alone already gives L6.
BoxSlack >= 0 therefore cannot be the missing reverse source by itself. -/
theorem L6ReducedInequality_of_DExactLower_and_box
    (hMO : MestreOesterleBound) (C : PrimeConductorCurve)
    (l : Nat) (L : ThetaDataLegality C l) (D D_exact Q S Tstar : Real)
    (hD : D = D_exact)
    (hL7 : DExactLowerTarget C (l : Real) D_exact)
    (hlogp : 0 <= Real.log (C.p : Real))
    (_hbox : 0 <= boxSlack (l : Real) D Q S Tstar) :
    L6ReducedInequality C (l : Real) D := by
  rw [hD]
  exact l6Reduced_of_dExactLower hMO C l L D_exact hL7 hlogp

#check L6ReducedInequality_of_DExactLower_and_box

#check boxSlack_nonneg_not_implies_L6

end LeanFormal.IUT.XiFPaper.Mzk1P3DictCDirectionActual

end
