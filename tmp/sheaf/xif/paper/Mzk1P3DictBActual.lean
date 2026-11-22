import tmp.sheaf.xif.paper.Mzk1P3DictionaryActual
import Mathlib.Tactic

/-!
# Mzk1P3DictBActual

GAP-P3-DICT second segment (DICT-B): explicit structure for the paper-side
(D,Q,S,T) dictionary and the integrated targetM <=> paperBox theorem.

P3DictB contains:
* the paper objects V, gap, sF, A, l, D, Q, S, Tstar, c1;
* c1_pos and the exact DICT-B identity MExpr = c1 * boxSlack;
* arithmetic candidates D_arith, Q_arith, S_arith, T_arith together with the
  explicit equalities D=D_arith etc.

The theorem targetM_nonneg_iff_paperBox is the same condition as
Mzk1P3DictionaryActual.targetM_nonneg_iff_paperBox, now packaged on P3DictB.

The arithmetic identifications D_arith=log disc, Q_arith=q coefficient,
S_arith=s^Q, T_arith=T(l)D_exact are NOT constructed here; they are the
DICT-B GAP (see coord/P3-TARGET-EQUIV.md).  The structure does not assert a
particular arithmetic value as true.

No sorry/axiom/True/PUnit/toy.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictBActual

open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual

/-- Explicit DICT-B structure: paper objects + arithmetic candidates. -/
structure P3DictB where
  V : Real
  gap : Real
  sF : Real
  A : Real
  lval : Real
  Dval : Real
  Qval : Real
  Sval : Real
  Tval : Real
  c1 : Real
  D_arith : Real
  Q_arith : Real
  S_arith : Real
  T_arith : Real
  c1_pos : 0 < c1
  M_eq : Mzk1TargetReductionActual.MExpr V gap sF A = c1 * Mzk1P3DictionaryActual.boxSlack lval Dval Qval Sval Tval
  D_eq : Dval = D_arith
  Q_eq : Qval = Q_arith
  S_eq : Sval = S_arith
  T_eq : Tval = T_arith

namespace P3DictB

/-- Integrated DICT-B theorem: target M >= 0 is the paper StepV box inequality. -/
theorem targetM_nonneg_iff_paperBox (dict : P3DictB) :
    0 <= Mzk1TargetReductionActual.MExpr dict.V dict.gap dict.sF dict.A <->
      Mzk1PaperStepVBoxActual.paperLHS dict.lval dict.Dval dict.Qval dict.Sval dict.Tval <=
        Mzk1PaperStepVBoxActual.paperRHS dict.lval dict.Dval dict.Qval dict.Sval dict.Tval :=
  Mzk1P3DictionaryActual.targetM_nonneg_iff_paperBox
    (hc1 := dict.c1_pos) (hDICTB := dict.M_eq)

/-- The explicit arithmetic candidates of DICT-B, stated separately as GAP. -/
def ArithmeticDictionary (dict : P3DictB) : Prop :=
  dict.Dval = dict.D_arith ∧ dict.Qval = dict.Q_arith ∧
    dict.Sval = dict.S_arith ∧ dict.Tval = dict.T_arith

theorem arithmeticDictionary_holds (dict : P3DictB) :
    ArithmeticDictionary dict :=
  ⟨dict.D_eq, dict.Q_eq, dict.S_eq, dict.T_eq⟩

end P3DictB

#check Mzk1P3DictBActual.P3DictB
#check P3DictB.targetM_nonneg_iff_paperBox
#check P3DictB.ArithmeticDictionary
#check P3DictB.arithmeticDictionary_holds

end LeanFormal.IUT.XiFPaper.Mzk1P3DictBActual

end
