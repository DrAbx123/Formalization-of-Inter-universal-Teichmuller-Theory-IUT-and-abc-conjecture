import tmp.sheaf.xif.paper.Mzk1P3DictBActual
import tmp.sheaf.xif.paper.Mzk1DExactActual
import Mathlib.Tactic

/-! # CONDITIONAL: P3DictB builder with D_arith = nativeDExact -/

noncomputable section
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictBDArithNativeActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1DExactActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictBActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetReductionActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperStepVBoxActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- P3DictB with the actual nativeDExact as both Dval and D_arith. -/
noncomputable def P3DictB.ofNativeDExact
    (arch : Real)
    (V gap sF A lval Qval Sval Tval c1 : Real)
    (hc1 : 0 < c1)
    (hM : Mzk1TargetReductionActual.MExpr V gap sF A =
      c1 * Mzk1P3DictionaryActual.boxSlack lval
        (nativeDExact T arch) Qval Sval Tval) :
    Mzk1P3DictBActual.P3DictB where
  V := V
  gap := gap
  sF := sF
  A := A
  lval := lval
  Dval := nativeDExact T arch
  Qval := Qval
  Sval := Sval
  Tval := Tval
  c1 := c1
  D_arith := nativeDExact T arch
  Q_arith := Qval
  S_arith := Sval
  T_arith := Tval
  c1_pos := hc1
  M_eq := hM
  D_eq := rfl
  Q_eq := rfl
  S_eq := rfl
  T_eq := rfl

/-- Integrated target/box equivalence for the nativeDExact D candidate. -/
theorem ofNativeDExact_target_iff
    (arch : Real)
    (V gap sF A lval Qval Sval Tval c1 : Real)
    (hc1 : 0 < c1)
    (hM : Mzk1TargetReductionActual.MExpr V gap sF A =
      c1 * Mzk1P3DictionaryActual.boxSlack lval
        (nativeDExact T arch) Qval Sval Tval) :
    0 <= Mzk1TargetReductionActual.MExpr V gap sF A <->
      Mzk1PaperStepVBoxActual.paperLHS lval (nativeDExact T arch)
          Qval Sval Tval <=
        Mzk1PaperStepVBoxActual.paperRHS lval (nativeDExact T arch)
          Qval Sval Tval :=
  Mzk1P3DictBActual.P3DictB.targetM_nonneg_iff_paperBox
    (P3DictB.ofNativeDExact (T := T) arch V gap sF A lval Qval Sval Tval c1 hc1 hM)

#check P3DictB.ofNativeDExact
#check ofNativeDExact_target_iff
end LeanFormal.IUT.XiFPaper.Mzk1P3DictBDArithNativeActual
end
