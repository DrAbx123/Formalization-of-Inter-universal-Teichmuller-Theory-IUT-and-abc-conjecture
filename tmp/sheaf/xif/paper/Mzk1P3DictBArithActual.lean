import tmp.sheaf.xif.paper.Mzk1P3DictBActual
import tmp.sheaf.xif.paper.Mzk1PrimeConductorRouteActual
import tmp.sheaf.xif.paper.NativeGlobalQPilotNormalizedLogVolumeActual
import Mathlib.Tactic

/-!
# Mzk1P3DictBArithActual

DICT-B actual arithmetic candidates:
* primeConductorLogDisc C := (C.e : Real) * log(C.p) is the log of the
  prime-conductor minimal discriminant under the PrimeConductorCurve carrier
  (C.e is defined as ord_p(Delta_min); the carrier has no separate Delta field).
* nativeQArith T := nativeGlobalQPilotNormalizedLogMagnitude T is the actual
  weighted native q-pilot log-magnitude.

P3DictB.ofPrimeConductorData packages these candidates with the remaining
M_eq/Q_eq identifications as explicit inputs.  It is a builder, not a proof of
DICT-B: the paper Q = (l+1)/24 log q = sF*A identification and the actual
Delta/Q dictionary remain GAP.

No sorry/axiom/True/PUnit/toy.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.Mzk1P3DictBArithActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.Mzk1P3DictBActual
open LeanFormal.IUT.XiFPaper.Mzk1PrimeConductorRouteActual
open LeanFormal.IUT.XiFPaper.NativeGlobalQPilotNormalizedLogVolumeActual
open LeanFormal.IUT.XiFPaper.Mzk1P3DictionaryActual
open LeanFormal.IUT.XiFPaper.Mzk1TargetReductionActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The prime-conductor log discriminant: e * log p. -/
noncomputable def primeConductorLogDisc (C : PrimeConductorCurve) : Real :=
  (C.e : Real) * Real.log (C.p : Real)

/-- Definitional formula for the prime-conductor log discriminant. -/
theorem primeConductorLogDisc_eq (C : PrimeConductorCurve) :
    primeConductorLogDisc C = (C.e : Real) * Real.log (C.p : Real) := rfl

/-- Actual native q-pilot arithmetic Q candidate. -/
noncomputable def nativeQArith : Real :=
  nativeGlobalQPilotNormalizedLogMagnitude T

/-- nativeQArith is exactly the native global q-pilot log-magnitude. -/
theorem nativeQArith_eq :
    nativeQArith T = nativeGlobalQPilotNormalizedLogMagnitude T := rfl

/-- Builder for P3DictB with the actual D = prime-conductor log disc and
Q_arith = native q-pilot magnitude.  M_eq and Q_eq are explicit inputs. -/
noncomputable def P3DictB.ofPrimeConductorData
    (C : PrimeConductorCurve)
    (V gap sF A lval Qval Sval Tval c1 : Real)
    (hc1 : 0 < c1)
    (hQ : Qval = nativeQArith T)
    (hM : Mzk1TargetReductionActual.MExpr V gap sF A =
      c1 * Mzk1P3DictionaryActual.boxSlack lval
        (primeConductorLogDisc C) Qval Sval Tval) :
    Mzk1P3DictBActual.P3DictB where
  V := V
  gap := gap
  sF := sF
  A := A
  lval := lval
  Dval := primeConductorLogDisc C
  Qval := Qval
  Sval := Sval
  Tval := Tval
  c1 := c1
  D_arith := primeConductorLogDisc C
  Q_arith := nativeQArith T
  S_arith := Sval
  T_arith := Tval
  c1_pos := hc1
  M_eq := hM
  D_eq := rfl
  Q_eq := hQ
  S_eq := rfl
  T_eq := rfl

/-- The integrated target/box equivalence for the actual candidate builder. -/
theorem ofPrimeConductorData_target_iff
    (C : PrimeConductorCurve)
    (V gap sF A lval Qval Sval Tval c1 : Real)
    (hc1 : 0 < c1)
    (hQ : Qval = nativeQArith T)
    (hM : Mzk1TargetReductionActual.MExpr V gap sF A =
      c1 * Mzk1P3DictionaryActual.boxSlack lval
        (primeConductorLogDisc C) Qval Sval Tval) :
    0 <= Mzk1TargetReductionActual.MExpr V gap sF A <->
      Mzk1PaperStepVBoxActual.paperLHS lval (primeConductorLogDisc C)
          Qval Sval Tval <=
        Mzk1PaperStepVBoxActual.paperRHS lval (primeConductorLogDisc C)
          Qval Sval Tval :=
  Mzk1P3DictBActual.P3DictB.targetM_nonneg_iff_paperBox
    (P3DictB.ofPrimeConductorData (l := l) T C V gap sF A lval Qval Sval Tval c1 hc1 hQ hM)

#check primeConductorLogDisc
#check primeConductorLogDisc_eq
#check nativeQArith
#check P3DictB.ofPrimeConductorData
#check ofPrimeConductorData_target_iff

end LeanFormal.IUT.XiFPaper.Mzk1P3DictBArithActual

end
