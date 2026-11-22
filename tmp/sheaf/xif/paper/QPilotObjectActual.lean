import tmp.sheaf.n8.closure.C9Paper
import tmp.sheaf.n8.closure.SourceInputBinding
import tmp.sheaf.n8.closure.SourceLogKummerRealization
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # Paper-level q-pilot object at (1,0)

This file builds the actual paper q-pilot object at (1,0) from actual project
types.  It is not the theta-label-1 value-layer surrogate of
SourceXiFConstruction.

Layers:
* source strip: actual SourceFTimesMuPrimeStrip V;
* q-pilot line/rank-one data: actual C3 q data, actual q-pilot tensor-unit
  region, actual q scalar, and actual q-pilot log-volume;
* log-Kummer representation on 1,circ U_Q: actual SourceLogKummerData plus an
  actual SourceOneColumnArithmeticHolomorphicStructure;
* (1,0) binding: actual integer indices n=1, m=0.

The fields C1, C2, C3, strip, oneColumn and logKummer are actual source
objects not constructed in this file.  No PUnit, True, arbitrary Type, axiom or
sorry is used.  The object is not inhabited here; existence is the source
obligation.

The signed q-pilot log-volume is localSignedLog C3.q = Real.log ||C3.q.q||,
negative; its negative is the paper magnitude |log q|.  This is the actual
q-side log, not sourceQPilotLogVolume / card(SourceVolumeIndex l). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.dupNamespace false

namespace LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.ArithmeticQPilotLogVolume

universe ua uv upi umon ui uC3 uD3 uM uP

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. The (1,0) index binding -/

structure OneZeroPoint where
  n : Int
  m : Int
  n_eq : n = 1
  m_eq : m = 0

def oneZeroPoint : OneZeroPoint where
  n := 1
  m := 0
  n_eq := rfl
  m_eq := rfl

@[simp] theorem oneZeroPoint_n : oneZeroPoint.n = 1 := rfl

@[simp] theorem oneZeroPoint_m : oneZeroPoint.m = 0 := rfl

theorem oneZeroPoint_eq (P : OneZeroPoint) : P = oneZeroPoint := by
  cases P with
  | mk n m hn hm =>
    cases hn
    cases hm
    rfl

/-! ## 2. Actual q-pilot line/rank-one data -/

structure QPilotLineActual (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  C1 : SourceInputBinding I
  C2 : SourceLogKummerData I C1
  C3 : SourcePilotRegionData.{ua, uv, upi, umon, ui, uC3, uD3}
    (l := l) (V := V) I

namespace QPilotLineActual

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (L : QPilotLineActual (I := I))

/-- The actual q-pilot region: the C3 tensor unit.  This is the rank-one
q-pilot region, not a theta-label-1 value-layer point. -/
def qPilotRegion : Set (ArithmeticTensorTupleBlock
    L.C3.tensorPlaces L.C3.tensorTuple) :=
  {(L.C3.tensorUnit : ArithmeticTensorTupleBlock
    L.C3.tensorPlaces L.C3.tensorTuple)}

theorem qPilotRegion_eq_unit : L.qPilotRegion =
    {(L.C3.tensorUnit : ArithmeticTensorTupleBlock
      L.C3.tensorPlaces L.C3.tensorTuple)} := rfl

/-- The actual q-pilot scalar: localSignedLog of the source q. -/
def qScalar : Real :=
  localSignedLog L.C3.q

theorem qScalar_eq : L.qScalar = localSignedLog L.C3.q := rfl

/-- The actual q-pilot log-volume as WithTop Real. -/
def qPilotLogVolume : WithTop Real :=
  (L.qScalar : WithTop Real)

theorem qPilotLogVolume_eq : L.qPilotLogVolume = (L.qScalar : WithTop Real) := rfl

theorem qPilotLogVolume_eq_signed :
    L.qPilotLogVolume = (localSignedLog L.C3.q : WithTop Real) := by
  rw [L.qPilotLogVolume_eq, L.qScalar_eq]

theorem qScalar_neg : L.qScalar < 0 :=
  localSignedLog_neg L.C3.q

theorem qScalar_eq_neg_magnitude :
    L.qScalar = -localLogMagnitude L.C3.q :=
  localSignedLog_eq_neg_magnitude L.C3.q

theorem qPilotLogVolume_eq_neg_magnitude :
    L.qPilotLogVolume = (-localLogMagnitude L.C3.q : WithTop Real) := by
  unfold qPilotLogVolume qScalar
  rw [localSignedLog_eq_neg_magnitude]
  simp

theorem qPilotLogVolume_eq_log_norm :
    L.qPilotLogVolume = (Real.log ‖L.C3.q.q‖ : WithTop Real) := by
  rw [L.qPilotLogVolume_eq_signed]
  rfl

theorem tensorUnit_mem_qPilotRegion :
    (L.C3.tensorUnit : ArithmeticTensorTupleBlock
      L.C3.tensorPlaces L.C3.tensorTuple) ∈ L.qPilotRegion := by
  rw [L.qPilotRegion_eq_unit]
  exact Set.mem_singleton _

theorem qPilotRegion_nonempty : L.qPilotRegion.Nonempty :=
  ⟨_, L.tensorUnit_mem_qPilotRegion⟩

theorem qScalar_abs : |L.qScalar| = localLogMagnitude L.C3.q :=
  abs_of_neg L.qScalar_neg

end QPilotLineActual

/-! ## 3. The paper-level q-pilot object -/

structure PaperQPilotObjectActual
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  line : QPilotLineActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I)
  strip : SourceFTimesMuPrimeStrip.{uv, uM, uP} V
  oneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  logKummer : SourceLogKummerData I line.C1
  logKummer_eq : logKummer = line.C2
  oneZero : OneZeroPoint
  oneZero_eq : oneZero = oneZeroPoint

namespace PaperQPilotObjectActual

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (P : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} (I := I))

def signedQPilotLogVolume : Real :=
  localSignedLog P.line.C3.q

def qPilotLogMagnitude : Real :=
  - P.signedQPilotLogVolume

theorem qPilotLogVolume_eq_signed :
    P.line.qPilotLogVolume = (P.signedQPilotLogVolume : WithTop Real) := by
  unfold signedQPilotLogVolume
  rw [P.line.qPilotLogVolume_eq_signed]

theorem signedQPilotLogVolume_eq_log_norm :
    P.signedQPilotLogVolume = Real.log ‖P.line.C3.q.q‖ :=
  rfl

theorem signedQPilotLogVolume_neg : P.signedQPilotLogVolume < 0 :=
  localSignedLog_neg P.line.C3.q

theorem signedQPilotLogVolume_eq_neg_magnitude :
    P.signedQPilotLogVolume = -localLogMagnitude P.line.C3.q :=
  localSignedLog_eq_neg_magnitude P.line.C3.q

theorem qPilotLogMagnitude_pos : 0 < P.qPilotLogMagnitude := by
  unfold qPilotLogMagnitude
  exact neg_pos.mpr P.signedQPilotLogVolume_neg

theorem qPilotLogMagnitude_eq_localLogMagnitude :
    P.qPilotLogMagnitude = localLogMagnitude P.line.C3.q := by
  unfold qPilotLogMagnitude
  rw [signedQPilotLogVolume_eq_neg_magnitude]
  ring

theorem qPilotRegion_eq_unit :
    P.line.qPilotRegion =
      {(P.line.C3.tensorUnit : ArithmeticTensorTupleBlock
        P.line.C3.tensorPlaces P.line.C3.tensorTuple)} :=
  P.line.qPilotRegion_eq_unit

theorem sourceQ_ne_zero : P.line.C3.q.q ≠ 0 :=
  P.line.C3.q.q_ne_zero

theorem sourceQ_norm_pos : 0 < ‖P.line.C3.q.q‖ :=
  qNorm_pos P.line.C3.q

theorem sourceQ_norm_lt_one : ‖P.line.C3.q.q‖ < 1 :=
  qNorm_lt_one P.line.C3.q

theorem qPilotLogVolume_eq_neg_magnitude :
    P.line.qPilotLogVolume =
      (-localLogMagnitude P.line.C3.q : WithTop Real) :=
  QPilotLineActual.qPilotLogVolume_eq_neg_magnitude P.line

theorem qPilotLogVolume_eq_log_norm :
    P.line.qPilotLogVolume = (Real.log ‖P.line.C3.q.q‖ : WithTop Real) := by
  rw [P.line.qPilotLogVolume_eq_signed]
  rfl

theorem tensorUnit_mem_qPilotRegion :
    (P.line.C3.tensorUnit : ArithmeticTensorTupleBlock
      P.line.C3.tensorPlaces P.line.C3.tensorTuple) ∈ P.line.qPilotRegion :=
  P.line.tensorUnit_mem_qPilotRegion

theorem qPilotRegion_nonempty : P.line.qPilotRegion.Nonempty :=
  P.line.qPilotRegion_nonempty

theorem qPilotScalar_eq : P.line.qScalar = P.signedQPilotLogVolume :=
  P.line.qScalar_eq

theorem logKummer_eq_C2 : P.logKummer = P.line.C2 :=
  P.logKummer_eq

theorem sourceQ_norm_le_one : ‖P.line.C3.q.q‖ ≤ 1 :=
  le_of_lt P.sourceQ_norm_lt_one

theorem oneZero_n : P.oneZero.n = 1 := by
  rw [P.oneZero_eq, oneZeroPoint_n]

theorem oneZero_m : P.oneZero.m = 0 := by
  rw [P.oneZero_eq, oneZeroPoint_m]

theorem qPilotScalar_neg : P.line.qScalar < 0 :=
  P.line.qScalar_neg

theorem strip_oneZero_binding :
    P.strip = P.strip ∧ P.oneZero = oneZeroPoint :=
  ⟨rfl, P.oneZero_eq⟩

end PaperQPilotObjectActual

/-! ## 4. Exact source obligations

The fields of PaperQPilotObjectActual are the actual source objects that the
frozen project does not construct as a single q-pilot object: strip,
oneColumn, logKummer, C1/C2/C3 and line q data, and the (1,0) binding.

The object is a structure, not an inhabitant.  No existence theorem, axiom,
PUnit, True, or toy instance is asserted. -/

end LeanFormal.IUT.N8Closure.PaperQPilotObjectActual

end
