import tmp.sheaf.xif.paper.QPilotObjectActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.IUTIII.Theorem311.SourceArithmeticHolomorphicLanding
import LeanFormal.IUT.IUTIII.Theorem311.SourceFTimesMuPrimeStripPolyIsomorphism
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # Actual q-pilot identifications

This file attaches the identification layer to the paper q-pilot object of
QPilotObjectActual.  It identifies:

* the source strip of the object with a canonical F^value x mu-prime-strip;
* the one-column arithmetic holomorphic structure;
* the log-Kummer representation on 1,circ U_Q;
* the (1,0) binding;
* the q-pilot log-volume with the negative signed magnitude -|log q|.

Only actual project types are used.  The canonical strip and canonical
one-column structure are fields because their actual source realization is not
constructed in this file.  No PUnit, True, arbitrary Type, axiom or sorry is
used.  The identification structure is not inhabited here; existence of the
canonical objects is the exact source obligation.

The q-pilot log lemmas are proved from the actual source q completion
localSignedLog C3.q.  They are not the theta-label-1 value-layer surrogate
sourceQPilotLogVolume / card(SourceVolumeIndex l). -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.SourceLogKummerRealization
open LeanFormal.IUT.N8Closure.SourceInputBinding
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui uC3 uD3 uM uP

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-! ## 1. Identification data for the source strip, one-column structure,
and log-Kummer representation -/

/-- The actual q-pilot identifications.  The canonical source strip,
canonical one-column structure, canonical log-Kummer data and canonical
(1,0) binding are fields; the identifications with the q-pilot object are
field equalities. -/
structure QPilotIdentificationActual where
  /-- The paper q-pilot object of QPilotObjectActual. -/
  object : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} I
  /-- The canonical actual F^value x mu-prime-strip. -/
  canonicalStrip : SourceFTimesMuPrimeStrip.{uv, uM, uP} V
  /-- The source strip of the q-pilot object is the canonical strip. -/
  strip_eq : object.strip = canonicalStrip
  /-- The canonical one-column arithmetic holomorphic structure. -/
  canonicalOneColumn : SourceOneColumnArithmeticHolomorphicStructure V
  /-- The object one-column structure is the canonical one. -/
  oneColumn_eq : object.oneColumn = canonicalOneColumn
  /-- The canonical log-Kummer representation on 1,circ U_Q. -/
  canonicalLogKummer : SourceLogKummerData I object.line.C1
  /-- The object log-Kummer data is the canonical representation. -/
  logKummer_eq : object.logKummer = canonicalLogKummer
  /-- The canonical (1,0) index binding. -/
  canonicalOneZero : OneZeroPoint
  /-- The object (1,0) binding is the canonical binding. -/
  oneZero_eq : object.oneZero = canonicalOneZero

namespace QPilotIdentificationActual

variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (A : QPilotIdentificationActual (l := l) (V := V) I)

/-- The underlying paper q-pilot object. -/
abbrev qPilot : PaperQPilotObjectActual.{ua, uv, upi, umon, ui, uC3, uD3} I :=
  A.object

/-- The q-pilot log-volume read from the object. -/
def qPilotLogVolume : WithTop Real :=
  A.object.line.qPilotLogVolume

/-- The paper q-pilot magnitude |log q|. -/
def qPilotLogMagnitude : Real :=
  A.object.qPilotLogMagnitude

/-! ## 2. Identification lemmas -/

/-- The source strip of the q-pilot object is the canonical strip. -/
theorem strip_identification : A.object.strip = A.canonicalStrip :=
  A.strip_eq

/-- The one-column structure is the canonical one-column structure. -/
theorem oneColumn_identification :
    A.object.oneColumn = A.canonicalOneColumn :=
  A.oneColumn_eq

/-- The log-Kummer representation is the canonical one. -/
theorem logKummer_identification :
    A.object.logKummer = A.canonicalLogKummer :=
  A.logKummer_eq

/-- The (1,0) binding is the canonical binding. -/
theorem oneZero_identification :
    A.object.oneZero = A.canonicalOneZero :=
  A.oneZero_eq

/-- The canonical binding is the canonical (1,0) point. -/
theorem canonicalOneZero_eq : A.canonicalOneZero = oneZeroPoint :=
  A.oneZero_eq.symm.trans A.object.oneZero_eq

/-- The q-pilot log-volume is the object's line value. -/
theorem qPilotLogVolume_eq_object :
    A.qPilotLogVolume = A.object.line.qPilotLogVolume := rfl

/-- The q-pilot log-volume is the negative local q magnitude. -/
theorem qPilotLogVolume_eq_neg_magnitude :
    A.qPilotLogVolume =
      (-localLogMagnitude A.object.line.C3.q : WithTop Real) := by
  unfold qPilotLogVolume
  exact A.object.qPilotLogVolume_eq_neg_magnitude

/-- The q-pilot log-volume is the log-norm of the actual source q. -/
theorem qPilotLogVolume_eq_log_norm :
    A.qPilotLogVolume =
      (Real.log ‖A.object.line.C3.q.q‖ : WithTop Real) := by
  unfold qPilotLogVolume
  exact A.object.qPilotLogVolume_eq_log_norm

/-- The q-pilot log-volume is the negative paper magnitude |log q|. -/
theorem qPilotLogVolume_eq_neg_magnitude_def :
    A.qPilotLogVolume = (-A.qPilotLogMagnitude : WithTop Real) := by
  unfold qPilotLogVolume
  rw [show A.qPilotLogMagnitude =
    localLogMagnitude A.object.line.C3.q from
      A.object.qPilotLogMagnitude_eq_localLogMagnitude]
  exact A.object.qPilotLogVolume_eq_neg_magnitude

/-- The paper magnitude is the actual local log magnitude. -/
theorem qPilotLogMagnitude_eq_localLogMagnitude :
    A.qPilotLogMagnitude = localLogMagnitude A.object.line.C3.q :=
  A.object.qPilotLogMagnitude_eq_localLogMagnitude

/-- The q-pilot log-volume equals -|log q| in the paper magnitude notation. -/
theorem qPilotLogVolume_eq_neg_abs :
    A.qPilotLogVolume =
      (-(A.object.qPilotLogMagnitude) : WithTop Real) := by
  unfold qPilotLogVolume
  rw [show A.object.qPilotLogMagnitude =
    localLogMagnitude A.object.line.C3.q from
      A.object.qPilotLogMagnitude_eq_localLogMagnitude]
  exact A.object.qPilotLogVolume_eq_neg_magnitude

/-- The actual q is nonzero. -/
theorem sourceQ_ne_zero : A.object.line.C3.q.q ≠ 0 :=
  A.object.sourceQ_ne_zero

/-- The actual q norm is positive. -/
theorem sourceQ_norm_pos : 0 < ‖A.object.line.C3.q.q‖ :=
  A.object.sourceQ_norm_pos

/-- The actual q norm is less than one. -/
theorem sourceQ_norm_lt_one : ‖A.object.line.C3.q.q‖ < 1 :=
  A.object.sourceQ_norm_lt_one

/-! ## 3. The q-pilot region and scalar under identification -/

/-- The q-pilot region is the actual tensor-unit region. -/
theorem qPilotRegion_eq_unit :
    A.object.line.qPilotRegion =
      {(A.object.line.C3.tensorUnit : LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock
        A.object.line.C3.tensorPlaces A.object.line.C3.tensorTuple)} :=
  A.object.qPilotRegion_eq_unit

/-- The q-pilot region is nonempty. -/
theorem qPilotRegion_nonempty : A.object.line.qPilotRegion.Nonempty :=
  A.object.qPilotRegion_nonempty

/-- The tensor unit belongs to the q-pilot region. -/
theorem tensorUnit_mem_qPilotRegion :
    (A.object.line.C3.tensorUnit : LeanFormal.IUT.NumberFieldFinitePlace.ArithmeticTensorTupleBlock
      A.object.line.C3.tensorPlaces A.object.line.C3.tensorTuple) ∈
      A.object.line.qPilotRegion :=
  A.object.tensorUnit_mem_qPilotRegion

/-- The q scalar is the signed q-pilot log-volume. -/
theorem qPilotScalar_eq :
    A.object.line.qScalar = A.object.signedQPilotLogVolume :=
  A.object.qPilotScalar_eq

/-- The q scalar is negative. -/
theorem qPilotScalar_neg : A.object.line.qScalar < 0 :=
  A.object.qPilotScalar_neg

/-- The q scalar equals the negative local q magnitude. -/
theorem qPilotScalar_eq_neg_magnitude :
    A.object.line.qScalar = -localLogMagnitude A.object.line.C3.q :=
  A.object.line.qScalar_eq_neg_magnitude

/-! ## 4. The (1,0) binding -/

/-- The object (1,0) binding has first coordinate one. -/
theorem oneZero_n : A.object.oneZero.n = 1 :=
  A.object.oneZero_n

/-- The object (1,0) binding has second coordinate zero. -/
theorem oneZero_m : A.object.oneZero.m = 0 :=
  A.object.oneZero_m

/-- The canonical (1,0) binding has first coordinate one. -/
theorem canonicalOneZero_n : A.canonicalOneZero.n = 1 := by
  rw [canonicalOneZero_eq, oneZeroPoint_n]

/-- The canonical (1,0) binding has second coordinate zero. -/
theorem canonicalOneZero_m : A.canonicalOneZero.m = 0 := by
  rw [canonicalOneZero_eq, oneZeroPoint_m]

/-- Reverse identification of the canonical strip. -/
theorem canonicalStrip_eq_object : A.canonicalStrip = A.object.strip :=
  A.strip_eq.symm

/-- Reverse identification of the canonical one-column structure. -/
theorem canonicalOneColumn_eq_object :
    A.canonicalOneColumn = A.object.oneColumn :=
  A.oneColumn_eq.symm

/-- Reverse identification of the canonical log-Kummer data. -/
theorem canonicalLogKummer_eq_object :
    A.canonicalLogKummer = A.object.logKummer :=
  A.logKummer_eq.symm

/-- Reverse identification of the canonical (1,0) binding. -/
theorem canonicalOneZero_eq_object :
    A.canonicalOneZero = A.object.oneZero :=
  A.oneZero_eq.symm

/-- The q-pilot magnitude is positive. -/
theorem qPilotLogMagnitude_pos : 0 < A.qPilotLogMagnitude :=
  A.object.qPilotLogMagnitude_pos

/-- The q-pilot magnitude is nonnegative. -/
theorem qPilotLogMagnitude_nonneg : 0 ≤ A.qPilotLogMagnitude :=
  le_of_lt A.qPilotLogMagnitude_pos

theorem strip_binding_identification :
    A.object.strip = A.canonicalStrip ∧
      A.object.oneZero = A.canonicalOneZero :=
  ⟨A.strip_eq, A.oneZero_eq⟩

/-! ## 5. Exact missing fields

The structure QPilotIdentificationActual has fields for the actual source
objects not constructed in this file:

* canonicalStrip: the canonical F^value x mu-prime-strip;
* canonicalOneColumn: the canonical 1,circ arithmetic holomorphic structure;
* canonicalLogKummer: the canonical log-Kummer representation on 1,circ U_Q;
* canonicalOneZero: the canonical (1,0) binding;
* object: the paper q-pilot object of QPilotObjectActual.

The equalities are field identifications, not constructed canonical objects.
No inhabitant/existence theorem, axiom, PUnit, True, or toy instance is
asserted.  The q-pilot log lemmas are proved from the actual source q
completion and its localSignedLog, not from the theta-label-1 surrogate. -/

end QPilotIdentificationActual

end LeanFormal.IUT.N8Closure.PaperQPilotIdentificationActual

end
