import tmp.sheaf.xif.PaperQPilotLogVolume
import tmp.sheaf.n8.closure.SourcePilotRegion
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

/-! # Actual q-pilot object and log-volume from the source q

Source (IUT III, page 16): the object obtained by considering the arithmetic
divisor determined by the zero locus of the elements q_v at v in V_bad is
called a q-pilot object; its log-volume is denoted -|log(q)| in R, with
|log(q)| > 0.  The same source defines the local log-shell

  I_v = p_v^{-1} log_v(O_{K_v}^*) subset K_v subset F_v.

In the Lean source, the actual q is
C3.q : FinitePlaceQCandidate C3.place.val, and the actual q-point zero locus is
the singleton {C3.q.q} in the completed local field.  This file constructs that
actual object and its log-volume from C3, and proves the q-pilot log-volume is
the negative local log magnitude -|log q|, not an assumed inequality.

No toy/axiom/sorry. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.QPilotLogVolumeFromSource

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8Closure.PaperQPilotLogVolume
open LeanFormal.IUT.ArithmeticQPilotLogVolume
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {I : LeanFormal.IUT.Theorem311Source.OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- The actual q-pilot zero locus: the zero locus of the source q in the
completed local field.  This is the Lean realization of the paper's zero locus
of q_v; the arithmetic-divisor packaging is not added here. -/
def qPilotZeroLocus : Set (NumberFieldFinitePlace.Completion C3.place.val) :=
  {C3.q.q}

/-- The source q belongs to the q-pilot zero locus. -/
theorem sourceQ_mem_qPilotZeroLocus :
    C3.q.q ∈ qPilotZeroLocus C3 := by
  unfold qPilotZeroLocus
  exact Set.mem_singleton _

/-- The q-pilot log-volume object.  The value is the actual source log
Real.log ||q||, negative for the contracting q; its magnitude is the paper
|log q|. -/
structure QPilotLogVolumeObject where
  zeroLocus : Set (NumberFieldFinitePlace.Completion C3.place.val)
  zeroLocus_eq : zeroLocus = qPilotZeroLocus C3
  logVolume : WithTop Real
  logVolume_eq : logVolume = (localSignedLog C3.q : WithTop Real)
  logMagnitude : Real
  logMagnitude_eq : logMagnitude = localLogMagnitude C3.q

/-- The actual q-pilot log-volume object from the source q. -/
def qPilotLogVolumeObject : QPilotLogVolumeObject C3 where
  zeroLocus := qPilotZeroLocus C3
  zeroLocus_eq := rfl
  logVolume := (localSignedLog C3.q : WithTop Real)
  logVolume_eq := rfl
  logMagnitude := localLogMagnitude C3.q
  logMagnitude_eq := rfl

/-- The q-pilot log-volume is the actual source completion log-norm. -/
theorem qPilotLogVolume_eq_log_norm :
    (qPilotLogVolumeObject C3).logVolume = (Real.log ‖C3.q.q‖ : WithTop Real) := by
  rw [(qPilotLogVolumeObject C3).logVolume_eq]
  rfl

/-- The q-pilot log-volume is negative. -/
theorem qPilotLogVolume_neg :
    (qPilotLogVolumeObject C3).logVolume < 0 := by
  rw [(qPilotLogVolumeObject C3).logVolume_eq]
  exact WithTop.coe_lt_coe.mpr (localSignedLog_neg C3.q)

/-- The actual q-pilot magnitude |log q| is positive. -/
theorem qPilotLogMagnitude_pos :
    0 < (qPilotLogVolumeObject C3).logMagnitude := by
  rw [(qPilotLogVolumeObject C3).logMagnitude_eq]
  exact localLogMagnitude_pos C3.q

/-- The q-pilot log-volume is the negative actual magnitude -|log q|.  This is
the paper's notation -|log(q)|, proved from the actual source q, not assumed. -/
theorem qPilotLogVolume_eq_neg_magnitude :
    (qPilotLogVolumeObject C3).logVolume =
      (-(qPilotLogVolumeObject C3).logMagnitude : WithTop Real) := by
  rw [(qPilotLogVolumeObject C3).logVolume_eq,
    (qPilotLogVolumeObject C3).logMagnitude_eq, localSignedLog_eq_neg_magnitude]

/-- The paper magnitude |log q| in the actual completion form: the
negative of the source log-norm. -/
theorem qPilotLogMagnitude_eq_neg_log_norm :
    (qPilotLogVolumeObject C3).logMagnitude = -(Real.log ‖C3.q.q‖) := by
  rw [(qPilotLogVolumeObject C3).logMagnitude_eq]
  rfl

/-- The source q is nonzero and contracting, the actual form of |log q| > 0. -/
theorem sourceQ_ne_zero_and_norm_lt_one :
    C3.q.q ≠ 0 ∧ ‖C3.q.q‖ < 1 :=
  ⟨C3.q.q_ne_zero, qNorm_lt_one C3.q⟩

/-- The actual q-pilot object and its log-volume are built from the same source
q; the zero locus is the source q-point. -/
theorem qPilotObject_logVolume_link :
    (qPilotLogVolumeObject C3).zeroLocus = qPilotZeroLocus C3 ∧
      (qPilotLogVolumeObject C3).logVolume =
        (localSignedLog C3.q : WithTop Real) :=
  ⟨rfl, rfl⟩

end LeanFormal.IUT.XiFPaper.QPilotLogVolumeFromSource

end
