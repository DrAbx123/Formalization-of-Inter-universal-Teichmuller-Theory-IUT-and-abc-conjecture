import tmp.sheaf.xif.paper.GlobalThetaHullVsQPilotComparisonActual

/-!
# Paper q parameter and xi-f reduction at the global hull

The actual q-pilot signed log-volume is I.qPilotSignedLogVolume.  This file
defines the actual q parameter

  qPilotQ := Real.exp I.qPilotSignedLogVolume

and proves

  Real.log qPilotQ = I.qPilotSignedLogVolume.

Thus the paper xi-f comparison is exactly the signed comparison

  I.qPilotSignedLogVolume <= thetaHullSignedLogVolume,

equivalently

  -log qPilotQ <= - globalThetaHullLogVolume.

No local/global q equality is introduced and no comparison inequality is
asserted.  The exact comparison condition is retained; only the q parameter and
its logarithm are actual.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalHullPaperXiFActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.GlobalThetaPilotHullLogVolumeActual
open LeanFormal.IUT.XiFPaper.GlobalThetaHullVsQPilotComparisonActual

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable [Fintype V]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l)

/-- Actual paper q parameter from the signed q-pilot log-volume. -/
def paperQParameter : Real :=
  Real.exp I.qPilotSignedLogVolume

/-- The actual q parameter is positive. -/
theorem paperQParameter_pos : 0 < paperQParameter (I := I) :=
  Real.exp_pos _

/-- The logarithm of the actual q parameter is the signed q-pilot log. -/
theorem log_paperQParameter :
    Real.log (paperQParameter (I := I)) = I.qPilotSignedLogVolume := by
  unfold paperQParameter
  exact Real.log_exp _

/-- The actual q parameter is at most one, from the signed q-pilot sign. -/
theorem paperQParameter_le_one : paperQParameter (I := I) ≤ 1 := by
  unfold paperQParameter
  exact Real.exp_le_one_iff.mpr (qPilotSignedLogVolume_nonpos (I := I))

/-- The actual q parameter lies in (0,1]. -/
theorem paperQParameter_mem_Ioc : paperQParameter (I := I) ∈ Set.Ioc 0 1 :=
  ⟨paperQParameter_pos (I := I), paperQParameter_le_one (I := I)⟩

/-- The paper xi-f comparison at the global hull, stated with the actual q
parameter. -/
def PaperXiFComparison : Prop :=
  Real.log (paperQParameter (I := I)) <=
    thetaHullSignedLogVolume (I := I) R n

/-- The q-parameter form is exactly the scaled q-pilot comparison. -/
theorem PaperXiFComparison_iff :
    PaperXiFComparison (I := I) R n ↔
      I.qPilotSignedLogVolume <= thetaHullSignedLogVolume (I := I) R n := by
  unfold PaperXiFComparison
  rw [log_paperQParameter]

/-- The paper comparison is exactly the q-pilot/Theta-hull comparison. -/
theorem PaperXiFComparison_iff_qPilotThetaHull :
    PaperXiFComparison (I := I) R n ↔
      qPilotThetaHullComparison (I := I) R n := by
  rw [PaperXiFComparison_iff]
  rfl

/-- The paper comparison is exactly the global hull log-volume condition. -/
theorem PaperXiFComparison_iff_hullLogVolume :
    PaperXiFComparison (I := I) R n ↔
      globalThetaHullLogVolume (I := I) R n <= qPilotMagnitude (I := I) :=
  (PaperXiFComparison_iff_qPilotThetaHull (I := I) R n).trans
    (qPilotThetaHullComparison_iff (I := I) R n)

/-- Conditional xi-f conclusion from the exact global comparison condition. -/
theorem PaperXiFComparison_of_condition
    (h : GlobalComparisonCondition (I := I) R n) :
    PaperXiFComparison (I := I) R n :=
  (PaperXiFComparison_iff_hullLogVolume (I := I) R n).mpr h

/-- The actual q parameter and its signed log data. -/
structure GlobalHullPaperXiFData
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  qPilotQ : Real
  qPilotQ_eq : qPilotQ = paperQParameter (I := I)
  log_qPilotQ : Real
  log_qPilotQ_eq : log_qPilotQ = I.qPilotSignedLogVolume
  q_pos : 0 < qPilotQ
  q_le_one : qPilotQ ≤ 1

/-- Actual paper q parameter data. -/
noncomputable def globalHullPaperXiFData :
    GlobalHullPaperXiFData (I := I) R n where
  qPilotQ := paperQParameter (I := I)
  qPilotQ_eq := rfl
  log_qPilotQ := I.qPilotSignedLogVolume
  log_qPilotQ_eq := rfl
  q_pos := paperQParameter_pos (I := I)
  q_le_one := paperQParameter_le_one (I := I)

/-- The actual q parameter's log equality. -/
@[simp] theorem globalHullPaperXiFData_log :
    Real.log ((globalHullPaperXiFData (I := I) R n).qPilotQ) =
      I.qPilotSignedLogVolume :=
  log_paperQParameter (I := I)

/-- Paper-level xi-f scalar comparison: log q <= theta. -/
def paperXiF (q theta : Real) : Prop :=
  Real.log q <= theta

/-- The direct comparison is exactly paperXiF at the actual q parameter. -/
theorem paperXiF_paperQParameter_iff :
    paperXiF (paperQParameter (I := I))
        (thetaHullSignedLogVolume (I := I) R n) ↔
      I.qPilotSignedLogVolume <= thetaHullSignedLogVolume (I := I) R n := by
  unfold paperXiF
  rw [log_paperQParameter]

/-- PaperXiFComparison is exactly the paper-level paperXiF proposition. -/
theorem PaperXiFComparison_eq_paperXiF :
    PaperXiFComparison (I := I) R n =
      paperXiF (paperQParameter (I := I))
        (thetaHullSignedLogVolume (I := I) R n) := rfl

/-- Actual scalar data for the paper xi-f comparison. -/
structure PaperXiFScalarData
    (R : ∀ v : V, I.SourceImageRealization v) (n : ThetaPilotCarrier l) where
  q : Real
  q_eq : q = paperQParameter (I := I)
  theta : Real
  theta_eq : theta = thetaHullSignedLogVolume (I := I) R n
  log_q_eq : Real.log q = I.qPilotSignedLogVolume

/-- The actual paper xi-f scalar data. -/
noncomputable def paperXiFScalarData :
    PaperXiFScalarData (I := I) R n where
  q := paperQParameter (I := I)
  q_eq := rfl
  theta := thetaHullSignedLogVolume (I := I) R n
  theta_eq := rfl
  log_q_eq := log_paperQParameter (I := I)

/-- The positive scalar cTheta_lowerBound from the actual q parameter. -/
def cTheta_lowerBound : Real :=
  paperQParameter (I := I)

/-- The cTheta lower bound is positive. -/
theorem cTheta_lowerBound_pos : 0 < cTheta_lowerBound (I := I) :=
  paperQParameter_pos (I := I)

/-- The logarithm of cTheta_lowerBound is the signed q-pilot log. -/
theorem cTheta_lowerBound_log :
    Real.log (cTheta_lowerBound (I := I)) = I.qPilotSignedLogVolume :=
  log_paperQParameter (I := I)

/-- From the exact comparison condition, cTheta_lowerBound gives the paper xi-f
lower-bound form. -/
theorem cTheta_lowerBound_le_theta_of_exact
    (h : I.qPilotSignedLogVolume <= thetaHullSignedLogVolume (I := I) R n) :
    Real.log (cTheta_lowerBound (I := I)) <=
      thetaHullSignedLogVolume (I := I) R n := by
  rw [cTheta_lowerBound_log]
  exact h

end LeanFormal.IUT.XiFPaper.GlobalHullPaperXiFActual

end