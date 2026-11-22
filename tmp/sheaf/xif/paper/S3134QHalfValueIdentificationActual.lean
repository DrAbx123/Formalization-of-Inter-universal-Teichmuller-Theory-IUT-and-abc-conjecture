import tmp.sheaf.xif.paper.S3134LastSeamExactMissingActual

/-!
# S3134 task-35: sharpened q-half — actual q-value equality, and the q < 1 source condition

**Component, not paper object.**  The last-seam q half
(`S3134LastSeamQHalf`: actual fourth-triangle signed q readout = Stage-2 signed q
readout) is shrunk here to the equality of two *actual q values* of the same fixed
input C:

  `S3134QParameter J = ‖P.line.C3.q.q‖`

(the actual `(1,0)`-column q of the fourth triangle vs. the actual C3 source
completion q norm).  Equality of these actual numbers CONSTRUCTS the q half
(proved below).  The converse needs the paper source condition `q < 1` at the
bad-reduction places (IUT I, Def. 3.1, (b); IUT III, Cor. 3.12, corpus
`III-T.txt:10349-10352`, where `|log q| > 0`); for an abstract `OriginalInput`
the tree does not prove `q < 1`, so it is recorded as a source obligation, and
its consequence `log q != 0` (the q field of `S3134QThetaComparisonGap`) is
derived from it.

Owner of the remaining q-value equality: mainline/qpilot same-C model
instantiation M2 (`S3131BadTensorPrimeMatch`; IUT I Example 3.2(iv); IUT III
Def. 3.8(i) p. 112).  Consumer: shehdd's `S3134LastSeamExactMissingActual` /
`S3134FourthTriangleResidual_of_exactMissing`.

No sorry/axiom/arbitrary carrier.  WRITE-ONLY: no lake/lean.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.XiFPaper.S3134FourthJointQThetaActual
open LeanFormal.IUT.XiFPaper.S3134Step3115To312Actual
open LeanFormal.IUT.XiFPaper.S3134LastSeamExactMissingActual

namespace LeanFormal.IUT.XiFPaper.S3134QHalfValueIdentificationActual

universe uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {V0 : Type} {I0 : OriginalInput l V0}
variable (J : OriginalInput.{0, uv, upi, umon, ui} l V)
variable (P : PaperQPilotObjectActual (l := l) (I := I0))

/-- The sharpened q-half residual: equality of the two actual q values of the
same fixed input C. -/
def S3134SameCQParameterIdentification : Prop :=
  S3134QParameter J = ‖P.line.C3.q.q‖

/-- Construction: equality of the two actual q values gives the q half. -/
theorem S3134LastSeamQHalf_of_qParameterIdentification
    (h : S3134SameCQParameterIdentification (J := J) P) :
    S3134LastSeamQHalf (J := J) P :=
  S3134LastSeamQHalf_of_qParameter_eq (J := J) P h

/-- Construction: equality of the two actual q values gives the field-level q
exact missing (magnitude form). -/
theorem S3134LastSeamQMissing_of_qParameterIdentification
    (h : S3134SameCQParameterIdentification (J := J) P) :
    S3134LastSeamQMissing (J := J) P :=
  (S3134LastSeamQHalf_iff_magnitudes (J := J) P).mp
    (S3134LastSeamQHalf_of_qParameterIdentification (J := J) P h)

/-- The paper source condition at the bad-reduction places: the actual q
parameter is contracting, `q < 1` (IUT I Def. 3.1(b); IUT III Cor. 3.12,
`|log q| > 0`).  Not a consequence of the abstract `OriginalInput` data. -/
def S3134QParameterContracting : Prop :=
  S3134QParameter J < 1

/-- Contracting q gives `log q != 0`: this discharges the q field of
`S3134QThetaComparisonGap`. -/
theorem S3134QParameter_log_ne_zero_of_contracting
    (h : S3134QParameterContracting (J := J)) :
    Real.log (S3134QParameter J) ≠ 0 :=
  (Real.log_neg (S3134QParameter_pos (J := J)) h).ne

/-- Contracting q gives `|log q| > 0`. -/
theorem S3134QParameter_abs_log_pos_of_contracting
    (h : S3134QParameterContracting (J := J)) :
    0 < |Real.log (S3134QParameter J)| :=
  abs_pos.mpr (S3134QParameter_log_ne_zero_of_contracting (J := J) h)

#check S3134SameCQParameterIdentification
#check S3134LastSeamQHalf_of_qParameterIdentification
#check S3134LastSeamQMissing_of_qParameterIdentification
#check S3134QParameterContracting
#check S3134QParameter_log_ne_zero_of_contracting
#check S3134QParameter_abs_log_pos_of_contracting

end LeanFormal.IUT.XiFPaper.S3134QHalfValueIdentificationActual
