import tmp.sheaf.xif.paper.S3137QThetaPilotLogVolumeReadingsActual
import tmp.sheaf.xif.paper.Mzk1PaperFaithful312NormedActual
import tmp.sheaf.xif.paper.Mzk1HaarProductStrictMainlineActual
import tmp.sheaf.xif.paper.Mzk1SignedLogVolumeCor312Actual
import Mathlib.Tactic

/-!
# A746 true paper 3.12 statement shape vs our normalized geometric inequality (shehdd)

## Paper shape (S3137 actual readings)
`qThetaPilotLogVolumeComparison C3 P` is DEFINITIONALLY
`qPilotLogVolumeReading P ≤ thetaPilotHullLogVolumeReal C3`, and
`qPilotLogVolumeReading P = -|Real.log (‖P.line.C3.q.q‖)|`;
`thetaPilotHullLogVolumeReal C3` is the real log of the actual tensor Haar of the
actual Theta-pilot hull (`thetaPilotHull = the tensor log-shell region`).
So the paper 3.12 shape is exactly
`-|log q| ≤ log( Haar(theta-hull) )`  (equivalently `-|log q| ≤ -|log Θ|` with the
hull log-volume as `-|log Θ|`).  This comparison is the explicit pending gap
(`Iut.Audit.qThetaPilotLogVolumeComparison`, status pending); it is NOT proved.

## Our normalized route
`Mzk1PaperFaithful312NormedActual` uses `rpVolumeNorm` and
`rpRequirementNorm`; its `Cor312Conclusion` reduces to
`log (rpVolumeNorm rpRegion) ≤ 0` — a GEOMETRIC containment inequality for the
`R/p` region versus the full region (ratio < 1).  It contains no Θ-value
arithmetic and is trivially true by construction, so it is NOT the paper statement.

The exact gap between the two is the single comparison above, on a DIFFERENT
carrier (C3 tensor vs S1902 product); no Lean bridge is proved.

No RETRACTED statement is used.  No sorry/axiom/True.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Cor312TrueStatementShapeShaActual

section PaperShape

open LeanFormal.IUT.XiFPaper.S3137QThetaPilotLogVolumeReadingsActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.C3LogShellTensorPacketActual
open LeanFormal.IUT.XiFPaper.C3LogShellTensorHolomorphicHullActual
open LeanFormal.IUT.N8Closure.PaperQPilotObjectActual
open LeanFormal.IUT.N8Closure.SourcePilotRegion

variable {l : PrimeGeFive} {V : Type} {I : OriginalInput l V}
variable (C3 : SourcePilotRegionData (l := l) (V := V) I)

/-- Exact expansion of the paper 3.12 shape in terms of `-|log q|` and the actual
theta-hull Haar log-volume. -/
theorem paper312_shape_expansion
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qThetaPilotLogVolumeComparison C3 P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤
        Real.log ((actualC3LogShellTensorHaar C3)
          (thetaPilotHull C3)).toReal := by
  unfold qThetaPilotLogVolumeComparison thetaPilotHullLogVolumeReal
  rw [qPilotLogVolumeReading_eq_neg_abs_qParameter]
  rfl

/-- Same expansion with the hull replaced by the actual tensor region. -/
theorem paper312_shape_expansion_region
    (P : PaperQPilotObjectActual (l := l) (I := I)) :
    qThetaPilotLogVolumeComparison C3 P ↔
      -|Real.log (‖P.line.C3.q.q‖)| ≤
        Real.log ((actualC3LogShellTensorHaar C3)
          (actualC3LogShellTensorRegion C3)).toReal := by
  rw [paper312_shape_expansion]
  constructor
  · intro h
    rwa [thetaPilotHull_eq_region] at h
  · intro h
    rwa [thetaPilotHull_eq_region]

end PaperShape

section OurNormalized

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1HaarProductStrictMainlineActual
open LeanFormal.IUT.XiFPaper.Mzk1SignedLogVolumeCor312Actual
open LeanFormal.IUT.XiFPaper.Mzk1PaperFaithful312NormedActual
open MeasureTheory
open scoped ENNReal BigOperators

variable {l2 : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l2)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Our normalized q-side value is the real log of the normalized rpVolume. -/
theorem ourQ_eq :
    requirementSignedQ (rpRequirementNorm T) =
      Real.log (rpVolumeNorm T (rpRegion T)) := rfl

/-- Our normalized theta-side value is ZERO (hull normalized to the full region). -/
theorem ourTheta_eq_zero :
    requirementSignedTheta (rpRequirementNorm T) = 0 := by
  unfold requirementSignedTheta signedLogVolume
  change Real.log (rpVolumeNorm T (fullRegion T)) = 0
  rw [rpVolumeNorm_fullRegion]
  exact Real.log_one

/-- Our normalized `Cor312Conclusion` is exactly the volume-ratio inequality
`log(rpVolumeNorm rpRegion) ≤ 0`, i.e. a GEOMETRIC containment fact, not the
paper's Theta-value comparison. -/
theorem ourCor312_shape :
    requirementSignedQ (rpRequirementNorm T) ≤
      requirementSignedTheta (rpRequirementNorm T) ↔
        Real.log (rpVolumeNorm T (rpRegion T)) ≤ 0 := by
  rw [ourQ_eq, ourTheta_eq_zero]

end OurNormalized

structure StrengthRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def strengthRows : List StrengthRow :=
  [ ⟨"paper 3.12 shape", "-|log q| <= log(Haar(theta-hull)) = -|log Theta|", "PENDING_GAP"⟩
  , ⟨"paper shape expansion", "paper312_shape_expansion (machine-checked iff)", "GREEN"⟩
  , ⟨"our normalized route", "Cor312Conclusion <=> log(rpVolumeNorm rpRegion) <= 0", "GEOMETRIC_ONLY"⟩
  , ⟨"our theta value", "requirementSignedTheta (rpRequirementNorm T) = 0", "GREEN"⟩
  , ⟨"exact gap", "qThetaPilotLogVolumeComparison C3 P (pending Audit obligation)", "PENDING_GAP"⟩
  , ⟨"carrier bridge", "C3 tensor carrier vs S1902 product carrier; no Lean bridge", "AUDIT_GAP"⟩
  , ⟨"scope", "strength audit only; no RETRACTED use", "INTEGRITY"⟩
  ]

theorem strengthRows_length : strengthRows.length = 7 := rfl

theorem strengthRows_has_pending_gap :
    strengthRows.any (fun r => r.status = "PENDING_GAP") = true := by
  decide

theorem strengthRows_has_geometric_only :
    strengthRows.any (fun r => r.status = "GEOMETRIC_ONLY") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1Cor312TrueStatementShapeShaActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312TrueStatementShapeShaActual.paper312_shape_expansion
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312TrueStatementShapeShaActual.paper312_shape_expansion_region
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312TrueStatementShapeShaActual.ourTheta_eq_zero
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Cor312TrueStatementShapeShaActual.ourCor312_shape
