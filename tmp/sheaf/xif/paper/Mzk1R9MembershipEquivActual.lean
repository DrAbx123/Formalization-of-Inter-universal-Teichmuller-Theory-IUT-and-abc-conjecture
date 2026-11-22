import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardHullRealR9PointMembershipAudit

/-!
# Mzk1R9MembershipEquivActual — derived equivalence of the R9 comparison forms
(new theorem from the existing R9 membership audit asset: pointwise point-volume form
equivalent to the log-degree form). No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.Mzk1R9MembershipEquivActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Derived: the pointwise point-volume comparison form is equivalent to the log-degree
comparison form for the R9 hull membership statement (composition of the two existing
equivalences in the R9 audit asset). -/
theorem r9_pointwise_iff_logDegree (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    ((∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v z ≤ I.sourceImageVolume v R n) ↔
      (∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ (I.sourceImageVolume v R n).toReal)) :=
  Iff.trans
    (Iff.symm (LeanFormal.IUT.Theorem311Source.OriginalInput.sourceHullVolume_le_iff_pointwise_pointVolume_le I v R n))
    (LeanFormal.IUT.Theorem311Source.OriginalInput.sourceHullVolume_le_iff_points_logDegree_le_toReal I v R n)

/-- Derived: the R9 hull comparison is equivalent to the log-degree comparison. -/
theorem r9_hull_le_iff_logDegree (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourceLocalLogDegree v z ≤ (I.sourceImageVolume v R n).toReal :=
  LeanFormal.IUT.Theorem311Source.OriginalInput.sourceHullVolume_le_iff_points_logDegree_le_toReal I v R n

/-- Derived: the R9 hull comparison is equivalent to the pointwise point-volume form. -/
theorem r9_hull_le_iff_pointwise (v : V) (R : I.SourceImageRealization v)
    (n : ThetaPilotCarrier l) :
    I.sourceHullVolume v R n ≤ I.sourceImageVolume v R n ↔
      ∀ z ∈ (I.sourceHolomorphicHull v R n : Set (I.ThetaPilotPoint v)),
        I.sourcePointVolume v z ≤ I.sourceImageVolume v R n :=
  LeanFormal.IUT.Theorem311Source.OriginalInput.sourceHullVolume_le_iff_pointwise_pointVolume_le I v R n

#check r9_pointwise_iff_logDegree
#check r9_hull_le_iff_logDegree
#check r9_hull_le_iff_pointwise

end LeanFormal.IUT.XiFPaper.Mzk1R9MembershipEquivActual
end
