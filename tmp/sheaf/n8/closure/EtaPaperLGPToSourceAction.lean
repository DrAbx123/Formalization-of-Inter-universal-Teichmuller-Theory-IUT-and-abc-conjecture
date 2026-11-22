import tmp.sheaf.n8.closure.EtaSourceTheorem311Qualification
import tmp.sheaf.n8.closure.C4IndActionPaperAttempt
import tmp.sheaf.n8.closure.SourceWitnessedOutput
import tmp.sheaf.n8.closure.EtaSourceActionCarrierCorrected

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Paper LGP to source action / C4 carrier

Actual part: the completion realization gives actual packet, vertical and
evaluation fields; its realization procession is actually equal to the paper
LGP procession.  The actual LGP ind1/ind2 action on that realization is
attached.  The completion has no C4/ThetaPilot carrier: no OriginalInput, no
SourceWitnessedOutputData, no map from the LGP Choice index to ThetaPilotCarrier
or ThetaPilotPoint, and no compatibility with C4.U.  No arbitrary map is made.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.EtaSourceTheorem311Qualification
open LeanFormal.IUT.N8Closure.EtaLGPProcessionNondegenerate
open LeanFormal.IUT.N8Closure.C4IndActionPaperAttempt
open LeanFormal.IUT.N8Closure.EtaSourceActionCarrierCorrected
open ABCBridge.N8.C4Actual
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.ConcreteFiniteTheorem311

namespace LeanFormal.IUT.N8Closure.EtaPaperLGPToSourceAction

universe u v w ua uv upi umon ui

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual realization procession of the fifth card. -/
noncomputable def paperRealizationProcession
    (I : SourceWithFiveQualifications (X := X)) :
    SourceLGPProcession l ℤ ℕ :=
  I.completion.realization.procession

/-- Actual equality: the realization procession is the paper LGP procession. -/
theorem paperRealizationProcession_eq_paperLGP
    (I : SourceWithFiveQualifications (X := X)) :
    paperRealizationProcession (X := X) I =
      paperLGPProcession (X := X) I :=
  by
    simpa [paperRealizationProcession, paperLGPProcession] using
      I.completion.realization_procession

/-- Actual packet attached to the realization procession. -/
noncomputable def paperPacket
    (I : SourceWithFiveQualifications (X := X)) :
    SourcePacketRealization (paperRealizationProcession (X := X) I) :=
  I.completion.realization.packet

/-- Actual vertical realization attached to the realization packet. -/
noncomputable def paperVertical
    (I : SourceWithFiveQualifications (X := X)) :
    SourceVerticalRealization (paperRealizationProcession (X := X) I)
      (paperPacket (X := X) I) :=
  I.completion.realization.vertical

/-- Actual evaluation bridge attached to the realization data. -/
noncomputable def paperEvaluation
    (I : SourceWithFiveQualifications (X := X)) :
    SourceEvaluationBridge (paperRealizationProcession (X := X) I)
      (paperPacket (X := X) I) (paperVertical (X := X) I) :=
  I.completion.realization.evaluation

/-- Actual LGP ind1/ind2 action on the realization procession. -/
noncomputable def paperRealizationAction
    (I : SourceWithFiveQualifications (X := X)) :
    LGPSourceActionCarrier (paperRealizationProcession (X := X) I) :=
  lgpSourceActionCarrier (paperRealizationProcession (X := X) I)

theorem paperRealizationAction_laws
    (I : SourceWithFiveQualifications (X := X)) :
    (paperRealizationAction (X := X) I).action1 0 = 1 :=
  (paperRealizationAction (X := X) I).action1_zero

/-- Exact C4/ThetaPilot carrier bridge target: maps from the LGP choice index
to the actual C4 theta-pilot carrier and point.  This is the missing carrier
data; it is not constructed from the completion fields. -/
structure C4ThetaPilotCarrierBridge
    {V : Type uv} (OI : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) OI (Multiplicative ℤ)) where
  pilotMap : ℕ → ThetaPilotCarrier l
  thetaMap : ℕ → OI.ThetaPilotPoint C4.place.v

/-- Exact gap predicate: no C4ThetaPilotCarrierBridge is supplied by the
completion. -/
def MissingC4ThetaPilotCarrierMap : Prop :=
  ∀ {V : Type uv} (OI : OriginalInput.{ua, uv, upi, umon, ui} l V)
    (C4 : SourceWitnessedOutputData (l := l) (V := V) OI (Multiplicative ℤ)),
      ¬ Nonempty (C4ThetaPilotCarrierBridge OI C4)

end LeanFormal.IUT.N8Closure.EtaPaperLGPToSourceAction

end