import tmp.sheaf.n8.closure.EtaRemainingDonorsAssembly
import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionFromContract
import tmp.sheaf.n8.closure.EtaSourceActionCarrierCorrected

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Actual LGP procession from the four source cards

Uses production `sourceLGPProcessionOfDefinition31Data` with the actual
`sourceDefinition31DataOfFour` derived from the four qualification layers.
Instantiation: Label = Z, Choice = Nat, base = 0.  The resulting procession is
actual but degenerate identity (production constructor), not the paper LGP; the
ind1/ind2 carrier action is attached and its laws are actual.

Exact no-go for unconditional native LGP: the constructor needs a
SourceDefinition31Data, which the four cards supply only conditionally; the
four source cards are not constructed from native S.  No arbitrary procession.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt
open LeanFormal.IUT.N8Closure.NativeTorsionClauseActual
open LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual
open LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly
open LeanFormal.IUT.N8Closure.EtaSourceWithBadFiniteCondition
open LeanFormal.IUT.N8Closure.EtaReductionRestAssemblyActual
open LeanFormal.IUT.N8Closure.EtaSplitCardSourceQualification
open LeanFormal.IUT.N8Closure.EtaSourceDefinition31NativeAttempt
open LeanFormal.IUT.N8Closure.EtaTorsionSourceQualification
open LeanFormal.IUT.N8Closure.EtaRemainingDonorsAssembly
open LeanFormal.IUT.N8Closure.EtaSourceActionCarrierCorrected
open LeanFormal.IUT.SourceProcessionAttack

namespace LeanFormal.IUT.N8Closure.EtaSourceLGPProcessionFromCards

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual SourceDefinition31Data from the four qualification layers. -/
noncomputable def sourceDataFromFour
    (I : SourceWithFourQualifications (X := X)) :
    SourceDefinition31Data.{0} l :=
  sourceDefinition31DataOfFour (X := X) I

/-- Actual LGP procession from the cards, using the production constructor
with Label = Z, Choice = Nat, base = 0. -/
noncomputable def lgpProcessionFromFour
    (I : SourceWithFourQualifications (X := X)) :
    SourceLGPProcession.{0, 0} l ℤ ℕ :=
  sourceLGPProcessionOfDefinition31Data
    (Label := ℤ) (Choice := ℕ) (sourceDataFromFour (X := X) I) 0

/-- Conditional native LGP procession: the four source cards are the exact
input condition. -/
noncomputable def conditionalNativeLGPProcession
    (h : CorrectedDefinition31TargetWithRemainingCards (X := X)) :
    SourceLGPProcession.{0, 0} l ℤ ℕ :=
  lgpProcessionFromFour (X := X) h.some

/-- Actual LGP ind1/ind2 carrier action attached to the conditional procession. -/
noncomputable def conditionalNativeLGPAction
    (h : CorrectedDefinition31TargetWithRemainingCards (X := X)) :
    LGPSourceActionCarrier (conditionalNativeLGPProcession (X := X) h) :=
  lgpSourceActionCarrier (conditionalNativeLGPProcession (X := X) h)

/-- Actual action laws for the conditional native LGP action. -/
theorem conditionalNativeLGPAction_laws
    (h : CorrectedDefinition31TargetWithRemainingCards (X := X)) :
    (conditionalNativeLGPAction (X := X) h).action1 0 = 1 ∧
      (∀ g hc c, (conditionalNativeLGPAction (X := X) h).action1 (g + hc) c =
        (conditionalNativeLGPAction (X := X) h).action1 hc
          ((conditionalNativeLGPAction (X := X) h).action1 g c)) :=
  ⟨(conditionalNativeLGPAction (X := X) h).action1_zero,
   (conditionalNativeLGPAction (X := X) h).action1_add⟩

/-- Exact target: unconditional native LGP procession. -/
def NativeLGPProcessionTarget : Prop :=
  Nonempty (SourceLGPProcession.{0, 0} l ℤ ℕ)

/-- Exact gap: the four source cards are not constructed from native S, so the
unconditional target is not available; the conditional construction above is
the actual part. -/
def MissingNativeLGPInstantiation : Prop :=
  ¬ Nonempty (CorrectedDefinition31TargetWithRemainingCards (X := X))

end LeanFormal.IUT.N8Closure.EtaSourceLGPProcessionFromCards

end