import tmp.sheaf.n8.closure.EtaLGPProcessionNondegenerate

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# Fifth source qualification: SourceTheorem311Completion

Adds the full source completion `SourceTheorem311Completion l ℤ ℕ` as an
explicit source qualification of the corrected LGP target, aligned with the
four-card SourceDefinition31Data.  Its production `.procession` uses the actual
`input.prime` ind1/ind2 actions (not the degenerate identity constructor), so
the attached LGP carrier action is the conditional paper-shape procession.
No completion is constructed from the four cards; that is the exact gap.
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
open LeanFormal.IUT.N8Closure.EtaSourceLGPProcessionFromCards
open LeanFormal.IUT.N8Closure.EtaLGPProcessionNondegenerate
open LeanFormal.IUT.N8Closure.EtaSourceActionCarrierCorrected

namespace LeanFormal.IUT.N8Closure.EtaSourceTheorem311Qualification

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Corrected LGP input with the fifth source qualification: the full
SourceTheorem311Completion, aligned with the four-card source data. -/
structure SourceWithFiveQualifications (X : N8NativeInput l) where
  /-- The four preceding source qualification layers. -/
  cards : SourceWithFourQualifications (X := X)
  /-- SOURCE card 5: full Theorem 3.11 source completion. -/
  completion : SourceTheorem311Completion.{0, 0, 0} l ℤ ℕ
  /-- Alignment: the completion's source is the four-card source. -/
  source_alignment : completion.source = sourceDataFromFour (X := X) cards

def CorrectedDefinition31TargetWithCompletion : Prop :=
  Nonempty (SourceWithFiveQualifications (l := l) X)

def fiveQualifications_completion
    (h : CorrectedDefinition31TargetWithCompletion (X := X)) :
    SourceTheorem311Completion.{0, 0, 0} l ℤ ℕ :=
  h.some.completion

theorem fiveQualifications_source_aligned
    (h : CorrectedDefinition31TargetWithCompletion (X := X)) :
    h.some.completion.source = sourceDataFromFour (X := X) h.some.cards :=
  h.some.source_alignment

/-- Actual paper-shape LGP procession: production `.procession` from the
completion card.  Its ind1/ind2 come from the completion input prime, not from
the degenerate identity constructor. -/
noncomputable def paperLGPProcession
    (I : SourceWithFiveQualifications (X := X)) :
    SourceLGPProcession l ℤ ℕ :=
  I.completion.procession

theorem paperLGPProcession_ind1_eq_input
    (I : SourceWithFiveQualifications (X := X)) (g : ℤ) (c : ℕ) :
    (paperLGPProcession (X := X) I).ind1 g c =
      I.completion.input.prime.ind1 g c := by
  rw [paperLGPProcession, ← I.completion.realization_procession]
  exact I.completion.realization_procession_ind1 g c

theorem paperLGPProcession_ind2_eq_input
    (I : SourceWithFiveQualifications (X := X)) (g : ℤ) (c : ℕ) :
    (paperLGPProcession (X := X) I).ind2 g c =
      I.completion.input.prime.ind2 g c := by
  rw [paperLGPProcession, ← I.completion.realization_procession]
  exact I.completion.realization_procession_ind2 g c

/-- Actual LGP ind1/ind2 carrier action on the paper-shape procession. -/
noncomputable def paperLGPAction
    (I : SourceWithFiveQualifications (X := X)) :
    LGPSourceActionCarrier (paperLGPProcession (X := X) I) :=
  lgpSourceActionCarrier (paperLGPProcession (X := X) I)

theorem paperLGPAction_laws
    (I : SourceWithFiveQualifications (X := X)) :
    (paperLGPAction (X := X) I).action1 0 = 1 ∧
      (∀ g hc c, (paperLGPAction (X := X) I).action1 (g + hc) c =
        (paperLGPAction (X := X) I).action1 hc
          ((paperLGPAction (X := X) I).action1 g c)) :=
  ⟨(paperLGPAction (X := X) I).action1_zero,
   (paperLGPAction (X := X) I).action1_add⟩

theorem conditionalPaperLGP
    (h : CorrectedDefinition31TargetWithCompletion (X := X)) :
    Nonempty (SourceLGPProcession l ℤ ℕ) :=
  ⟨paperLGPProcession (X := X) h.some⟩

theorem conditionalPaperLGPAction_laws
    (h : CorrectedDefinition31TargetWithCompletion (X := X)) :
    (paperLGPAction (X := X) h.some).action1 0 = 1 :=
  (paperLGPAction (X := X) h.some).action1_zero

/-- Exact gap: no SourceTheorem311Completion is constructed from the four
cards.  Missing fields are the source Input prime procession, q/scale data, and
label/initial alignment. -/
def MissingSourceTheorem311Completion : Prop :=
  ¬ Nonempty (SourceTheorem311Completion.{0, 0, 0} l ℤ ℕ)

end LeanFormal.IUT.N8Closure.EtaSourceTheorem311Qualification

end