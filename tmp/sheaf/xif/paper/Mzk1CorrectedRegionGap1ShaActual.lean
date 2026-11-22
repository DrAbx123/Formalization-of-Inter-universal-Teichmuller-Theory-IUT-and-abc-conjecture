import tmp.sheaf.xif.paper.Mzk1CorrectedRegionGap1Actual
import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import Mathlib.Tactic

/-!
# shehdd A668/A669 CorrectedRegionGap1 consumer (Sha, read-only)

Thin consumer of the GREEN mainline `Mzk1CorrectedRegionGap1Actual`:
* re-exports `correctedRegion`, `correctedPaperRegion`, `CorrectedRegionLogLaw`;
* wires mainline `corrected_gap1_of_fullSupport` into the root `Gap1Prop` interface;
* records that the corrected-region log law is still an explicit hypothesis.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1ShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.PaperRootCompletionTensorActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1Actual
open Mzk1LanaBridgeAuditActual

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))] [Nonempty (Bad (nativePlaceSelection T))]

/-- Re-export: corrected region log law (mainline definition). -/
abbrev correctedRegionLogLaw
    (point : Nat → Nat → Nat → S1902Carrier T)
    (e : Bad (nativePlaceSelection T) → Nat) : Prop :=
  CorrectedRegionLogLaw T point e

/-- **Corrected-region Gap1 wiring**: mainline conditional Gap1 expressed as `Gap1Prop`
for the corrected comparison region. -/
theorem corrected_gap1Prop_of_fullSupport
    (point : Nat → Nat → Nat → S1902Carrier T)
    (e : Bad (nativePlaceSelection T) → Nat)
    (hlog : CorrectedRegionLogLaw T point e)
    (hd : ∀ b : Bad (nativePlaceSelection T),
      1 ≤ (Module.finrank ℚ_[(qVFamTensorP T b)] (rootNormedExtension T b) : Real))
    (hfull : ∀ a b c : Nat, IsABCTriple a b c →
      a + b + c + 1 = ∏ b : Bad (nativePlaceSelection T), (qVFamTensorP T b) ^ (e b))
    (hunit : 0 ≤ (s1902LogVolume T (s1902UnitRegion T)).toReal) :
    Gap1Prop (s1902IQHullLogVolumeInterface T) (correctedPaperRegion T point) := by
  intro ε hε a b c htriple
  exact corrected_gap1_of_fullSupport T point e hlog hd hfull hunit ε hε a b c htriple

structure CorrectedRow where
  item : String
  content : String
  status : String
  deriving Repr, DecidableEq

def correctedRows : List CorrectedRow :=
  [ ⟨"mainline corrected region", "correctedRegion/correctedPaperRegion (green)", "GREEN_SOURCE"⟩
  , ⟨"log-form hypothesis", "CorrectedRegionLogLaw (explicit hypothesis)", "GREEN_DEF"⟩
  , ⟨"arithmetic core", "log_height_le_badSum (proved, gate trio)", "GREEN"⟩
  , ⟨"conditional Gap1", "corrected_gap1_of_fullSupport (gate trio)", "GREEN"⟩
  , ⟨"Gap1Prop wiring", "corrected_gap1Prop_of_fullSupport", "GREEN_CONDITIONAL"⟩
  , ⟨"scope", "consumer only; no gap claimed", "INTEGRITY"⟩
  ]

theorem correctedRows_length : correctedRows.length = 6 := rfl

theorem correctedRows_statuses_ok :
    correctedRows.all (fun r =>
      r.status ∈ ["GREEN_SOURCE", "GREEN_DEF", "GREEN", "GREEN_CONDITIONAL", "INTEGRITY"]) = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1ShaActual

#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1ShaActual.corrected_gap1Prop_of_fullSupport
#print axioms LeanFormal.IUT.XiFPaper.Mzk1CorrectedRegionGap1Actual.corrected_gap1_of_fullSupport
