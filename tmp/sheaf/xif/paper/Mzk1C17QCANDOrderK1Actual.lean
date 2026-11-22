/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import tmp.sheaf.xif.paper.S1413SourceKPlaceQComparisonActual
import tmp.sheaf.xif.paper.Mzk1C17QCANDOrderResidueActual
import tmp.sheaf.xif.paper.Mzk1C17QPLACEChoiceGapActual
import Mathlib.Tactic

/-! # P6-E1: ORDER from k=1 / QPLACE data (single cluster, CONDITIONAL) -/
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S1413SourceKPlaceQComparisonActual
open LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderResidueActual
namespace LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderK1Actual
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The k=1 data needed to identify baseQ order with qVFamily order:
QPLACE (F-shadow equality), section ramification index 1, and the
badPlaceQCandidate-to-sectionQ order identification. -/
def KOneOrderData : Prop :=
  S1413ShadowEqualsNative T b ∧
    eSource T b = 1 ∧
      (badPlaceQCandidate (nativePlaceSelection T) b).order = (sectionQ T b).order

/-- Under k=1 data, the baseQ order equals the qVFamily order. -/
theorem qcandOrderGap_of_k1 (h : KOneOrderData T b) :
    (nativeBaseQFamily T b).order = (qVFamily T b).order := by
  rcases h with ⟨hF, hE, hbad⟩
  have hsection : (nativeBaseQFamily T b).order = (sectionQ T b).order := by
    rw [nativeBaseQFamily_eq_badPlaceQCandidate]
    exact hbad
  rw [hsection, sectionQ_order (T := T) (b := b), hE, one_mul,
    shadowQ_order_eq_of_shadow_eq T b hF]

/-- Global ORDER gap from pointwise k=1 data. -/
theorem qcandOrderGap_of_k1_all
    (h : ∀ b : Bad (nativePlaceSelection T), KOneOrderData T b) :
    QCANDOrderGap T := by
  intro b
  exact qcandOrderGap_of_k1 T b (h b)

def orderK1Rows : List (String × String × String) :=
  [ ("KOneOrderData", "QPLACE + eSource=1 + bad=sectionQ order", "CONDITIONAL"),
    ("qcandOrderGap_of_k1", "k=1 data => baseQ order = qVFamily order", "PROVED conditional"),
    ("qcandOrderGap_of_k1_all", "global ORDER gap", "PROVED conditional") ]
theorem orderK1Rows_length : orderK1Rows.length = 3 := rfl
end LeanFormal.IUT.XiFPaper.Mzk1C17QCANDOrderK1Actual

-- retry marker after compile-fix batch
