import tmp.sheaf.xif.paper.Mzk1LanaBridgeAuditActual
import tmp.sheaf.xif.paper.Mzk1PaperComparisonRegionScalingActual
import tmp.sheaf.xif.paper.Mzk1HullScalingDecisionPointShaActual
import Mathlib.Tactic

/-!
# shehdd A657 scaling-element audit and Gap1 full-ratio theorem (Sha)

1. **Gap 1 full-ratio form**: for positive `1+ε`, the estimate
   `height ≤ (1+ε) * regionVolume` is EQUIVALENT to the ratio bound
   `height / (1+ε) ≤ regionVolume`.  This is a pure theorem-ization of Gap 1
   (full ratio, not a weakened form).
2. **Scaling-element audit**: catalogs the scaling elements used by the paper /
   green files: canonical `tripleScale` scalar `a+b+c+1` (≥1), S2727's `lam`
   (HullBlock scaling), S2733's p-adic `qPilotLambdaFromOrder = p^order`, and the
   paper's `q_v^{j²}` (textual).  All give a positive scaling lever for Gap 1;
   the decision from A655 (keep growing direction) is recorded.

No sorry, axiom, True or placeholder.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT.XiFPaper.Mzk1Gap1FullRatioScalingElementAuditShaActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open Mzk1LanaBridgeAuditActual
open LeanFormal.IUT.XiFPaper.Mzk1PaperComparisonRegionScalingActual

/-- Ratio re-formulation: `h ≤ c * L ↔ h / c ≤ L` for `c > 0`. -/
theorem le_mul_iff_div_le {h L c : Real} (hc : 0 < c) :
    h ≤ c * L ↔ h / c ≤ L := by
  constructor
  · intro hle
    rw [div_le_iff₀ hc]
    linarith
  · intro hle
    have := (div_le_iff₀ hc).mp hle
    linarith

/-- **Gap 1 full-ratio theorem**: the ε-form is exactly the family of ratio bounds
`height/(1+ε) ≤ regionVolume`. -/
theorem gap1_full_ratio_form {X : Type*}
    (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X) :
    Gap1Prop W region ↔
      ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
        Height.logHeight₁ (abcRationalPoint a c) / (1 + ε) ≤
          (W.logVolume (region a b c)).toReal := by
  constructor
  · intro h ε hε a b c htriple
    exact (le_mul_iff_div_le (by linarith)).mp (h ε hε a b c htriple)
  · intro h ε hε a b c htriple
    exact (le_mul_iff_div_le (by linarith)).mpr (h ε hε a b c htriple)

/-- Gap 1, full-ratio, specialized to a concrete region (definitional wrapper). -/
theorem gap1_full_ratio_concrete {X : Type*}
    (W : IQHullLogVolumeInterface X)
    (region : Nat → Nat → Nat → Set X)
    (h : Gap1Prop W region) :
    ∀ ε : Real, 0 < ε → ∀ a b c : Nat, IsABCTriple a b c →
      Height.logHeight₁ (abcRationalPoint a c) / (1 + ε) ≤
        (W.logVolume (region a b c)).toReal :=
  (gap1_full_ratio_form W region).mp h

structure ScalingElementRow where
  scalingElement : String
  source : String
  content : String
  status : String
  deriving Repr, DecidableEq

def scalingElementRows : List ScalingElementRow :=
  [ ⟨"tripleScale scalar", "Mzk1PaperComparisonRegionScalingActual.tripleScale", "a+b+c+1 : Nat, >= 1, multiplicative growth", "GREEN"⟩
  , ⟨"S2727 lam scaling", "S2727ScalingTargetsActual lam : HullBlock C3", "scaled region lam·O", "GREEN_SOURCE"⟩
  , ⟨"qPilotLambdaFromOrder", "S2733ScalingActual.qPilotLambdaFromOrder", "p^order in Q_p (p-adic scaling element)", "GREEN_SOURCE"⟩
  , ⟨"paper q_v^(j^2)", "IUT IV local estimate scaling element (textual)", "j^2 multiple of q_v; positive lever", "NAMED_AUDIT"⟩
  , ⟨"direction decision", "A655 decision point", "keep canonical growing direction; shrinking fails Gap1", "DECISION"⟩
  , ⟨"scope", "audit", "ratio-theorem only; gaps unchanged", "INTEGRITY"⟩
  ]

def allowedStatuses : List String :=
  ["GREEN", "GREEN_SOURCE", "NAMED_AUDIT", "DECISION", "INTEGRITY"]

theorem scalingElementRows_length : scalingElementRows.length = 6 := rfl

theorem scalingElementRows_statuses_ok :
    scalingElementRows.all (fun r => r.status ∈ allowedStatuses) = true := by
  decide

theorem scalingElement_has_tripleScale :
    scalingElementRows.any (fun r => r.scalingElement = "tripleScale scalar") = true := by
  decide

theorem scalingElement_has_padic :
    scalingElementRows.any (fun r => r.scalingElement = "qPilotLambdaFromOrder") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1Gap1FullRatioScalingElementAuditShaActual

/-! ### Axiom gates -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1FullRatioScalingElementAuditShaActual.gap1_full_ratio_form
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1FullRatioScalingElementAuditShaActual.gap1_full_ratio_concrete
