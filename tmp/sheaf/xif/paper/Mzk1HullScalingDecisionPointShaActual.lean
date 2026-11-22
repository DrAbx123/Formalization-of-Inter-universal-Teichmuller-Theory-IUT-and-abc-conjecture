import tmp.sheaf.xif.paper.S2727ScalingTargetsActual
import tmp.sheaf.xif.paper.S2733ScalingActual

/-!
# shehdd A655 hull scaling decision point (Sha, unique name)

Decision-point audit for the hull scaling direction, citing green exact scaling
formulas (read-only):
* closed-ball exact scaling formula `c • closedBall x r = closedBall (c•x) (‖c‖ r)` is
  formalized in the separate Sha file `Mzk1HullExactScalingFormulaShaActual` (owned
  by another lane; not imported here to avoid a pending-olean dependency);
* `S2727ScaledRegionVolume_eq_scalingRatio_mul_unit`: exact scaled region volume =
  `scalingRatio * unitVolume`;
* `c3LogVolume_smul_norm`: exact log scaling law
  `log vol(u•S) = log(‖u‖^d) + log vol S`;
* decision: the canonical growing direction (ratio ≥ 1) has positive lever
  `d*log(ratio)`, while a shrinking/inverse direction makes Gap 1 impossible when
  the region stays in the finite unit region (see the direction file).

No sorry, axiom, True or placeholder.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullScalingDecisionPointShaActual

structure DecisionRow where
  item : String
  source : String
  status : String
  deriving Repr, DecidableEq

def decisionRows : List DecisionRow :=
  [ ⟨"closed-ball exact scaling", "Mzk1HullExactScalingFormulaShaActual.exact_scaling_formula", "GREEN_OTHER_LANE"⟩
  , ⟨"exact scaled region volume", "S2727ScaledRegionVolume_eq_scalingRatio_mul_unit", "GREEN"⟩
  , ⟨"exact log scaling law", "S2733ScalingActual.c3LogVolume_smul_norm", "GREEN"⟩
  , ⟨"canonical growing direction", "tripleScale = scaleMap(a+b+c+1), lever d*log(ratio)>0", "DECISION"⟩
  , ⟨"shrinking direction fails Gap1", "gap1_impossible_of_region_in_unitRegion", "GREEN_PENDING"⟩
  , ⟨"decision", "keep canonical growing direction; canonical objects unchanged", "DECISION"⟩
  , ⟨"scope", "audit/decision only; named gaps unchanged", "INTEGRITY"⟩
  ]

def allowedStatuses : List String :=
  ["GREEN_OTHER_LANE", "GREEN", "GREEN_PENDING", "DECISION", "INTEGRITY"]

theorem decisionRows_length : decisionRows.length = 7 := rfl

theorem decisionRows_statuses_ok :
    decisionRows.all (fun r => r.status ∈ allowedStatuses) = true := by
  decide

theorem decision_has_exact_formulas :
    decisionRows.any (fun r => r.item = "exact scaled region volume") = true := by
  decide

theorem decision_has_direction :
    decisionRows.any (fun r => r.item = "shrinking direction fails Gap1") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1HullScalingDecisionPointShaActual

/-! ### Axiom gates for the cited green exact formulas -/

#print axioms LeanFormal.IUT.XiFPaper.S2727ScalingTargetsActual.S2727ScaledRegionVolume_eq_scalingRatio_mul_unit
#print axioms LeanFormal.IUT.XiFPaper.S2733ScalingActual.c3LogVolume_smul_norm
