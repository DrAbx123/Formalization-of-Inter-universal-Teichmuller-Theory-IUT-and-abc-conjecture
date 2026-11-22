import tmp.sheaf.xif.paper.Mzk1Gap1ScalingLawTargetActual

/-!
# shehdd A659 hull product / badInvScale scaling-law blocking report (Sha)

Read-only status/blocking audit for the inverse bad-prime scaling direction.

## Hull file `Mzk1ScalingDirectionActual` (hull-owned, in progress)
Already present (source, no ole yet): 1D inverse prime scaling laws
`prime_inv_smul_measure`, `prime_pow_inv_smul_measure`.
Still MISSING (key blocking for the product statement):
* `badInvScale` (coordinatewise inverse bad-prime scaling with exponents `e b`);
* `badInvScale_unitBall_measure` (product unit-ball measure ratio);
* `badInvScale_logVolume_ratio` (real log-volume increases by
  `∑ b, e b * (d_b * log p_b)`, the bad-support part; NOT `log N`);
* mainline `CorrectedRegionFormula` should carry `log N_bad` weighted by local
  degrees `d_b` rather than `log N`.

## Other lanes / shehdd Gap1 theorem-ization
Mainline `Mzk1Gap1ScalingLawTargetActual` is GREEN (gates below).
shehdd corroboration: `gap1_full_ratio_form` (full-ratio equivalence) and
`gap1_impossible_of_region_in_unitRegion` (shrinking direction impossible).

Decision: paper comparison uses the INVERSE bad-prime scaling direction
(`λ = N_bad^{-1}`); canonical objects unchanged; named Gap1/Gap2 unchanged.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1HullBadInvScaleBlockingShaActual

structure BlockingRow where
  item : String
  detail : String
  owner : String
  status : String
  deriving Repr, DecidableEq

def blockingRows : List BlockingRow :=
  [ ⟨"1D inverse prime scaling", "prime_inv_smul_measure, prime_pow_inv_smul_measure", "hull", "GREEN_SOURCE"⟩
  , ⟨"badInvScale definition", "coordinatewise inverse bad-prime scaling e b", "hull", "PENDING_HULL"⟩
  , ⟨"badInvScale_unitBall_measure", "mu(badInvScale e image unitBall) = (prod (primeFactor^-e)) * mu unitBall", "hull", "PENDING_HULL"⟩
  , ⟨"badInvScale_logVolume_ratio", "log-volume increases by sum e_b*d_b*log p_b", "hull", "PENDING_HULL"⟩
  , ⟨"Gap1 scaling-law target", "gap1_of_scalingLaw_and_arith / gap1_arithmetic_condition_iff / gap1_of_fullRatio", "mainline", "GREEN"⟩
  , ⟨"shehdd full-ratio", "gap1_full_ratio_form (full ratio equivalence)", "shehdd", "PENDING_FRESH"⟩
  , ⟨"shehdd shrinking obstruction", "gap1_impossible_of_region_in_unitRegion", "shehdd", "GREEN_GATE"⟩
  , ⟨"decision", "inverse bad-prime direction; corrected region formula log N_bad (d_b weighted)", "shared", "DECISION"⟩
  , ⟨"scope", "blocking report only; no canonical object changed", "audit", "INTEGRITY"⟩
  ]

def allowedStatuses : List String :=
  ["GREEN_SOURCE", "PENDING_HULL", "GREEN", "PENDING_FRESH", "GREEN_GATE", "DECISION", "INTEGRITY"]

theorem blockingRows_length : blockingRows.length = 9 := rfl

theorem blockingRows_statuses_ok :
    blockingRows.all (fun r => r.status ∈ allowedStatuses) = true := by
  decide

theorem blocking_has_badInvScale :
    blockingRows.any (fun r => r.item = "badInvScale definition") = true := by
  decide

theorem blocking_has_target :
    blockingRows.any (fun r => r.status = "GREEN") = true := by
  decide

theorem blocking_has_decision :
    blockingRows.any (fun r => r.status = "DECISION") = true := by
  decide

end LeanFormal.IUT.XiFPaper.Mzk1HullBadInvScaleBlockingShaActual

/-! ### Axiom gates: mainline Gap1 scaling-law target (read-only) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_of_scalingLaw_and_arith
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_arithmetic_condition_iff
#print axioms LeanFormal.IUT.XiFPaper.Mzk1Gap1ScalingLawTargetActual.gap1_of_fullRatio
