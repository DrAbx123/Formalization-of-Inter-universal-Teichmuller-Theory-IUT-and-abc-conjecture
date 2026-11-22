import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.CardAMPLThetaBoundSupply

/-! # Stage-4 host: reuse of CardAMPLThetaBoundSupply (Cor 3.12 Theta upper bound)

PRIOR ART (§7.9, checked first): CardAMPLThetaBoundSupply.lean:78 structure
CardAMPLThetaBoundSupply (theta, theta_nonneg, hull_logVolume_le :
W.logVolume W.hull <= ofReal theta); :94 realVolume_le; :101
ofReal_le_theta_of_imageSet_lower; :109 exists_hull_eq_ofReal; :116 of_realVolume_le;
:125 nonempty_iff; :193 cor312Conclusion.

CONSUMER: the (c) normalized-weight/unit-region upper bound side.  This file reuses
the supply and its reduction laws directly (no re-proof); the supply fields are the
exact Theta-constant upper-bound data that the Cor 3.12 assembly consumes.

LABEL: reuse adapters (class A interface supply).  Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136CardAMPLSupplyReuseActual

open LeanFormal.IUT

variable {X : Type*} {W : IQHullLogVolumeInterface X}

/-- Reuse: the supply's real-form upper bound. -/
theorem lgpCardAMPL_realVolume_le (S : CardAMPLThetaBoundSupply W) :
    iqHullRealVolume W ≤ S.theta :=
  CardAMPLThetaBoundSupply.realVolume_le S

/-- Reuse: the converse constructor from a real upper bound. -/
def lgpCardAMPL_of_realVolume_le {θ : ℝ} (hθ0 : 0 ≤ θ)
    (h : iqHullRealVolume W ≤ θ) :
    CardAMPLThetaBoundSupply W :=
  CardAMPLThetaBoundSupply.of_realVolume_le hθ0 h

/-- Reuse: existence characterization. -/
theorem lgpCardAMPL_nonempty_iff :
    Nonempty (CardAMPLThetaBoundSupply W) ↔
      ∃ θ : ℝ, 0 ≤ θ ∧ W.logVolume W.hull ≤ ENNReal.ofReal θ :=
  CardAMPLThetaBoundSupply.nonempty_iff

/-- The supply's data layout, for the (c) normalized-weight slot (data rows). -/
def lgpCardAMPLFields : List (String × String) :=
  [ ("theta", "Real upper-bound constant (Cor 3.12 Theta-data role)"),
    ("theta_nonneg", "0 <= theta sign normalization"),
    ("hull_logVolume_le", "W.logVolume W.hull <= ENNReal.ofReal theta (the Card-AMPL bound)") ]

theorem lgpCardAMPLFields_length : lgpCardAMPLFields.length = 3 := rfl

#check lgpCardAMPL_realVolume_le
#check lgpCardAMPL_of_realVolume_le
#check lgpCardAMPL_nonempty_iff
#check lgpCardAMPLFields_length

end LeanFormal.IUT.XiFPaper.S3136CardAMPLSupplyReuseActual
end