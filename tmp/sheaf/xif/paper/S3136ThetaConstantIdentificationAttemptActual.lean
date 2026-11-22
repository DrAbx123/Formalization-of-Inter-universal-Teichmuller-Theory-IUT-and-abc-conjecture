import tmp.sheaf.xif.paper.S3136CardAMPLSupplyReuseActual
import tmp.sheaf.xif.paper.S3136ThetaQPilotLogVolumeComparisonActual

/-! # Stage-4 host: Theta-constant identification attempt (model packet <-> CardAMPL)

PRIOR ART (§7.9, checked first): CardAMPLThetaBoundSupply.lean:78 fields
(theta : Real; theta_nonneg : 0<=theta; hull_logVolume_le : W.logVolume W.hull <= ofReal theta);
:116 of_realVolume_le converse constructor; :94 realVolume_le.

WHAT IS ATTEMPTED: identify the Card-AMPL Theta constant `theta` with the actual model
Theta-packet log-volume (S3136ThetaQPilotLogVolumeComparisonActual.lgpModelThetaLogVolume).
Constructed conditionally on the sign hypothesis 0 <= theta and the hull upper bound;
both are explicit hypotheses, not proved here.  If they hold, the supply is produced
and the prior-art reduction laws apply.

LABEL: conditional identification (no claim). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136ThetaConstantIdentificationAttemptActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3136CardAMPLSupplyReuseActual
open LeanFormal.IUT.XiFPaper.S3136ThetaQPilotLogVolumeComparisonActual

variable {X : Type*} {W : IQHullLogVolumeInterface X}
variable {l : PrimeGeFive}

/-- Conditional Card-AMPL supply with theta := the model Theta-packet log-volume. -/
def lgpCardAMPLSupplyModelTheta
    (hθ0 : 0 ≤ lgpModelThetaLogVolume l)
    (hbound : W.logVolume W.hull ≤ ENNReal.ofReal (lgpModelThetaLogVolume l)) :
    CardAMPLThetaBoundSupply W :=
  CardAMPLThetaBoundSupply.of_realVolume_le hθ0
    ((iqHullRealVolume_le_theta_iff W (θ := lgpModelThetaLogVolume l) hθ0).mpr hbound)

/-- Its constant is the model Theta log-volume (projection). -/
theorem lgpCardAMPLSupplyModelTheta_theta
    (hθ0 : 0 ≤ lgpModelThetaLogVolume l)
    (hbound : W.logVolume W.hull ≤ ENNReal.ofReal (lgpModelThetaLogVolume l)) :
    (lgpCardAMPLSupplyModelTheta (l := l) hθ0 hbound).theta =
      lgpModelThetaLogVolume l := rfl

/-- The prior-art realForm reduction applies to the identified supply. -/
theorem lgpCardAMPLSupplyModelTheta_realVolume_le
    (hθ0 : 0 ≤ lgpModelThetaLogVolume l)
    (hbound : W.logVolume W.hull ≤ ENNReal.ofReal (lgpModelThetaLogVolume l)) :
    iqHullRealVolume W ≤ lgpModelThetaLogVolume l :=
  CardAMPLThetaBoundSupply.realVolume_le
    (lgpCardAMPLSupplyModelTheta (l := l) hθ0 hbound)

/-- The two open hypotheses for the identification (data rows). -/
def lgpThetaIdentificationOpenHypotheses : List (String × String) :=
  [ ("sign", "0 <= lgpModelThetaLogVolume l (depends on gaussianFiveThetaQ sign)"),
    ("hull bound", "W.logVolume W.hull <= ENNReal.ofReal (lgpModelThetaLogVolume l)"),
    ("carrier", "W must be the actual IQ carrier (carrier bridge missing, S3136CarrierBridgeAttemptActual)") ]

theorem lgpThetaIdentificationOpenHypotheses_length :
    lgpThetaIdentificationOpenHypotheses.length = 3 := rfl

#check lgpCardAMPLSupplyModelTheta
#check lgpCardAMPLSupplyModelTheta_realVolume_le
#check lgpThetaIdentificationOpenHypotheses_length

end LeanFormal.IUT.XiFPaper.S3136ThetaConstantIdentificationAttemptActual
end