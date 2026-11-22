import tmp.sheaf.xif.paper.S3136LGPXMuDegreeActual
import tmp.sheaf.xif.paper.S3136LGPThetaMuQuasiLatticeActual

/-! # Stage-4 host: actual theta-class log-weight scalar channel

Source anchors: IUT III, Prop. 3.4, (ii) (pp. 102--103); IUT III, Prop. 3.9,
(i), p. 115; IUT III, Rem. 3.9.4.

This file exposes the actual scalar log-weight of the theta classes, the
additive channel consumers need for realified/log-volume readout:
* lgpThetaClassLogWeight b j: the actual divisor log-weight j^2 * ord_v(q_v)
  of the theta class;
* lgpThetaClassLogWeight_pos: positivity;
* lgpThetaClassLogWeight_eq_total: it equals the actual total theta divisor
  degree of the corresponding LGP prime divisor;
* LGPThetaClassLogChannelMissing/Gap: exact missing data (Theta-link/label
  component compatibility of the scalar channel; refs above).

LABEL: prerequisite component only.  Consumer: lattice R1, stepxi C2, abc F4. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136LGPThetaClassLogWeightActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSymbolTypesActual
open LeanFormal.IUT.XiFPaper.S3136LGPPhiInputSourceActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual
open LeanFormal.IUT.XiFPaper.S3136LGPXMuDegreeActual
open LeanFormal.IUT.XiFPaper.S3136LGPLocalFractionalIdealCandidate

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual scalar log-weight of a theta class: j^2 * ord_v(q_v) as a real. -/
def lgpThetaClassLogWeight (b : Bad (nativePlaceSelection T))
    (j : PaperThetaLabel l) : ℝ :=
  ((lgpThetaLabelWeight j * lgpQVDivisorExponent T b : ℕ) : ℝ)

/-- The actual theta-class log-weight is positive. -/
theorem lgpThetaClassLogWeight_pos (b : Bad (nativePlaceSelection T))
    (j : PaperThetaLabel l) : 0 < lgpThetaClassLogWeight T b j := by
  unfold lgpThetaClassLogWeight
  have h := lgpThetaDivisorExponent_pos T (b, j)
  rw [lgpThetaDivisorExponent_eq_gauss_mul_order] at h
  exact_mod_cast h

/-- The scalar log-weight equals the actual total theta divisor degree of the
corresponding LGP prime divisor. -/
theorem lgpThetaClassLogWeight_eq_total (b : Bad (nativePlaceSelection T))
    (j : PaperThetaLabel l) :
    lgpThetaClassLogWeight T b j =
      ((lgpThetaDivisorTotalExponent T
        (lgpThetaPilotPrimeDivisor T (b, j)) : ℕ) : ℝ) := by
  unfold lgpThetaClassLogWeight
  rw [lgpThetaDivisorTotalExponent_single]
  rfl

/-- Exact missing data for the theta-class log channel (IUT III, Prop. 3.4,
(ii), pp. 102--103; Rem. 3.9.4; Prop. 3.9, (i), p. 115):
* thetaLinkCompatibility: compatibility of the scalar channel with the
  Theta-link;
* labelComponentCompatibility: compatibility with the label components in the
  IQ packet;
* logVolumeNormalization: the realified log-volume normalization identity. -/
structure LGPThetaClassLogChannelMissing where
  thetaLinkCompatibility : Prop
  labelComponentCompatibility : Prop
  logVolumeNormalization : Prop

/-- The exact theta-class log-channel gap. -/
def LGPThetaClassLogChannelGap : Prop :=
  Nonempty LGPThetaClassLogChannelMissing

#check lgpThetaClassLogWeight
#check lgpThetaClassLogWeight_pos
#check lgpThetaClassLogWeight_eq_total
#check LGPThetaClassLogChannelGap

end LeanFormal.IUT.XiFPaper.S3136LGPThetaClassLogWeightActual
end