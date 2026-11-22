import tmp.sheaf.xif.paper.S3136WeightedAveragePriorArtReuseActual
import tmp.sheaf.xif.paper.S3136ModelThetaPacketLawsActual

/-! # Stage-4 host: theta-label weighted-average mapping (LGP labels <-> IV Step V)

PRIOR ART (§7.9, checked first): IUTIV/Estimates/StepVProcessionAverage.lean:35
collectionBound l D Q S T j = (j+1)D - j^2/(2l)Q + S + 4(j+1)T (IV L1736-1741);
:68 processionAverage_le; reused in S3136WeightedAveragePriorArtReuseActual.

CONSUMER: mainline's weighted-average side of (c).  This file reuses the prior-art
collection bound and records the correspondence between the LGP theta label weights
(gaussExponent j)^2 and the Step V collection terms; the identification row is data,
while the reused formula is a definitional equality (rfl).

LABEL: reuse + mapping (class A). Registry frozen; new file only. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3136WeightedAverageLabelMappingActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3136ModelThetaPacketActual

variable {l : PrimeGeFive}

/-- The LGP theta label weight is the Step V j^2 collection term numerator. -/
def lgpThetaLabelCollectionTerm (j : SignedLabel l.value) : ℕ :=
  (gaussExponent j.1).toNat

/-- The theta label collection term matches the exponent in the packet scale law. -/
theorem lgpThetaLabelCollectionTerm_eq (j : SignedLabel l.value) :
    lgpThetaLabelCollectionTerm j = (gaussExponent j.1).toNat := rfl

/-- Reuse: the Step V collection bound from the prior art (alias for consumers). -/
noncomputable def lgpStepVCollectionBound (ell D Q S T : ℝ) (j : ℕ) : ℝ :=
  LeanFormal.IUT.IUTIV.StepVProcessionAverage.collectionBound ell D Q S T j

/-- The alias is the prior-art formula (definitional). -/
theorem lgpStepVCollectionBound_eq (ell D Q S T : ℝ) (j : ℕ) :
    lgpStepVCollectionBound ell D Q S T j =
      ((j : ℝ) + 1) * D - (j : ℝ) ^ 2 / (2 * ell) * Q + S +
        4 * ((j : ℝ) + 1) * T := rfl

/-- Mapping rows: LGP theta data <-> IV Step V collection data. -/
def lgpThetaStepVMapping : List (String × String) :=
  [ ("lgpThetaLabelCollectionTerm j = (gaussExponent j)^2", "j^2 Q term of collectionBound"),
    ("theta scale law q^(gaussExponent j)", "Q = log(q) coefficient (j^2/(2l) Q)"),
    ("label independent terms", "D (log d_K), S (log s_Q), T (log p / e*_mod terms)"),
    ("procession l = 2n+1, labels j = 1..n", "processionAverage_eq / processionAverage_le (IV L1744-1783)") ]

theorem lgpThetaStepVMapping_length : lgpThetaStepVMapping.length = 4 := rfl

#check lgpThetaLabelCollectionTerm_eq
#check lgpStepVCollectionBound_eq
#check lgpThetaStepVMapping_length

end LeanFormal.IUT.XiFPaper.S3136WeightedAverageLabelMappingActual
end