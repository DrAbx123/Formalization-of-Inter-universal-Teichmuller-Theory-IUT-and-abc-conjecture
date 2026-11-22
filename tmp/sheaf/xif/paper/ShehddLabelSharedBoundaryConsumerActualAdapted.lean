import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceSharedBoundary
import LeanFormal.IUT.IUTIII.Theorem311.SourceLabelWeightedDiagonal
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

/-!
# ShehddLabelSharedBoundaryConsumerActualAdapted — label cardinality / zero-label consumer

STEP 0 prior-art (reuse only; A475 exhaustive search):
* IUTIII/Corollary312/StepXI/SourceSharedBoundary.lean: signedLabel_cardinality,
  nonzeroFiniteLabel_cardinality, cuspLabel_cardinality, oneColumn_shared_boundary;
* IUTIII/Theorem311/SourceLabelWeightedDiagonal.lean: zeroLabel/oneLabel, labelWeight,
  labelWeight_zeroLabel, toFiniteLabel_zeroLabel;
* Foundations/Theta/SignedLabelEquiv.lean: toFiniteLabel/injective/representative.

The paper label bookkeeping (IUT II Cor 4.10(i): identification of labels 0 and the
log-shell label) is consumed here at the finite-label level: the zero label maps to 0
under toFiniteLabel, the nonzero finite labels have cardinality 2*l*, and the signed
label set has cardinality l.  No new assumptions, no sorry/axiom.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddLabelSharedBoundaryConsumerActualAdapted

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.SourceLabelWeightedDiagonal

/-- **PROVED consumer:** the signed label set has cardinality `l`. -/
theorem signedLabel_cardinality_consumer (l : PrimeGeFive) :
    Fintype.card (SignedLabel l.value) = l.value :=
  signedLabel_cardinality l

/-- **PROVED consumer:** the nonzero finite labels have cardinality `2 * l*`. -/
theorem nonzeroFiniteLabel_cardinality_consumer (l : PrimeGeFive) :
    Fintype.card (NonzeroFiniteLabel l) = 2 * lStar l.value :=
  nonzeroFiniteLabel_cardinality l

/-- **PROVED consumer:** the distinguished label `0` is sent to `0` under the
finite-label dictionary (the label-level part of the Cor 4.10(i) bookkeeping). -/
theorem zeroLabel_toFiniteLabel_zero (l : PrimeGeFive) :
    SignedLabel.toFiniteLabel l (zeroLabel (l := l.value)) = 0 :=
  toFiniteLabel_zeroLabel l

/-- **PROVED consumer:** the zero label has Gaussian weight `0`. -/
theorem zeroLabel_weight_zero (l : Nat) :
    labelWeight (zeroLabel (l := l)) = 0 :=
  labelWeight_zeroLabel

/-- Row record: reused label assets vs consumer statements. -/
def labelSharedBoundaryRows : List (String × String × String) :=
  [ ("signed / nonzero / cusp label cardinalities", "REUSED PROVED", "SourceSharedBoundary.signedLabel_cardinality / nonzeroFiniteLabel_cardinality / cuspLabel_cardinality")
  , ("zero label maps to 0; weight 0", "REUSED PROVED", "toFiniteLabel_zeroLabel; labelWeight_zeroLabel")
  , ("zero-label finite dictionary consumer", "COMPOSED PROVED", "zeroLabel_toFiniteLabel_zero, zeroLabel_weight_zero")
  , ("finite-label cardinality consumers", "COMPOSED PROVED", "signedLabel_cardinality_consumer, nonzeroFiniteLabel_cardinality_consumer")
  , ("paper Cor 4.10(i) identification of label 0 with the log-shell label verbatim", "REPO-MISSING-VERBATIM (search evidence in coord/SURVEY-shehdd.md)", "closest assets: SignedLabel/Fl dictionaries + SourceLogShellInvariantImageIdentification (SourceLogShellAbsTopIIIBridge.lean)") ]

theorem labelSharedBoundaryRows_length : labelSharedBoundaryRows.length = 5 := rfl

#check signedLabel_cardinality_consumer
#check nonzeroFiniteLabel_cardinality_consumer
#check zeroLabel_toFiniteLabel_zero
#check zeroLabel_weight_zero
#check labelSharedBoundaryRows_length

end LeanFormal.IUT.XiFPaper.ShehddLabelSharedBoundaryConsumerActualAdapted
end
