import LeanFormal/IUT/IUTII/Kummer/SourceThetaPilotIQContainment
import LeanFormal/IUT/IUTII/Kummer/AbsoluteKummerContinuity
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceSHETransportObligations
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/SourceHullInterfaceDischarge
import LeanFormal/IUT/IUTIII/Theorem311/SourceK1K2VolumeTranslationLaw
import LeanFormal/IUT/IUTIII/Theorem311/Indeterminacy/Ind3UpperSemiConstruction
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceLogShellMuNQuotientCarrier
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/HullDeterminantLogVolumeReduction
import LeanFormal/IUT/ABCBridge/Bridge/ABCFrontierReductions

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ChainInferredReuseActual — A475 inferred-type chained adapters

Each `chain_*` theorem is a composition/re-export built from an existing donor
with its type inferred by lambda/application (no signature restatement, no new
axioms, no theory duplication). Sources:
* SourceThetaPilotIQContainment.lean:126/141;
* SourceSHETransportObligations.lean:191/197 (namespace SourceSHESquareSupply);
* SourceHullInterfaceDischarge.lean:149;
* SourceK1K2VolumeTranslationLaw.lean:79/90 (namespace K1K2Realization);
* Ind3UpperSemiConstruction.lean:51/56/66 (namespace Ind3UpperSemi);
* SourceLogShellMuNQuotientCarrier.lean:75/80;
* HullDeterminantLogVolumeReduction.lean:213/302;
* AbsoluteKummerContinuity.lean:74;
* ABCFrontierReductions.lean:301/256.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainInferredReuseActual

open LeanFormal.IUT

/-- theta-pilot generator containment -> possible image subset (inferred chain). -/
theorem chain_thetaIQ_subset :=
  fun T hgen => possibleImage_subset_sourceThetaPilotIQPacket T hgen

/-- theta-pilot product map image inside tensor IQ packet (inferred chain). -/
theorem chain_thetaIQ_product :=
  fun T hgen => sourceThetaPilotProductMap_image_subset_tensorIQPacket T hgen

/-- SHE square statement evidence (inferred chain). -/
theorem chain_she_statement :=
  fun W => SourceSHESquareSupply.sheStatement_evidence W

/-- SHE square slot evidence (inferred chain). -/
theorem chain_she_slot :=
  fun W h => SourceSHESquareSupply.sheSlot_evidence W h

/-- Haar-contraction interface hull log-volume finiteness (inferred chain). -/
theorem chain_hull_haar_finite :=
  fun E => haarContractionInterface_hull_logVolume_lt_top E

/-- K1/K2 volume-class law from volume-translation data (inferred chain). -/
theorem chain_volumeClass :=
  fun h => K1K2Realization.volumeClassLaw_of_volumeTranslationData h

/-- K1/K2 fiber-factor law iff volume-class law (inferred chain). -/
theorem chain_volumeFiberIff :=
  K1K2Realization.volumeFiberFactorLaw_iff_volumeClassLaw

/-- Ind3 output image family carrier (inferred chain). -/
theorem chain_ind3_carrier :=
  fun l c => Ind3UpperSemi.outputImageFamily_carrier l c

/-- Ind3 output image family membership (inferred chain). -/
theorem chain_ind3_mem :=
  fun l c => Ind3UpperSemi.outputImageFamily_mem_iff l c

/-- Ind3 output image family value (inferred chain). -/
theorem chain_ind3_value :=
  fun l c => Ind3UpperSemi.outputImageFamily_value l c

/-- Absolute Kummer map continuity (inferred chain). -/
theorem chain_absKummer_cont :=
  AbsoluteKummerContinuity.continuous_absoluteKummerMap

/-- muN quotient kernel (inferred chain). -/
theorem chain_muN_ker := fun D => muNQuotientMap_ker D

/-- muN quotient surjectivity (inferred chain). -/
theorem chain_muN_surj := fun D => muNQuotientMap_surjective D

/-- Packet tensor-power log-volume law (inferred chain). -/
theorem chain_packetPower :=
  fun packet M => packetLogVolume_tensorPower packet M

/-- Matrix log-det power law (inferred chain). -/
theorem chain_matrixLogDet_pow :=
  fun hA M => matrixLogDet_pow_posDef hA M

/-- Gap-reduced frontier -> ABC (inferred chain). -/
theorem chain_frontierGapReduced_abc :=
  fun h => abcConjecture_of_frontierGapReduced h

/-- Gap-reduced frontier -> ABCFrontier (inferred chain). -/
theorem chain_frontierGapReduced_reduce :=
  fun h => ABCFrontier.reduce_gapReductionInputs h

def chainInferredRows : List (String × String × String) :=
  [ ("theta-pilot IQ", "CHAIN PROVED", "chain_thetaIQ_subset/product"),
    ("SHE evidence", "CHAIN PROVED", "chain_she_statement/slot"),
    ("hull discharge", "CHAIN PROVED", "chain_hull_haar_finite"),
    ("K1/K2 volume laws", "CHAIN PROVED", "chain_volumeClass/volumeFiberIff"),
    ("Ind3 upper-semi kernel", "CHAIN PROVED", "chain_ind3_carrier/mem/value"),
    ("absolute Kummer continuity", "CHAIN PROVED", "chain_absKummer_cont"),
    ("muN quotient", "CHAIN PROVED", "chain_muN_ker/surj"),
    ("det tensor laws", "CHAIN PROVED", "chain_packetPower/matrixLogDet_pow"),
    ("ABC frontier reduction", "CHAIN PROVED", "chain_frontierGapReduced_abc/reduce") ]

theorem chainInferredRows_length : chainInferredRows.length = 9 := rfl

#check chain_thetaIQ_subset
#check chainInferredRows_length

end LeanFormal.IUT.XiFPaper.Mzk1ChainInferredReuseActual
end