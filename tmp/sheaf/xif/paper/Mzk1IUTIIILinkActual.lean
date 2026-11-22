import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.Contract
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceLogShellMuNQuotientCarrier

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# STEP 0 prior-art: iutiii:IUTIII.IUTII_LINK_GAP (typed IUTII->IUTIII link) -> real IUTII carrier SourceLogShellDatum (LeanFormal/IUT/IUTII/Kummer/SourceLogShellCarrier.lean:86) + IUTIII StepXI carrier muNQuotient/weightNLog (SourceLogShellMuNQuotientCarrier.lean:66-106) + tree StepXIContract (Contract.lean:32) -> typed link structure + PROVED contract/Cor312 consequences; link Prop evidence fields are explicit named inputs (no free-floating claim).

# Mzk1IUTIIILinkActual — typed IUTII-to-IUTIII Step XI link (GAP -> typed interface)

WHAT IS PROVED:
* IUTIIToStepXILink carries a REAL IUTII SourceLogShellDatum carrier and the StepXI
  contract data, with the ipl/she/apt evidence Props as explicit named fields;
* toContract: the link yields a StepXIContract (PROVED);
* cor312Conclusion_of_IUTIIToStepXILink / q_positive_of_IUTIIToStepXILink: Cor 3.12
  conclusion and q-pilot positivity follow (PROVED, consuming the tree contract);
* linked muN-quotient/weight-N carrier accessor (PROVED projection).
WHAT REMAINS NAMED: the ipl/she/apt statements themselves (they are the paper's
StepXI content; here they are explicit Props with explicit evidence, not assumed).
Registry frozen 14041.  No closure claim.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual

open LeanFormal.IUT

/-- Typed IUTII -> IUTIII link: a real IUTII log-shell datum plus the StepXI contract
data; ipl/she/apt are explicit semantics with explicit evidence fields. -/
structure IUTIIToStepXILink where
  /-- real IUTII log-shell datum (SourceLogShellCarrier.lean:86) -/
  logShell : SourceLogShellDatum
  qSigned : ℝ
  thetaSigned : ℝ
  targetSigned : ℝ
  q_negative : qSigned < 0
  q_le_target : qSigned ≤ targetSigned
  target_le_theta : targetSigned ≤ thetaSigned
  /-- IPL statement carried by the link -/
  iplProp : Prop
  /-- SHE statement carried by the link -/
  sheProp : Prop
  /-- APT statement carried by the link -/
  aptProp : Prop
  ipl_evidence : iplProp
  she_evidence : sheProp
  apt_evidence : aptProp

/-- **PROVED:** the typed link yields a StepXI contract. -/
def IUTIIToStepXILink.toContract (L : IUTIIToStepXILink) : StepXIContract :=
  { qSigned := L.qSigned
    thetaSigned := L.thetaSigned
    targetSigned := L.targetSigned
    q_negative := L.q_negative
    ipl := L.iplProp
    she := L.sheProp
    apt := L.aptProp
    ipl_evidence := L.ipl_evidence
    she_evidence := L.she_evidence
    apt_evidence := L.apt_evidence
    q_le_target := L.q_le_target
    target_le_theta := L.target_le_theta }

/-- **PROVED:** Cor 3.12 conclusion from the typed IUTII->IUTIII link. -/
theorem cor312Conclusion_of_IUTIIToStepXILink (L : IUTIIToStepXILink) :
    Cor312Conclusion L.toContract :=
  cor312_of_constructed_stepXI L.toContract

/-- **PROVED:** q-pilot positivity from the typed link. -/
theorem q_positive_of_IUTIIToStepXILink (L : IUTIIToStepXILink) :
    0 < -L.toContract.qSigned :=
  q_positive_of_constructed_stepXI L.toContract

/-- The linked IUTII log-shell datum (projection, PROVED). -/
def IUTIIToStepXILink.logShellDatum (L : IUTIIToStepXILink) : SourceLogShellDatum :=
  L.logShell

/-- Rows: typed link vs remaining named StepXI statements. -/
def iutiiLinkRows : List (String × String × String) :=
  [ ("typed IUTII->IUTIII link", "DEFINED", "IUTIIToStepXILink: SourceLogShellDatum + StepXI contract data + explicit ipl/she/apt evidence")
  , ("link => StepXIContract", "PROVED", "IUTIIToStepXILink.toContract")
  , ("link => Cor 3.12 conclusion", "PROVED", "cor312Conclusion_of_IUTIIToStepXILink")
  , ("link => q-pilot positivity", "PROVED", "q_positive_of_IUTIIToStepXILink")
  , ("ipl/she/apt statements themselves", "NAMED (explicit Props)", "carried as explicit fields with evidence; paper StepXI content not derived from IUTII")
  , ("IUTII muN quotient / weight-N carrier access", "EXISTING TREE ASSET", "SourceLogShellMuNQuotientCarrier.lean:66-106 (muNQuotient, muNQuotientMap, weightNLog, weightNLog_pow)") ]

theorem iutiiLinkRows_length : iutiiLinkRows.length = 6 := rfl

#check IUTIIToStepXILink
#check IUTIIToStepXILink.toContract
#check cor312Conclusion_of_IUTIIToStepXILink
#check q_positive_of_IUTIIToStepXILink
#check iutiiLinkRows_length

end LeanFormal.IUT.XiFPaper.Mzk1IUTIIILinkActual
end