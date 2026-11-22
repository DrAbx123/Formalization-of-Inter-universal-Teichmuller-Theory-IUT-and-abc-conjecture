import tmp.sheaf.xif.paper.S2428D9FinalActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2428D9FinalActual
open LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2430D9CloseActual

variable (S : Iut.SchemeOverField S1726K)

/-- Exact remaining D9 inputs, re-exported. -/
abbrev S2430D9Missing : Prop := S2428D9Missing S

/-- Conditional Psub NatIso, re-exported. -/
noncomputable def S2430PsubNatIso_of_missing
    (h : S2428PsubNatIsoMissing S)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2152Q.presheafHom M N ≅ S2332Psub S M N :=
  S2428PsubNatIso_of_missing S h M N

/-- Exact first missing for the Psub NatIso, re-exported. -/
abbrev S2430SignProjectionMissing : Prop := S2428PsubNatIsoMissing S

/-- Exact first missing for the stack target, re-exported. -/
abbrev S2430EffDescentMissing : Prop := S2134EffDescentOnEtaleFamilies S1726K

/-- Exact first missing for the prestack half, re-exported. -/
abbrev S2430PrestackMissing : Prop := S2103FirstMissing S1726K

#print axioms S2430PsubNatIso_of_missing

end LeanFormal.IUT.XiFPaper.S2430D9CloseActual

end
