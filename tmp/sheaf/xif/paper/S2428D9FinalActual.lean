import tmp.sheaf.xif.paper.S2427PsubNatIsoConditionalActual
import tmp.sheaf.xif.paper.S2134D9DescentActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
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

namespace LeanFormal.IUT.XiFPaper.S2428D9FinalActual

variable (S : Iut.SchemeOverField S1726K)

/-- The exact remaining Psub NatIso input, uniformly in M N. -/
def S2428PsubNatIsoMissing : Prop :=
  forall (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))),
    S2427SignProjection S M N

/-- Conditional Psub NatIso, packaged uniformly. -/
noncomputable def S2428PsubNatIso_of_missing
    (h : S2428PsubNatIsoMissing S)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2152Q.presheafHom M N ≅ S2332Psub S M N :=
  S2427NatIso_of_signProjection S M N (h M N)

/-- The exact remaining D9 inputs: prestack naturality, effective descent, and
the Psub sign projection. -/
def S2428D9Missing : Prop :=
  S2103FirstMissing S1726K ∧
    S2134EffDescentOnEtaleFamilies S1726K ∧
      S2428PsubNatIsoMissing S

#print axioms S2428PsubNatIso_of_missing
#print axioms S2428D9Missing

end LeanFormal.IUT.XiFPaper.S2428D9FinalActual

end
