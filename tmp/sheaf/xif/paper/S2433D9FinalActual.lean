import tmp.sheaf.xif.paper.S2430D9CloseActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2430D9CloseActual
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

namespace LeanFormal.IUT.XiFPaper.S2433D9FinalActual

variable (S : Iut.SchemeOverField S1726K)

/-- Exact form of the prestack-half missing: it is the D9 slice-push naturality,
not a D6 strong certificate. -/
theorem S2433PrestackOwnership :
    S2103FirstMissing S1726K ↔
      ∀ (X : Iut.SchemeOverField S1726K)
        (M N : Sheaf ((Iut.SchemeOverField.etaleTopology S1726K).over X) (Type)),
        SlicePushNaturality (J := Iut.SchemeOverField.etaleTopology S1726K) (A := Type) M N :=
  Iff.rfl

/-- Exact form of the effective-descent missing. -/
theorem S2433EffDescentOwnership :
    S2134FirstMissing S1726K ↔
      S2134EffDescentOnEtaleFamilies S1726K :=
  Iff.rfl

/-- The Psub NatIso first missing, uniformly in M N. -/
abbrev S2433SignProjectionMissing : Prop :=
  S2428PsubNatIsoMissing S

/-- Conditional Psub NatIso re-export. -/
noncomputable def S2433PsubNatIso_of_missing
    (h : S2433SignProjectionMissing S)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2152Q.presheafHom M N ≅ S2332Psub S M N :=
  S2430PsubNatIso_of_missing S h M N

/-- Exact three-input decomposition of the D9 missing. -/
theorem S2433D9Missing_iff_three :
    S2428D9Missing S ↔
      S2103FirstMissing S1726K ∧
        S2134EffDescentOnEtaleFamilies S1726K ∧
          S2433SignProjectionMissing S :=
  Iff.rfl

#print axioms S2433PrestackOwnership
#print axioms S2433EffDescentOwnership
#print axioms S2433D9Missing_iff_three

end LeanFormal.IUT.XiFPaper.S2433D9FinalActual

end
