import tmp.sheaf.xif.paper.EtTh08ThetaTransformationActual

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1500000

noncomputable section

/-!
# STEP 0 prior-art: modLThetaProjection|modLEllipticProjection|modLThetaToElliptic|thetaPowerKernel|quotient laws -> hits LeanFormal/IUT/IUTII/Theta/EtaleThetaQuotient.lean:62-140 (thetaPowerKernel/thetaCommutatorKernel/ModLThetaQuotient/modLThetaProjection/modLEllipticProjection/modLThetaToElliptic/modLThetaToElliptic_mk) -> REUSE (definitional equations + kernel containment; no re-proof).

# [EtTh] 10: theta quotient laws at the mod-l level (class A)

Corpus: papers/motizuki_corpus/text/The Etale Theta Function and its Frobenioid-theoretic
Manifestations.txt, theta-group quotient package (Prop 1.4 context).
CLASS A (reused/definitional): the mod-l theta and elliptic projections as
composites, their definitional equations, and the power-kernel containment of the
theta-to-elliptic map.  CLASS B (named): geometric realization of the theta groups;
the actual theta function transformation on the realized object.
Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.EtTh10ThetaQuotientLawsActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.EtTh08ThetaTransformationActual

universe u

/-- Definitional form of the mod-l theta projection: composite of the two
quotient maps (class A, definitional). -/
theorem etTh10_modLThetaProjection_eq (G : Type u) [Group G] (l : Nat) :
    modLThetaProjection G l =
      (QuotientGroup.mk' (thetaPowerKernel G l)).comp
        (QuotientGroup.mk' (thetaCommutatorKernel G)) :=
  rfl

/-- Definitional form of the mod-l elliptic projection (class A, definitional). -/
theorem etTh10_modLEllipticProjection_eq (G : Type u) [Group G] (l : Nat) :
    modLEllipticProjection G l =
      (QuotientGroup.mk' (ellipticPowerKernel G l)).comp
        (QuotientGroup.mk' (thetaDerivedSubgroup G)) :=
  rfl

/-- Power-kernel containment for the theta-to-elliptic map (class A, reused). -/
theorem etTh10_thetaPowerKernel_le_comap (G : Type u) [Group G] (l : Nat) :
    thetaPowerKernel G l ≤ (ellipticPowerKernel G l).comap (thetaToElliptic G) :=
  thetaToElliptic_maps_powerKernel G l

/-- The mod-l theta-to-elliptic map on quotient classes (class A, reused). -/
theorem etTh10_modLThetaToElliptic_mk (G : Type u) [Group G] (l : Nat)
    (x : ThetaQuotient G) :
    modLThetaToElliptic G l (QuotientGroup.mk x) =
      QuotientGroup.mk (thetaToElliptic G x) :=
  modLThetaToElliptic_mk G l x

/-- Theta quotient law rows. -/
def etTh10Rows : List (String × String × String) :=
  [ ("mod-l theta projection composite form", "A", "PROVED etTh10_modLThetaProjection_eq (definitional)")
  , ("mod-l elliptic projection composite form", "A", "PROVED etTh10_modLEllipticProjection_eq (definitional)")
  , ("power-kernel containment theta -> elliptic", "A", "REUSED EtaleThetaQuotient:103 thetaToElliptic_maps_powerKernel (etTh10_thetaPowerKernel_le_comap)")
  , ("mod-l theta-to-elliptic on quotient classes", "A", "REUSED EtaleThetaQuotient:122 modLThetaToElliptic_mk (etTh10_modLThetaToElliptic_mk)")
  , ("geometric realization of the theta groups", "B", "NAMED paper input (EtaleThetaQuotient header: later obligations)")
  , ("actual theta function transformation on the realized object", "B", "NAMED; only the abstract ThetaShiftData package (EtTh08/09) is formalized") ]

/-- The mod-l quotient law row record has six rows. -/
theorem etTh10Rows_length : etTh10Rows.length = 6 := rfl

#check etTh10_modLThetaProjection_eq
#check etTh10_modLEllipticProjection_eq
#check etTh10_thetaPowerKernel_le_comap
#check etTh10_modLThetaToElliptic_mk
#check etTh10Rows_length

end LeanFormal.IUT.XiFPaper.EtTh10ThetaQuotientLawsActual
end