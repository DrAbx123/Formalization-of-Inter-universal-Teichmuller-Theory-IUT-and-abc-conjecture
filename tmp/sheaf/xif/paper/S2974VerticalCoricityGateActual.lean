import LeanFormal.IUT.IUTIII.Theorem311.SourceDThetaConstruction

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S2974VerticalCoricityGateActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- Actual VerticalCoricityGate from the source D-shadow: the theater family is
the shadow dStrip, the vertical links are the shadow dLink, the bridge is the
reflexive equivalence, and the source equations hold definitionally. -/
noncomputable def S2974VerticalCoricityGate : I.VerticalCoricityGate where
  dTheater := (I.dThetaShadow).dStrip
  verticalLink := fun i j => (I.dThetaShadow).dLink i j
  bridge := fun i => DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i)
  source_dTheater := fun i => rfl
  link_source := fun i j => rfl

/-- The induced DThetaRealizationGate. -/
noncomputable def S2974DThetaRealizationGate : I.DThetaRealizationGate :=
  verticalCoricityGate_of_shadow I (S2974VerticalCoricityGate I)

theorem S2974_dTheater (i : I.family.index) :
    (S2974VerticalCoricityGate I).dTheater i =
      (I.dThetaShadow).dStrip i := rfl

theorem S2974_verticalLink (i j : I.family.index) :
    (S2974VerticalCoricityGate I).verticalLink i j =
      (I.dThetaShadow).dLink i j := rfl

theorem S2974_bridge (i : I.family.index) :
    (S2974VerticalCoricityGate I).bridge i =
      DPrimeStripEquiv.refl ((I.dThetaShadow).dStrip i) := rfl

theorem S2974_realization_dTheater (i : I.family.index) :
    (S2974DThetaRealizationGate I).dTheater i =
      (I.dThetaShadow).dStrip i := rfl

#check S2974VerticalCoricityGate
#check S2974DThetaRealizationGate
#check S2974_dTheater
#check S2974_verticalLink
#check S2974_bridge
#check S2974_realization_dTheater
#print axioms S2974VerticalCoricityGate

end LeanFormal.IUT.XiFPaper.S2974VerticalCoricityGateActual
end
