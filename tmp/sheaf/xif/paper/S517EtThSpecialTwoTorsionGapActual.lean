import tmp.sheaf.xif.paper.S509OddLiftChoiceActual

-- S517 audit: repo has actual special fiber and component types, but no
-- reduction map on points, origin component, or special 2-torsion selector.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 800000

namespace LeanFormal.IUT.XiFPaper.S517EtThSpecialTwoTorsionGapActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S509OddLiftChoiceActual

universe u

-- Exact missing EtTh special 2-torsion data: point reduction, origin,
-- component-of-point, and same-component condition.
structure EtThSpecialTwoTorsionGap where
  curvePointType : Type u
  fiberPointType : Type u
  componentType : Type u
  reductionMap : curvePointType → fiberPointType
  origin : fiberPointType
  componentOf : fiberPointType → componentType
  point : curvePointType
  point_two_torsion : Prop
  point_special_component :
    componentOf (reductionMap point) = componentOf origin
  qSqrtSelection : Prop

-- No repo API found for the following (recorded exactly):
-- 1. reduction map E(K) -> special fiber;
-- 2. origin point/component of the special fiber;
-- 3. component-of-point incidence for actual points;
-- 4. EtTh special 2-torsion point whose reduction lies in the origin component.
#check EtThSpecialTwoTorsionGap

end LeanFormal.IUT.XiFPaper.S517EtThSpecialTwoTorsionGapActual

end