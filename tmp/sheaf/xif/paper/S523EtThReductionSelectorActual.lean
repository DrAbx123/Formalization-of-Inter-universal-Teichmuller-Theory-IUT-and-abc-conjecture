import tmp.sheaf.xif.paper.S517EtThSpecialTwoTorsionGapActual

/-! # S523: reduction/origin/component selector from Psi special-fiber APIs

Repo has:
* `SourcePsiActualSpecialFiber` (Weierstrass curve over the residue field);
* `SourcePsiComponentVertex`, `SourcePsiComponentIntersectionGraph`
  (components and their incidence graph);
* `ActualComponentType`, `ActualComponentPointIncidence` (component/point
  incidence on the reduced curve).

Repo does NOT have:
1. a point-level reduction map `E(K) -> special fiber` (only coefficient
   reduction `actualMinimalReduction`/`residueMap`);
2. an `origin` point/component in that special fiber;
3. a `componentOf` map from special-fiber points to components;
4. a `sameComponent` selector on special-fiber points.

Accordingly the exact data structure is recorded with no inhabitant.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S523EtThReductionSelectorActual

universe u

/-- Exact missing EtTh reduction/component selector data. -/
structure EtThReductionSelectorData where
  curvePointType : Type u
  fiberPointType : Type u
  componentType : Type u
  reductionMap : curvePointType → fiberPointType
  origin : fiberPointType
  componentOf : fiberPointType → componentType
  sameComponent : fiberPointType → fiberPointType → Prop
  sameComponent_iff : Prop
  point : curvePointType
  point_two_torsion : Prop
  point_special_component :
    sameComponent (reductionMap point) origin
  qSqrtSelection : Prop

/-- Exact-missing predicate for the EtTh special 2-torsion selector. -/
def EtThReductionSelectorDataRequired : Prop :=
  Nonempty EtThReductionSelectorData.{u}

end LeanFormal.IUT.XiFPaper.S523EtThReductionSelectorActual
end
