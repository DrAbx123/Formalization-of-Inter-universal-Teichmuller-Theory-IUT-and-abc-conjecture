import LeanFormal/IUT/IUTIII/Corollary312/StepXI/HolomorphicHull/CardAMPLThetaBoundSupply
import LeanFormal/IUT/IUTIII/Corollary312/StepXI/SourceProcessionStepXI

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

/-!
# Mzk1ConsumerAMPLProcessionActual — A476 real consumer theorems (AMPL supply / procession wall)

New conclusions combining existing donor theorems:

* AMPL theta-bound supply (\`CardAMPLThetaBoundSupply.lean:94/101/109\`):
  \`ampl_supply_package\` — real upper bound, image-lower transfer and exact
  ofReal reconstruction jointly.
* Procession wall (\`SourceProcessionStepXI.lean:45/61/64/69/74\`):
  \`wall_package\` — the route wall's dStage, source, target and output laws
  jointly.

No sorry/axioms; no closure claim. Registry frozen 14041.
-/

namespace LeanFormal.IUT.XiFPaper.Mzk1ConsumerAMPLProcessionActual

open LeanFormal.IUT

/-- **AMPL theta-bound supply package consumer.** -/
theorem ampl_supply_package {X : Type*} {W : IQHullLogVolumeInterface X}
    (S : CardAMPLThetaBoundSupply W) {q : Real}
    (hq : ENNReal.ofReal q ≤ W.logVolume W.imageSet) :
    iqHullRealVolume W ≤ S.theta ∧ q ≤ S.theta ∧
      (∃ M : Real, W.logVolume W.hull = ENNReal.ofReal M ∧ M ≤ S.theta) :=
  ⟨S.realVolume_le,
   S.ofReal_le_theta_of_imageSet_lower hq,
   S.exists_hull_eq_ofReal⟩

/-- **Procession route-wall package consumer**: all four wall laws jointly. -/
theorem wall_package {l : PrimeGeFive} {V : Type*} {Label : Type*} {Choice : Type*}
    (input : SourceProcessionBoundary.Input (l := l) (V := V) (Label := Label) (Choice := Choice))
    (route : List (RouteStep Label)) :
    (SourceProcessionStepXI.routeWall input route).dStage = input.dStage ∧
      (SourceProcessionStepXI.routeWall input route).routeOutput.algorithmInput.source =
        input.carrier.core.base ∧
      (SourceProcessionStepXI.routeWall input route).wall.theorem311.target =
        routeTarget input.carrier route input.carrier.core.base ∧
      (SourceProcessionStepXI.routeWall input route).wall.theorem311 =
        (input.routeOutput route).output :=
  ⟨SourceProcessionStepXI.wall_dStage input route,
   SourceProcessionStepXI.wall_source input route,
   SourceProcessionStepXI.wall_target input route,
   SourceProcessionStepXI.wall_output input route⟩

#check ampl_supply_package
#check wall_package

end LeanFormal.IUT.XiFPaper.Mzk1ConsumerAMPLProcessionActual
end