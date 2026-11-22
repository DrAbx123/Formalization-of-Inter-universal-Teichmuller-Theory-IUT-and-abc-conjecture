import tmp.sheaf.xif.paper.Mzk1Cor312FinalAssemblyActual
import tmp.sheaf.xif.paper.Mzk1KummerProjectionLayerActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# XiE layer separation in the final assembly

The final requirement has three distinct layers:
1. `q_in_possible`: definitional projection of the Kummer realization
   (`qImageInS1902 = kummerProjection thetaImageOne`);
2. `possible_in_hull`: the real xi-e statement, from `kummerXiE_containment`
   (norm-bound proof, not rfl);
3. `strict_measure`: the unique named input (strict actual volume increase).
This file states the separation as Lean theorems. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentLayerV2Actual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.XiFPaper.Mzk1Cor312FinalAssemblyActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerRealizationActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerTransportActual
open LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentRequirementActual
open LeanFormal.IUT.XiFPaper.Mzk1KummerProjectionLayerActual
open LeanFormal.IUT.XiFPaper.S1902ActualThetaHullActual
open LeanFormal.IUT.N8Closure

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- Layer 1: q in possibleImages is the Kummer projection (rfl-level). -/
theorem q_in_possible_is_kummer_projection (R : PaperKummerReading T) :
    (requirementOfReading T R).q_in_possible =
      (fun _ hx => hx) := rfl

/-- Layer 2: possibleImages ⊆ hull is the genuine xi-e statement. -/
theorem possible_in_hull_is_genuine (R : PaperKummerReading T) :
    ((requirementOfReading T R).qRegion : Set (S1902Carrier T)) ⊆
      (requirementOfReading T R).hullRegion :=
  kummerXiE_containment (T := T) R.D

/-- Layer 3: strict_measure is the named strict-volume input. -/
theorem strict_measure_is_named (R : PaperKummerReading T) :
    R.D.vol {qPilotInThetaCarrier T} < R.D.vol (s1902Hull T) :=
  R.D.strict_measure

/-- The three layers are separated in the final requirement. -/
theorem xie_layers_separated (R : PaperKummerReading T) :
    (requirementOfReading T R).q_in_possible = (fun _ hx => hx) ∧
      ((requirementOfReading T R).qRegion : Set (S1902Carrier T)) ⊆
      (requirementOfReading T R).hullRegion ∧
      R.D.vol {qPilotInThetaCarrier T} < R.D.vol (s1902Hull T) :=
  ⟨rfl, possible_in_hull_is_genuine T R, strict_measure_is_named T R⟩

end LeanFormal.IUT.XiFPaper.Mzk1XiEContainmentLayerV2Actual

end
