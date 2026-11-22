import LeanFormal.IUT.IUTIII.Theorem311.ParametricCarrier
import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring

-- S1153: algorithm output audit.  ParametricCarrier.runAlgorithm produces
-- target + level/profile/image monotonicity; sourceAlgorithmOfCarrier keeps
-- only the output target and the two permutation actions.  SourceRun records
-- the full run; forgetRun is the forgetful map to the reduced algorithm.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S1153AlgorithmOutputAuditActual

open LeanFormal.IUT
open LeanFormal.IUT.ParametricTheorem311
open LeanFormal.IUT.SourceMultiradialPresentationWiring
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.MultiradialKernel
open LeanFormal.IUT.MultiradialKernel.Core

universe uG1 uG2 u v uv ua upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable {Label : Type u} {Choice : Type v} [AddGroup Label]
variable {G1 : Type uG1} [Group G1] {G2 : Type uG2} [Group G2]
variable {I : OriginalInput l V} {n : Int}

/-- A full source run: it preserves the carrier choice, input source/route,
and the entire AlgorithmOutput (target plus level/profile/image facts). -/
structure SourceRun
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier) where
  source : Choice
  source_eq : source = input.source
  route : List (RouteStep Label)
  route_eq : route = input.route
  output : AlgorithmOutput carrier input
  output_is_run : output = runAlgorithm carrier input

/-- Actual SourceRun from the actual runAlgorithm. -/
noncomputable def sourceRunOf
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier) :
    SourceRun carrier autom ind2Data input where
  source := input.source
  source_eq := rfl
  route := input.route
  route_eq := rfl
  output := runAlgorithm carrier input
  output_is_run := rfl

/-- forgetRun: keep only the reduced Choice output and the two actions. -/
noncomputable def forgetRun
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (_R : SourceRun carrier autom ind2Data input) :
    Theorem311Source.SourceTheorem311MultiradialAlgorithm G1 G2 I n Choice :=
  sourceAlgorithmOfCarrier (I := I) (n := n) carrier autom ind2Data input

/-- forgetRun's output is exactly the run target; everything else in
SourceRun (source, route, level/profile/image facts) is discarded. -/
theorem forgetRun_output
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (R : SourceRun carrier autom ind2Data input) :
    (forgetRun (I := I) (n := n) carrier autom ind2Data input R).presentation.output =
      R.output.target := by
  unfold forgetRun sourceAlgorithmOfCarrier sourcePresentationOfCarrier
  rw [R.output_is_run, runAlgorithm_target]

/-- SourceRun retains the source choice. -/
theorem sourceRun_source_eq
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (R : SourceRun carrier autom ind2Data input) :
    R.source = input.source := R.source_eq

/-- SourceRun retains the route. -/
theorem sourceRun_route_eq
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (R : SourceRun carrier autom ind2Data input) :
    R.route = input.route := R.route_eq

/-- SourceRun retains level monotonicity. -/
theorem sourceRun_level_monotone
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (R : SourceRun carrier autom ind2Data input) :
    carrier.core.level input.source ≤ carrier.core.level R.output.target :=
  R.output.level_monotone

/-- SourceRun retains profile monotonicity. -/
theorem sourceRun_profile_monotone
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (R : SourceRun carrier autom ind2Data input) :
    carrier.profile.logVolume input.source ≤
      carrier.profile.logVolume R.output.target :=
  R.output.profile_monotone

/-- SourceRun retains the image upper witnesses. -/
theorem sourceRun_image_upper
    (carrier : Carrier Label Choice)
    (autom : SourceProcessionAutomorphismData carrier G1)
    (ind2Data : Ind2ActionData carrier autom G2)
    (input : AlgorithmInput carrier)
    (R : SourceRun carrier autom ind2Data input)
    (z : Real) (hz : z ∈ carrier.profile.possibleImage input.source) :
    ∃ w, w ∈ carrier.profile.possibleImage R.output.target ∧ z ≤ w :=
  R.output.target_image_upper z hz

#check forgetRun_output
#check sourceRun_source_eq
#check sourceRun_level_monotone
#check sourceRun_profile_monotone
#check sourceRun_image_upper

end LeanFormal.IUT.XiFPaper.S1153AlgorithmOutputAuditActual

end