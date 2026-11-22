import tmp.sheaf.xif.paper.GlobalQPilotNormalizedLogVolumeActual
noncomputable section
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.GlobalQPilotNormalizedLogVolumeActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1QPilotNormalizedSpecActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

structure S3128Stage1QPilotNormalizedSpec : Prop where
  local_eq :
    ∀ b : Bad (nativePlaceSelection T),
      qPilotLocalNormalizedLogMagnitude T b =
        nativeBadLocalWeight T b * baseQLogMagnitude T b
  global_eq :
    paperQPilotNormalizedLogMagnitude T =
      ∑ b : Bad (nativePlaceSelection T),
        nativeBadLocalWeight T b * baseQLogMagnitude T b
  weight_pos :
    ∀ b, 0 < qPilotLocalNormalizedWeight T b
  local_pos :
    ∀ b, 0 < qPilotLocalNormalizedLogMagnitude T b
  global_pos :
    [Nonempty (Bad (nativePlaceSelection T))] →
      0 < paperQPilotNormalizedLogMagnitude T

theorem S3128Stage1QPilotNormalizedSpec_ofSource :
    S3128Stage1QPilotNormalizedSpec T :=
  { local_eq := fun b => qPilotLocalNormalizedLogMagnitude_eq T b
    global_eq := paperQPilotNormalizedLogMagnitude_eq T
    weight_pos := fun b => qPilotLocalNormalizedWeight_pos T b
    local_pos := fun b => qPilotLocalNormalizedLogMagnitude_pos T b
    global_pos := fun _ => paperQPilotNormalizedLogMagnitude_pos T }

#check S3128Stage1QPilotNormalizedSpec
#check S3128Stage1QPilotNormalizedSpec_ofSource
end LeanFormal.IUT.XiFPaper.S3128Stage1QPilotNormalizedSpecActual