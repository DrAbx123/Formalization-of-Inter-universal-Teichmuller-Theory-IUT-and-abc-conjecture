import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S593PositivePreimageQvOrderActual
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid
open Iut.SourceFinitePlaceReconstruction
open Additive

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))

noncomputable def positiveQvPhiPreimageAtQvOrder :
    PositiveQvPhiPreimage (K := K) P A (qVFamilyK T b).order :=
  S575QvPhiPositivePreimageActual.positiveQvPhiPreimage (K := K) P A (qVFamilyK T b).order
    (qVFamilyK T b).order_pos

end LeanFormal.IUT.XiFPaper.S593PositivePreimageQvOrderActual
end