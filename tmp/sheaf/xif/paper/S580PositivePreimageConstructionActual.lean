import tmp.sheaf.xif.paper.S591PositiveUnitDivisorEvalActual
import tmp.sheaf.xif.paper.S565QvOrderFromS556InputActual

-- S580: actual PositiveQvPhiPreimage from S575 positiveUnit and S591
-- divisor evaluation; actual S556QOrderWitness at qVFamilyK.order.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S580PositivePreimageConstructionActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S565QvOrderFromS556InputActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid
open Additive

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi P.ramification))

noncomputable def positiveQvPhiPreimage (qOrder : ℕ) (hpos : 0 < qOrder) :
    PositiveQvPhiPreimage P A qOrder where
  qOrder_pos := hpos
  rationalFunction := Additive.ofMul (ULift.up (positiveUnit (K := K) P A qOrder))
  divisor := ULift.up qOrder
  divisor_eq := _root_.positiveUnit_divisor_eval P A qOrder

noncomputable def s556QOrderWitnessOfPositive :
    S556QOrderWitness T b (s561InputData P) A where
  rationalFunction := Additive.ofMul
    (ULift.up (positiveUnit (K := K) P A (qVFamilyK T b).order))
  divisor_eq := _root_.positiveUnit_divisor_eval P A (qVFamilyK T b).order

#check positiveQvPhiPreimage
#check s556QOrderWitnessOfPositive

end LeanFormal.IUT.XiFPaper.S580PositivePreimageConstructionActual

end