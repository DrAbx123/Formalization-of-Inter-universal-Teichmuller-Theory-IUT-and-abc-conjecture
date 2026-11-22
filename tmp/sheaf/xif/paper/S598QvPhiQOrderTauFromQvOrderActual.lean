import tmp.sheaf.xif.paper.S593PositivePreimageQvOrderActual
import tmp.sheaf.xif.paper.S566QvPhiQOrderFieldsActual
import tmp.sheaf.xif.paper.S563QvOrderElementConstructionActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S598QvPhiQOrderTauFromQvOrderActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S593PositivePreimageQvOrderActual
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

noncomputable def positivePreimageAtQvOrder :
    PositiveQvPhiPreimage (K := K) P A (qVFamilyK T b).order :=
  positiveQvPhiPreimageAtQvOrder (K := K) T b P A

noncomputable def qOrderFieldsAtQvOrder :
    QvPhiQOrderFields (K := K) P.ramification (s566Input (K := K) P) A where
  divisor := (positivePreimageAtQvOrder (K := K) T b P A).divisor
  rationalFunction := (positivePreimageAtQvOrder (K := K) T b P A).rationalFunction
  divisor_eq := (positivePreimageAtQvOrder (K := K) T b P A).divisor_eq

noncomputable def qOrderEndomorphismAtQvOrder :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A :=
  qOrderEndomorphismOfFields (K := K) P.ramification (s566Input (K := K) P) A
    (qOrderFieldsAtQvOrder (K := K) T b P A)

noncomputable def tauAtQvOrder :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A) :=
  tauOfQOrderFields (K := K) P.ramification (s566Input (K := K) P) A
    (qOrderFieldsAtQvOrder (K := K) T b P A)

theorem qOrderFieldsAtQvOrder_divisor :
    (qOrderFieldsAtQvOrder (K := K) T b P A).divisor =
      (ULift.up (qVFamilyK T b).order :
        ((qvPhi (K := K) P.ramification).obj A.base).carrier) := rfl

end LeanFormal.IUT.XiFPaper.S598QvPhiQOrderTauFromQvOrderActual

end
