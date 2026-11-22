import tmp.sheaf.xif.paper.S556QvPhiInputActual
import tmp.sheaf.xif.paper.S563QvOrderElementConstructionActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

-- S565: instantiate S563 QvPhiQOrderFields from S556 Input.
-- The aligned divisor map is actual; no rational function with divisor
-- qVFamilyK.order is selected.  Exact witness recorded.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S565QvOrderFromS556InputActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S550QvPhiPreFrobenioidActual
open LeanFormal.IUT.XiFPaper.S556QvPhiInputActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid

universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (D : S556InputDataActual (K := K))
abbrev Dat (D : S556InputDataActual (K := K)) := s556InputActual D
variable (A : Object (qvPhi D.ramification))

structure S556QOrderWitness where
  rationalFunction : (Dat D).rationalFunctions.obj A.base
  divisor_eq : (Dat D).divisor A.base rationalFunction =
    Algebra.GrothendieckAddGroup.of
      (ULift.up ((qVFamilyK T b).order) :
        ((qvPhi D.ramification).obj A.base).carrier)

noncomputable def qOrderFieldsOfWitness
    (W : S556QOrderWitness (K := K) T b D A) :
    QvPhiQOrderFields D.ramification (Dat D) A where
  divisor := ULift.up ((qVFamilyK T b).order)
  rationalFunction := W.rationalFunction
  divisor_eq := W.divisor_eq

noncomputable def qOrderEndomorphismS556
    (W : S556QOrderWitness (K := K) T b D A) :
    (qvPreFrobenioid D.ramification (Dat D)).LinearBaseIdentityEndomorphism A :=
  qOrderEndomorphismOfFields D.ramification (Dat D) A
    (qOrderFieldsOfWitness (K := K) T b D A W)

noncomputable def tauS556
    (W : S556QOrderWitness (K := K) T b D A) :
    Submonoid ((qvPreFrobenioid D.ramification (Dat D)).LinearBaseIdentityEndomorphism A) :=
  tauOfQOrderFields D.ramification (Dat D) A
    (qOrderFieldsOfWitness (K := K) T b D A W)

#check S556QOrderWitness
#check qOrderFieldsOfWitness
#check qOrderEndomorphismS556
#check tauS556

end LeanFormal.IUT.XiFPaper.S565QvOrderFromS556InputActual

end