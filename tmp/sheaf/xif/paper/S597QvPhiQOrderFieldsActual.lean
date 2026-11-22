import tmp.sheaf.xif.paper.S563QvOrderElementConstructionActual
import tmp.sheaf.xif.paper.S593PositivePreimageQvOrderActual
import tmp.sheaf.xif.paper.S575QvPhiPositivePreimageActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
/-! # S597: actual QvPhiQOrderFields and tau from S593 positive preimage
The S593 positiveQvPhiPreimageAtQvOrder is actual; its divisor/rationalFunction/
divisor_eq fields directly give S563's QvPhiQOrderFields, then the qOrder
endomorphism and tau = Submonoid.powers. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
namespace LeanFormal.IUT.XiFPaper.S597QvPhiQOrderFieldsActual
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
open LeanFormal.IUT.XiFPaper.S561QvPhiMinimalPackageActual
open LeanFormal.IUT.XiFPaper.S563QvOrderElementConstructionActual
open LeanFormal.IUT.XiFPaper.S566QvPhiQOrderFieldsActual
open LeanFormal.IUT.XiFPaper.S575QvPhiPositivePreimageActual
open LeanFormal.IUT.XiFPaper.S593PositivePreimageQvOrderActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid
universe u
variable {K : Type u} [Field K]
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable (P : S561MinimalPackage (K := K))
variable (A : Object (qvPhi (K := K) P.ramification))
/-- Actual positive qOrder preimage at qVFamilyK.order. -/
noncomputable abbrev positivePreimage
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    PositiveQvPhiPreimage (K := K) P A (qVFamilyK T b).order :=
  positiveQvPhiPreimageAtQvOrder (K := K) (T := T) (b := b) P A
/-- Actual QvPhiQOrderFields from the positive preimage. -/
noncomputable def qOrderFields
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    QvPhiQOrderFields (K := K) P.ramification (s566Input (K := K) P) A where
  divisor := (positivePreimage (K := K) P A T b).divisor
  rationalFunction :=
    (positivePreimage (K := K) P A T b).rationalFunction
  divisor_eq :=
    (positivePreimage (K := K) P A T b).divisor_eq
/-- Actual qOrder endomorphism from the fields. -/
noncomputable def qOrderEndomorphism
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A :=
  qOrderEndomorphismOfFields (K := K) P.ramification (s566Input (K := K) P) A
    (qOrderFields (K := K) P A T b)
/-- Actual tau = powers of the qOrder endomorphism. -/
noncomputable def qOrderTau
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    Submonoid (PreFrobenioid.LinearBaseIdentityEndomorphism
      (P := qvPreFrobenioid (K := K) P.ramification (s566Input (K := K) P)) A) :=
  tauOfQOrderFields (K := K) P.ramification (s566Input (K := K) P) A
    (qOrderFields (K := K) (T := T) (b := b) P A)
theorem qOrderEndomorphism_mem_qOrderTau
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    qOrderEndomorphism (K := K) P A T b ∈
      qOrderTau (K := K) P A T b :=
  Submonoid.mem_powers _
theorem qOrderTau_eq_powers
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) :
    qOrderTau (K := K) (T := T) (b := b) P A =
      Submonoid.powers (qOrderEndomorphism (K := K) (T := T) (b := b) P A) := rfl
end LeanFormal.IUT.XiFPaper.S597QvPhiQOrderFieldsActual
