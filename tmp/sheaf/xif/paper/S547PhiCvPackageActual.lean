import tmp.sheaf.xif.paper.S533QvPhiSubmonoidActual
import tmp.sheaf.xif.paper.S522QvPhiRamificationModelActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual
/-! # S547: package Phi_Cv^⊢ from S522 model + S533 submonoid
qOrder is the actual qVFamilyK.order; the N*qOrder submonoid and its
ramification pullback_mem are S533; the DivisorialMonoidOn is S522's
qvPhiRamificationModel.  The ramification-index data is an explicit parameter;
no index is fabricated. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000
namespace LeanFormal.IUT.XiFPaper.S547PhiCvPackageActual
open CategoryTheory
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S533QvPhiSubmonoidActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceModelFrobenioid
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
abbrev BaseField : Type := T.arithmetic.K
/-- Package for Phi_Cv^⊢: qOrder, N*qOrder submonoid, pullback_mem, and the
actual S522 DivisorialMonoidOn. -/
structure PhiCvPackage where
  ramification : RamificationIndexData (K := BaseField T)
  phi : DivisorialMonoidOn (Example32SmallBase (BaseField T))
    (fun {_ _} f => IsIso f)
  phi_eq : phi = qvPhiRamificationModel (K := BaseField T) ramification
  qOrder : ℕ
  qOrder_eq : qOrder = (qVFamilyK T b).order
  qOrder_pos : 0 < qOrder
  submonoid : AddSubmonoid (ULift.{1} ℕ)
  submonoid_eq : submonoid = qvOrderSubmonoid qOrder
  pullback_mem : ∀ {X Y : Example32SmallBase (BaseField T)} (f : X ⟶ Y)
    {x : ULift.{1} ℕ}, x ∈ submonoid →
      (qvPhiRamificationModel (K := BaseField T) ramification).pullback f x ∈ submonoid
/-- Actual package from a ramification-index datum. -/
noncomputable def phiCvPackageOf
    (R : RamificationIndexData (K := BaseField T)) : PhiCvPackage T b where
  ramification := R
  phi := qvPhiRamificationModel (K := BaseField T) R
  phi_eq := rfl
  qOrder := qvOrder T b
  qOrder_eq := rfl
  qOrder_pos := qvOrder_pos T b
  submonoid := qvOrderSubmonoid (qvOrder T b)
  submonoid_eq := rfl
  pullback_mem := by
    intro X Y f x hx
    exact qvPhi_pullback_mem (K := BaseField T) R (qvOrder T b) f hx
/-- Exact missing ramification-index datum for the package. -/
def PhiCvPackageRequired : Prop :=
  Nonempty (RamificationIndexData (K := BaseField T))
end LeanFormal.IUT.XiFPaper.S547PhiCvPackageActual
