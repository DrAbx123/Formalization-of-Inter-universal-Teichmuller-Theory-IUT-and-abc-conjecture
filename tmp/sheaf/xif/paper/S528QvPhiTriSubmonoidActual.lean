import tmp.sheaf.xif.paper.S516ULiftNatPhiActual
import tmp.sheaf.xif.paper.S438QVFamilyKSideCandidateActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 3000000

namespace LeanFormal.IUT.XiFPaper.S528QvPhiTriSubmonoidActual

open CategoryTheory
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S516ULiftNatPhiActual
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open Iut.SourceFinitePlaceReconstruction
open Iut.SourceModelFrobenioid

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

theorem uliftNatMulLeft_apply_nsmul (e : ℕ) (n : ULift.{u+1} ℕ) :
    uliftNatMulLeft e n = e • n := by
  apply ULift.ext
  simp [uliftNatMulLeft, nsmul_eq_mul]

noncomputable def qvTriQOrder
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (N : ℕ) : ℕ :=
  N * (qVFamilyK T b).order

theorem qvTriQOrder_pos
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) (N : ℕ) (hN : 0 < N) :
    0 < qvTriQOrder T b N :=
  Nat.mul_pos hN (qVFamilyK T b).order_pos

/-- The S516 Qv-Phi model specialized to K. -/
noncomputable def dvQvPhiModel
    (E : QvRamificationIndexData (T.arithmetic.K)) :
    DivisorialMonoidOn (Example32SmallBase T.arithmetic.K)
      (fun {_ _} f => IsIso f) :=
  qvPhiRamificationModel E

/-- The N*qOrder submonoid of the ULift Nat carrier. -/
noncomputable def qvTriSubmonoid (qOrder : ℕ) : AddSubmonoid (ULift.{1} ℕ) :=
  AddSubmonoid.closure ({qOrder • (ULift.up (1 : ℕ) : ULift.{1} ℕ)} :
    Set (ULift.{1} ℕ))

structure QvPhiTriCandidate (N : ℕ) (hN : 0 < N) where
  ramification : QvRamificationIndexData (T.arithmetic.K)
  qOrder : ℕ
  qOrder_eq : qOrder = N * (qVFamilyK T b).order
  split : ∀ _X : Example32SmallBase T.arithmetic.K, AddSubmonoid (ULift.{1} ℕ)
  split_eq : split = fun _ => qvTriSubmonoid qOrder
  pullback_mem : ∀ {X Y : Example32SmallBase T.arithmetic.K}
    (f : X ⟶ Y) (n : ULift.{1} ℕ),
    n ∈ split Y → (dvQvPhiModel (T := T) ramification).pullback f n ∈ split X

noncomputable def qvPhiTriCandidate (N : ℕ) (hN : 0 < N)
    (E : QvRamificationIndexData (T.arithmetic.K)) :
    QvPhiTriCandidate (T := T) (b := b) N hN where
  ramification := E
  qOrder := qvTriQOrder T b N
  qOrder_eq := rfl
  split := fun _ => qvTriSubmonoid (qvTriQOrder T b N)
  split_eq := rfl
  pullback_mem := by
    intro X Y f n hn
    change uliftNatMulLeft (E.index f) n ∈ qvTriSubmonoid (qvTriQOrder T b N)
    rw [uliftNatMulLeft_apply_nsmul]
    exact AddSubmonoid.nsmul_mem _ hn (E.index f)

def QvPhiTriCandidateRequired
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) : Prop :=
  Nonempty (QvRamificationIndexData (T.arithmetic.K))

end LeanFormal.IUT.XiFPaper.S528QvPhiTriSubmonoidActual

end
