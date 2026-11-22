import tmp.sheaf.xif.paper.S533QvPhiSubmonoidActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S549QvPhiTriSubmonoidActual
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S522QvPhiRamificationModelActual
open LeanFormal.IUT.XiFPaper.S533QvPhiSubmonoidActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
variable {K : Type u} [Field K]
structure QvPhiTriSubmonoidData
    (R : S511PhiCvCandidateActual.RamificationIndexData (K := K)) where
  qOrder : ℕ
  qOrder_pos : 0 < qOrder
  split : AddSubmonoid (ULift.{u+1} ℕ)
  pullback_mem :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y) {x : ULift.{u+1} ℕ},
      x ∈ split → (qvPhiRamificationModel R).pullback f x ∈ split
  qOrder_eq : qOrder = qvOrder (l := l) T b
noncomputable def qvPhiTriSubmonoidData
    (R : S511PhiCvCandidateActual.RamificationIndexData (K := K)) :
    QvPhiTriSubmonoidData (l := l) T b R where
  qOrder := qvOrder (l := l) T b
  qOrder_pos := qvOrder_pos (l := l) T b
  split := qvOrderSubmonoid (qvOrder (l := l) T b)
  pullback_mem := by
    intro X Y f x hx
    exact qvPhi_pullback_mem (K := K) R (qvOrder (l := l) T b) f hx
  qOrder_eq := rfl
end LeanFormal.IUT.XiFPaper.S549QvPhiTriSubmonoidActual
end