import tmp.sheaf.xif.paper.S539PhiCvSubmonoidActual

/-! # S553: actual QvPhiTriData packaging

Packages the S539 qOrder-generated submonoids and S524 ramification pullback
into a structure with qOrder/qOrder_pos/split/split_eq/pullback_mem/qOrder_link.
The constructor qvPhiTriDataOf takes a positive constant qOrder and an explicit
link proposition. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 6000000

namespace LeanFormal.IUT.XiFPaper.S553QvPhiTriDataActual

open CategoryTheory
open Iut
open LeanFormal.IUT.XiFPaper.S432SmallModelActual
open LeanFormal.IUT.XiFPaper.S511PhiCvCandidateActual
open LeanFormal.IUT.XiFPaper.S524QvPhiRamificationModelS518Actual
open LeanFormal.IUT.XiFPaper.S539PhiCvSubmonoidActual
open LeanFormal.IUT.XiFPaper.S438QVFamilyKSideCandidateActual
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure

universe u
variable {K : Type u} [Field K]

/-- Actual data: ramification model, qOrder, generated submonoids and their
pullback preservation, plus the candidate link proposition. -/
structure QvPhiTriData (K : Type u) [Field K] where
  ramification : RamificationIndexData (K := K)
  qOrder : Example32SmallBase K → ℕ
  qOrder_pos : ∀ X : Example32SmallBase K, 0 < qOrder X
  split : Example32SmallBase K → AddSubmonoid (ULift.{u+1} ℕ)
  split_eq : ∀ X : Example32SmallBase K,
    split X = s539PhiSubmonoid (K := K) (qOrder X) X
  pullback_mem :
    ∀ {X Y : Example32SmallBase K} (f : X ⟶ Y) {n : ULift.{u+1} ℕ},
      n ∈ split Y →
        uliftNatMulLeft (ramification.e f).val n ∈ split X
  qOrder_link : Prop

/-- Constructor from a positive constant qOrder and an explicit link. -/
noncomputable def qvPhiTriDataOf
    (ramification : RamificationIndexData (K := K))
    (qOrder : ℕ) (qOrder_pos : 0 < qOrder)
    (qOrder_link : Prop) :
    QvPhiTriData K where
  ramification := ramification
  qOrder := fun _ => qOrder
  qOrder_pos := fun _ => qOrder_pos
  split := fun X => s539PhiSubmonoid (K := K) qOrder X
  split_eq := fun _ => rfl
  pullback_mem := by
    intro X Y f n hn
    exact s539Pullback_mem (K := K) ramification qOrder f hn
  qOrder_link := qOrder_link

/-- Constructor whose qOrder is the actual K-side qVFamily order. -/
noncomputable def qvPhiTriDataOfQvFamilyK
    (ramification : RamificationIndexData (K := K))
    {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData l)
    (b : Bad (nativePlaceSelection T)) :
    QvPhiTriData K where
  ramification := ramification
  qOrder := fun _ => (qVFamilyK T b).order
  qOrder_pos := fun _ => (qVFamilyK T b).order_pos
  split := fun X =>
    s539PhiSubmonoid (K := K) (qVFamilyK T b).order X
  split_eq := fun _ => rfl
  pullback_mem := by
    intro X Y f n hn
    exact s539Pullback_mem (K := K) ramification (qVFamilyK T b).order f hn
  qOrder_link := True

end LeanFormal.IUT.XiFPaper.S553QvPhiTriDataActual

end
