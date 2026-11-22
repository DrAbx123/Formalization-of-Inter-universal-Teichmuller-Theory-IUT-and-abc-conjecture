import tmp.sheaf.xif.paper.S2610M2WitnessPartialActual

/-! # S2613 C1: whiskerRight_comp step -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial
open LeanFormal.IUT.XiFPaper.S2605M2BaseWitnessActual

namespace LeanFormal.IUT.XiFPaper.S2613C1WhiskerRightCompActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

theorem whiskerRight_comp_step
    (W : EtaleStackPseudofunctor S1726K)
    {f f' : Pseudofunctor.StrongTrans W
      (schemeRepresentableEtalePseudofunctor S1726K
        (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))}
    (L : f ⟶ f') :
    Pseudofunctor.StrongTrans.whiskerRight L
      (Pseudofunctor.StrongTrans.vcomp
        (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX
        Q.toSource) =
    (S2058D6FiniteEtaleActual.S2058AssociatorIso f
      (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).inv
      ≫ Pseudofunctor.StrongTrans.whiskerRight
          (Pseudofunctor.StrongTrans.whiskerRight L
            (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX) Q.toSource
      ≫ (S2058D6FiniteEtaleActual.S2058AssociatorIso f'
          (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX Q.toSource).hom :=
  CategoryTheory.Bicategory.whiskerRight_comp
    (B := EtaleStackPseudofunctor S1726K)
    (a := W)
    (b := schemeRepresentableEtalePseudofunctor S1726K
      (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    (c := schemeRepresentableEtalePseudofunctor S1726K Q.pullbackScheme)
    (d := X.fiber) L
    (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).toX
    Q.toSource

#check whiskerRight_comp_step
#print axioms whiskerRight_comp_step

end LeanFormal.IUT.XiFPaper.S2613C1WhiskerRightCompActual
end
