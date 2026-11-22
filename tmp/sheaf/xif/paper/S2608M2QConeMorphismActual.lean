import tmp.sheaf.xif.paper.S2607M2SchemeConeMorphismPartial
import tmp.sheaf.xif.paper.S2175BaseChangePresentationActual
import tmp.sheaf.xif.paper.S2600M2CommutesActual

/-! # S2608: qConeMorphism via a local copy of baseSquare -/

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
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual
open LeanFormal.IUT.XiFPaper.S2600M2CommutesActual
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial

namespace LeanFormal.IUT.XiFPaper.S2608M2QConeMorphismActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- Local copy with explicitly written legs. -/
noncomputable def baseSquareLocal : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K
      (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    X.fiber
    (schemeRepresentableEtalePseudofunctor S1726K T)
    Y.fiber where
  toX := S2175ToSource (m := m) (s := s) (vy := vy) (Q := Q)
  toY := S1742StrongTransOfHom (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))
  xToBase := m
  yToBase := basePoint (s := s) vy
  commutes := S2224Commutes (m := m) (s := s) (vy := vy) (Q := Q)

theorem baseSquareLocal_eq : baseSquareLocal (m := m) (s := s) (vy := vy) (Q := Q) =
    baseSquare (m := m) (s := s) (vy := vy) (Q := Q) := rfl

noncomputable def coneQLocal {W : EtaleStackPseudofunctor S1726K}
    (c : (baseSquareLocal (m := m) (s := s) (vy := vy) (Q := Q)).Cone W) :
    (qSquare (m := m) (vy := vy) (Q := Q)).Cone W where
  toX := c.toX
  toY := Pseudofunctor.StrongTrans.vcomp c.toY (S1742StrongTransOfHom s)
  commutes := c.commutes.trans
    (S2058AssociatorIso c.toY (S1742StrongTransOfHom s) vy).symm

noncomputable def qConeMorphismLocal
    {W : EtaleStackPseudofunctor S1726K}
    {source target : (baseSquareLocal (m := m) (s := s) (vy := vy) (Q := Q)).Cone W}
    (f : (baseSquareLocal (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    (qSquare (m := m) (vy := vy) (Q := Q)).ConeMorphism
      (coneQLocal (m := m) (s := s) (vy := vy) (Q := Q) source)
      (coneQLocal (m := m) (s := s) (vy := vy) (Q := Q) target) where
  toX := f.toX
  toY := Pseudofunctor.StrongTrans.whiskerRight f.toY (S1742StrongTransOfHom s)
  compatibility := by
    let tc : Iso (Pseudofunctor.StrongTrans.vcomp target.toX m)
        (Pseudofunctor.StrongTrans.vcomp target.toY
          (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy)) :=
      target.commutes
    let sc : Iso (Pseudofunctor.StrongTrans.vcomp source.toX m)
        (Pseudofunctor.StrongTrans.vcomp source.toY
          (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy)) :=
      source.commutes
    have hf' : Pseudofunctor.StrongTrans.whiskerRight f.toX m ≫ tc.hom =
        sc.hom ≫ Pseudofunctor.StrongTrans.whiskerRight f.toY
          (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy) :=
      f.compatibility
    simp only [qSquare, coneQLocal, Iso.trans_hom, Category.assoc]
    change Pseudofunctor.StrongTrans.whiskerRight f.toX m ≫
        tc.hom ≫
        (S2058AssociatorIso target.toY (S1742StrongTransOfHom s) vy).symm.hom =
      sc.hom ≫
        (S2058AssociatorIso source.toY (S1742StrongTransOfHom s) vy).symm.hom ≫
        Pseudofunctor.StrongTrans.whiskerRight
          (Pseudofunctor.StrongTrans.whiskerRight f.toY
            (S1742StrongTransOfHom s)) vy
    rw [← Category.assoc]
    rw [hf']
    rw [Category.assoc]
    rw [cancel_epi (sc.hom)]
    exact CategoryTheory.Bicategory.associator_inv_naturality_left
      (B := EtaleStackPseudofunctor S1726K)
      (a := W) (b := schemeRepresentableEtalePseudofunctor S1726K T)
      (c := schemeRepresentableEtalePseudofunctor S1726K A) (d := Y.fiber)
      (f := source.toY) (f' := target.toY)
      (η := f.toY) (g := S1742StrongTransOfHom s) (h := vy)

noncomputable def qConeMorphism
    {W : EtaleStackPseudofunctor S1726K}
    {source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W}
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target) :
    (qSquare (m := m) (vy := vy) (Q := Q)).ConeMorphism
      (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source)
      (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target) := by
  exact qConeMorphismLocal (m := m) (s := s) (vy := vy) (Q := Q) f

#check qConeMorphism
#print axioms qConeMorphism

end LeanFormal.IUT.XiFPaper.S2608M2QConeMorphismActual
end
