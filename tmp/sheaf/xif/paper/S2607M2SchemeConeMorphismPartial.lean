import tmp.sheaf.xif.paper.S2604M2BaseWitnessPartial
import tmp.sheaf.xif.paper.S2601M2WitnessGoal
import tmp.sheaf.xif.paper.S2602M2SchemeWitnessGoal
import tmp.sheaf.xif.paper.S2512StackOpenImmersionUB

/-! # S2607: schemeConeMorphism partial, conditional on the lift 2-cell -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2512StackOpenImmersionUB
open LeanFormal.IUT.XiFPaper.S2601M2WitnessGoal
open LeanFormal.IUT.XiFPaper.S2602M2SchemeWitnessGoal
open LeanFormal.IUT.XiFPaper.S2604M2BaseWitnessPartial

namespace LeanFormal.IUT.XiFPaper.S2607M2SchemeConeMorphismPartial

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def schemeConeMorphismOf
    {W : EtaleStackPseudofunctor S1726K}
    {source target : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W}
    (f : (baseSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism source target)
    (h : Q.isPullback.lift W (coneQ (m := m) (s := s) (vy := vy) (Q := Q) source) ⟶
      Q.isPullback.lift W (coneQ (m := m) (s := s) (vy := vy) (Q := Q) target)) :
    (schemeSquare (m := m) (s := s) (vy := vy) (Q := Q)).ConeMorphism
      (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) source)
      (schemeCone (m := m) (s := s) (vy := vy) (Q := Q) target) where
  toX := h
  toY := f.toY
  compatibility := by
    exact (S2512Modification_subsingleton (F := S1726K) _ _).elim _ _

#check schemeConeMorphismOf
#print axioms schemeConeMorphismOf

end LeanFormal.IUT.XiFPaper.S2607M2SchemeConeMorphismPartial
end
