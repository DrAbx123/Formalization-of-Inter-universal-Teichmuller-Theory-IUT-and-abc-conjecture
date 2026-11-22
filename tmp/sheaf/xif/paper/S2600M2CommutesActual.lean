import tmp.sheaf.xif.paper.S2224BaseChangeCommutesFinalActual
import tmp.sheaf.xif.paper.S2175BaseChangePresentationActual
import tmp.sheaf.xif.paper.S2165BaseChangeWitnessActual

/-! # S2600: M2 commutes actual -/

noncomputable section
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual

namespace LeanFormal.IUT.XiFPaper.S2600M2CommutesActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def projectionMap :
    SchemeRepresentableMap (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)) where
  transformation := S1742StrongTransOfHom
    (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))
  app_eq := fun _ => rfl

noncomputable def toSource : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K
      (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q))) X.fiber :=
  S2175ToSource (m := m) (s := s) (vy := vy) (Q := Q)

noncomputable def basePoint : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy

structure PartialPresentation
    (m : X.Hom Y)
    (pt : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) Y.fiber) where
  pullbackScheme : SchemeOverField S1726K
  projection : pullbackScheme ⟶ T
  projectionMap : SchemeRepresentableMap projection
  toSource : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K pullbackScheme) X.fiber
  commutes : Iso
    (Pseudofunctor.StrongTrans.vcomp toSource m)
    (Pseudofunctor.StrongTrans.vcomp projectionMap.transformation pt)

noncomputable def S2600PartialPresentation :
    PartialPresentation (m := m) (pt := basePoint (s := s) vy) where
  pullbackScheme := S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)
  projection := S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)
  projectionMap := projectionMap (m := m) (s := s) (vy := vy) (Q := Q)
  toSource := toSource (m := m) (s := s) (vy := vy) (Q := Q)
  commutes := S2224Commutes (m := m) (s := s) (vy := vy) (Q := Q)

#check S2600PartialPresentation
#print axioms S2600PartialPresentation

end LeanFormal.IUT.XiFPaper.S2600M2CommutesActual
end
