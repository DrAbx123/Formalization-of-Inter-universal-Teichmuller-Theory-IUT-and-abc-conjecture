import tmp.sheaf.xif.paper.S2175BaseChangePresentationActual

/-! # S2208: factored commutes 2-cell for the base-changed presentation

Factors the S2175 commutes chain into small component isomorphisms to avoid a
giant nested `Iso.trans` elaboration.  The two-pullback witness is still the
separate missing input.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2208BaseChangeCommutesActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

noncomputable def S2208LeftAssoc :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
          Q.toSource) m)
      (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp Q.toSource m)) :=
  S2058AssociatorIso (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
    Q.toSource m

noncomputable def S2208WhiskerLeft :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp Q.toSource m))
      (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp Q.projectionMap.transformation vy)) :=
  S2058WhiskerLeft (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q)) Q.commutes

noncomputable def S2208RightAssoc :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp Q.projectionMap.transformation vy))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
          Q.projectionMap.transformation) vy) :=
  (S2058AssociatorIso (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
    Q.projectionMap.transformation vy).symm

noncomputable def S2208ProjectionWhisker :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
          Q.projectionMap.transformation) vy)
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
          (S2175sT (s := s))) vy) :=
  S2058WhiskerRight (S2175ProjectionIso (m := m) (s := s) (vy := vy) (Q := Q)) vy


#check S2208LeftAssoc
#check S2208WhiskerLeft
#check S2208RightAssoc
#check S2208ProjectionWhisker

end LeanFormal.IUT.XiFPaper.S2208BaseChangeCommutesActual

end
