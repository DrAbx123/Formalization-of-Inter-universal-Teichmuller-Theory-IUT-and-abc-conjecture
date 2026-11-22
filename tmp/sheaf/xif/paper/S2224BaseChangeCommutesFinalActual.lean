import tmp.sheaf.xif.paper.S2208BaseChangeCommutesActual

/-! # S2224: final associator and composition of the base-change commutes chain

Small intermediate definitions avoid the whnf/elaboration blow-up of one giant
`Iso.trans` term.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2208BaseChangeCommutesActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)

/-- The final associator, stated with the explicit `S1742StrongTransOfHom s`
to avoid unfolding the `S2175sT` abbreviation. -/
noncomputable def S2224FinalAssoc :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
          (S1742StrongTransOfHom s)) vy)
      (Pseudofunctor.StrongTrans.vcomp (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy)) :=
  S2058AssociatorIso (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
    (S1742StrongTransOfHom s) vy


noncomputable def S2224Comp1 :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
          Q.toSource) m)
      (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp Q.projectionMap.transformation vy)) :=
  Iso.trans
    (S2208LeftAssoc (m := m) (s := s) (vy := vy) (Q := Q))
    (S2208WhiskerLeft (m := m) (s := s) (vy := vy) (Q := Q))

noncomputable def S2224Comp2 :
    Iso (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp Q.projectionMap.transformation vy))
      (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
          (S2175sT (s := s))) vy) :=
  Iso.trans
    (S2208RightAssoc (m := m) (s := s) (vy := vy) (Q := Q))
    (S2208ProjectionWhisker (m := m) (s := s) (vy := vy) (Q := Q))

noncomputable def S2224Commutes :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
          Q.toSource) m)
      (Pseudofunctor.StrongTrans.vcomp (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
        (Pseudofunctor.StrongTrans.vcomp (S2175sT (s := s)) vy)) :=
  Iso.trans
    (S2224Comp1 (m := m) (s := s) (vy := vy) (Q := Q))
    (Iso.trans
      (S2224Comp2 (m := m) (s := s) (vy := vy) (Q := Q))
      (S2224FinalAssoc (m := m) (s := s) (vy := vy) (Q := Q)))

#print axioms S2224Comp1
#print axioms S2224Comp2
#print axioms S2224Commutes

#print axioms S2224FinalAssoc

end LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual

end
