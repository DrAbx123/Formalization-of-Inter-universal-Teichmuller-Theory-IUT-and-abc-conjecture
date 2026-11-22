import tmp.sheaf.xif.paper.S2165BaseChangeWitnessActual
import tmp.sheaf.xif.paper.S2058D6FiniteEtaleActual

/-! # S2175: (a2) toSource and commutes of the base-changed presentation

Constructs the source map and the commutes 2-cell of the presentation obtained
by base-changing Q along a finite-etale s : T -> A.  The two-pullback witness
is still the separate missing input (b).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual

open CategoryTheory
open CategoryTheory.Bicategory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2161BaseChangeAPIActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)
variable (hs : IsFinite s.left) (hse : Etale s.left)
variable (hq : IsFinite (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)
variable (hqe : Etale (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)

abbrev S2175FstT : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    (schemeRepresentableEtalePseudofunctor S1726K Q.pullbackScheme) :=
  S1742StrongTransOfHom (S2165Fst (m := m) (s := s) (vy := vy) (Q := Q))

abbrev S2175SndT : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    (schemeRepresentableEtalePseudofunctor S1726K T) :=
  S1742StrongTransOfHom (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q))

abbrev S2175sT : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K T)
    (schemeRepresentableEtalePseudofunctor S1726K A) :=
  S1742StrongTransOfHom s

/-- The source map of the base-changed presentation. -/
noncomputable def S2175ToSource : Pseudofunctor.StrongTrans
    (schemeRepresentableEtalePseudofunctor S1726K (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    X.fiber :=
  Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q)) Q.toSource

theorem S2175HomEq :
    S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.vcomp (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
          Q.projectionMap.transformation) =
      S1742HomOfStrongTrans
        (Pseudofunctor.StrongTrans.vcomp (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
          (S2175sT (s := s))) := by
  rw [S2096HomOfVcomp, S2096HomOfVcomp,
    S1742HomOfStrongTrans_strongTransOfHom,
    S2096HomOfSchemeRepresentableMap Q.projection Q.projectionMap,
    S1742HomOfStrongTrans_strongTransOfHom]
  change S2165Fst (m := m) (s := s) (vy := vy) (Q := Q) ≫ Q.projection =
    S2165Snd (m := m) (s := s) (vy := vy) (Q := Q) ≫ s
  exact S2165Square (m := m) (s := s) (vy := vy) (Q := Q)

/-- The comparison between the two composites of base-changed structure maps. -/
noncomputable def S2175ProjectionIso :
    Iso (Pseudofunctor.StrongTrans.vcomp
        (S2175FstT (m := m) (s := s) (vy := vy) (Q := Q))
        Q.projectionMap.transformation)
      (Pseudofunctor.StrongTrans.vcomp
        (S2175SndT (m := m) (s := s) (vy := vy) (Q := Q))
        (S2175sT (s := s))) :=
  (S1742StrongTransIsoOfHom _).symm.trans
    ((eqToIso (congrArg S1742StrongTransOfHom
      (S2175HomEq (m := m) (s := s) (vy := vy) (Q := Q)))).trans
      (S1742StrongTransIsoOfHom _))


#print axioms S2175ProjectionIso
#check S2175ToSource
#check S2175ProjectionIso

end LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual

end
