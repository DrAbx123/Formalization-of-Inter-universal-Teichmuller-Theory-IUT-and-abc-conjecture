import tmp.sheaf.xif.paper.S2224BaseChangeCommutesFinalActual
import tmp.sheaf.xif.paper.S2165BaseChangeWitnessActual
import tmp.sheaf.xif.paper.S2175BaseChangePresentationActual

/-! # S2247: actual base-changed presentation square

Uses accepted S2165 apex/projections/projectionMap, S2175 toSource and S2224
commutes.  Explicit universe/typeclass binders avoid the S2231 elaboration
failure.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2247BaseChangeSquareActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)
variable (hs : AlgebraicGeometry.IsFinite s.left)
variable (hse : AlgebraicGeometry.Etale s.left)
variable (hq : AlgebraicGeometry.IsFinite (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)
variable (hqe : AlgebraicGeometry.Etale (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)

noncomputable def S2247Square : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K
      (S2165Apex (m := m) (s := s) (vy := vy) (Q := Q)))
    X.fiber
    (schemeRepresentableEtalePseudofunctor S1726K T)
    Y.fiber where
  toX := S2175ToSource (m := m) (s := s) (vy := vy) (Q := Q)
  toY := (S2165ProjectionMap (m := m) (s := s) (vy := vy) (Q := Q) hs hse hq hqe).transformation
  xToBase := m
  yToBase := Pseudofunctor.StrongTrans.vcomp (S1742StrongTransOfHom s) vy
  commutes := S2224Commutes (m := m) (s := s) (vy := vy) (Q := Q)

#check S2247Square

end LeanFormal.IUT.XiFPaper.S2247BaseChangeSquareActual

end
