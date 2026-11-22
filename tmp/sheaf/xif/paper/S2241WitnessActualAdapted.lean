import tmp.sheaf.xif.paper.S2231WitnessBaseChangeActual

/-! # S2241: step (1) of the witness transport -- cone over Q's square

From a cone over the base-changed square, build a cone over Q's square using
`S2224Commutes`-compatible legs.  Steps (2)/(3) (lift to the base-changed apex
and 2-cell coherence) remain missing and are recorded as such.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2241WitnessActualAdapted

open CategoryTheory
open AlgebraicGeometry
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2175BaseChangePresentationActual
open LeanFormal.IUT.XiFPaper.S2224BaseChangeCommutesFinalActual
open LeanFormal.IUT.XiFPaper.S2231WitnessBaseChangeActual

universe u

variable {X Y : EtaleStackOverField S1726K} (m : X.Hom Y)
variable {A T : SchemeOverField S1726K} (s : T ⟶ A)
variable (vy : Pseudofunctor.StrongTrans
  (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber)
variable (Q : EtaleStackBaseChangePresentation m A vy)
variable (hs : IsFinite s.left) (hse : Etale s.left)
variable (hq : IsFinite (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)
variable (hqe : Etale (S2165Snd (m := m) (s := s) (vy := vy) (Q := Q)).left)

/-- Q's own presentation square. -/
noncomputable def S2241QSquare : EtalePseudofunctorSquare
    (schemeRepresentableEtalePseudofunctor S1726K Q.pullbackScheme) X.fiber
    (schemeRepresentableEtalePseudofunctor S1726K A) Y.fiber where
  toX := Q.toSource
  toY := Q.projectionMap.transformation
  xToBase := m
  yToBase := vy
  commutes := Q.commutes

/-- Step (1): a cone over the base-changed square gives a cone over Q. -/
noncomputable def S2241ConeOverQ {W : EtaleStackPseudofunctor S1726K}
    (c : (S2231Square (m := m) (s := s) (vy := vy) (Q := Q) hs hse hq hqe).Cone W) :
    (S2241QSquare (m := m) (s := s) (vy := vy) (Q := Q)).Cone W where
  toX := c.toX
  toY := Pseudofunctor.StrongTrans.vcomp c.toY (S1742StrongTransOfHom s)
  commutes := c.commutes.trans
    (S2058AssociatorIso c.toY (S1742StrongTransOfHom s) vy).symm

#check S2241QSquare
#check S2241ConeOverQ

end LeanFormal.IUT.XiFPaper.S2241WitnessActualAdapted

end
