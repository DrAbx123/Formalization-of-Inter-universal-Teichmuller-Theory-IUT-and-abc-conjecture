import tmp.sheaf.xif.paper.S2231WitnessBaseChangeActual
import tmp.sheaf.xif.paper.S1852CoherentCoverActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

/-! # S2244: step (1) cone transport, using the existing weak square of Q

Avoids defining a new Q-square (universe/elaboration issues in S2241) by using
`S1852WeakSquare Q`.  Binders are fully qualified to avoid IsFinite/Etale
resolution failures.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2244ConeTransportActualAdapted

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2058D6FiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2096StackMorphismActual
open LeanFormal.IUT.XiFPaper.S2165BaseChangeWitnessActual
open LeanFormal.IUT.XiFPaper.S2231WitnessBaseChangeActual

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

/-- Step (1): a cone over the base-changed square gives a cone over Q's
weak square. -/
noncomputable def S2244ConeOverQ {W : EtaleStackPseudofunctor S1726K}
    (c : (S2231Square (m := m) (s := s) (vy := vy) (Q := Q) hs hse hq hqe).Cone W) :
    (S1852WeakSquare Q).Cone W where
  toX := c.toX
  toY := Pseudofunctor.StrongTrans.vcomp c.toY (S1742StrongTransOfHom s)
  commutes := c.commutes.trans
    (S2058AssociatorIso c.toY (S1742StrongTransOfHom s) vy).symm

#check S2244ConeOverQ

end LeanFormal.IUT.XiFPaper.S2244ConeTransportActualAdapted

end
