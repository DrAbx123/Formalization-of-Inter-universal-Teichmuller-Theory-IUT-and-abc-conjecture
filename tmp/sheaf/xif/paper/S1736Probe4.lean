import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import Mathlib.CategoryTheory.Galois.Basic
import Mathlib.CategoryTheory.Limits.Shapes.Equivalence
import Mathlib.CategoryTheory.Adjunction.Limits
import Mathlib.CategoryTheory.Functor.EpiMono
import Mathlib.CategoryTheory.EssentialImage

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1736Probe4

open CategoryTheory
open CategoryTheory.Limits
open Iut
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open scoped Pseudofunctor.StrongTrans

universe u

variable {F : Type u} [Field F] {X : HyperbolicOrbicurve F}

abbrev ActualCat : Category.{u+1,u+1} (OrbicurveFiniteEtaleCover X) :=
  S1728CoverCategory11 (F := F) (X := X)

def terminalCover
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber)) :
    OrbicurveFiniteEtaleCover X where
  source := X.stack
  map := Pseudofunctor.StrongTrans.id X.stack.fiber
  finiteEtale := h

noncomputable def terminalCoverMap
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (A : OrbicurveFiniteEtaleCover X) :
    OrbicurveFiniteEtaleCoverMap A (terminalCover h) := by
  let Bicat := EtaleStackPseudofunctor F
  letI : Bicategory Bicat := inferInstance
  exact
    { map := A.map
      commutes := @Bicategory.rightUnitor Bicat _ A.source.fiber X.stack.fiber A.map }

noncomputable def terminalMorphism
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (A : OrbicurveFiniteEtaleCover X) :
    @Quiver.Hom _ (ActualCat (F := F) (X := X)).toQuiver A (terminalCover h) :=
  Quot.mk _ (terminalCoverMap h A)

theorem terminalMorphism_unique
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber))
    (A : OrbicurveFiniteEtaleCover X)
    (f : @Quiver.Hom _ (ActualCat (F := F) (X := X)).toQuiver A (terminalCover h)) :
    f = terminalMorphism h A := by
  induction f using Quot.inductionOn with
  | h f =>
      change Quot.mk _ f = Quot.mk _ (terminalCoverMap h A)
      apply Quot.sound
      exact ⟨(S1728RightUnitorIso f).symm ≪≫ f.commutes⟩

def terminalCover_isTerminal
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber)) :
    @IsTerminal _ (ActualCat (F := F) (X := X)) (terminalCover h) :=
  IsTerminal.ofUniqueHom (fun A => terminalMorphism h A)
    (fun A f => terminalMorphism_unique h A f)

theorem hasTerminal_of_identity_finiteEtale
    (h : EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.id X.stack.fiber)) :
    @HasTerminal _ (ActualCat (F := F) (X := X)) :=
  (terminalCover_isTerminal h).hasTerminal

end LeanFormal.IUT.XiFPaper.S1736Probe4
