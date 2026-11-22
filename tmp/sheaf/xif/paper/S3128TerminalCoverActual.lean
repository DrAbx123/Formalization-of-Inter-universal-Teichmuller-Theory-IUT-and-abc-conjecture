import tmp.sheaf.xif.paper.S3127CoverMorphismActual
import Mathlib.CategoryTheory.Limits.Shapes.Terminal
import tmp.sheaf.xif.paper.S1742HomVcompActual
import tmp.sheaf.xif.paper.S1896BoundaryCuspActual
import tmp.sheaf.xif.paper.S1536SourceSignQuotientFromOrbicurveActual
import tmp.sheaf.xif.paper.S3121StrongTransVcompActual
import tmp.sheaf.xif.paper.S1742TwoYonedaActual

noncomputable section
open CategoryTheory CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.RepresentableCoverChosenCategoryActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S1896BoundaryCuspActual
open LeanFormal.IUT.XiFPaper.S1536SourceSignQuotientFromOrbicurveActual
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1348D6OrbicurveActual
open LeanFormal.IUT.XiFPaper.S1419D6NonterminalStackActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S3121StrongTransVcompActual
open LeanFormal.IUT.XiFPaper.S3127CoverMorphismActual
open LeanFormal.IUT.XiFPaper.S3119StrongTransEqActual
open LeanFormal.IUT.XiFPaper.S1742HomVcompActual
open CategoryTheory.Limits
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S3128TerminalCoverActual

variable {l : PrimeGeFive}

/-- The identity morphism of an etale stack is representably finite etale. -/
noncomputable def S3128IdentityFiniteEtale (Y : EtaleStackOverField (S1348K l)) :
    EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.id Y.fiber) where
  baseChange T point := S1896IdentityBaseChange Y T point
  hasProperty T point := by
    change AlgebraicGeometry.IsFinite
        (S1896IdentityBaseChange Y T point).projection.left ∧
      AlgebraicGeometry.Etale
        (S1896IdentityBaseChange Y T point).projection.left
    rw [show (S1896IdentityBaseChange Y T point).projection = 𝟙 T from rfl]
    change AlgebraicGeometry.IsFinite (𝟙 T.left) ∧
      AlgebraicGeometry.Etale (𝟙 T.left)
    constructor <;> infer_instance


/-- Identity finite-etale for the terminal cover, with source S3127Source and
target S1536XF.stack; their fibers are definitionally the same representable
pseudofunctor. -/
noncomputable def S3128TerminalFiniteEtale :
    EtaleStackFiniteEtaleMorphism
      (source := S3127Source (l := l) (S1419AffineOver (l := l)))
      (target := (S1536XF (l := l)).stack)
      (Pseudofunctor.StrongTrans.id
        (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))) where
  baseChange T point := S1896IdentityBaseChange (S1536XF (l := l)).stack T point
  hasProperty T point := by
    change AlgebraicGeometry.IsFinite
      (S1896IdentityBaseChange (S1536XF (l := l)).stack T point).projection.left ∧
      AlgebraicGeometry.Etale
      (S1896IdentityBaseChange (S1536XF (l := l)).stack T point).projection.left
    rw [show (S1896IdentityBaseChange (S1536XF (l := l)).stack T point).projection =
      𝟙 T from rfl]
    change AlgebraicGeometry.IsFinite (𝟙 T.left) ∧
      AlgebraicGeometry.Etale (𝟙 T.left)
    constructor <;> infer_instance

/-- The terminal cover: identity cover of S1536XF. -/
noncomputable abbrev S3128TerminalCover : S3127Cover (l := l) where
  scheme := S1419AffineOver (l := l)
  map := Pseudofunctor.StrongTrans.id
    (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))
  finiteEtale := by
    let f : S1419AffineOver (l := l) ⟶ S1419AffineOver (l := l) := 𝟙 _
    have hmap : S1742HomOfStrongTrans (F := S1348K l)
        (Pseudofunctor.StrongTrans.id
          (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))) = f := by
      rw [← S3121StrongTransOfHom_id (F := S1348K l)
        (S1419AffineOver (l := l))]
      exact S1742HomOfStrongTrans_strongTransOfHom (F := S1348K l) f
    rw [hmap]
    exact ⟨inferInstance, inferInstance⟩



/-- The chosen representable source stack of the terminal cover is literally the
S1536XF stack. -/
theorem S3128hStack :
    S3127Source (l := l) (S1419AffineOver (l := l)) =
      (S1536XF (l := l)).stack := rfl

/-- The identity map of the terminal cover, with explicit source/target. -/
noncomputable def S3128TerminalMap :
    (S3127Source (l := l) (S1419AffineOver (l := l))).Hom
      (S1536XF (l := l)).stack :=
  Pseudofunctor.StrongTrans.id
    (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))





/-- H of the identity strong transformation is the identity scheme morphism. -/
theorem S3128HomOfStrongTrans_id (S : SchemeOverField (S1348K l)) :
    S1742HomOfStrongTrans (F := S1348K l)
      (Pseudofunctor.StrongTrans.id (S1742YS (F := S1348K l) S)) = 𝟙 S := by
  rw [← S3121StrongTransOfHom_id (F := S1348K l) S]
  exact S1742HomOfStrongTrans_strongTransOfHom (F := S1348K l) (𝟙 S)


/-- The canonical map from an arbitrary cover to the terminal cover. -/
noncomputable def S3128TerminalHom (A : S3127Cover (l := l)) :
    S3127RepMap A (S3128TerminalCover (l := l)) where
  hom := S1742HomOfStrongTrans (F := S1348K l) A.map
  commutes := by
    let tmap : Pseudofunctor.StrongTrans (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))
        (S1536XF (l := l)).stack.fiber :=
      Pseudofunctor.StrongTrans.id (S1742YS (F := S1348K l) (S1419AffineOver (l := l)))
    let e : Iso (S1742StrongTransOfHom (F := S1348K l)
        (S1742HomOfStrongTrans (F := S1348K l) A.map)) A.map :=
      S1742StrongTransIsoOfHom (F := S1348K l) A.map
    exact ⟨(Bicategory.whiskerRightIso
      (a := S1742YS (F := S1348K l) A.scheme)
      (b := S1742YS (F := S1348K l) (S1419AffineOver (l := l)))
      (c := (S1536XF (l := l)).stack.fiber) e tmap).trans
        (Pseudofunctor.StrongTrans.rightUnitor A.map)⟩

/-- Uniqueness of the map to the terminal cover. -/
theorem S3128TerminalHom_unique (A : S3127Cover (l := l))
    (f : S3127RepMap A (S3128TerminalCover (l := l))) :
    f = S3128TerminalHom (l := l) A := by
  apply S3127RepMap_ext
  have hf' : Iso (Pseudofunctor.StrongTrans.vcomp
      (S1742StrongTransOfHom (F := S1348K l) f.hom)
      (Pseudofunctor.StrongTrans.id
        (S1742YS (F := S1348K l) (S1419AffineOver (l := l))))) A.map :=
    f.commutes.some
  have hcongr := S1742HomOfStrongTrans_congr (F := S1348K l) hf'
  rw [S1742HomOfStrongTrans_vcomp] at hcongr
  rw [S1742HomOfStrongTrans_strongTransOfHom,
    S3128HomOfStrongTrans_id (l := l) (S := S1419AffineOver (l := l)),
    Category.comp_id] at hcongr
  simpa [S3128TerminalHom] using hcongr

/-- The terminal cover is terminal. -/
noncomputable def S3128Terminal_isTerminal :
    IsTerminal (S3128TerminalCover (l := l)) :=
  IsTerminal.ofUniqueHom (fun A => S3128TerminalHom (l := l) A)
    (fun A f => S3128TerminalHom_unique (l := l) A f)



/-- The chosen-scheme category has a terminal object. -/
noncomputable def S3128HasTerminal : HasTerminal (S3127Cover (l := l)) :=
  S3128Terminal_isTerminal (l := l) |>.hasTerminal


/-- Target: a terminal cover object in the chosen-scheme category. -/
def S3128TerminalCoverTarget : Prop :=
  Nonempty (S3127Cover (l := l))

/-- The terminal cover target is inhabited. -/
theorem S3128TerminalCoverTarget_proof :
    S3128TerminalCoverTarget (l := l) :=
  ⟨S3128TerminalCover (l := l)⟩

#check S3128IdentityFiniteEtale
#check S3128TerminalFiniteEtale
#check S3128hStack
#check S3128TerminalMap
#check S3128TerminalCover
#check S3128TerminalHom
#check S3128TerminalHom_unique
#check S3128Terminal_isTerminal
#check S3128HasTerminal
#check S3128TerminalCoverTarget
#check S3128TerminalCoverTarget_proof

end LeanFormal.IUT.XiFPaper.S3128TerminalCoverActual
end