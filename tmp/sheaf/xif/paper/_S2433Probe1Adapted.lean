/-
Probe S2433: build the fold cover from S1943's strong structure.
-/
import tmp.sheaf.xif.paper.S1943AssembleEssSurjActual
import tmp.sheaf.xif.paper.S2431CompositeMapIsoActual
import tmp.sheaf.xif.paper.S1850RefuteS1756Actual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S1850RefuteS1756Actual
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1897CoherentEssSurjActual
open LeanFormal.IUT.XiFPaper.S1816OrbicurveCoversToAffineActual
open LeanFormal.IUT.XiFPaper.S1943AssembleEssSurjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations

namespace LeanFormal.IUT.XiFPaper.S2433Probe

abbrev S2433T : SchemeOverField S1726K := S1726AffineOver

/-- The doubled affine base as a finite etale cover of Spec R'. -/
noncomputable def S2433FoldCover : S1816Target :=
  FiniteEtaleCover.mk (S := S1816Base) (X := (S1850P S2433T).left)
    (S1850Fold S2433T).left (S1850Fold_etale S2433T) (S1850Fold_finite S2433T)

example : (S1897CoverScheme S2433FoldCover).left = (S1850P S2433T).left := rfl

/-- The first inclusion as an object of the over-category. -/
noncomputable def S2433G0 : S2433T ⟶ S1897CoverScheme S2433FoldCover :=
  Over.homMk (Limits.coprod.inl : S2433T.left ⟶ (S1850P S2433T).left) (by
    show Limits.coprod.inl ≫ ((S1850Fold S2433T).left ≫ S2433T.hom) = S2433T.hom
    rw [← Category.assoc, S1850Fold_left, Limits.coprod.inl_desc, Category.id_comp])

example : Over.Hom.left S2433G0 = Limits.coprod.inl := rfl

theorem S2433G0_comp : S2433G0 ≫ S1897CoverOver S2433FoldCover = 𝟙 S2433T := by
  apply Over.OverMorphism.ext
  show Over.Hom.left (S2433G0 ≫ S1897CoverOver S2433FoldCover) = Over.Hom.left (𝟙 S2433T)
  rw [Over.comp_left, Over.id_left, S1897CoverOver_left]
  show Limits.coprod.inl ≫ (S1850Fold S2433T).left = 𝟙 S2433T.left
  rw [S1850Fold_left, Limits.coprod.inl_desc]

theorem S2433G0_mono : Mono S2433G0 := by
  haveI : IsSplitMono S2433G0 :=
    ⟨⟨{ retraction := S1897CoverOver S2433FoldCover, id := S2433G0_comp }⟩⟩
  inferInstance

#check S1943Strong S2433FoldCover
#check S1897ExtMap S2433FoldCover
#check S1897ExtSource S2433FoldCover
#check S1943BaseChange S2433FoldCover

noncomputable def S2433FoldStrong : StrongCover S1726Orbicurve where
  source := S1897ExtSource S2433FoldCover
  map := S1897ExtMap S2433FoldCover
  finiteEtale := S1943Strong S2433FoldCover

noncomputable def S2433FoldCoherent : CoherentCover :=
  CoherentCover.ofStrong S2433FoldStrong

example : (CoherentCover.cover S2433FoldCoherent).source.fiber
    = S1742YS (F := S1726K) (S1897CoverScheme S2433FoldCover) := rfl

example : (CoherentCover.cover S1852TerminalCoherent).source.fiber
    = S1742YS (F := S1726K) S2433T := rfl

end LeanFormal.IUT.XiFPaper.S2433Probe
end
