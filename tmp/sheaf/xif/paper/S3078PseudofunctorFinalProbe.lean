import tmp.sheaf.xif.paper.S3078QPrimePseudofunctorTarget
import tmp.sheaf.xif.paper.S3078MapCompNatIsoActual
noncomputable section
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3078QPrimePseudofunctorTarget
open LeanFormal.IUT.XiFPaper.S3078MapCompNatIsoActual
namespace LeanFormal.IUT.XiFPaper.S3078PseudofunctorFinalProbe
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

noncomputable def S3078MapComp
    {U V W : CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)}
    (f : U ⟶ V) (g : V ⟶ W) :
    S3078PrelaxFunctor.map (f ≫ g) ≅
      S3078PrelaxFunctor.map f ≫ S3078PrelaxFunctor.map g :=
  Cat.Hom.isoMk (S3078MapCompNatIso f g)


noncomputable def S3078Pseudofunctor :
    Pseudofunctor (CategoryTheory.LocallyDiscrete (S3078Kᵒᵖ)) Cat.{0, 1} :=
  Pseudofunctor.mk S3078PrelaxFunctor S3078MapId S3078MapComp
    (by
      intro a b c f g h eta
      ext
      simp [S3078PrelaxFunctor, S3078MapComp])
    (by
      intro a b c f g h eta
      ext
      simp [S3078PrelaxFunctor, S3078MapComp])
    (by
      intro a b c d f g h
      ext
      simp [S3078PrelaxFunctor, S3078MapComp])
    (by
      intro a b f
      ext x
      apply S3049TorsorIso.ext
      apply pullback.hom_ext
        (f := (S3073PullbackFiber (𝟙 a) x).projection) (g := f.as.unop)
      · simp [S3078PrelaxFunctor, S3078MapComp, S3078MapId,
          S3076MapId, S3074MapIso, S3074Map, S3073PullbackAction,
          pullback.lift_fst, pullback.lift_snd, Category.assoc]
      · simp [S3078PrelaxFunctor, S3078MapComp, S3078MapId,
          S3076MapId, S3074MapIso, S3074Map, S3073PullbackAction,
          pullback.lift_fst, pullback.lift_snd, Category.assoc])
    (by
      intro a b f
      ext x
      apply S3049TorsorIso.ext
      apply pullback.hom_ext
        (f := (S3073PullbackFiber (𝟙 a) x).projection) (g := f.as.unop)
      · simp [S3078PrelaxFunctor, S3078MapComp, S3078MapId,
          S3076MapId, S3074MapIso, S3074Map, S3073PullbackAction,
          pullback.lift_fst, pullback.lift_snd, Category.assoc]
      · simp [S3078PrelaxFunctor, S3078MapComp, S3078MapId,
          S3076MapId, S3074MapIso, S3074Map, S3073PullbackAction,
          pullback.lift_fst, pullback.lift_snd, Category.assoc])

#check S3078Pseudofunctor

#check S3078MapComp
end LeanFormal.IUT.XiFPaper.S3078PseudofunctorFinalProbe
end
