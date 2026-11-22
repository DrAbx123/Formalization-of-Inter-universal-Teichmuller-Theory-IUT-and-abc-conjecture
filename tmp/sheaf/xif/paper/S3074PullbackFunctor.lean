import tmp.sheaf.xif.paper.S3073TorsorPullbackActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3073TorsorPullbackActual
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S2994A6Stackification
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 0

namespace LeanFormal.IUT.XiFPaper.S3074PullbackFunctor

noncomputable abbrev S3074Map
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) {P Q : S3048SignTorsorFiber U}
    (h : S3049TorsorIso U P Q) :
    (S3073PullbackFiber f P).total ⟶ (S3073PullbackFiber f Q).total :=
  pullback.lift
    (pullback.fst (f := P.projection) (g := f.as.unop) ≫ h.hom)
    (pullback.snd (f := P.projection) (g := f.as.unop))
    (by
      calc
        (pullback.fst (f := P.projection) (g := f.as.unop) ≫ h.hom) ≫
            Q.projection
            = pullback.fst (f := P.projection) (g := f.as.unop) ≫
                (h.hom ≫ Q.projection) := by rw [Category.assoc]
        _ = pullback.fst (f := P.projection) (g := f.as.unop) ≫
              P.projection := by rw [h.comm]
        _ = pullback.snd (f := P.projection) (g := f.as.unop) ≫
              f.as.unop := pullback.condition)

noncomputable abbrev S3074MapInv
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) {P Q : S3048SignTorsorFiber U}
    (h : S3049TorsorIso U P Q) :
    (S3073PullbackFiber f Q).total ⟶ (S3073PullbackFiber f P).total :=
  haveI : IsIso h.hom := h.isIso
  pullback.lift
    (pullback.fst (f := Q.projection) (g := f.as.unop) ≫
      CategoryTheory.inv h.hom)
    (pullback.snd (f := Q.projection) (g := f.as.unop))
    (by
      haveI : IsIso h.hom := h.isIso
      have hInvComm : CategoryTheory.inv h.hom ≫ P.projection = Q.projection := by
        rw [← h.comm, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
      calc
        (pullback.fst (f := Q.projection) (g := f.as.unop) ≫
            CategoryTheory.inv h.hom) ≫ P.projection
            = pullback.fst (f := Q.projection) (g := f.as.unop) ≫
                (CategoryTheory.inv h.hom ≫ P.projection) := by
                rw [Category.assoc]
        _ = pullback.fst (f := Q.projection) (g := f.as.unop) ≫
              Q.projection := by rw [hInvComm]
        _ = pullback.snd (f := Q.projection) (g := f.as.unop) ≫
              f.as.unop := pullback.condition)

theorem S3074_map_comp_inv
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) {P Q : S3048SignTorsorFiber U}
    (h : S3049TorsorIso U P Q) :
    S3074Map f h ≫ S3074MapInv f h =
      𝟙 (S3073PullbackFiber f P).total := by
  haveI : IsIso h.hom := h.isIso
  apply pullback.hom_ext (f := P.projection) (g := f.as.unop)
  · calc
      (S3074Map f h ≫ S3074MapInv f h) ≫
          pullback.fst (f := P.projection) (g := f.as.unop)
          = S3074Map f h ≫ (S3074MapInv f h ≫
              pullback.fst (f := P.projection) (g := f.as.unop)) := by
                rw [Category.assoc]
      _ = S3074Map f h ≫ (pullback.fst (f := Q.projection) (g := f.as.unop) ≫
            CategoryTheory.inv h.hom) := by
                rw [pullback.lift_fst (f := P.projection) (g := f.as.unop)]
      _ = (S3074Map f h ≫ pullback.fst (f := Q.projection) (g := f.as.unop)) ≫
            CategoryTheory.inv h.hom := by rw [Category.assoc]
      _ = (pullback.fst (f := P.projection) (g := f.as.unop) ≫ h.hom) ≫
            CategoryTheory.inv h.hom := by
                rw [pullback.lift_fst (f := Q.projection) (g := f.as.unop)]
      _ = pullback.fst (f := P.projection) (g := f.as.unop) := by
                rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  · calc
      (S3074Map f h ≫ S3074MapInv f h) ≫
          pullback.snd (f := P.projection) (g := f.as.unop)
          = S3074Map f h ≫ (S3074MapInv f h ≫
              pullback.snd (f := P.projection) (g := f.as.unop)) := by
                rw [Category.assoc]
      _ = S3074Map f h ≫ pullback.snd (f := Q.projection) (g := f.as.unop) := by
                rw [pullback.lift_snd (f := P.projection) (g := f.as.unop)]
      _ = pullback.snd (f := P.projection) (g := f.as.unop) := by
                rw [pullback.lift_snd (f := Q.projection) (g := f.as.unop)]

theorem S3074_inv_comp_map
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) {P Q : S3048SignTorsorFiber U}
    (h : S3049TorsorIso U P Q) :
    S3074MapInv f h ≫ S3074Map f h =
      𝟙 (S3073PullbackFiber f Q).total := by
  haveI : IsIso h.hom := h.isIso
  apply pullback.hom_ext (f := Q.projection) (g := f.as.unop)
  · calc
      (S3074MapInv f h ≫ S3074Map f h) ≫
          pullback.fst (f := Q.projection) (g := f.as.unop)
          = S3074MapInv f h ≫ (S3074Map f h ≫
              pullback.fst (f := Q.projection) (g := f.as.unop)) := by
                rw [Category.assoc]
      _ = S3074MapInv f h ≫ (pullback.fst (f := P.projection) (g := f.as.unop) ≫ h.hom) := by
                rw [pullback.lift_fst (f := Q.projection) (g := f.as.unop)]
      _ = (S3074MapInv f h ≫ pullback.fst (f := P.projection) (g := f.as.unop)) ≫ h.hom := by
                rw [Category.assoc]
      _ = (pullback.fst (f := Q.projection) (g := f.as.unop) ≫
            CategoryTheory.inv h.hom) ≫ h.hom := by
                rw [pullback.lift_fst (f := P.projection) (g := f.as.unop)]
      _ = pullback.fst (f := Q.projection) (g := f.as.unop) := by
                rw [Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  · calc
      (S3074MapInv f h ≫ S3074Map f h) ≫
          pullback.snd (f := Q.projection) (g := f.as.unop)
          = S3074MapInv f h ≫ (S3074Map f h ≫
              pullback.snd (f := Q.projection) (g := f.as.unop)) := by
                rw [Category.assoc]
      _ = S3074MapInv f h ≫ pullback.snd (f := P.projection) (g := f.as.unop) := by
                rw [pullback.lift_snd (f := Q.projection) (g := f.as.unop)]
      _ = pullback.snd (f := Q.projection) (g := f.as.unop) := by
                rw [pullback.lift_snd (f := P.projection) (g := f.as.unop)]

noncomputable def S3074MapIso
    {U V : LocallyDiscrete (Iut.SchemeOverField S2994A6K)ᵒᵖ}
    (f : U ⟶ V) {P Q : S3048SignTorsorFiber U}
    (h : S3049TorsorIso U P Q) :
    S3049TorsorIso V (S3073PullbackFiber f P) (S3073PullbackFiber f Q) where
  hom := S3074Map f h
  comm := by
    simp only [S3074Map, S3073PullbackProjection, pullback.lift_snd]
  equivariant := by
    intro g
    apply pullback.hom_ext (f := Q.projection) (g := f.as.unop)
    · change (S3074Map f h ≫ S3073PullbackAction f Q g) ≫
        pullback.fst (f := Q.projection) (g := f.as.unop) =
      (S3073PullbackAction f P g ≫ S3074Map f h) ≫
        pullback.fst (f := Q.projection) (g := f.as.unop)
      calc
        (S3074Map f h ≫ S3073PullbackAction f Q g) ≫
            pullback.fst (f := Q.projection) (g := f.as.unop)
            = S3074Map f h ≫ (S3073PullbackAction f Q g ≫
                pullback.fst (f := Q.projection) (g := f.as.unop)) := by
                  rw [Category.assoc]
        _ = S3074Map f h ≫ (pullback.fst (f := Q.projection) (g := f.as.unop) ≫
              Q.action g) := by
                  rw [S3073PullbackAction,
                    pullback.lift_fst (f := Q.projection) (g := f.as.unop)]
        _ = (S3074Map f h ≫ pullback.fst (f := Q.projection) (g := f.as.unop)) ≫
              Q.action g := by rw [Category.assoc]
        _ = (pullback.fst (f := P.projection) (g := f.as.unop) ≫ h.hom) ≫
              Q.action g := by
                  rw [S3074Map, pullback.lift_fst (f := Q.projection) (g := f.as.unop)]
        _ = pullback.fst (f := P.projection) (g := f.as.unop) ≫
              (h.hom ≫ Q.action g) := by rw [Category.assoc]
        _ = pullback.fst (f := P.projection) (g := f.as.unop) ≫
              (P.action g ≫ h.hom) := by rw [h.equivariant g]
        _ = (pullback.fst (f := P.projection) (g := f.as.unop) ≫ P.action g) ≫
              h.hom := by rw [Category.assoc]
        _ = (S3073PullbackAction f P g ≫
              pullback.fst (f := P.projection) (g := f.as.unop)) ≫ h.hom := by
                  rw [S3073PullbackAction,
                    pullback.lift_fst (f := P.projection) (g := f.as.unop)]
        _ = (S3073PullbackAction f P g ≫ S3074Map f h) ≫
              pullback.fst (f := Q.projection) (g := f.as.unop) := by
                  conv_rhs =>
                    rw [Category.assoc, pullback.lift_fst (f := Q.projection) (g := f.as.unop)]
                  rw [Category.assoc]
    · change (S3074Map f h ≫ S3073PullbackAction f Q g) ≫
        pullback.snd (f := Q.projection) (g := f.as.unop) =
      (S3073PullbackAction f P g ≫ S3074Map f h) ≫
        pullback.snd (f := Q.projection) (g := f.as.unop)
      calc
        (S3074Map f h ≫ S3073PullbackAction f Q g) ≫
            pullback.snd (f := Q.projection) (g := f.as.unop)
            = S3074Map f h ≫ (S3073PullbackAction f Q g ≫
                pullback.snd (f := Q.projection) (g := f.as.unop)) := by
                  rw [Category.assoc]
        _ = S3074Map f h ≫ pullback.snd (f := Q.projection) (g := f.as.unop) := by
                  rw [S3073PullbackAction,
                    pullback.lift_snd (f := Q.projection) (g := f.as.unop)]
        _ = pullback.snd (f := P.projection) (g := f.as.unop) := by
                  rw [S3074Map, pullback.lift_snd (f := Q.projection) (g := f.as.unop)]
        _ = S3073PullbackAction f P g ≫
              pullback.snd (f := P.projection) (g := f.as.unop) := by
                  rw [S3073PullbackAction,
                    pullback.lift_snd (f := P.projection) (g := f.as.unop)]
        _ = (S3073PullbackAction f P g ≫ S3074Map f h) ≫
              pullback.snd (f := Q.projection) (g := f.as.unop) := by
                  conv_rhs =>
                    rw [Category.assoc, pullback.lift_snd (f := Q.projection) (g := f.as.unop)]
  isIso := ⟨S3074MapInv f h, S3074_map_comp_inv f h, S3074_inv_comp_map f h⟩

#check S3074Map
#check S3074MapInv
#check S3074_map_comp_inv
#check S3074_inv_comp_map
#check S3074MapIso

end LeanFormal.IUT.XiFPaper.S3074PullbackFunctor
end
