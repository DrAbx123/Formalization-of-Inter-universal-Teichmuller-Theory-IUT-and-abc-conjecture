import tmp.sheaf.xif.paper.S3128AwayRingEquivAttempt

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt

open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayEquivAttempt
open LeanFormal.IUT.XiFPaper.S3128AwayRingEquivAttempt

variable {G : Type} [Group G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

theorem S3128AwayMap_one (f : A) (hf : forall g : G, g • f = f) :
    S3128AwayMap f hf 1 = RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [S3128AwayMap_algebraMap]
  simp

theorem S3128AwayMap_mul (f : A) (hf : forall g : G, g • f = f) (g h : G) :
    S3128AwayMap f hf (g * h) =
      (S3128AwayMap f hf g).comp (S3128AwayMap f hf h) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply]
  rw [S3128AwayMap_algebraMap, S3128AwayMap_algebraMap, S3128AwayMap_algebraMap]
  rw [smul_smul]


/-- The monoid hom G →* Aut(A_f). -/
noncomputable def S3128AwayActionHom (f : A) (hf : forall g : G, g • f = f) :
    G →* (Localization.Away f ≃+* Localization.Away f) where
  toFun g := S3128AwayEquiv f hf g
  map_one' := by
    apply RingEquiv.ext
    intro x
    change S3128AwayMap f hf 1 x = x
    rw [S3128AwayMap_one]
    rfl
  map_mul' g h := by
    apply RingEquiv.ext
    intro x
    change S3128AwayMap f hf (g * h) x =
      S3128AwayMap f hf g (S3128AwayMap f hf h x)
    rw [S3128AwayMap_mul]
    rfl

#check S3128AwayActionHom


/-- The induced MulSemiringAction on A_f. -/
noncomputable def S3128AwayMulSemiringAction (f : A)
    (hf : forall g : G, g • f = f) :
    MulSemiringAction G (Localization.Away f) where
  smul g x := S3128AwayEquiv f hf g x
  one_smul x := by
    change S3128AwayMap f hf 1 x = x
    rw [S3128AwayMap_one]
    rfl
  mul_smul g h x := by
    change S3128AwayMap f hf (g * h) x =
      S3128AwayMap f hf g (S3128AwayMap f hf h x)
    rw [S3128AwayMap_mul]
    rfl
  smul_zero g := map_zero (S3128AwayMap f hf g)
  smul_add g x y := map_add (S3128AwayMap f hf g) x y
  smul_one g := map_one (S3128AwayMap f hf g)
  smul_mul g x y := map_mul (S3128AwayMap f hf g) x y


/-- Equivariance of the action on A_f. -/
theorem S3128Away_smul_algebraMap (f : A) (hf : forall g : G, g • f = f)
    (g : G) (a : A) :
    letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
    g • algebraMap A (Localization.Away f) a =
      algebraMap A (Localization.Away f) (g • a) := by
  letI := S3128AwayMulSemiringAction (G := G) (A := A) f hf
  change S3128AwayMap f hf g (algebraMap A (Localization.Away f) a) =
    algebraMap A (Localization.Away f) (g • a)
  exact S3128AwayMap_algebraMap f hf g a

#check S3128Away_smul_algebraMap

#check S3128AwayMulSemiringAction

#check S3128AwayMap_one
#check S3128AwayMap_mul

end LeanFormal.IUT.XiFPaper.S3128AwayActionHomAttempt
end