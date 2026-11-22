import tmp.sheaf.xif.paper.S3128AwayActionActual
import Mathlib.RingTheory.Localization.Away.Basic

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128AwayEquivAttempt

open LeanFormal.IUT.XiFPaper.S3128AwayActionActual

variable {G : Type} [Group G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- phi_g on algebraMap. -/
theorem S3128AwayMap_algebraMap (f : A) (hf : forall g : G, g • f = f)
    (g : G) (a : A) :
    S3128AwayMap f hf g (algebraMap A (Localization.Away f) a) =
      algebraMap A (Localization.Away f) (g • a) := by
  unfold S3128AwayMap
  exact IsLocalization.lift_eq _ a

/-- phi_g is inverse to phi_{g⁻¹}. -/
theorem S3128AwayMap_comp_inv (f : A) (hf : forall g : G, g • f = f) (g : G) :
    (S3128AwayMap f hf g).comp (S3128AwayMap f hf g⁻¹) =
      RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [S3128AwayMap_algebraMap, S3128AwayMap_algebraMap, smul_smul]
  simp

/-- phi_g is inverse to phi_{g⁻¹}, other direction. -/
theorem S3128AwayMap_inv_comp (f : A) (hf : forall g : G, g • f = f) (g : G) :
    (S3128AwayMap f hf g⁻¹).comp (S3128AwayMap f hf g) =
      RingHom.id (Localization.Away f) := by
  apply IsLocalization.ringHom_ext (Submonoid.powers f)
  ext a
  simp only [RingHom.comp_apply, RingHom.id_apply]
  rw [S3128AwayMap_algebraMap, S3128AwayMap_algebraMap, smul_smul]
  simp

#check S3128AwayMap_comp_inv
#check S3128AwayMap_inv_comp

end LeanFormal.IUT.XiFPaper.S3128AwayEquivAttempt
end