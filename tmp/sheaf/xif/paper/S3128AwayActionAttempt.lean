import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.Algebra.Ring.Action.Group
open scoped BigOperators

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S3128AwayActionAttempt

variable {G : Type} [Group G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- Ring endomorphism of A_f induced by an invariant f and g : G. -/
noncomputable def S3128AwayMap (f : A) (hf : forall g : G, g • f = f) (g : G) :
    Localization.Away f →+* Localization.Away f :=
  IsLocalization.lift (M := Submonoid.powers f)
    (g := (algebraMap A (Localization.Away f)).comp
      (MulSemiringAction.toRingHom G A g)) (by
        intro y
        obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff y.val f).mp y.property
        rw [← hn]
        change IsUnit ((algebraMap A (Localization.Away f))
          ((MulSemiringAction.toRingHom G A g) (f ^ n)))
        rw [map_pow]
        change IsUnit ((algebraMap A (Localization.Away f))
          (((MulSemiringAction.toRingHom G A g) f) ^ n))
        rw [show (MulSemiringAction.toRingHom G A g) f = f from hf g]
        rw [map_pow]
        exact (IsLocalization.Away.algebraMap_isUnit (R := A) (S := Localization.Away f) f).pow n)

#check S3128AwayMap

end LeanFormal.IUT.XiFPaper.S3128AwayActionAttempt
end