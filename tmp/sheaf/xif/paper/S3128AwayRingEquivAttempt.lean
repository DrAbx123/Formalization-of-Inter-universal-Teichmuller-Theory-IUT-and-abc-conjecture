import tmp.sheaf.xif.paper.S3128AwayEquivAttempt

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.S3128AwayRingEquivAttempt

open LeanFormal.IUT.XiFPaper.S3128AwayActionActual
open LeanFormal.IUT.XiFPaper.S3128AwayEquivAttempt

variable {G : Type} [Group G]
variable {A : Type} [CommRing A] [MulSemiringAction G A]

/-- phi_g is injective. -/
theorem S3128AwayMap_injective (f : A) (hf : forall g : G, g • f = f) (g : G) :
    Function.Injective (S3128AwayMap f hf g) := by
  apply Function.LeftInverse.injective
  intro x
  have h := congrArg (fun q : Localization.Away f →+* Localization.Away f => q x)
    (S3128AwayMap_inv_comp f hf g)
  simpa using h

/-- phi_g is surjective. -/
theorem S3128AwayMap_surjective (f : A) (hf : forall g : G, g • f = f) (g : G) :
    Function.Surjective (S3128AwayMap f hf g) := by
  apply Function.RightInverse.surjective
  intro x
  have h := congrArg (fun q : Localization.Away f →+* Localization.Away f => q x)
    (S3128AwayMap_comp_inv f hf g)
  simpa using h

/-- Ring automorphism of A_f induced by g. -/
noncomputable def S3128AwayEquiv (f : A) (hf : forall g : G, g • f = f)
    (g : G) : Localization.Away f ≃+* Localization.Away f :=
  RingEquiv.ofBijective (S3128AwayMap f hf g)
    ⟨S3128AwayMap_injective f hf g, S3128AwayMap_surjective f hf g⟩

#check S3128AwayEquiv

end LeanFormal.IUT.XiFPaper.S3128AwayRingEquivAttempt
end