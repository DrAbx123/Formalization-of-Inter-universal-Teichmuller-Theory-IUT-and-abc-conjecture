import Mathlib.RingTheory.Etale.Finite
#check AlgEquiv.commutes
#check Module.Finite.isArtinian
#check IsArtinianRing.of_finite
#check isArtinian_of_finite
#check Module.Finite.isArtinian
#check Algebra.FormallyUnramified.finite_of_free
example (K : Type) [Field K] (A : Type) [CommRing A] [Algebra K A] [Module.Finite K A] :
    IsArtinianRing A := by
  haveI : IsArtinian K A := inferInstance
  exact isArtinian_of_tower K inferInstance
