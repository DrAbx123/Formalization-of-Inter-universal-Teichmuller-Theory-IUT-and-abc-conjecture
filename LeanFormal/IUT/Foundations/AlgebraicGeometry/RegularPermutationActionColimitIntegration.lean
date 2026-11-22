import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationCoconeUniqueness
import LeanFormal.IUT.Foundations.AlgebraicGeometry.RegularPermutationQuotientConsumer
import Mathlib.Tactic

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open LeanFormal.IUT.Foundations.AlgebraicGeometry.AffineLocalQuotientGluingConstruct
open AffineLocalQuotientGluingConstruct

noncomputable section

namespace ABCBridge.RegularPermutationQuotientDataUnconditional

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G] [Fintype G]

/-- The actual regular-permutation quotient data, unconditional. -/
noncomputable def regularPermutationQuotientDataUnconditional :
    ABCBridge.RegularPermutationQuotientConsumer.RegularPermutationQuotientData R G :=
  ABCBridge.RegularPermutationQuotientConsumer.regularPermutationQuotientData
    (R := R) (G := G)
    (RegularPermutationCoconeUniqueness.regularPermutationCocone_isColimit R G)

/-- The actual regular-permutation action functor has a colimit, unconditional. -/
noncomputable def regularPermutationHasColimitUnconditional :
    HasColimit (regularPermutationActionFunctor R G) :=
  ABCBridge.RegularPermutationQuotientConsumer.regularPermutationHasColimit
    (R := R) (G := G)
    (RegularPermutationCoconeUniqueness.regularPermutationCocone_isColimit R G)

end ABCBridge.RegularPermutationQuotientDataUnconditional
