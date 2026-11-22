import tmp.sheaf.xif.paper.S1385HDDHullDetActual
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128Stage1HDDCompositionConsumerActual

theorem S3128Stage1HDDComposition_frozen :
    HullDeterminantLogVolumeFrozenSpec :=
  s1385FrozenSpec_actual

theorem S3128Stage1HDDComposition_integralSpan_eq_hull
    {J : Type*} [Finite J] {E : J → Type*} [∀ j, NormedField (E j)]
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    {S : Set ((j : J) → E j)} (hS : IsCompact S) (hne : S.Nonempty)
    (hcoord : ∀ j, ∃ x ∈ S, x j ≠ 0) :
    (Submodule.span (LocalFieldProductHull.integralRing hna) S :
      Set ((j : J) → E j)) = LocalFieldProductHull.hull S :=
  s1385ActualIntegralSpan_eq_hull hna hS hne hcoord

#check S3128Stage1HDDComposition_frozen
#check S3128Stage1HDDComposition_integralSpan_eq_hull
end LeanFormal.IUT.XiFPaper.S3128Stage1HDDCompositionConsumerActual