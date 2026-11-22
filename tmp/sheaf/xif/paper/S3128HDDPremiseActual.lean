import tmp.sheaf.xif.paper.S1385HDDHullDetActual
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldProductHull
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.LocalFieldIntegralHull
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.LocalFieldProductHull
open LeanFormal.IUT.XiFPaper.S1385HDDHullDetActual
namespace LeanFormal.IUT.XiFPaper.S3128HDDPremiseActual

theorem S3128Stage1HDD_frozenSpec :
    HullDeterminantLogVolumeFrozenSpec.{0, 0, 0, 0, 0, 0, 0, 0, 0} :=
  s1385FrozenSpec_actual

theorem S3128Stage1HDD_integralSpan_eq_hull
    {J : Type*} [Finite J] {E : J → Type*} [∀ j, NormedField (E j)]
    (hna : ∀ j, IsNonarchimedean (Norm.norm : E j → ℝ))
    {S : Set ((j : J) → E j)} (hS : IsCompact S) (hne : S.Nonempty)
    (hcoord : ∀ j, ∃ x ∈ S, x j ≠ 0) :
    (Submodule.span (LocalFieldProductHull.integralRing hna) S :
      Set ((j : J) → E j)) = LocalFieldProductHull.hull S :=
  s1385ActualIntegralSpan_eq_hull hna hS hne hcoord

#check S3128Stage1HDD_frozenSpec
#check S3128Stage1HDD_integralSpan_eq_hull
end LeanFormal.IUT.XiFPaper.S3128HDDPremiseActual