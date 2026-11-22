import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S1987D5LargeImageFiveActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual

open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2186PairBijectiveActual
open LeanFormal.IUT.XiFPaper.S2172AffineBasisLiftActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual

/-- The actual basis-compatible pair equivalence. -/
noncomputable def S2218PairEquiv : S2009Pairs ≃ S2056Pair :=
  (S2186BasisCompatiblePairEquiv S2172AffineBasis).pairEquiv

/-- The transported action of `GL_2(F_5)` on actual affine pairs. -/
noncomputable def S2218PairPerm (g : GL2) : Equiv.Perm S2056Pair :=
  S2218PairEquiv.permCongr (pairPermHom g)

/-- On an equivalence orbit, the transported permutation is the
basis-compatible pair map. -/
theorem S2218PairPerm_apply (g : GL2) (x : S2009Pairs) :
    S2218PairPerm g (S2218PairEquiv x) =
      S2218PairEquiv (pairAct g x) := by
  simp [S2218PairPerm, Equiv.permCongr_apply, pairPermHom, pairEquiv]

/-- Affine-pair transitivity of a subgroup, under the transported action. -/
def S2218AffinePairTransitive (H : Subgroup GL2) : Prop :=
  ∀ x y : S2056Pair, ∃ g ∈ H, S2218PairPerm g x = y

/-- Actual transport: affine-pair transitivity is equivalent to the S2009
finite pair transitivity. -/
theorem S2218AffinePairTransitive_iff (H : Subgroup GL2) :
    S2218AffinePairTransitive H ↔ PairTransitive H := by
  constructor
  · intro h x y
    obtain ⟨g, hg, hgxy⟩ := h (S2218PairEquiv x) (S2218PairEquiv y)
    refine ⟨g, hg, ?_⟩
    apply S2218PairEquiv.injective
    calc
      S2218PairEquiv (pairAct g x) = S2218PairPerm g (S2218PairEquiv x) :=
        (S2218PairPerm_apply g x).symm
      _ = S2218PairEquiv y := hgxy
  · intro h x y
    obtain ⟨g, hg, hgxy⟩ := h (S2218PairEquiv.symm x) (S2218PairEquiv.symm y)
    refine ⟨g, hg, ?_⟩
    have h := congrArg S2218PairEquiv hgxy
    simpa [S2218PairPerm, Equiv.permCongr_apply, pairPermHom, pairEquiv] using h

/-- Exact first missing: affine-pair transitivity of the actual mod-5 range at
a basis. -/
def S2218RangeAffinePairTransitiveRequired
    (b : S1725TorsionBasis S1987Five) : Prop :=
  S2218AffinePairTransitive
    (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range

/-- Exact equivalence with the S2203 finite pair-transitivity hypothesis. -/
theorem S2218RangeAffinePairTransitiveRequired_iff
    (b : S1725TorsionBasis S1987Five) :
    S2218RangeAffinePairTransitiveRequired b ↔
      S2203RangePairTransitiveRequired b := by
  unfold S2218RangeAffinePairTransitiveRequired
    S2203RangePairTransitiveRequired
  exact S2218AffinePairTransitive_iff _

end LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual

end
