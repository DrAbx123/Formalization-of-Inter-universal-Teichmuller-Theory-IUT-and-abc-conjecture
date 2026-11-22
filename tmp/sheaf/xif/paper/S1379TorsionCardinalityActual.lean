import tmp.sheaf.xif.paper.S1362PrePsiSeparabilityActual
/-! # S1379: l-torsion cardinality from the group-law criterion and separability
Route: criterion (S1329) + separability of prePsi_l give the exact root count
(S1362), and the criterion identifies that root count with Nat.card E[l] = l^2.
The two inputs are exact; no zero/x-coordinate criterion is re-proved here. -/
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
namespace LeanFormal.IUT.XiFPaper.S1379TorsionCardinalityActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1298TorsionClauseActual
open LeanFormal.IUT.XiFPaper.S1329RankTwoTorsionBasisActual
open LeanFormal.IUT.XiFPaper.S1362PrePsiSeparabilityActual
universe u
variable {l : PrimeGeFive}
theorem s1379NatCard_eq_sq_of_criterion_and_separable
    (hcrit : S1329ConcreteCriterion l)
    (hsep : S1362PreΨSeparable l) :
    Nat.card (S1298TorsionCarrier l) = l.value ^ 2 :=
  (s1362RootCount_iff_natCard_of_criterion l hcrit).mp
    ((s1362RootCount_iff_separable l).mpr hsep)
theorem s1379TorsionCardinalityCard_of_criterion_and_separable
    (hcrit : S1329ConcreteCriterion l)
    (hsep : S1362PreΨSeparable l) :
    S1298TorsionCardinalityCard l :=
  ⟨s1329Finite_of_natCard
      (l := l) (s1379NatCard_eq_sq_of_criterion_and_separable hcrit hsep),
    s1379NatCard_eq_sq_of_criterion_and_separable hcrit hsep⟩
theorem s1379TorsionBasis_of_criterion_and_separable
    (hcrit : S1329ConcreteCriterion l)
    (hsep : S1362PreΨSeparable l) :
    Nonempty (S1298TorsionBasisType l) :=
  s1298TorsionBasisType_of_cardinalityCard l
    (s1379TorsionCardinalityCard_of_criterion_and_separable hcrit hsep)
end LeanFormal.IUT.XiFPaper.S1379TorsionCardinalityActual
