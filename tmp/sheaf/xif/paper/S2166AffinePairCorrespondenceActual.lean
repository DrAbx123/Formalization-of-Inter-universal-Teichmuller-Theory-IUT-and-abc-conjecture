import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S1982D5FiveActual
import tmp.sheaf.xif.paper.S2009DicksonActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual

open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual

/-- The actual projective/affine comparison for E' over the algebraic closure. -/
noncomputable def S2166ProjAffineEquiv :
    WeierstrassCurve.Projective.Point S2056W ≃+ S2056W.Point := 
  S1906ProjAffineEquiv

/-- The actual rank-two torsion basis of S1982. -/
noncomputable def S2166Basis :
    (Fin 2 → ZMod S1982Five.value) ≃ₗ[ZMod S1982Five.value] (S1720Curve.LTorsion S1982Five) :=
  S1982Basis

/-- Fintype instance on the affine pair set, transported from the actual root
set via S2056RootPairEquiv. -/
noncomputable instance S2166PairFintype : Fintype S2056Pair :=
  Fintype.ofEquiv S2056Root S2056RootPairEquiv

/-- Actual existence of a bijection between the twelve affine pairs and the
twelve S2009 representative pairs (by the two independently proved cardinality
twelve facts).  This is an existence statement; the basis-compatible
correspondence is the exact missing structure below. -/
theorem S2166AffinePairEquiv_exists :
    Nonempty (S2009Pairs ≃ S2056Pair) := by
  have h1 : Fintype.card S2009Pairs = 12 := card_pairRep
  have h2 : Fintype.card S2056Pair = 12 := by
    rw [← Nat.card_eq_fintype_card, S2056Pair_card]
  exact ⟨Fintype.equivOfCardEq (h1.trans h2.symm)⟩

/-- Exact first missing: an actual affine lift of the S1982 basis, i.e. a
ZMod-5-linear equivalence from coordinate space to the affine 5-torsion.
The projective/affine additive equivalence and the projective basis are
both actual; composing them through additive torsion subgroups is the
remaining API step. -/
structure S2166AffineBasisLift where
  affineBasis : (Fin 2 → ZMod S1982Five.value) ≃+ S2056Torsion

def S2166AffineBasisLiftRequired : Prop :=
  Nonempty S2166AffineBasisLift

/-- Exact first missing pair statement: a basis-compatible bijection between
S2009 representative pairs and affine pairs. -/
structure S2166BasisCompatiblePairEquiv (L : S2166AffineBasisLift) where
  pairEquiv : S2009Pairs ≃ S2056Pair

def S2166BasisCompatiblePairEquivRequired : Prop :=
  ∃ L : S2166AffineBasisLift, Nonempty (S2166BasisCompatiblePairEquiv L)

end LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual

end
