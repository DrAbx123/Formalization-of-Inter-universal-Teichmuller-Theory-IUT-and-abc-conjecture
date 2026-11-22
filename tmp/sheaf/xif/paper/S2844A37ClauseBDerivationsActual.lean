import tmp.sheaf.xif.paper.S2842A37ClauseAssemblyConditionalActual
import tmp.sheaf.xif.paper.S2806TateParameterActual
import tmp.sheaf.xif.paper.S2836RebuildOnKernelArithmetic
import tmp.sheaf.xif.paper.S2837PlaceSelectionArithmetic37Actual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlaceTateComparisonConstruction
open LeanFormal.IUT.XiFPaper.S2842A37ClauseAssemblyConditionalActual
open LeanFormal.IUT.XiFPaper.S2806TateParameterActual
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
open LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual
open LeanFormal.IUT.XiFPaper.S2836ClauseBCRebuildActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 16000000

local instance s2844GaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2844A37ClauseBDerivationsActual

/-- The q-candidate for arithmetic37 places, retyped from S2806Candidate. -/
noncomputable def S2844Candidate
    (p : NumberField.FinitePlace arithmetic37.F) :
    NumberFieldFinitePlace.FinitePlaceQCandidate p :=
  S2806Candidate (show NumberField.FinitePlace GaussianField from p)

/-- qWitness from an all-places realization.  No bad-place membership is used. -/
theorem S2844_qWitness
    (S : SourceSignQuotientData arithmetic37)
    (hreal : forall (p : NumberField.FinitePlace arithmetic37.F),
      CurveIndexedTateUniformization arithmetic37.curve p (S2844Candidate p)) :
    forall (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad ->
      Nonempty (SourceTateComparisonWitness arithmetic37 p) := by
  intro p hp
  refine ⟨SourceTateComparisonWitness.ofComparison (S2844Candidate p)
    (TateCurveComparison.ofUniformization (hreal p)) ?_⟩
  change Nat.Coprime
    (S2806Candidate (show NumberField.FinitePlace GaussianField from p)).order 5
  exact S2806Candidate_order_coprime _

#check S2844Candidate
#check S2844_qWitness
#print axioms S2844Candidate
#print axioms S2844_qWitness

end LeanFormal.IUT.XiFPaper.S2844A37ClauseBDerivationsActual
end
