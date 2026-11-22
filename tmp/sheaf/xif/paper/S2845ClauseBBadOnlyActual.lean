import tmp.sheaf.xif.paper.S2845A37CompletionWithCoreActual
import tmp.sheaf.xif.paper.S2842A37ClauseAssemblyConditionalActual
import tmp.sheaf.xif.paper.S2836ClauseBCRebuildActual
import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceTateComparisonSynthesis
noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S2784KernelFieldActual
open LeanFormal.IUT.XiFPaper.S2844A37ClauseBDerivationsActual
open LeanFormal.IUT.XiFPaper.S2845A37CompletionWithCoreActual
open LeanFormal.IUT.XiFPaper.S2842A37ClauseAssemblyConditionalActual
open LeanFormal.IUT.XiFPaper.S2836RebuildOnKernelArithmetic
open LeanFormal.IUT.XiFPaper.S2836ClauseBCRebuildActual
open LeanFormal.IUT.XiFPaper.S2837PlaceSelectionArithmetic37Actual
open LeanFormal.IUT.XiFPaper.S2846A37GeometricCoreConditionalActual
open LeanFormal.IUT.XiFPaper.S2806TateParameterActual
open LeanFormal.IUT.XiFPaper.S2771Gap1ClosedActual
open LeanFormal.IUT.NumberFieldFinitePlace
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

local instance s2845bGaussianFact :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

namespace LeanFormal.IUT.XiFPaper.S2845ClauseBBadOnlyActual

/-- Bad-place-only Tate witness: only the finitely many bad places require a
CurveIndexedTateUniformization, not all places.  This is the exact refinement of
S2844_qWitness. -/
theorem S2844_qWitness_badOnly
    (S : SourceSignQuotientData arithmetic37)
    (hreal : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
        CurveIndexedTateUniformization arithmetic37.curve p (S2844Candidate p)) :
    ∀ (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈ S.V_mod_bad →
      Nonempty (SourceTateComparisonWitness arithmetic37 p) := by
  intro p hp
  refine ⟨SourceTateComparisonWitness.ofComparison (S2844Candidate p)
    (TateCurveComparison.ofUniformization (hreal p hp)) ?_⟩
  change Nat.Coprime (S2844Candidate p).order 5
  exact S2806Candidate_order_coprime _

/-- Clause B for arithmetic37 with the weakest pointwise input: Tate
uniformization only at bad places (plus the geometric core G for S). -/
noncomputable def S2845ClauseB_badOnly
    (G : SourceSignQuotientGeometricCore arithmetic37)
    (hreal : ∀ (p : NumberField.FinitePlace arithmetic37.F),
      NumberFieldFinitePlace.comap (k := arithmetic37.Fmod) p ∈
        (S2845S G).V_mod_bad →
        CurveIndexedTateUniformization arithmetic37.curve p (S2844Candidate p)) :
    SourceClauseB arithmetic37 (S2845S G) (S2836ClauseA (S2845S G)) :=
  S2842ClauseB (S2845S G) (S2845_multiplicative G)
    (S2844_qWitness_badOnly (S2845S G) hreal) (S2845_residue G)

#check S2844_qWitness_badOnly
#check S2845ClauseB_badOnly
#print axioms S2844_qWitness_badOnly
#print axioms S2845ClauseB_badOnly

end LeanFormal.IUT.XiFPaper.S2845ClauseBBadOnlyActual
end
