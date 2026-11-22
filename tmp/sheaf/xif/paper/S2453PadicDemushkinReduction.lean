import tmp.sheaf.xif.paper.S2452ResidueFrobeniusActual
import tmp.sheaf.xif.paper.S2117TopFGActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2117TopFGActual
namespace LeanFormal.IUT.XiFPaper.S2453PadicDemushkinReduction
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The concrete two-generator statement for G_Qp. -/
def S2453TwoGenerators : Prop :=
  ∃ σ τ : LocalAbsoluteGalois p,
    (Subgroup.closure ({σ, τ} : Set (LocalAbsoluteGalois p))).topologicalClosure = ⊤
/-- Demushkin/Jannsen-Wingberg two-generation implies the target topological
finite generation of G_Qp. -/
theorem S2453PadicFG_of_twoGenerators
    (h : S2453TwoGenerators (p := p)) :
    PadicAbsoluteGaloisTopologicallyFinitelyGenerated (p := p) := by
  rcases h with ⟨σ, τ, hστ⟩
  classical
  refine ⟨{σ, τ}, ?_⟩
  simpa [Finset.coe_insert, Finset.coe_singleton] using hστ
/-- Exact missing Demushkin/Jannsen-Wingberg theorem: two explicit topological
generators of G_Qp with their relation. -/
def S2453DemushkinTwoGeneratorRequired : Prop :=
  S2453TwoGenerators (p := p)
#check S2453TwoGenerators
#check S2453PadicFG_of_twoGenerators
#check S2453DemushkinTwoGeneratorRequired
end LeanFormal.IUT.XiFPaper.S2453PadicDemushkinReduction
end
