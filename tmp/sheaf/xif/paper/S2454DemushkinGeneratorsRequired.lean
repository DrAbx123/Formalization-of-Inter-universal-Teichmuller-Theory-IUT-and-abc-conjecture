import tmp.sheaf.xif.paper.S2453PadicDemushkinReduction
import tmp.sheaf.xif.paper.S2452ResidueFrobeniusActual
import tmp.sheaf.xif.paper.S2447WildTameInertiaAPI
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2447WildTameInertiaAPI
open LeanFormal.IUT.XiFPaper.S2452ResidueFrobeniusActual
open LeanFormal.IUT.XiFPaper.S2453PadicDemushkinReduction
namespace LeanFormal.IUT.XiFPaper.S2454DemushkinGeneratorsRequired
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The exact Demushkin/Jannsen-Wingberg generator datum still missing:
a Frobenius lift and an inertia element generating G_Qp topologically. -/
structure S2454DemushkinGenerators where
  sigma : LocalAbsoluteGalois p
  tau : LocalAbsoluteGalois p
  sigma_residue : LeanFormal.IUT.XiFPaper.S2442ResidueAction.PadicResidueAction p sigma
    = S2452FrobeniusAut p
  tau_in_wild : tau ∈ S2447WildInertia p
  generate : (Subgroup.closure ({sigma, tau} : Set (LocalAbsoluteGalois p))).topologicalClosure = ⊤
theorem S2454TwoGenerators_of_demushkin
    (D : S2454DemushkinGenerators p) :
    S2453TwoGenerators (p := p) :=
  ⟨D.sigma, D.tau, D.generate⟩
/-- Exact first missing target: an inhabitant of the explicit Demushkin
generator datum. -/
def S2454DemushkinGeneratorsRequired : Prop :=
  Nonempty (S2454DemushkinGenerators p)
#check S2454DemushkinGenerators
#check S2454TwoGenerators_of_demushkin
#check S2454DemushkinGeneratorsRequired
end LeanFormal.IUT.XiFPaper.S2454DemushkinGeneratorsRequired
end
