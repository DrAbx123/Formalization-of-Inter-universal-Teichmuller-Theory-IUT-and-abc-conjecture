import tmp.sheaf.xif.paper.S2446PadicFGExactMissing
import tmp.sheaf.xif.paper.S2442ResidueAction
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442InertiaAPI
open LeanFormal.IUT.XiFPaper.S2442ResidueAction
open LeanFormal.IUT.XiFPaper.S2117TopFGActual
open LeanFormal.IUT.XiFPaper.S2446PadicFGExactMissing
namespace LeanFormal.IUT.XiFPaper.S2447WildTameInertiaAPI
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The actual wild inertia subgroup: kernel of the prime-to-p torsion action. -/
abbrev S2447WildInertia : Subgroup (LocalAbsoluteGalois p) :=
  PadicAbsoluteGaloisInertia p
instance S2447WildInertia_normal : (S2447WildInertia p).Normal :=
  PadicAbsoluteGaloisInertia_normal (p := p)
/-- The actual tame inertia quotient G_Qp / wild inertia. -/
abbrev S2447TameInertiaQuotient : Type :=
  LocalAbsoluteGalois p ⧸ S2447WildInertia p
/-- Exact missing: the tame inertia quotient is topologically procyclic
(Frobenius lift). -/
def S2447TameInertiaProcyclicRequired : Prop :=
  ∃ σ : S2447TameInertiaQuotient p,
    (Subgroup.closure ({σ} : Set (S2447TameInertiaQuotient p))).topologicalClosure = ⊤
/-- Exact missing: wild inertia is topologically finitely generated (pro-p,
not procyclic). -/
def S2447WildInertiaFGRequired : Prop :=
  ∃ s : Finset (S2447WildInertia p),
    (Subgroup.closure (s : Set (S2447WildInertia p))).topologicalClosure = ⊤
/-- Exact target: G_Qp topologically finitely generated. -/
def S2447PadicFGRequired : Prop :=
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated (p := p)
#check S2447WildInertia
#check S2447TameInertiaQuotient
#check S2447TameInertiaProcyclicRequired
#check S2447WildInertiaFGRequired
#check S2447PadicFGRequired
end LeanFormal.IUT.XiFPaper.S2447WildTameInertiaAPI
end
