import tmp.sheaf.xif.paper.S2442InertiaAPI
import tmp.sheaf.xif.paper.S2117TopFGActual
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442InertiaAPI
open LeanFormal.IUT.XiFPaper.S2117TopFGActual
namespace LeanFormal.IUT.XiFPaper.S2446PadicFGExactMissing
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The subgroup called `PadicAbsoluteGaloisInertia` in S2442InertiaAPI is the
kernel of the action on prime-to-p torsion, i.e. the wild inertia subgroup. -/
abbrev S2446WildInertia : Subgroup (LocalAbsoluteGalois p) :=
  PadicAbsoluteGaloisInertia p
/-- Exact missing input: the wild inertia subgroup is topologically finitely
generated (it is pro-p, not procyclic; procyclic would be false). -/
def S2446WildInertiaTopologicallyFinitelyGenerated : Prop :=
  ∃ s : Finset (S2446WildInertia p),
    (Subgroup.closure (s : Set (S2446WildInertia p))).topologicalClosure = ⊤
/-- Exact missing input: the tame inertia quotient is topologically procyclic
(Frobenius lift). -/
def S2446InertiaQuotientProcyclic : Prop :=
  PadicInertiaQuotientProcyclic (p := p)
/-- Exact target: finite generation of the absolute Galois group of Q_p. -/
def S2446PadicFGRequired : Prop :=
  PadicAbsoluteGaloisTopologicallyFinitelyGenerated (p := p)
/-- The correct inertia-side inputs: tame quotient procyclic and wild inertia
topologically finitely generated. -/
def S2446InertiaInputs : Prop :=
  S2446InertiaQuotientProcyclic (p := p) ∧
    S2446WildInertiaTopologicallyFinitelyGenerated (p := p)
#check S2446WildInertia
#check S2446WildInertiaTopologicallyFinitelyGenerated
#check S2446InertiaQuotientProcyclic
#check S2446PadicFGRequired
#check S2446InertiaInputs
end LeanFormal.IUT.XiFPaper.S2446PadicFGExactMissing
end
