import tmp.sheaf.xif.paper.S2447WildTameInertiaAPI
import tmp.sheaf.xif.paper.S2442ResidueAction
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2442ResidueAction
open LeanFormal.IUT.XiFPaper.S2447WildTameInertiaAPI
namespace LeanFormal.IUT.XiFPaper.S2448ResidueFrobeniusAPI
variable (p : Nat) [Fact (Nat.Prime p)]
/-- The corrected residue-Frobenius object: a ring automorphism of the actual
residue field whose underlying map is x |-> x^p. -/
structure S2448FrobeniusData where
  frob : RingAut (PadicResidueField p)
  frob_apply : ∀ x : PadicResidueField p, frob x = x ^ p
/-- Exact missing API: the actual residue field is algebraically closed, which
makes x |-> x^p bijective. -/
def S2448ResidueAlgClosedRequired : Prop :=
  IsAlgClosed (PadicResidueField p)
/-- The procyclic closure of a Frobenius automorphism in the residue
automorphism group. -/
def S2448ZRes [TopologicalSpace (RingAut (PadicResidueField p))]
    [IsTopologicalGroup (RingAut (PadicResidueField p))]
    (F : S2448FrobeniusData p) :
    Subgroup (RingAut (PadicResidueField p)) :=
  (Subgroup.closure ({F.frob} : Set (RingAut (PadicResidueField p)))).topologicalClosure
/-- Exact missing: the residue action image is dense in the procyclic closure
of Frobenius (NOT equal to all RingAut). -/
def S2448ResidueImageDense [TopologicalSpace (RingAut (PadicResidueField p))]
    [IsTopologicalGroup (RingAut (PadicResidueField p))]
    (F : S2448FrobeniusData p) : Prop :=
  (Subgroup.closure (Set.range (PadicResidueAction p))).topologicalClosure =
    S2448ZRes p F
/-- Exact missing: the kernel of the residue action is wild inertia. -/
def S2448ResidueKernelEqWildInertia : Prop :=
  PadicResidueKernel p = S2447WildInertia p
/-- Exact missing: a Frobenius lift in G_Qp whose residue action is F. -/
structure S2448FrobeniusLift (F : S2448FrobeniusData p) where
  sigma : LocalAbsoluteGalois p
  residue_eq : PadicResidueAction p sigma = F.frob
/-- Exact missing: the class of the lift generates the tame inertia quotient. -/
def S2448TameQuotientGeneratedByLift (F : S2448FrobeniusData p)
    (L : S2448FrobeniusLift p F) : Prop :=
  (Subgroup.closure ({(QuotientGroup.mk L.sigma : S2447TameInertiaQuotient p)} :
    Set (S2447TameInertiaQuotient p))).topologicalClosure = ⊤
#check S2448FrobeniusData
#check S2448ResidueAlgClosedRequired
#check S2448ZRes
#check S2448ResidueImageDense
#check S2448ResidueKernelEqWildInertia
#check S2448FrobeniusLift
#check S2448TameQuotientGeneratedByLift
end LeanFormal.IUT.XiFPaper.S2448ResidueFrobeniusAPI
end
