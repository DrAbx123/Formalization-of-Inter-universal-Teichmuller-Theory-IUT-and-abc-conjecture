import tmp.sheaf.xif.paper.S346OrbifoldStructuralSheafActual
/-! # S348: abstract mu_{2l} action / rootSection interface on S346 spec
On the abstract S346 carrier spec (carrier, qSection, rootSection, rootSection^2l
= qSection, structural condition), define a mu_{2l} action as an explicit
self-map with iterate order 2l and rootSection compatibility.  The action is
interface data, not constructed; no carrier or root inhabitant is claimed. -/
noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000
namespace LeanFormal.IUT.XiFPaper.S348OrbifoldMu2lInterfaceActual
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.S346OrbifoldStructuralSheafActual
universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))
/-- Minimal abstract mu_{2l} interface on the S346 carrier. -/
structure OrbifoldMu2lInterface
    (C : OrbifoldStructuralSheafCarrierSpec T b) where
  muAction : C.carrier → C.carrier
  muAction_pow_twoL : ∀ x : C.carrier,
    (muAction^[2 * l.value]) x = x
  muAction_rootSection : muAction C.rootSection = C.rootSection
/-- The abstract mu-action. -/
noncomputable def mu2lAction
    {C : OrbifoldStructuralSheafCarrierSpec T b}
    (I : OrbifoldMu2lInterface T b C) (x : C.carrier) : C.carrier :=
  I.muAction x
/-- The root section of the S346 spec. -/
noncomputable def rootSectionOf
    (C : OrbifoldStructuralSheafCarrierSpec T b) : C.carrier :=
  C.rootSection
/-- Theta section from the root section and the abstract action. -/
noncomputable def thetaSection
    {C : OrbifoldStructuralSheafCarrierSpec T b}
    (I : OrbifoldMu2lInterface T b C) (j : Nat) : C.carrier :=
  (I.muAction^[j]) C.rootSection
/-- The abstract mu-orbit of a theta section. -/
noncomputable def thetaOrbit
    {C : OrbifoldStructuralSheafCarrierSpec T b}
    (I : OrbifoldMu2lInterface T b C) (j : Nat) : Set C.carrier :=
  {x | ∃ k : Nat, k < 2 * l.value ∧
    x = (I.muAction^[k]) (thetaSection T b I j)}
/-- The abstract mu-image union over natural theta labels. -/
noncomputable def thetaOrbitUnion
    {C : OrbifoldStructuralSheafCarrierSpec T b}
    (I : OrbifoldMu2lInterface T b C) : Set C.carrier :=
  ⋃ j : Nat, thetaOrbit T b I j
/-- Each theta section lies in the union via k=0. -/
theorem thetaSection_mem_union
    {C : OrbifoldStructuralSheafCarrierSpec T b}
    (I : OrbifoldMu2lInterface T b C) (j : Nat) :
    thetaSection T b I j ∈ thetaOrbitUnion T b I :=
  Set.mem_iUnion.mpr ⟨j, by
    have hpos : 0 < 2 * l.value := by
      exact Nat.mul_pos (by norm_num) l.prime.pos
    refine ⟨0, hpos, ?_⟩
    simp [thetaSection]⟩
/-- The interface action has order dividing 2l. -/
theorem mu2lAction_pow_twoL
    {C : OrbifoldStructuralSheafCarrierSpec T b}
    (I : OrbifoldMu2lInterface T b C) (x : C.carrier) :
    ((mu2lAction T b I)^[2 * l.value]) x = x :=
  I.muAction_pow_twoL x
/-- Exact missing abstract mu-root interface (no inhabitant). -/
def OrbifoldMu2lInterfaceRequired
    (C : OrbifoldStructuralSheafCarrierSpec T b) : Prop :=
  Nonempty (OrbifoldMu2lInterface T b C)
end LeanFormal.IUT.XiFPaper.S348OrbifoldMu2lInterfaceActual
