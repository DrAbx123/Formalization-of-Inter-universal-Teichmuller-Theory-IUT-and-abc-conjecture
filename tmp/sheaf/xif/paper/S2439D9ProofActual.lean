import tmp.sheaf.xif.paper.S2434D9AttackActual
import tmp.sheaf.xif.paper.S2134D9DescentActual
import tmp.sheaf.xif.paper.S2425NatIsoCastHelpersActual
import tmp.sheaf.xif.paper.S2427PsubNatIsoConditionalActual
import tmp.sheaf.xif.paper.S2428D9FinalActual

noncomputable section
open CategoryTheory Opposite Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2434D9AttackActual
open LeanFormal.IUT.XiFPaper.S2134D9DescentActual
open LeanFormal.IUT.XiFPaper.S2427PsubNatIsoConditionalActual
open LeanFormal.IUT.XiFPaper.S2428D9FinalActual
open LeanFormal.IUT.XiFPaper.S2152PointwiseColimitActual
open LeanFormal.IUT.XiFPaper.S2332PsubCorrectActual
open LeanFormal.IUT.XiFPaper.S2425NatIsoCastHelpersActual
open LeanFormal.IUT.XiFPaper.S2103D9PrestackActual
open LeanFormal.IUT.XiFPaper.S2093D9StackActual
open LeanFormal.IUT.XiFPaper.S2029GiraudStackificationActual
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2439D9ProofActual

universe v u v' u'
variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {A : Type u'} [Category.{v'} A]

/-- Minimal reusable interface for the missing slice-push coherence: the explicit
pullHom equality. -/
def S2439PullHomCoherence {S : C} (M N : Sheaf (J.over S) A) : Prop :=
  forall ⦃X₁ X₂ : (Over S)ᵒᵖ⦄ (f : X₁ ⟶ X₂)
    (φ : (CategoryTheory.sheafHom' (J := J.over S) M N).obj X₁),
    (slicePush (J := J) (A := A) X₂.unop).map
        (((J.over S).overMapPullback A f.unop).map φ) =
      Pseudofunctor.LocallyDiscreteOpToCat.pullHom (F := J.pseudofunctorOver A)
        ((slicePush (J := J) (A := A) X₁.unop).map φ) f.unop.left X₂.unop.hom X₂.unop.hom

/-- Actual equivalence: SlicePushNaturality is exactly the pullHom coherence. -/
theorem S2439SlicePush_iff_coherence {S : C} (M N : Sheaf (J.over S) A) :
    SlicePushNaturality (J := J) (A := A) M N ↔
      S2439PullHomCoherence (J := J) (A := A) M N :=
  S2434SlicePush_iff_pullHom (J := J) (A := A) M N

section Field

variable {K : Type u} [Field K]

/-- Minimal reusable interface for general effective descent: amalgamation for
every descent datum on every actual etale covering presieve. -/
def S2439AmalgamationInterface : Prop :=
  forall (S : Iut.SchemeOverField K) (R : Presieve S),
    R ∈ (S2093EtalePrecoverage K).coverings S ->
      forall D : (S2029SheafPrestack K).DescentData
        (fun (g : R.category) => g.obj.hom),
        Nonempty (Amalgam (S2029SheafPrestack K)
          (fun (g : R.category) => g.obj.hom) D)

/-- Actual equivalence: general effective descent is exactly the amalgamation
interface. -/
theorem S2439EffDescent_iff_amalgamation :
    S2134EffDescentOnEtaleFamilies (K := K) ↔
      S2439AmalgamationInterface (K := K) :=
  S2134EffDescentOnEtaleFamilies_iff_amalgam (K := K)

end Field

variable (S : Iut.SchemeOverField S1726K)

/-- Exact sign projection input for the Psub NatIso. -/
abbrev S2439SignProjectionMissing : Prop := S2428PsubNatIsoMissing S

/-- Conditional Psub NatIso re-export. -/
noncomputable def S2439PsubNatIso_of_missing
    (h : S2439SignProjectionMissing S)
    (M N : S2152Q.obj (LocallyDiscrete.mk (Opposite.op S))) :
    S2152Q.presheafHom M N ≅ S2332Psub S M N :=
  S2427NatIso_of_signProjection S M N (h M N)

#print axioms S2439SlicePush_iff_coherence
#print axioms S2439EffDescent_iff_amalgamation
#print axioms S2439PsubNatIso_of_missing

end LeanFormal.IUT.XiFPaper.S2439D9ProofActual

end
