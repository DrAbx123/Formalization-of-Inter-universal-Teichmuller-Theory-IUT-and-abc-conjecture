import tmp.sheaf.xif.paper.ConcreteKummerActionOnLiteralIQActual
import tmp.sheaf.xif.paper.LogKummerCorrespondenceFromSource

/-!
# Global Theta-pilot log-Kummer compatibility: concrete action and exact gap

ConcreteKummerActionOnLiteralIQActual supplies the actual tensor ambient
ConcreteLiteralIQAmbient and the actual completion-image map
concreteCompletionImageToLiteralIQ, together with the actual completion-unit
action kummerUnitAction by tensor multiplication.

This file:

* constructs the concrete qUnit-power action on the image (from the actual
  concreteQUnit) and proves its action on the concrete completion image;
* records the exact missing multiradial action of the actual
  SourceTimesMuKummerLayer on the literal IQ ambient, and the resulting exact
  log-Kummer compatibility obligation.

The concrete qUnit action is actual.  The SourceTimesMuKummerLayer action on the
tensor packet is not supplied by the current tree, so no compatibility with that
layer is asserted or fabricated.

No PUnit/True, arbitrary data, axiom or sorry is used.
-/

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section
open scoped BigOperators

namespace LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogKummerCompatibilityActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.ConcreteC3DonorActual
open LeanFormal.IUT.Theorem311Source.LogKummerCorrespondenceFromSource
open LeanFormal.IUT.XiFPaper.ConcreteCompletionImageToLiteralIQActual
open LeanFormal.IUT.XiFPaper.ConcreteKummerActionOnLiteralIQActual
open LeanFormal.IUT.XiFPaper.ThetaPilotQImagePartialActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe ua uv upi umon ui uG

variable {l : PrimeGeFive} {V : Type uv}
variable (j : Nat)
variable (I : OriginalInput.{ua, 0, upi, umon, ui} l (FinitePrimePlace 2 7))
variable {p : Nat} [Fact p.Prime]
variable (place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p)

/-- The actual qUnit-power action on the concrete literal IQ ambient. -/
noncomputable def concreteQUnitPowerAction
    (j : Nat) (e : Nat) :
    ConcreteLiteralIQAmbient I place j → ConcreteLiteralIQAmbient I place j :=
  kummerUnitAction I place j
    ((concreteQUnit I place) ^ e)

/-- The actual qUnit-power action is tensor multiplication by the qUnit power. -/
theorem concreteQUnitPowerAction_apply
    (j e : Nat) (x : ConcreteLiteralIQAmbient I place j) :
    concreteQUnitPowerAction I place j e x =
      kummerUnitImage I place j ((concreteQUnit I place) ^ e) * x := rfl

/-- The actual qUnit-power action maps the concrete completion image to the
concrete completion image with shifted exponent. -/
theorem concreteQUnitPowerAction_completionImage
    (j e : Nat) (idx : ThetaPilotImageIndex (l := l)) :
    concreteQUnitPowerAction I place j e
        (concreteCompletionImageToLiteralIQ I place j idx) =
      kummerUnitImage I place j
        ((concreteQUnit I place) ^ (e + thetaImageExponent (l := l) idx)) := by
  rw [concreteQUnitPowerAction_apply]
  rw [concreteCompletionImageToLiteralIQ_eq_kummerImage]
  rw [← kummerUnitImage_mul, concreteThetaImage_eq, ← pow_add]

/-- Exact missing multiradial action of the actual SourceTimesMuKummerLayer on
the concrete literal IQ tensor packet. -/
structure SourceLayerMultiradialAction
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) where
  layer : SourceTimesMuKummerLayer G upper lower
  action : G → ConcreteLiteralIQAmbient I place j →
    ConcreteLiteralIQAmbient I place j
  action_one : ∀ x, action 1 x = x
  action_mul : ∀ (g h : G) (x),
    action (g * h) x = action g (action h x)

/-- Exact log-Kummer compatibility obligation: the layer action on the literal
IQ ambient must send the concrete completion image to the qUnit-power action of
the corresponding Kummer unit.  The actual layer-to-completion-unit comparison
is not supplied by the source; this is recorded as an obligation, not asserted. -/
def LogKummerLayerCompatibility
    (G : Type uG) [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V)
    (A : SourceLayerMultiradialAction (I := I) place j G upper lower) : Prop :=
  ∀ (g : G) (idx : ThetaPilotImageIndex (l := l)),
    A.action g (concreteCompletionImageToLiteralIQ I place j idx) =
      concreteQUnitPowerAction I place j (thetaImageExponent (l := l) idx)
        (concreteCompletionImageToLiteralIQ I place j idx)

/-- Exact obstruction: no actual multiradial layer action is supplied. -/
def SourceLayerMultiradialActionObstruction : Prop :=
  Nonempty (SourceLayerMultiradialAction (I := I) place j
    (ActualKummerGroup (I := I)) (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0))

/-- The obstruction is exactly the missing multiradial action. -/
theorem SourceLayerMultiradialActionObstruction_iff :
    SourceLayerMultiradialActionObstruction (I := I) place j ↔
      Nonempty (SourceLayerMultiradialAction (I := I) place j
        (ActualKummerGroup (I := I)) (I.fPrimeStripAt 1 0) (I.fPrimeStripAt 1 0)) :=
  Iff.rfl

end LeanFormal.IUT.XiFPaper.GlobalThetaPilotLogKummerCompatibilityActual

end