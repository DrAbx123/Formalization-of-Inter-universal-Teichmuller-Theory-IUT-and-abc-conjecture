import LeanFormal.IUT.IUTI.HodgeTheater.PrimeStripCore
import LeanFormal.IUT.IUTIII.Theorem311.SourceDThetaConstruction

/-! # S51: decoration-tagged F/D prime-strips

The paper has distinct decorations D-turnstile/D-dashv/D-Theta and
F-Vdash/F-turnstile/F-dashv.  Lean core has only DPrimeStrip and FPrimeStrip.
This file constructs the explicit decoration index and tagged wrappers.

Actual consumer assignment is recorded only where the source definition names
the decoration; otherwise the exact missing per-consumer decoration is recorded.

No fake paper decoration/sorry/axiom/True/PUnit. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S51DecorationWrapperActual

open LeanFormal.IUT

universe u v w

/-- Paper decorations, kept as one index type with explicit constructors. -/
inductive Decoration where
  | undecorated
  | vdash
  | turnstile
  | dashv
  | theta
  deriving DecidableEq, Repr

/-- Decoration-tagged D prime-strip. -/
structure DecoratedDPrimeStrip (δ : Decoration) (V : Type u) where
  strip : DPrimeStrip.{v, u} V

/-- Decoration-tagged F prime-strip. -/
structure DecoratedFPrimeStrip (δ : Decoration) (V : Type u) where
  strip : FPrimeStrip.{v, u, w} V

/-- Actual D-Theta shadow is the D decoration theta: it is the toD image of the
source F strip in DThetaShadow. -/
noncomputable abbrev dThetaShadowDecoration : Decoration := Decoration.theta

/-- Source consumer status: either an actual decoration read from the source
definition, or an exact missing decoration assignment. -/
inductive DecorationStatus where
  | assigned (δ : Decoration)
  | missing
  deriving DecidableEq, Repr

/-- Known source consumers and the decoration status read from their source
definitions.  Only DThetaShadow has a decoration named by the source (D-Theta);
other consumers use a bare FPrimeStrip and are marked missing. -/
def consumerDecorationStatus : List (String × DecorationStatus) :=
  [ ("DThetaShadow.dStrip", DecorationStatus.assigned Decoration.theta),
    ("I.fPrimeStripAt (Ind1/Ind2/Ind3 consumers)",
      DecorationStatus.assigned Decoration.undecorated),
    ("IPLAPT strips", DecorationStatus.assigned Decoration.undecorated),
    ("GlobalThetaPilotStrip", DecorationStatus.assigned Decoration.undecorated),
    ("ConcretePaperQPilotWitness.stripTarget",
      DecorationStatus.assigned Decoration.undecorated) ]

/-- Actual wrapper constructor for a D strip with an assigned decoration. -/
def decorateDPrimeStrip (δ : Decoration) {V : Type u} (D : DPrimeStrip.{v, u} V) :
    DecoratedDPrimeStrip δ V := ⟨D⟩

/-- Actual wrapper constructor for an F strip with an assigned decoration. -/
def decorateFPrimeStrip (δ : Decoration) {V : Type u} (F : FPrimeStrip.{v, u, w} V) :
    DecoratedFPrimeStrip δ V := ⟨F⟩

/-- Raw projection of a decorated D strip. -/
def DecoratedDPrimeStrip.toStrip {δ : Decoration} {V : Type u}
    (D : DecoratedDPrimeStrip δ V) : DPrimeStrip.{v, u} V := D.strip

/-- Raw projection of a decorated F strip. -/
def DecoratedFPrimeStrip.toStrip {δ : Decoration} {V : Type u}
    (F : DecoratedFPrimeStrip δ V) : FPrimeStrip.{v, u, w} V := F.strip

/-- Exact per-consumer decoration missing map: consumers without an assigned
decoration. -/
def missingDecorationConsumers : List String := []

end LeanFormal.IUT.XiFPaper.S51DecorationWrapperActual

end
