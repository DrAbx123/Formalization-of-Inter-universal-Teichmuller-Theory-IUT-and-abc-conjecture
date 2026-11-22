import LeanFormal.IUT.IUTII.Frobenioid.SourceKappaOrbitUnitsActionSupply
import LeanFormal.IUT.IUTIII.Theorem311.SourceKummerEvaluationArrows
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.SourceEvaluationUnitPortionConjugation

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Nontrivial Kummer/evaluation arrows from actual kappa-orbit data

Task-582 write-only construction.

Input: an actual KappaOrbitUnitsActionPairDatum D over two source strips
upper and lower. Its fields are production kappa-orbit/units-action data:
sourceUnits, sourceAction, factorUpper/factorLower, and the two actual
TimesMuKummer.Isomorphism representatives kappaUpper/kappaLower.

Constructed here, not assumed:
* kummerOfPair: the actual upper -> lower TimesMuKummer.Isomorphism whose
  equiv is kappaUpper.equiv.symm.trans kappaLower.equiv, with equivariance and
  the invariant-image law proved from D.kappaUpper and D.kappaLower;
* layerOfPair: the actual SourceTimesMuKummerLayer G upper lower with the
  production strip actions (upper.unitsAction).comp factorUpper and
  (lower.unitsAction).comp factorLower and kummerOfPair;
* evalPortionOfPair: the Card-EV SourceEvaluationUnitPortion extracted from
  layerOfPair by SourceEvaluationUnitPortion.ofKummerLayer;
* kummerArrowOfPair and evaluationArrowOfPair from an actual strip
  isomorphism FPrimeStripEquiv upper lower.

No identity-strip witness, no trivial actions, no True/PUnit, no axiom or
sorry is used. The only inputs are the actual kappa-orbit pair datum and the
actual strip isomorphism.

Exact missing donor: the KappaOrbitUnitsActionPairDatum itself, i.e. the
kappa-orbit Ism representatives kappaUpper/kappaLower over the common
group-theoretic unit module. The production supply file records this as the
arithmetic G1-SRC-a source obligation; it is not constructed here.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.KummerEvaluationArrowsActual2

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.TimesMuKummer

universe uG uU uW vV ua uv upi umon ui uL

variable {G : Type uG} [Group G] [TopologicalSpace G]
variable {V : Type vV}
variable {upper lower : FPrimeStrip V}

/-- The actual upper -> lower kappa isomorphism assembled from a kappa-orbit
pair datum. -/
noncomputable def kummerOfPair
    (D : KappaOrbitUnitsActionPairDatum G upper lower) (v : V) :
    TimesMuKummer.Isomorphism
      ((upper.unitsAction v).comp (D.factorUpper v))
      ((lower.unitsAction v).comp (D.factorLower v)) where
  equiv := (D.kappaUpper v).equiv.symm.trans (D.kappaLower v).equiv
  equivariant := by
    intro g x
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply]
    have hsymm :
        (D.kappaUpper v).equiv.symm
            (TimesMuQuotient.action ((upper.unitsAction v).comp (D.factorUpper v)) g x) =
          TimesMuQuotient.action (D.sourceAction v) g
            ((D.kappaUpper v).equiv.symm x) := by
      have h := (D.kappaUpper v).equivariant g
        ((D.kappaUpper v).equiv.symm x)
      have h' : (D.kappaUpper v).equiv
          (TimesMuQuotient.action (D.sourceAction v) g
            ((D.kappaUpper v).equiv.symm x)) =
        TimesMuQuotient.action ((upper.unitsAction v).comp (D.factorUpper v)) g x := by
        simpa only [MulEquiv.apply_symm_apply] using h
      calc
        (D.kappaUpper v).equiv.symm
            (TimesMuQuotient.action ((upper.unitsAction v).comp (D.factorUpper v)) g x)
          = (D.kappaUpper v).equiv.symm
              ((D.kappaUpper v).equiv
                (TimesMuQuotient.action (D.sourceAction v) g
                  ((D.kappaUpper v).equiv.symm x))) := by rw [h']
        _ = TimesMuQuotient.action (D.sourceAction v) g
              ((D.kappaUpper v).equiv.symm x) := by
            rw [MulEquiv.symm_apply_apply]
    rw [hsymm]
    exact (D.kappaLower v).equivariant g ((D.kappaUpper v).equiv.symm x)
  invariantImage := by
    intro H
    change ((D.kappaLower v).equiv ∘ (D.kappaUpper v).equiv.symm) ''
        (TimesMuKummer.invariantImage
          ((upper.unitsAction v).comp (D.factorUpper v)) H :
            Set (TimesMuQuotient ((upper.Mon v)ˣ))) =
      (TimesMuKummer.invariantImage
        ((lower.unitsAction v).comp (D.factorLower v)) H :
          Set (TimesMuQuotient ((lower.Mon v)ˣ)))
    rw [Set.image_comp, ← (D.kappaUpper v).invariantImage H]
    have hsymm :
        (D.kappaUpper v).equiv.symm ''
          ((D.kappaUpper v).equiv ''
            TimesMuKummer.invariantImage (D.sourceAction v) H) =
          TimesMuKummer.invariantImage (D.sourceAction v) H :=
      Equiv.symm_image_image (D.kappaUpper v).equiv.toEquiv _
    rw [hsymm]
    exact (D.kappaLower v).invariantImage H

/-- The actual source Kummer layer from the kappa-orbit pair datum. -/
noncomputable def layerOfPair
    (D : KappaOrbitUnitsActionPairDatum G upper lower) :
    SourceTimesMuKummerLayer G upper lower where
  sourceAction := fun v => (upper.unitsAction v).comp (D.factorUpper v)
  targetAction := fun v => (lower.unitsAction v).comp (D.factorLower v)
  kummer := fun v => kummerOfPair D v

/-- The layer's action is exactly the production strip action. -/
@[simp] theorem layerOfPair_sourceAction
    (D : KappaOrbitUnitsActionPairDatum G upper lower) (v : V) :
    (layerOfPair D).sourceAction v =
      (upper.unitsAction v).comp (D.factorUpper v) := rfl

/-- The layer's target action is exactly the production strip action. -/
@[simp] theorem layerOfPair_targetAction
    (D : KappaOrbitUnitsActionPairDatum G upper lower) (v : V) :
    (layerOfPair D).targetAction v =
      (lower.unitsAction v).comp (D.factorLower v) := rfl

/-- The actual Card-EV unit portion extracted from the layer. -/
noncomputable def evalPortionOfPair
    (D : KappaOrbitUnitsActionPairDatum G upper lower) :
    SourceEvaluationUnitPortion G upper lower :=
  SourceEvaluationUnitPortion.ofKummerLayer (layerOfPair D)

/-- The eval portion's unit layer is the layer's actual kappa composition. -/
@[simp] theorem evalPortionOfPair_unitLayer
    (D : KappaOrbitUnitsActionPairDatum G upper lower) (v : V) :
    (evalPortionOfPair D).unitLayer v = (kummerOfPair D v).equiv := rfl

/-- Actual Kummer arrow from an actual strip isomorphism and the kappa layer. -/
noncomputable def kummerArrowOfPair
    (D : KappaOrbitUnitsActionPairDatum G upper lower)
    (iso : FPrimeStripEquiv upper lower) :
    SourceKummerArrow G upper lower :=
  sourceKummerArrowOfLayer iso (layerOfPair D)

/-- Actual evaluation arrow from an actual strip isomorphism and the Card-EV
unit portion. -/
noncomputable def evaluationArrowOfPair
    (D : KappaOrbitUnitsActionPairDatum G upper lower)
    (iso : FPrimeStripEquiv upper lower) :
    SourceEvaluationArrow G upper lower :=
  sourceEvaluationArrowOfUnitPortion iso (evalPortionOfPair D)

/-- Nonempty Kummer arrow from an actual pair datum and strip isomorphism. -/
theorem kummerArrowOfPair_nonempty
    (D : KappaOrbitUnitsActionPairDatum G upper lower)
    (iso : FPrimeStripEquiv upper lower) :
    Nonempty (SourceKummerArrow G upper lower) :=
  ⟨kummerArrowOfPair D iso⟩

end LeanFormal.IUT.N8Closure.KummerEvaluationArrowsActual2

end