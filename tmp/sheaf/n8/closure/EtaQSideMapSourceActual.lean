import tmp.sheaf.n8.closure.EtaQRegionRepresentation
import tmp.sheaf.n8.closure.EtaRegionAdmVariation
import tmp.sheaf.n8.closure.EtaValueGroupLineActual

/-!
# Eta q-side map source actual (no fabricated if)

Replaces the fabricated two-point qSideMap by the actual q multiplication
action on the actual qO region in the native F-completion.

- QUnits = (Completion (nativeFPlaceOverBad X))^x;
- LocalHaarRss is the actual equal-Haar-mass quotient of subsets of the F-
  completion;
- qSourceClass r = [r • qORegion X], using actual scalar multiplication;
- qSourceClass_one and qSourceClass_mul_action are actual action laws.

Nonconstancy of qSourceClass is the exact remaining scaling/noncollapse gap: it
requires distinguishing q-action masses (the production qO Haar scaling is
itself a named gap).  No if-branch or arbitrary map is used.

Mapping this q-action class to the global VaryingRegionRss is an exact no-go:
the q carrier is the F-completion, while global regions are indexed by the base
native (Fmod) places; no bridge is introduced.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQSideMapSourceActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC3
open LeanFormal.IUT.N8Closure.C9QPilotRegion
open LeanFormal.IUT.N8Closure.EtaQRegionRepresentation
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRegionAdmVariation

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Actual q-side units at the native F-completion. -/
abbrev QUnits : Type _ := (QCompletion X)ˣ

/-- Actual q multiplication action on subsets of the F-completion. -/
def qAction (r : QUnits X) (A : Set (QCompletion X)) : Set (QCompletion X) :=
  {x | ∃ a ∈ A, x = (r : QCompletion X) * a}

/-- Equal-Haar-mass relation on subsets of the F-completion. -/
def SameHaarMass (μ : Measure (QCompletion X)) (A B : Set (QCompletion X)) : Prop :=
  μ A = μ B

def sameHaarMassSetoid (μ : Measure (QCompletion X)) : Setoid (Set (QCompletion X)) where
  r := SameHaarMass X μ
  iseqv := by
    refine ⟨?_, ?_, ?_⟩
    · intro A; rfl
    · intro A B h; exact h.symm
    · intro A B C hAB hBC; exact hAB.trans hBC

/-- Actual local q-side Rss: equal-Haar-mass classes on the F-completion. -/
abbrev LocalHaarRss (μ : Measure (QCompletion X)) : Type _ :=
  Quotient (sameHaarMassSetoid X μ)

/-- Actual q-source class map: r maps to the class of r • qORegion. -/
noncomputable def qSourceClass
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] :
    QUnits X → LocalHaarRss X μ :=
  fun r => Quotient.mk (sameHaarMassSetoid X μ) (qAction X r (qORegion X))

/-- The neutral q-unit maps to the actual qO class. -/
theorem qSourceClass_one
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] :
    qSourceClass X μ (1 : QUnits X) =
      Quotient.mk (sameHaarMassSetoid X μ) (qORegion X) := by
  unfold qSourceClass qAction
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩; simpa using ha
  · intro hx; exact ⟨x, hx, by simp⟩

/-- Actual q-multiplication action law. -/
theorem qSourceClass_mul_action
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ]
    (r s : QUnits X) :
    qSourceClass X μ (r * s) =
      Quotient.mk (sameHaarMassSetoid X μ)
        (qAction X r (qAction X s (qORegion X))) := by
  unfold qSourceClass qAction
  congr 1
  ext x
  constructor
  · rintro ⟨a, ha, rfl⟩
    refine ⟨(s : QCompletion X) * a, ⟨a, ha, rfl⟩, ?_⟩
    rw [Units.val_mul]; ring
  · rintro ⟨a, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, by rw [Units.val_mul]; ring⟩

/-- Exact noncollapse target for the q-source class map. -/
def QSourceClassNonconstant
    (μ : Measure (QCompletion X)) [Measure.IsAddHaarMeasure μ] : Prop :=
  ¬ ∃ c : LocalHaarRss X μ, ∀ r : QUnits X, qSourceClass X μ r = c

end LeanFormal.IUT.N8Closure.EtaQSideMapSourceActual
