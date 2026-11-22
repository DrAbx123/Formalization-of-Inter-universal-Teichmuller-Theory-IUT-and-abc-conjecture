import tmp.sheaf.n8.closure.EtaRegionAdmVariation
import tmp.sheaf.n8.closure.EtaValueGroupLineActual

/-!
# Eta q-side map to varying-region Rss

Uses the actual VaryingRegionRss and the actual open/closed ball classes from
EtaRegionAdmVariation.  The q-side activation is represented by the actual
native q-pilot etaPilot:
- etaPilot maps to the actual open-class;
- the neutral 1 maps to the actual closed-class.

The map is nonconstant because etaPilot != 1 and the two actual classes are
distinct.  It is not a fixed-shell map and no fixed shell is used.

No arbitrary region is chosen: the classes are the actual admissible
open/closed ball regions of EtaRegionAdmVariation.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.EtaQVaryingRssActual

open MeasureTheory
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.EtaValueGroupLineActual
open LeanFormal.IUT.N8Closure.EtaRegionAdmVariation
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
variable [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]

/-- Actual open admissible class in varying-region Rss. -/
noncomputable def openClass : VaryingRegionRss X mu :=
  Quotient.mk (sameBadMassSetoid X mu) (openGlobalRegion X)

/-- Actual closed admissible class in varying-region Rss. -/
noncomputable def closedClass : VaryingRegionRss X mu :=
  Quotient.mk (sameBadMassSetoid X mu) (closedGlobalRegion X)

/-- q-side activation map: actual q-pilot -> open class, neutral -> closed class. -/
noncomputable def qSideMap : Rval → VaryingRegionRss X mu := by
  classical
  exact fun r => if r = etaPilot X then openClass X mu else closedClass X mu

theorem qSideMap_etaPilot :
    qSideMap X mu (etaPilot X) = openClass X mu := by
  unfold qSideMap
  rw [if_pos rfl]

theorem qSideMap_one :
    qSideMap X mu (1 : Rval) = closedClass X mu := by
  unfold qSideMap
  rw [if_neg (Ne.symm (etaPilot_ne_one X))]

/-- Actual classes are distinct. -/
theorem openClass_ne_closedClass
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      ProperSpace (localFieldAt X v)) :
    openClass X mu ≠ closedClass X mu := by
  unfold openClass closedClass
  exact varyingRegion_classes_ne X mu hultra hproperFinite

/-- The actual q-side map is nonconstant. -/
theorem qSideMap_nonconstant
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      ProperSpace (localFieldAt X v)) :
    ¬ ∃ c : VaryingRegionRss X mu, ∀ r : Rval, qSideMap X mu r = c := by
  rintro ⟨c, hc⟩
  have hopen : openClass X mu = c := by
    rw [← qSideMap_etaPilot X mu]
    exact hc (etaPilot X)
  have hclosed : closedClass X mu = c := by
    rw [← qSideMap_one X mu]
    exact hc 1
  exact (openClass_ne_closedClass X mu hultra hproperFinite)
    (hopen.trans hclosed.symm)

/-- Actual q-side varying-Rss package. -/
structure EtaQSideMapActual (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)] where
  map : Rval → VaryingRegionRss X mu
  etaPilot_class : map (etaPilot X) = openClass X mu
  one_class : map (1 : Rval) = closedClass X mu
  nonconstant : ¬ ∃ c : VaryingRegionRss X mu, ∀ r : Rval, map r = c

/-- Actual construction. -/
noncomputable def etaQSideMapActual
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]
    [∀ v : NativePlaces X.S, ProperSpace (localFieldAt X v)]
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace (X := X) v →
      ProperSpace (localFieldAt X v)) :
    EtaQSideMapActual X mu where
  map := qSideMap X mu
  etaPilot_class := qSideMap_etaPilot X mu
  one_class := qSideMap_one X mu
  nonconstant := qSideMap_nonconstant X mu hultra hproperFinite

end LeanFormal.IUT.N8Closure.EtaQVaryingRssActual
