import tmp.sheaf.n8.closure.P6RelaxedGlobalReadoutActual
import tmp.sheaf.n8.closure.P6RelaxedSourceRouteIntegration
import tmp.sheaf.n8.closure.P6GlobalLqDonorUnderconstrained
import Mathlib

/-!
# Relaxed readout route integration

Converts the actual `RelaxedGlobalReadout` (finite nonarch sphere + archimedean
closed ball, actual weights/dimensions) into a `P6AdmRedesign.RelaxedP6Readout`,
thus replacing `P6AdmRedesign.relaxedP6Readout` in the corrected route and C9
target.  No arbitrary region is used.
-/

noncomputable section

open MeasureTheory BigOperators
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6NonarchAdmActual
open LeanFormal.IUT.N8Closure.P6FinitePlaceReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedReadoutActual
open LeanFormal.IUT.N8Closure.P6ArchReadoutActual
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadoutActual
open LeanFormal.IUT.N8Closure.P6AdmRedesign
open LeanFormal.IUT.N8Closure.P6RelaxedSourceRouteIntegration
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6GlobalLqDonorUnderconstrained

namespace LeanFormal.IUT.N8Closure.P6RelaxedReadoutRouteIntegration

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)
variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

noncomputable def combinedSupport
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) : Finset (NativePlaces X.S) := by
  classical
  exact G.finite.support.image (fun v => v.1) ∪ G.arch.support.image (fun v => v.1)

noncomputable def combinedWeight
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) :
    NativePlaces X.S → ℝ := by
  classical
  exact fun v => if h : IsFiniteNativePlace (X := X) v then
    G.finite.weight ⟨v, h⟩ else G.arch.weight ⟨v, h⟩

noncomputable def combinedDimension
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) :
    NativePlaces X.S → ℝ := by
  classical
  exact fun v => if h : IsFiniteNativePlace (X := X) v then
    G.finite.dimension ⟨v, h⟩ else G.arch.dimension ⟨v, h⟩

theorem combinedDimension_ne_zero
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) (v : NativePlaces X.S) :
    combinedDimension (X := X) (mu := mu) G v ≠ 0 := by
  classical
  unfold combinedDimension
  split
  · exact G.finite.dimension_ne_zero _
  · exact G.arch.dimension_ne_zero _

noncomputable def combinedReference
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) : GlobalRegion X := by
  classical
  exact fun v => if h : IsFiniteNativePlace (X := X) v then
    G.finite.reference ⟨v, h⟩ else archClosedBall (X := X) ⟨v, h⟩

noncomputable def combinedRegion
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) : GlobalRegion X := by
  classical
  exact fun v => if h : IsFiniteNativePlace (X := X) v then
    G.finite.region ⟨v, h⟩ else archClosedBall (X := X) ⟨v, h⟩

theorem combinedAdm
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) :
    RelaxedAdm (X := X) (mu := mu)
      (combinedReference (X := X) (mu := mu) G)
      (combinedRegion (X := X) (mu := mu) G) := by
  classical
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro v
    unfold combinedReference
    split
    · exact G.finite.adm.1 ⟨v, ‹IsFiniteNativePlace X v›⟩
    · exact G.arch.adm.1 ⟨v, ‹¬ IsFiniteNativePlace X v›⟩
  · intro v
    unfold combinedReference
    split
    · exact G.finite.adm.2.1 ⟨v, ‹IsFiniteNativePlace X v›⟩
    · exact G.arch.adm.2.1 ⟨v, ‹¬ IsFiniteNativePlace X v›⟩
  · intro v
    unfold combinedReference
    split
    · exact G.finite.adm.2.2.1 ⟨v, ‹IsFiniteNativePlace X v›⟩
    · exact G.arch.adm.2.2.1 ⟨v, ‹¬ IsFiniteNativePlace X v›⟩
  · intro v
    unfold combinedRegion
    split
    · exact G.finite.adm.2.2.2.1 ⟨v, ‹IsFiniteNativePlace X v›⟩
    · exact G.arch.adm.2.2.2.1 ⟨v, ‹¬ IsFiniteNativePlace X v›⟩
  · intro v
    unfold combinedRegion
    split
    · exact G.finite.adm.2.2.2.2.1 ⟨v, ‹IsFiniteNativePlace X v›⟩
    · exact G.arch.adm.2.2.2.2.1 ⟨v, ‹¬ IsFiniteNativePlace X v›⟩
  · intro v
    unfold combinedRegion
    split
    · exact G.finite.adm.2.2.2.2.2 ⟨v, ‹IsFiniteNativePlace X v›⟩
    · exact G.arch.adm.2.2.2.2.2 ⟨v, ‹¬ IsFiniteNativePlace X v›⟩

noncomputable def relaxedP6ReadoutOfGlobal
    (G : RelaxedGlobalReadout (X := X) (mu := mu)) :
    RelaxedP6Readout (X := X) (mu := mu) :=
  { support := combinedSupport (X := X) (mu := mu) G
    weight := combinedWeight (X := X) (mu := mu) G
    dimension := combinedDimension (X := X) (mu := mu) G
    dimension_ne_zero := combinedDimension_ne_zero (X := X) (mu := mu) G
    reference := combinedReference (X := X) (mu := mu) G
    region := combinedRegion (X := X) (mu := mu) G
    adm := combinedAdm (X := X) (mu := mu) G
    value := ellOut (X := X) (mu := mu)
      (combinedSupport (X := X) (mu := mu) G)
      (combinedWeight (X := X) (mu := mu) G)
      (combinedDimension (X := X) (mu := mu) G)
      (combinedReference (X := X) (mu := mu) G)
      (combinedRegion (X := X) (mu := mu) G)
    value_eq := rfl }

noncomputable def relaxedRouteActualGlobal
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    RelaxedRouteObligations X mu where
  chainA := constantChainA X
  readout := relaxedP6ReadoutOfGlobal (X := X) (mu := mu)
    (relaxedGlobalReadoutActual (X := X) (mu := mu)
      hultra hproperFinite hproperArch)

theorem relaxedRouteActualGlobal_nonempty
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (RelaxedRouteObligations X mu) :=
  ⟨relaxedRouteActualGlobal X mu hultra hproperFinite hproperArch⟩

theorem relaxedC9PaperTargetActualGlobal
    (hultra : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      IsUltrametricDist (localFieldAt X v))
    (hproperFinite : ∀ v : NativePlaces X.S, IsFiniteNativePlace X v →
      ProperSpace (localFieldAt X v))
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (RelaxedC9PaperTarget X mu) :=
  ⟨relaxedC9PaperTargetOfRoute X mu
    (relaxedRouteActualGlobal X mu hultra hproperFinite hproperArch)⟩

end LeanFormal.IUT.N8Closure.P6RelaxedReadoutRouteIntegration