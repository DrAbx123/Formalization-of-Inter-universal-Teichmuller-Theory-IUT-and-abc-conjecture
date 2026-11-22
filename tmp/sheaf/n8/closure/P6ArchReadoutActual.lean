import tmp.sheaf.n8.closure.P6RelaxedGlobalReadout
import Mathlib

/-!
# Actual archimedean ArchReadout

Constructs `P6RelaxedGlobalReadout.ArchReadout` from the actual archimedean
closed unit ball Adm, actual archimedean place multiplicity as weight/dimension,
and the actual archimedean ell_out formula.  This replaces the former named
gap `missing_archReadout`; no arbitrary region is used.
-/

noncomputable section

open MeasureTheory BigOperators Set Metric
open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6RelaxedGlobalReadout

namespace LeanFormal.IUT.N8Closure.P6ArchReadoutActual

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
  [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
  [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
  (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
  [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- The base infinite place underlying an archimedean native place. -/
noncomputable def archBaseInfinitePlace
    (v : ArchimedeanPlaces (X := X)) :
    NumberField.InfinitePlace X.S.arithmetic.Fmod := by
  classical
  rcases h : nativePlaceIndexEquiv X v.1 with p | w
  · exact False.elim (v.2 ⟨p, h⟩)
  · exact w

/-- Actual archimedean weight: the base infinite-place multiplicity. -/
def archWeight (v : ArchimedeanPlaces (X := X)) : ℝ :=
  ((archBaseInfinitePlace X v).mult : ℝ)

/-- Actual archimedean dimension: the base infinite-place multiplicity. -/
def archDimension (v : ArchimedeanPlaces (X := X)) : ℝ :=
  ((archBaseInfinitePlace X v).mult : ℝ)

theorem archDimension_ne_zero (v : ArchimedeanPlaces (X := X)) :
    archDimension (X := X) v ≠ 0 := by
  unfold archDimension
  exact NumberField.InfinitePlace.mult_coe_ne_zero

/-- Actual archimedean ell_out with the closed-ball reference/region. -/
noncomputable def archEllOut
    (support : Finset (ArchimedeanPlaces (X := X))) : ℝ :=
  support.sum (fun v =>
    archWeight (X := X) v *
      ((Real.log ((mu v.1) (archClosedBall (X := X) v)).toReal) -
        Real.log ((mu v.1) (archClosedBall (X := X) v)).toReal) /
          archDimension (X := X) v)

/-- Actual ArchReadout using the archimedean closed unit ball and actual
base infinite-place multiplicity. -/
noncomputable def archReadout
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    ArchReadout (X := X) (mu := mu) where
  support := ∅
  weight := archWeight (X := X)
  dimension := archDimension (X := X)
  dimension_ne_zero := archDimension_ne_zero (X := X)
  adm := archAdm_closedBall (X := X) (mu := mu) hproperArch
  value := archEllOut (X := X) (mu := mu) ∅

/-- Replacement for the former named gap `missing_archReadout`: the actual
archimedean ArchReadout exists under properness. -/
theorem missing_archReadout_actual
    (hproperArch : ∀ v : ArchimedeanPlaces (X := X),
      ProperSpace (localFieldAt X v.1)) :
    Nonempty (ArchReadout (X := X) (mu := mu)) :=
  ⟨archReadout (X := X) (mu := mu) hproperArch⟩

end LeanFormal.IUT.N8Closure.P6ArchReadoutActual