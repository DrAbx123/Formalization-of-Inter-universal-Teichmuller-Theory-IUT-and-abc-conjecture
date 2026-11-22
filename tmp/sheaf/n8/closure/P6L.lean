import tmp.sheaf.n8.closure.NativeC1
import Mathlib

/-!
# P6-L: global signed procession-normalized L / ell_out and Adm regions

Defines the global (finite-support, place-indexed) signed procession-normalized
volume `ell_out`, the admissible region conditions `Adm` (a.e. zero local log,
positive finite mass, reference region), and the P6 readout interface.

This is not a single tensor-block `normalizedLogVolume`: `ell_out` sums local
normalized mass logarithms over the actual native places with procession
weights and dimensions.  The actual global normalization/region donor is
missing; `p6ReadoutExists_obligation` is the theorem-level named sorry.
-/

noncomputable section

open MeasureTheory BigOperators
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1

namespace LeanFormal.IUT.N8Closure.P6L

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Global local-field carrier over all native selected places. -/
abbrev GlobalCarrier : Type _ :=
  ∀ v : NativePlaces X.S, localFieldAt X v

/-- Global region family: one local region at each native place. -/
abbrev GlobalRegion : Type _ :=
  ∀ v : NativePlaces X.S, Set (localFieldAt X v)

variable [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
variable [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
variable (mu : ∀ v : NativePlaces X.S, Measure (localFieldAt X v))
variable [∀ v : NativePlaces X.S, Measure.IsAddHaarMeasure (mu v)]

/-- Pointwise local log used for the almost-everywhere zero condition. -/
def localLog (v : NativePlaces X.S) (x : localFieldAt X v) : ℝ :=
  Real.log ‖x‖

/-- Admissible regions: measurable, positive finite local mass, global
almost-everywhere zero local log, and a reference region with the same
conditions.  This is the exact Adm condition, not a pointwise equality to a
reference unit region. -/
def Adm (reference region : GlobalRegion X) : Prop :=
  (∀ v, MeasurableSet (reference v)) ∧
  (∀ v, 0 < mu v (reference v)) ∧
  (∀ v, mu v (reference v) < ⊤) ∧
  (∀ v, ∀ᵐ x ∂(mu v), x ∈ reference v → localLog X v x = 0) ∧
  (∀ v, MeasurableSet (region v)) ∧
  (∀ v, 0 < mu v (region v)) ∧
  (∀ v, mu v (region v) < ⊤) ∧
  (∀ v, ∀ᵐ x ∂(mu v), x ∈ region v → localLog X v x = 0)

/-- Global signed procession-normalized log-volume `ell_out`: a finite-support
sum over native places of weighted local mass logarithms relative to the
reference region and divided by the actual local dimension.  No single-block
normalizedLogVolume is used. -/
def ellOut
    (support : Finset (NativePlaces X.S))
    (weight dimension : NativePlaces X.S → ℝ)
    (reference region : GlobalRegion X) : ℝ :=
  support.sum (fun v =>
    weight v *
      ((Real.log ((mu v (region v)).toReal) -
        Real.log ((mu v (reference v)).toReal)) / dimension v))

/-- P6 readout interface: a global admissible region pair, the finite support
and procession weights/dimensions, and the signed ell_out value. -/
structure P6Readout where
  support : Finset (NativePlaces X.S)
  weight : NativePlaces X.S → ℝ
  dimension : NativePlaces X.S → ℝ
  dimension_ne_zero : ∀ v, dimension v ≠ 0
  reference : GlobalRegion X
  region : GlobalRegion X
  adm : Adm (X := X) (mu := mu) reference region
  value : ℝ
  value_eq : value = ellOut (X := X) (mu := mu) support weight dimension reference region

/-- The P6 global readout exists as soon as the actual global procession
normalization/region donor exists.  Exact missing production donor: no actual
global admissible region family with procession weights/dimensions is
constructed in the tree.  Named sorry, no fake data. -/
def p6ReadoutExists : Prop :=
  Nonempty (P6Readout (X := X) (mu := mu))

theorem p6ReadoutExists_obligation :
    p6ReadoutExists (X := X) (mu := mu) := by
  sorry

/-- Readout projection: the signed global ell_out of a P6 readout. -/
def P6Readout.ellOutValue (R : P6Readout (X := X) (mu := mu)) : ℝ :=
  R.value

theorem P6Readout.ellOutValue_eq (R : P6Readout (X := X) (mu := mu)) :
    R.ellOutValue = R.value := rfl

end LeanFormal.IUT.N8Closure.P6L
