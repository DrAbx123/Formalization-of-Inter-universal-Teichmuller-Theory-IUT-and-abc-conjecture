import tmp.sheaf.n8.closure.P6ChainA
import tmp.sheaf.n8.closure.P6ChainB
import tmp.sheaf.n8.closure.P6Hull
import tmp.sheaf.n8.closure.P6L
import tmp.sheaf.n8.closure.P6Comparison

/-!
# N8 route closure: P6 component obligations

This file assembles the current N8/P6 route components only.  It does not
connect ABC, Cor312, or any old-layer interface.

N8RouteObligations X contains:
- P6ChainA.P6ChainAData X (native q -> local q-pilot -> global L_q -> Q)
- P6ChainB.MissingSLToCompleteAlpha X (S/L -> complete alpha exact gap)
- P6Hull.P6HullSetup (R_alpha/U/H/HullPoss)
- P6L.P6Readout X mu (global ell_out)
- P6Comparison.P6Exact X Q or P6Epsilon X Q (source-allowed J, J range
  independent of Q)

The exact missing source objects are named component sorries:
- P6ChainA.globalLqDonor_nonempty
- P6ChainB.missing_sl_to_complete_alpha
- p6HullSetup_nonempty (this file)
- P6L.p6ReadoutExists_obligation
- p6ComparisonObligation (this file)

No total-goal sorry and no Q<=Theta input are used.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.N8RouteClosure

open LeanFormal.IUT
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeC1
open LeanFormal.IUT.N8Closure.P6ChainA
open LeanFormal.IUT.N8Closure.P6ChainB
open LeanFormal.IUT.N8Closure.P6Hull
open LeanFormal.IUT.N8Closure.P6L
open LeanFormal.IUT.N8Closure.P6Comparison

universe u

variable {l : PrimeGeFive}

/-- Exact named P6 hull/setup gap: a paper hull package with actual R_alpha /
Adm_out / paper hull operator is missing. -/
theorem p6HullSetup_nonempty :
    Nonempty (P6Hull.P6HullSetup.{0, 0}) := by
  sorry

/-- Exact named P6 comparison gap: for an actual Chain A Q, a source-allowed
J in HullPoss realizes Q exactly or one-sided.  J ranges over P6Comparison
SourceAllowedOutput X, independent of Q<=Theta. -/
theorem p6ComparisonObligation (X : N8NativeInput l)
    (C : P6ChainAData X) :
    P6Comparison.P6Exact X C.Q ∨ P6Comparison.P6Epsilon X C.Q := by
  sorry

/-- Current N8/P6 route obligations. -/
structure N8RouteObligations
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] where
  /-- P6 Chain A: native q -> local q-pilot -> global L_q -> Q. -/
  chainA : P6ChainA.P6ChainAData X
  /-- P6 Chain B: exact S/L -> complete alpha gap. -/
  chainB : P6ChainB.MissingSLToCompleteAlpha.{0, 0, 0, 0} X
  /-- P6 hull: R_alpha/U/H/HullPoss package. -/
  hull : P6Hull.P6HullSetup.{0, 0}
  /-- P6 L: global ell_out readout. -/
  readout : P6L.P6Readout (X := X) (mu := mu)
  /-- P6 comparison: exact or epsilon realization of Q by a source-allowed J. -/
  comparison : P6Comparison.P6Exact X chainA.Q ∨ P6Comparison.P6Epsilon X chainA.Q

/-- Assembly from the exact named component gaps.  The proof uses only the
named P6 component obligations; it has no total-goal sorry. -/
theorem n8RouteObligations_nonempty
    (X : N8NativeInput l)
    [∀ v : NativePlaces X.S, NormedField (localFieldAt X v)]
    [∀ v : NativePlaces X.S, MeasurableSpace (localFieldAt X v)]
    [∀ v : NativePlaces X.S, BorelSpace (localFieldAt X v)]
    (mu : ∀ v : NativePlaces X.S, MeasureTheory.Measure (localFieldAt X v))
    [∀ v : NativePlaces X.S, MeasureTheory.Measure.IsAddHaarMeasure (mu v)] :
    Nonempty (N8RouteObligations X mu) := by
  let Dq : P6ChainA.GlobalLqDonor X :=
    Classical.choice (P6ChainA.globalLqDonor_nonempty X)
  let A : P6ChainA.P6ChainAData X := P6ChainA.p6ChainAOfGlobalLq X Dq
  let B : P6ChainB.MissingSLToCompleteAlpha X :=
    P6ChainB.missing_sl_to_complete_alpha X
  let H : P6Hull.P6HullSetup.{0, 0} := Classical.choice (p6HullSetup_nonempty)
  let R : P6L.P6Readout (X := X) (mu := mu) :=
    Classical.choice (P6L.p6ReadoutExists_obligation (X := X) (mu := mu))
  let Cmp : P6Comparison.P6Exact X A.Q ∨
      P6Comparison.P6Epsilon X A.Q := p6ComparisonObligation X A
  exact ⟨A, B, H, R, Cmp⟩

end LeanFormal.IUT.N8Closure.N8RouteClosure
