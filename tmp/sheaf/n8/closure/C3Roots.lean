import LeanFormal.IUT.IUTII.Kummer.NatRootSystem
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import Mathlib

/-!
# C3 roots in the algebraic closure

Correct root-system domain: roots of a local completion unit are taken in
an algebraic closure of the completion, not in the discrete-valuation
completion itself.  Uses the `rootSystemOfAlgClosed` donor.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.C3Roots

open LeanFormal.IUT

universe u

variable {K : Type u} [Field K]

/-- Map a local unit into the algebraic closure of its field. -/
noncomputable def unitToAlgClosed (u : Kˣ) : (AlgebraicClosure K)ˣ :=
  Units.mk0 (algebraMap K (AlgebraicClosure K) (u : K)) (by
    intro h
    apply u.ne_zero
    apply (algebraMap K (AlgebraicClosure K)).injective
    simpa using h)

/-- The correct-domain natural root system of a local completion unit. -/
noncomputable def algClosedRootSystem (u : Kˣ) : NatRootSystem (unitToAlgClosed u) :=
  AlgebraicClosureRootSystem.rootSystemOfAlgClosed (unitToAlgClosed u)

theorem algClosedRootSystem_pow_self (u : Kˣ) (n : Nat) (hn : n ≠ 0) :
    (algClosedRootSystem u).root n ^ n = unitToAlgClosed u :=
  NatRootSystem.pow_self (algClosedRootSystem u) n hn


/-- Root system of an actual finite-place q candidate, in the algebraic
closure of the local completion. -/
noncomputable def qCandidateRootSystem
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) (q : NumberFieldFinitePlace.FinitePlaceQCandidate place) :
    NatRootSystem (unitToAlgClosed (Units.mk0 q.q q.q_ne_zero)) :=
  algClosedRootSystem (Units.mk0 q.q q.q_ne_zero)

theorem qCandidateRootSystem_pow_self
    {K : Type u} [Field K] [NumberField K]
    (place : NumberField.FinitePlace K) (q : NumberFieldFinitePlace.FinitePlaceQCandidate place)
    (n : Nat) (hn : n ≠ 0) :
    (qCandidateRootSystem place q).root n ^ n =
      unitToAlgClosed (Units.mk0 q.q q.q_ne_zero) :=
  NatRootSystem.pow_self (qCandidateRootSystem place q) n hn

end LeanFormal.IUT.N8Closure.C3Roots