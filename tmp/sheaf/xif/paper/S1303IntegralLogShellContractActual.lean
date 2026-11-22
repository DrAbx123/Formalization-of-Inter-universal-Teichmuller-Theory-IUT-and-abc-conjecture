import tmp.sheaf.xif.paper.S1270NontrivialCapsuleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice

/-! # S1303: actual integral log-shell lattice in a capsule contract

S1270 uses IQSpan (the rational span) as Shell, which is a Q-vector and loses
the integral Z_p lattice.  This file instead uses the actual
`integralLogShellLattice : Submodule Z_p K` on each actual finite place,
viewed as a Z-module so that one coefficient ring can serve all places.

The contract coefficient ring is Z (not Q): the lattice carrier is retained.
The exact loss is the Z_p-linear structure uniformly across varying p; the
polyIso below is Z-linear and uses the actual integral lattice, not IQSpan.
No PUnit and no Q-span surrogate is used for the shell module. -/

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1303IntegralLogShellContractActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual

universe ua uv upi umon ui
variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual integral log-shell lattice at an actual finite place. -/
abbrev actualIntegralLogShellLattice
    (vQ : ActualValuation) (v : actualPlace I vQ) : Type ua :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  ↥(integralLogShellLattice (K := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) v)
      (p := vQ.1))

noncomputable instance actualIntegralLogShellLatticeModule
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    Module ℤ (actualIntegralLogShellLattice I vQ v) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  exact Module.restrictScalars ℤ ℤ_[vQ.1] (actualIntegralLogShellLattice I vQ v)

noncomputable instance actualIntegralLogShellLatticeAddCommMonoid
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    AddCommMonoid (actualIntegralLogShellLattice I vQ v) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  infer_instance

/-- Actual integral log-shell family over all rational valuations and actual
finite places, as Z-modules. -/
noncomputable def actualIntegralLogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℤ (actualPlace I) j where
  Shell := fun _ vQ v => actualIntegralLogShellLattice I vQ v
  addCommMonoid := fun _ vQ v => actualIntegralLogShellLatticeAddCommMonoid I vQ v
  module := fun _ vQ v => actualIntegralLogShellLatticeModule I vQ v

/-- Actual poly-isomorphism on the integral lattice: reverse the labels and
negate each lattice.  This is Z-linear and does not go through IQSpan. -/
noncomputable def actualIntegralPolyIso (j : Nat) :
    PolyIsoAction (actualIntegralLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun _ vQ v =>
    (LinearEquiv.neg ℤ :
      actualIntegralLogShellLattice I vQ v ≃ₗ[ℤ]
        actualIntegralLogShellLattice I vQ v)

/-- The actual integral-log-shell capsule contract.  Coefficient ring is Z;
the shell is the actual Z_p lattice, not its Q-span. -/
noncomputable def actualIntegralCapsuleContract :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, 0, 0, ua, ua}
      ℤ l V I where
  procession := (canonicalCapsuleTheaterAssignment I 0).toProcession 0
  VQ := ActualValuation
  place := actualPlace I
  fintypePlace := fun vQ =>
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  logShell := fun j => actualIntegralLogShellFamily I j.val
  polyIso := fun j => actualIntegralPolyIso I j.val

@[simp] theorem actualIntegralCapsuleContract_logShell
    (j : Fin (capsuleLevels l)) :
    (actualIntegralCapsuleContract I).logShell j =
      actualIntegralLogShellFamily I j.val := rfl

@[simp] theorem actualIntegralCapsuleContract_polyIso
    (j : Fin (capsuleLevels l)) :
    (actualIntegralCapsuleContract I).polyIso j =
      actualIntegralPolyIso I j.val := rfl

theorem actualIntegralShell_eq_lattice
    (j : Nat) (i : Capsule j) (vQ : ActualValuation)
    (v : actualPlace I vQ) :
    (actualIntegralLogShellFamily I j).Shell i vQ v =
      actualIntegralLogShellLattice I vQ v := rfl

end LeanFormal.IUT.XiFPaper.S1303IntegralLogShellContractActual

end
