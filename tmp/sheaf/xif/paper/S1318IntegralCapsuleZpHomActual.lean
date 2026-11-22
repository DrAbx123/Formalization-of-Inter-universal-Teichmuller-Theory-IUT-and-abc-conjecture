import tmp.sheaf.xif.paper.S1270NontrivialCapsuleActual
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice

/-! # S1318: integral capsule with valuation-dependent coefficient ring

New structure, not a modification of `SourceProcessionCapsuleContract`:
the coefficient ring is `R : VQ -> Type` with a `CommSemiring (R vQ)` for
each valuation, and each shell is a module over `R vQ`.  For the actual
contract `R vQ = ℤ_[vQ.1]` and `Shell` is the actual
`integralLogShellLattice : Submodule ℤ_[p] K`.  No A = ℤ collapse, no IQSpan,
no Q-span, no PUnit. -/

noncomputable section
open scoped TensorProduct
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1318IntegralCapsuleZpHomActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.S1270NontrivialCapsuleActual

universe ua uv upi umon ui uVQ uPlace uR uShell

/-! ## 1. Log-shell family over a valuation-dependent coefficient ring -/

structure LogShellFamilyZp {VQ : Type uVQ} (R : VQ → Type uR)
    [commSemiringR : ∀ vQ, CommSemiring (R vQ)]
    (Place : VQ → Type uPlace) (j : Nat) where
  Shell : (i : Capsule j) → (vQ : VQ) → Place vQ → Type uShell
  [addCommMonoid : ∀ i vQ v, AddCommMonoid (Shell i vQ v)]
  [module : ∀ i vQ v, Module (R vQ) (Shell i vQ v)]

attribute [instance] LogShellFamilyZp.addCommMonoid LogShellFamilyZp.module

/-! ## 2. Poly-isomorphism over the family -/

structure PolyIsoActionZp {VQ : Type uVQ} {R : VQ → Type uR}
    [∀ vQ, CommSemiring (R vQ)] {Place : VQ → Type uPlace} {j : Nat}
    (L : LogShellFamilyZp R Place j) where
  labelPerm : Capsule j ≃ Capsule j
  shellEquiv : ∀ i (vQ : VQ) (v : Place vQ),
    L.Shell i vQ v ≃ₗ[R vQ] L.Shell (labelPerm i) vQ v

/-! ## 3. The actual valuation-dependent contract -/

structure SourceProcessionCapsuleContractZp (l : PrimeGeFive) (V : Type uv)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) where
  procession : Procession.{uv, umon, upi, ua} l V
  VQ : Type uVQ
  place : VQ → Type uPlace
  [fintypePlace : ∀ vQ, Fintype (place vQ)]
  R : VQ → Type uR
  [commSemiringR : ∀ vQ, CommSemiring (R vQ)]
  logShell : (j : Fin (capsuleLevels l)) →
    LogShellFamilyZp.{uVQ, uPlace, uR, uShell} R place j.val
  polyIso : (j : Fin (capsuleLevels l)) →
    PolyIsoActionZp.{uVQ, uPlace, uR, uShell} (logShell j)

attribute [instance] SourceProcessionCapsuleContractZp.fintypePlace
  SourceProcessionCapsuleContractZp.commSemiringR

/-! ## 4. Actual data: R vQ = ℤ_[vQ.1], Shell = integralLogShellLattice -/

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

noncomputable abbrev actualZpR (vQ : ActualValuation) : Type :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  ℤ_[vQ.1]

noncomputable instance actualZpRCommSemiring (vQ : ActualValuation) :
    CommSemiring (actualZpR vQ) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  infer_instance

noncomputable abbrev actualZpShell
    (vQ : ActualValuation) (v : actualPlace I vQ) : Type ua :=
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  ↥(integralLogShellLattice
      (K := CommonPrimeCompletion (K := I.initial.arithmetic.Fmod) v)
      (p := vQ.1))

noncomputable instance actualZpShellAddCommMonoid
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    AddCommMonoid (actualZpShell I vQ v) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  infer_instance

noncomputable instance actualZpShellModule
    (vQ : ActualValuation) (v : actualPlace I vQ) :
    Module (actualZpR vQ) (actualZpShell I vQ v) := by
  letI : Fact vQ.1.Prime := ⟨vQ.2⟩
  infer_instance

noncomputable def actualZpLogShellFamily (j : Nat) :
    LogShellFamilyZp (actualZpR) (actualPlace I) j where
  Shell := fun _ vQ v => actualZpShell I vQ v
  addCommMonoid := fun _ vQ v => actualZpShellAddCommMonoid I vQ v
  module := fun _ vQ v => actualZpShellModule I vQ v

noncomputable def actualZpPolyIso (j : Nat) :
    PolyIsoActionZp (actualZpLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun _ vQ v =>
    (LinearEquiv.neg (actualZpR vQ) :
      actualZpShell I vQ v ≃ₗ[actualZpR vQ] actualZpShell I vQ v)

noncomputable def actualZpCapsuleContract :
    SourceProcessionCapsuleContractZp l V I where
  procession := (canonicalCapsuleTheaterAssignment I 0).toProcession 0
  VQ := ActualValuation
  place := actualPlace I
  fintypePlace := fun vQ =>
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  R := actualZpR
  commSemiringR := fun vQ => actualZpRCommSemiring vQ
  logShell := fun j => actualZpLogShellFamily I j.val
  polyIso := fun j => actualZpPolyIso I j.val

@[simp] theorem actualZpCapsuleContract_logShell
    (j : Fin (capsuleLevels l)) :
    (actualZpCapsuleContract I).logShell j = actualZpLogShellFamily I j.val :=
  rfl

@[simp] theorem actualZpCapsuleContract_polyIso
    (j : Fin (capsuleLevels l)) :
    (actualZpCapsuleContract I).polyIso j = actualZpPolyIso I j.val :=
  rfl

theorem actualZpShell_eq_lattice
    (j : Nat) (i : Capsule j) (vQ : ActualValuation)
    (v : actualPlace I vQ) :
    (actualZpLogShellFamily I j).Shell i vQ v = actualZpShell I vQ v := rfl

theorem actualZpR_eq_padicIntegers (vQ : ActualValuation) :
    actualZpR vQ =
      (letI : Fact vQ.1.Prime := ⟨vQ.2⟩; ℤ_[vQ.1]) := rfl

end LeanFormal.IUT.XiFPaper.S1318IntegralCapsuleZpHomActual

end
