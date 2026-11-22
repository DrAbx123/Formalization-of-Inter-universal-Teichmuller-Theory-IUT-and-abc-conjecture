import LeanFormal.IUT.IUTIII.Theorem311.SourceProcessionCapsuleOriginalInput
import LeanFormal.IUT.IUTII.Kummer.SourceLocalLogShellDatum
import LeanFormal.IUT.IUTII.Kummer.SourceLogShellActualTensorSpan
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.LogShellSaturation
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFullPrimePacket
import Mathlib.Data.Fin.Rev

/-!
# S1313: the actual integral log-shell as the capsule log-shell module

S1301 audited two earlier capsule contracts and found the same defect in both:
the log-shell field was not the paper's integral log-shell.

* S1270NontrivialCapsuleActual used (sourceLocalLogShellDatum ...).IQSpan, the
  Q-span of the local log-shell.  That is a Q-vector space: division by every
  nonzero scalar is available, so the integral (Z and Z_p) structure of III,
  Definition 1.1, (i) is lost.
* S1264SourceCapsuleInd1Actual used the whole local field CommonPrimeCompletion
  v as the shell.  That is a field, hence a Q_p-vector space, and again not the
  integral log-shell.

This file replaces both substitutes by the actual integral object.  For an
arbitrary original input I it builds SourceProcessionCapsuleContract values whose
logShell field is, at every capsule label, rational valuation and actual finite
place, the integral log-shell

  I_v = (p*_v)^(-1) * log_v(O^×_{K_v})  subset  K_v

as a lattice (additive subgroup / submodule) of the common-prime completion
K_v = CommonPrimeCompletion v:

* the Z-module of the additive subgroup integralLogShell (K := K_v) (p := p),
  an actual compact additive subgroup of K_v with add and the canonical
  Z-module structure, used by actualIntegralCapsuleContract over all rational
  valuations, so the valuation type is still the genuine infinite set of
  rational primes;
* the Z_p-lattice integralLogShellLattice (K := K_v) (p := l), a genuine
  Submodule Z_[l] K_v, free of finite rank [K_v : Q_[l]], used by
  actualPadicLatticeCapsuleContract at the fixed arithmetic prime l.

The ingredient theorems of LeanFormal.IUT.IUTII.Kummer are kept as the carrier
identification (sourceLocalLogShellDatum_logShell_eq_integralLogShell) and the
tensor-donor comparison (SourceLogShellActualIQTensor): the IQSpan and
SourceLogShellActualIQTensor objects are exactly the Q-spans of the integral
shells constructed here, not replacements for them.

The integral structure is not asserted vacuously.  We prove that the shell is a
proper lattice in its own Q_p-span:
exists_padicSpan_not_mem_integralLogShell exhibits an element of
Submodule.span Q_[p] I outside I, obtained from the primitive (not divisible by
p inside the shell) element supplied by integralLogShell_primitive_notMem_smul.
Consequently the shell is not the whole local field and not a Q- or Q_p-vector
space surrogate, while its Q-span is exactly the IQSpan used by S1270.
-/

noncomputable section

open scoped TensorProduct Pointwise
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.FinitePadicIntegralLattice

universe ua uv upi umon ui

/-! ## 1. Integrality certificates for the actual log-shell

These statements are local-field facts, independent of the capsule data. -/

section IntegralityCertificate

variable {K : Type ua} [NormedField K] [CharZero K] [CompleteSpace K]
  [IsUltrametricDist K] [ProperSpace K] {p : Nat} [Fact p.Prime]
  [NormedAlgebra ℚ_[p] K] [FiniteDimensional ℚ_[p] K]

/-- The actual integral log-shell contains 1: the integer ring lies inside it,
so it is a nonzero lattice. -/
theorem one_mem_integralLogShell : (1 : K) ∈ integralLogShell (K := K) (p := p) :=
  integers_subset_integralLogShell (p := p) (Integers K).one_mem

/-- A primitive element of the actual integral log-shell: it is not divisible
by p inside the shell.  This is the saturation theorem of the local-field
layer applied to the unit 1 of the shell. -/
theorem integralLogShell_exists_primitive :
    ∃ (n : Nat) (z : K), z ∈ integralLogShell (K := K) (p := p) ∧
      (1 : K) = (p : ℤ_[p]) ^ n • z ∧
      z ∉ (p : ℤ_[p]) • (integralLogShell (K := K) (p := p) : Set K) :=
  integralLogShell_primitive_notMem_smul (K := K) (p := p)
    (one_mem_integralLogShell (K := K) (p := p)) one_ne_zero

/-- The integral log-shell is a proper lattice in its own Q_p-span: scaling a
primitive shell element by p^(-1) leaves the shell.  This is exactly the
integral structure that a Q-span or a field surrogate does not retain. -/
theorem exists_padicSpan_not_mem_integralLogShell :
    ∃ x : K, x ∈ Submodule.span ℚ_[p] (integralLogShell (K := K) (p := p) : Set K) ∧
      x ∉ integralLogShell (K := K) (p := p) := by
  obtain ⟨n, z, hzmem, -, hznot⟩ := integralLogShell_exists_primitive (K := K) (p := p)
  refine ⟨(p : ℚ_[p])⁻¹ • z, ?_, ?_⟩
  · exact (Submodule.span ℚ_[p] (integralLogShell (K := K) (p := p) : Set K)).smul_mem
      ((p : ℚ_[p])⁻¹) (Submodule.subset_span hzmem)
  · intro hw
    apply hznot
    refine Set.mem_smul_set.mpr ⟨(p : ℚ_[p])⁻¹ • z, hw, ?_⟩
    rw [padicInteger_smul_eq, smul_smul]
    simp only [PadicInt.coe_natCast]
    have hpne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
    rw [mul_inv_cancel₀ hpne, one_smul]

/-- The actual integral log-shell is not the whole local field. -/
theorem integralLogShell_ne_univ :
    (integralLogShell (K := K) (p := p) : Set K) ≠ Set.univ := by
  obtain ⟨x, -, hxnot⟩ := exists_padicSpan_not_mem_integralLogShell (K := K) (p := p)
  intro huniv
  have hxuniv : x ∉ (Set.univ : Set K) := by
    rw [← huniv]
    simpa using hxnot
  exact hxuniv (Set.mem_univ x)

/-- The integral log-shell is not closed under division by p: the actual
log-shell is a Z_p-lattice, not a Q_p-vector space (a field surrogate is closed
under every nonzero scalar). -/
theorem not_closed_under_inv_smul :
    ¬ (∀ x ∈ integralLogShell (K := K) (p := p),
        (p : ℚ_[p])⁻¹ • x ∈ integralLogShell (K := K) (p := p)) := by
  obtain ⟨n, z, hzmem, -, hznot⟩ := integralLogShell_exists_primitive (K := K) (p := p)
  intro h
  apply hznot
  refine Set.mem_smul_set.mpr ⟨(p : ℚ_[p])⁻¹ • z, h z hzmem, ?_⟩
  rw [padicInteger_smul_eq, smul_smul]
  simp only [PadicInt.coe_natCast]
  have hpne : (p : ℚ_[p]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero
  rw [mul_inv_cancel₀ hpne, one_smul]

/-- The Q_p-span of the integral log-shell is the whole local field, so the
strict inclusion above is the Z_p-lattice, not a failure of spanning. -/
theorem span_padic_integralLogShell_eq_top :
    Submodule.span ℚ_[p] (integralLogShell (K := K) (p := p) : Set K) = ⊤ :=
  span_padic_integralLogShellLattice_eq_top (K := K) (p := p)

end IntegralityCertificate

/-! ## 2. The integral log-shell family over all actual rational valuations -/

/-- The nonarchimedean valuations of the rational field: the actual infinite
set VQ of rational primes. -/
abbrev ActualIntegralValuation : Type := {p : Nat // p.Prime}

theorem actualIntegralValuation_five_ne_seven :
    (⟨5, by norm_num⟩ : ActualIntegralValuation) ≠ ⟨7, by norm_num⟩ := by
  intro h
  have hv := congrArg Subtype.val h
  norm_num at hv

/-- The valuation type is not a one-point index. -/
theorem actualIntegralValuation_nontrivial : Nontrivial ActualIntegralValuation where
  exists_pair_ne :=
    ⟨⟨5, by norm_num⟩, ⟨7, by norm_num⟩, actualIntegralValuation_five_ne_seven⟩

section IntegralContract

local instance actualIntegralValuationFact (vQ : ActualIntegralValuation) :
    Fact vQ.1.Prime := ⟨vQ.2⟩

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual finite-place fiber over a rational valuation: the actual finite
places of the source number field above vQ. -/
def actualIntegralPlace : ActualIntegralValuation → Type ua :=
  fun vQ => FinitePlaceAtPrime I.initial.arithmetic.Fmod vQ.1

/-- The actual local log-shell datum at an actual place. -/
abbrev actualIntegralLocalDatum (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) : SourceLogShellDatum :=
  sourceLocalLogShellDatum (p := vQ.1) v

/-- The actual integral log-shell I_v = (p*_v)^(-1) log_v(O^×_{K_v}) of the
common-prime completion, as an additive subgroup (a Z-submodule) of K_v. -/
abbrev actualIntegralLogShell (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) : AddSubgroup (CommonPrimeCompletion v) :=
  integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The same actual integral log-shell as the genuine Z_p-submodule of K_v. -/
abbrev actualIntegralLogShellLattice (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Submodule ℤ_[vQ.1] (CommonPrimeCompletion v) :=
  integralLogShellLattice (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The integral log-shell family: at every capsule label, rational valuation
and actual finite place, the actual integral log-shell as a Z-module. -/
noncomputable def integralLogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℤ (actualIntegralPlace I) j where
  Shell := fun _ vQ v => ↥(actualIntegralLogShell I vQ v)
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The first field of the family is literally the actual integral log-shell. -/
theorem integralLogShellFamily_Shell (j : Nat) (i : Capsule j)
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (integralLogShellFamily I j).Shell i vQ v = ↥(actualIntegralLogShell I vQ v) := rfl

/-- The integral shell is the actual compact image (p*_v)^(-1) log_v(O^×) of
the local units, not an abstract span. -/
theorem actualIntegralLogShell_eq_range (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      Set.range (fun u : (Integers (CommonPrimeCompletion v))ˣ =>
        (logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ *
          unitLog (K := CommonPrimeCompletion v) u) :=
  coe_integralLogShell_eq_range (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The integral shell is the log-shell of the actual source local datum. -/
theorem actualIntegralLogShell_eq_sourceLocalLogShellDatum
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      (actualIntegralLocalDatum I vQ v).logShell :=
  (sourceLocalLogShellDatum_logShell_eq_integralLogShell (p := vQ.1) v).symm

/-- The Z-module carrier is the carrier of the actual Z_p-lattice. -/
theorem actualIntegralLogShell_eq_latticeCarrier (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      (actualIntegralLogShellLattice I vQ v : Set (CommonPrimeCompletion v)) := rfl

/-- The integral shell is closed under the actual Z_p-scalars. -/
theorem actualIntegralLogShell_padicInt_mul_mem (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) (z : ℤ_[vQ.1]) {x : CommonPrimeCompletion v}
    (hx : x ∈ actualIntegralLogShell I vQ v) :
    algebraMap ℚ_[vQ.1] (CommonPrimeCompletion v) (z : ℚ_[vQ.1]) * x ∈
      actualIntegralLogShell I vQ v :=
  integralLogShell_padicInt_mul_mem (K := CommonPrimeCompletion v) (p := vQ.1) z hx

/-- The additive structure of the shell. -/
theorem actualIntegralLogShell_add_mem (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) {x y : CommonPrimeCompletion v}
    (hx : x ∈ actualIntegralLogShell I vQ v) (hy : y ∈ actualIntegralLogShell I vQ v) :
    x + y ∈ actualIntegralLogShell I vQ v :=
  (actualIntegralLogShell I vQ v).add_mem hx hy

/-- The Z-module structure of the shell: integer multiples stay in the shell
(this is the Module Z instance recorded in the log-shell family). -/
theorem actualIntegralLogShell_int_smul_mem (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) (n : ℤ) {x : CommonPrimeCompletion v}
    (hx : x ∈ actualIntegralLogShell I vQ v) :
    n • x ∈ actualIntegralLogShell I vQ v :=
  (actualIntegralLogShell I vQ v).zsmul_mem hx n

/-- The Q-span of the integral shell is exactly the IQSpan of the source local
datum: S1270's object is the Q-span completion of the shell, not the shell. -/
theorem actualIntegralLogShell_ratSpan_eq_sourceIQSpan
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    Submodule.span ℚ (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      (actualIntegralLocalDatum I vQ v).IQSpan := by
  rw [SourceLogShellDatum.IQSpan, actualIntegralLogShell_eq_sourceLocalLogShellDatum]
  rfl

/-- The Q_p-span of the integral shell is the whole local field. -/
theorem actualIntegralLogShell_span_padic_eq_top (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Submodule.span ℚ_[vQ.1]
      (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) = ⊤ :=
  span_padic_integralLogShell_eq_top (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The integral shell is strictly smaller than its Q_p-span. -/
theorem exists_padicSpan_not_mem_actualIntegralLogShell
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    ∃ x : CommonPrimeCompletion v,
      x ∈ Submodule.span ℚ_[vQ.1]
        (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) ∧
        x ∉ actualIntegralLogShell I vQ v :=
  exists_padicSpan_not_mem_integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The shell is not the whole local field: no field surrogate. -/
theorem actualIntegralLogShell_ne_univ (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) ≠ Set.univ :=
  integralLogShell_ne_univ (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The integral shell is not closed under division by the local prime: it is a
lattice, not a Q_p-vector space. -/
theorem actualIntegralLogShell_not_smul_inv_closed (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    ¬ (∀ x ∈ actualIntegralLogShell I vQ v,
        (vQ.1 : ℚ_[vQ.1])⁻¹ • x ∈ actualIntegralLogShell I vQ v) :=
  not_closed_under_inv_smul (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The poly-isomorphism of the integral contract: label reversal together with
the identity on the integral shells. -/
noncomputable def integralLogShellPolyIso (j : Nat) :
    PolyIsoAction (integralLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun _ _ _ => LinearEquiv.refl ℤ _

/-- The capsule contract whose log-shell field is the actual integral
log-shell, over all actual rational valuations and actual finite-place
fibers. -/
noncomputable def actualIntegralCapsuleContract :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, 0, 0, ua, ua} ℤ l V I where
  procession := (canonicalCapsuleTheaterAssignment I 0).toProcession 0
  VQ := ActualIntegralValuation
  place := actualIntegralPlace I
  fintypePlace := fun vQ =>
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  logShell := fun j => integralLogShellFamily I j.val
  polyIso := fun j => integralLogShellPolyIso I j.val

/-- The first field of the contract is the selected actual source procession. -/
theorem actualIntegralCapsuleContract_procession :
    (actualIntegralCapsuleContract I).procession =
      (canonicalCapsuleTheaterAssignment I 0).toProcession 0 := rfl

/-- The log-shell field of the contract is the integral family above. -/
theorem actualIntegralCapsuleContract_logShell (j : Fin (capsuleLevels l)) :
    (actualIntegralCapsuleContract I).logShell j = integralLogShellFamily I j.val := rfl

/-- The poly-isomorphism field is the actual action defined above. -/
theorem actualIntegralCapsuleContract_polyIso (j : Fin (capsuleLevels l)) :
    (actualIntegralCapsuleContract I).polyIso j = integralLogShellPolyIso I j.val := rfl

/-- The first field of the contract's log-shell family is the actual integral
log-shell itself. -/
theorem actualIntegralCapsuleContract_shell (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    ((actualIntegralCapsuleContract I).logShell j).Shell i vQ v =
      ↥(actualIntegralLogShell I vQ v) := rfl

/-- The theater at a capsule label is the actual source theater at the selected
source index. -/
theorem actualIntegralCapsuleContract_theater (j : Fin (capsuleLevels l))
    (i : Capsule j.val) :
    ((actualIntegralCapsuleContract I).procession).toPrimeStripOf.theater j i =
      I.theaterAt (Int.ofNat i.val) 0 := rfl

/-- The prime strip at a capsule label is the actual source prime strip. -/
theorem actualIntegralCapsuleContract_primeStrip (j : Fin (capsuleLevels l))
    (i : Capsule j.val) :
    ((actualIntegralCapsuleContract I).procession).toPrimeStripOf.primeStrip j i =
      I.primeStripAt (Int.ofNat i.val) 0 := rfl

/-- The actual theater family of the integral contract is nonconstant. -/
theorem actualIntegralCapsuleContract_theater_nontrivial :
    ∃ (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualIntegralCapsuleContract I).procession).toPrimeStripOf.theater j i ≠
        ((actualIntegralCapsuleContract I).procession).toPrimeStripOf.theater j i' := by
  simpa [actualIntegralCapsuleContract] using
    canonicalCapsuleTheaterAssignment.theater_nontrivial I 0

/-- The actual prime-strip family of the integral contract is nonconstant. -/
theorem actualIntegralCapsuleContract_primeStrip_nontrivial :
    ∃ (j : Fin (capsuleLevels l)) (i i' : Capsule j.val),
      ((actualIntegralCapsuleContract I).procession).toPrimeStripOf.primeStrip j i ≠
        ((actualIntegralCapsuleContract I).procession).toPrimeStripOf.primeStrip j i' := by
  simpa [actualIntegralCapsuleContract] using
    canonicalCapsuleTheaterAssignment.primeStrip_nontrivial I 0

/-- The label permutation of the integral action is not the identity. -/
theorem actualIntegralLogShellPolyIso_labelPerm_ne_refl :
    (integralLogShellPolyIso I 1).labelPerm ≠ Equiv.refl (Capsule 1) := by
  intro h
  have h0 := congrArg (fun e : Capsule 1 ≃ Capsule 1 => e ⟨0, by norm_num⟩) h
  simp [integralLogShellPolyIso, Fin.revPerm] at h0

/-- The poly-isomorphism of the integral contract is not the identity action. -/
theorem actualIntegralLogShellPolyIso_ne_refl :
    integralLogShellPolyIso I 1 ≠ PolyIsoAction.refl (integralLogShellFamily I 1) := by
  intro h
  exact actualIntegralLogShellPolyIso_labelPerm_ne_refl I
    (congrArg PolyIsoAction.labelPerm h)

/-- The tensor packet over the integral shells distributes as the tensor of the
integral log-shell lattices at every tuple of actual places. -/
noncomputable def integralTensorPacketEquiv (j : Nat) (vQ : ActualIntegralValuation) :
    TensorPacket (integralLogShellFamily I j) vQ ≃ₗ[ℤ]
      ((t : (i : Capsule j) → actualIntegralPlace I vQ) →
        ⨂[ℤ] i, ↥(actualIntegralLogShell I vQ (t i))) := by
  letI : Fintype (actualIntegralPlace I vQ) :=
    @fintype_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  exact tensorPacketEquiv (integralLogShellFamily I j) vQ

/-- The actual IQ tensor donor of SourceLogShellActualTensorSpan is generated,
over Q, by the integral log-shells constructed here: the integral pure tensors
of the actual local source data span the donor. -/
theorem actualIntegralTensors_span_eq_top (vQ : ActualIntegralValuation) :
    Submodule.span ℚ (sourceLogShellActualIntegralTensors
      (fun v : actualIntegralPlace I vQ => actualIntegralLocalDatum I vQ v)) = ⊤ := by
  letI : Finite (actualIntegralPlace I vQ) :=
    @finite_fullPrimePlaces I.initial.arithmetic.Fmod _ _ vQ.1 ⟨vQ.2⟩
  exact sourceLogShellActualIntegralTensors_span_eq_top
    (fun v : actualIntegralPlace I vQ => actualIntegralLocalDatum I vQ v)

/-- The actual finite-place fiber over 5 is nonempty. -/
theorem actualIntegralPlace_five_nonempty :
    Nonempty (actualIntegralPlace I (⟨5, by norm_num⟩ : ActualIntegralValuation)) :=
  @nonempty_fullPrimePlaces I.initial.arithmetic.Fmod _ _ 5 ⟨by norm_num⟩

end IntegralContract

/-! ## 3. The Z_p-lattice contract at the arithmetic prime l -/

section PadicLatticeContract

local instance factPrimeOfPrimeGeFive (l : PrimeGeFive) : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- The actual rational finite place at the arithmetic prime l. -/
abbrev RationalPlaceAt (l : PrimeGeFive) : Type := FinitePlaceAtPrime ℚ l.value

variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The actual finite places of the source number field above l. -/
abbrev PadicLatticePlace : Type ua :=
  FinitePlaceAtPrime I.initial.arithmetic.Fmod l.value

/-- The actual integral log-shell as the genuine Z_[l]-submodule of the
common-prime completion. -/
abbrev padicIntegralLogShellLattice (v : PadicLatticePlace I) :
    Submodule ℤ_[l.value] (CommonPrimeCompletion v) :=
  integralLogShellLattice (K := CommonPrimeCompletion v) (p := l.value)

/-- The Z_p-lattice log-shell family at the fixed arithmetic prime l. -/
noncomputable def padicLatticeLogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℤ_[l.value]
      (fun _ : RationalPlaceAt l => PadicLatticePlace I) j where
  Shell := fun _ _ v => ↥(padicIntegralLogShellLattice I v)
  addCommMonoid := fun _ _ _ => inferInstance
  module := fun _ _ _ => inferInstance

/-- The first field of the Z_p family is literally the Z_p-lattice. -/
theorem padicLatticeLogShellFamily_Shell (j : Nat) (i : Capsule j)
    (vQ : RationalPlaceAt l) (v : PadicLatticePlace I) :
    (padicLatticeLogShellFamily I j).Shell i vQ v =
      ↥(padicIntegralLogShellLattice I v) := rfl

/-- The poly-isomorphism of the Z_p contract. -/
noncomputable def padicLatticePolyIso (j : Nat) :
    PolyIsoAction (padicLatticeLogShellFamily I j) where
  labelPerm := Fin.revPerm
  shellEquiv := fun _ _ _ => LinearEquiv.refl ℤ_[l.value] _

/-- The capsule contract whose log-shell field is the actual Z_p-lattice, at
the fixed arithmetic prime l of the initial Theta-data. -/
noncomputable def actualPadicLatticeCapsuleContract :
    SourceProcessionCapsuleContract.{ua, uv, upi, umon, ui, 0, 0, ua, ua}
      ℤ_[l.value] l V I where
  procession := (canonicalCapsuleTheaterAssignment I 0).toProcession 0
  VQ := RationalPlaceAt l
  place := fun _ => PadicLatticePlace I
  fintypePlace := fun _ => inferInstance
  logShell := fun j => padicLatticeLogShellFamily I j.val
  polyIso := fun j => padicLatticePolyIso I j.val

/-- The log-shell field of the Z_p contract is the lattice family above. -/
theorem actualPadicLatticeCapsuleContract_logShell (j : Fin (capsuleLevels l)) :
    (actualPadicLatticeCapsuleContract I).logShell j =
      padicLatticeLogShellFamily I j.val := rfl

/-- The first field of the Z_p contract's log-shell family is the actual
integral log-shell lattice. -/
theorem actualPadicLatticeCapsuleContract_shell (j : Fin (capsuleLevels l))
    (i : Capsule j.val) (vQ : RationalPlaceAt l) (v : PadicLatticePlace I) :
    ((actualPadicLatticeCapsuleContract I).logShell j).Shell i vQ v =
      ↥(padicIntegralLogShellLattice I v) := rfl

/-- The carrier of the Z_p-lattice is the actual integral log-shell. -/
theorem padicIntegralLogShellLattice_eq_integralLogShell (v : PadicLatticePlace I) :
    (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) =
      (integralLogShell (K := CommonPrimeCompletion v) (p := l.value) :
        Set (CommonPrimeCompletion v)) := rfl

/-- The Z_p-module structure of the lattice. -/
theorem padicIntegralLogShellLattice_smul_mem (v : PadicLatticePlace I)
    (z : ℤ_[l.value]) {x : CommonPrimeCompletion v}
    (hx : x ∈ padicIntegralLogShellLattice I v) :
    z • x ∈ padicIntegralLogShellLattice I v :=
  (padicIntegralLogShellLattice I v).smul_mem z hx

/-- The Z_p-lattice is free of finite rank. -/
theorem padicIntegralLogShellLattice_free (v : PadicLatticePlace I) :
    Module.Free ℤ_[l.value] (padicIntegralLogShellLattice I v) := inferInstance

/-- The Z_p-lattice is a finite module. -/
theorem padicIntegralLogShellLattice_finite (v : PadicLatticePlace I) :
    Module.Finite ℤ_[l.value] (padicIntegralLogShellLattice I v) := inferInstance

/-- The rank of the Z_p-lattice is the local degree. -/
theorem padicIntegralLogShellLattice_finrank (v : PadicLatticePlace I) :
    Module.finrank ℤ_[l.value] (padicIntegralLogShellLattice I v) =
      Module.finrank ℚ_[l.value] (CommonPrimeCompletion v) :=
  finrank_integralLogShellLattice (K := CommonPrimeCompletion v) (p := l.value)

/-- The Z_p-lattice is a proper sublattice of its own Q_p-span. -/
theorem exists_padicSpan_not_mem_padicIntegralLogShellLattice
    (v : PadicLatticePlace I) :
    ∃ x : CommonPrimeCompletion v,
      x ∈ Submodule.span ℚ_[l.value]
        (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) ∧
        x ∉ padicIntegralLogShellLattice I v :=
  exists_padicSpan_not_mem_integralLogShell (K := CommonPrimeCompletion v) (p := l.value)

/-- The Z_p-lattice spans the local field over Q_p. -/
theorem padicIntegralLogShellLattice_span_padic_eq_top (v : PadicLatticePlace I) :
    Submodule.span ℚ_[l.value]
      (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) = ⊤ :=
  span_padic_integralLogShellLattice_eq_top (K := CommonPrimeCompletion v) (p := l.value)

/-- The Z_p-lattice is not the whole local field. -/
theorem padicIntegralLogShellLattice_ne_univ (v : PadicLatticePlace I) :
    (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) ≠ Set.univ :=
  integralLogShell_ne_univ (K := CommonPrimeCompletion v) (p := l.value)

/-- The Z_p-lattice is not closed under division by l. -/
theorem padicIntegralLogShellLattice_not_smul_inv_closed (v : PadicLatticePlace I) :
    ¬ (∀ x ∈ padicIntegralLogShellLattice I v,
        (l.value : ℚ_[l.value])⁻¹ • x ∈ padicIntegralLogShellLattice I v) :=
  not_closed_under_inv_smul (K := CommonPrimeCompletion v) (p := l.value)

end PadicLatticeContract

/-! ## 4. Axiom probes -/

#print axioms one_mem_integralLogShell
#print axioms integralLogShell_exists_primitive
#print axioms exists_padicSpan_not_mem_integralLogShell
#print axioms integralLogShell_ne_univ
#print axioms not_closed_under_inv_smul
#print axioms actualIntegralLogShell_eq_sourceLocalLogShellDatum
#print axioms actualIntegralLogShell_eq_range
#print axioms actualIntegralLogShell_padicInt_mul_mem
#print axioms actualIntegralLogShell_add_mem
#print axioms actualIntegralLogShell_int_smul_mem
#print axioms actualIntegralLogShell_ratSpan_eq_sourceIQSpan
#print axioms actualIntegralCapsuleContract
#print axioms actualIntegralCapsuleContract_logShell
#print axioms actualIntegralCapsuleContract_shell
#print axioms actualIntegralCapsuleContract_theater_nontrivial
#print axioms actualIntegralLogShellPolyIso_ne_refl
#print axioms integralTensorPacketEquiv
#print axioms actualIntegralTensors_span_eq_top
#print axioms actualPadicLatticeCapsuleContract
#print axioms actualPadicLatticeCapsuleContract_shell
#print axioms padicIntegralLogShellLattice_smul_mem
#print axioms padicIntegralLogShellLattice_finrank
#print axioms padicIntegralLogShellLattice_ne_univ
#print axioms actualIntegralLogShell_not_smul_inv_closed
#print axioms padicIntegralLogShellLattice_not_smul_inv_closed

end LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
