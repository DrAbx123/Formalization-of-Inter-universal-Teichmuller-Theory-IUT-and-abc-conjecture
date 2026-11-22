import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceVerticalRationalCarrier
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogShellLattice
import LeanFormal.IUT.IUTII.Frobenioid.Example36LogDomainActual

set_option relaxedAutoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

/-!
# L0.4 actual source card/type

Scratch.  Audit/instantiate the actual source card/type with no free field.
The actual objects used are the production source rational carrier
`Example36SourceVerticalRationalCarrier.sourceVerticalRationalCarrierData` and the
production actual local integral log-shell `integralLogShell` at the concrete
Gaussian place (`Example36LogShellLattice`).  The frozen cards
`SourceLogShellCard`, `SourceFrobeniusLogShellCard`, and
`SourceLogShellFrobeniusCard` are inhabited by those actual objects, not by an
arbitrary/alias carrier.  No production edits; no card.
-/

noncomputable section

namespace LeanFormal.IUT.SourceCardActual

open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

universe u

/-! ## 1. The actual source rational carrier -/

theorem sourceVerticalRationalCarrierData_nonempty
    {F : Type u} [Field F] [NumberField F]
    {F' : Type u} [Field F'] [NumberField F']
    (T : PlaceLocalizationTransport (numberFieldGlobalPlaceData (F := F))
      (numberFieldGlobalPlaceData (F := F'))) (w : HeightOneSpectrum (𝓞 F')) :
    Nonempty (SourceVerticalRationalCarrierData (F := F) T w) :=
  ⟨sourceVerticalRationalCarrierData (F := F) T w⟩

/-! ## 2. The actual local integral log-shell -/

/-- The actual source log-shell: the production integral log-shell at the
concrete Gaussian place. -/
abbrev actualLogShell : AddSubgroup concreteLogShellField :=
  integralLogShell (K := concreteLogShellField) (p := concreteRationalPrime)

theorem actualLogShell_isOpen :
    IsOpen (actualLogShell : Set concreteLogShellField) :=
  concrete_isOpen_integralLogShell

theorem actualLogShell_isCompact :
    IsCompact (actualLogShell : Set concreteLogShellField) :=
  concrete_isCompact_integralLogShell

theorem actualLogShell_one_mem :
    (1 : concreteLogShellField) ∈ actualLogShell := by
  have h : (1 : concreteLogShellField) ∈
      (Integers concreteLogShellField : Set concreteLogShellField) :=
    Subring.one_mem _
  simpa using concrete_integers_subset_integralLogShell h

theorem concreteRationalPrime_cast_ne_zero :
    (concreteRationalPrime : concreteLogShellField) ≠ 0 := by
  have hp : (concreteRationalPrime : ℕ) ≠ 0 :=
    (Fact.out : Nat.Prime concreteRationalPrime).ne_zero
  exact_mod_cast hp

/-- Actual p-power multiplication is additive on the actual log-shell. -/
theorem actualLogShell_p_mul_mem {x : concreteLogShellField}
    (hx : x ∈ actualLogShell) :
    (concreteRationalPrime : concreteLogShellField) * x ∈ actualLogShell := by
  have h := integralLogShell_padicInt_mul_mem
    (K := concreteLogShellField) (p := concreteRationalPrime)
    (concreteRationalPrime : ℤ_[concreteRationalPrime]) hx
  simpa using h

/-- Actual multiplication by p as an additive equivalence of the local field. -/
noncomputable def pMulAddEquiv :
    concreteLogShellField ≃+ concreteLogShellField where
  toFun x := (concreteRationalPrime : concreteLogShellField) * x
  invFun x := x / (concreteRationalPrime : concreteLogShellField)
  left_inv x := mul_div_cancel_left₀ x concreteRationalPrime_cast_ne_zero
  right_inv x := mul_div_cancel₀ x concreteRationalPrime_cast_ne_zero
  map_add' x y := by ring

/-! ## 3. Frozen log-shell cards inhabited by the actual object -/

noncomputable def actualSourceLogShellCard :
    SourceLogShellCard concreteLogShellField where
  shell := actualLogShell
  shell_isOpen := actualLogShell_isOpen
  shell_isCompact := actualLogShell_isCompact

noncomputable def actualSourceFrobeniusLogShellCard :
    SourceFrobeniusLogShellCard concreteLogShellField where
  shell := actualLogShell
  frobenius := pMulAddEquiv
  frobenius_preserves_shell := by
    intro x hx
    exact actualLogShell_p_mul_mem hx

/-- The full frozen source log-shell/Frobenius card, inhabited by the actual
integral log-shell and the actual p-power action. -/
noncomputable def actualSourceLogShellFrobeniusCard (l : PrimeGeFive) :
    SourceLogShellFrobeniusCard l where
  LogShell := {x : concreteLogShellField // x ∈ actualLogShell}
  toLocalField := Subtype.val
  toLocalField_injective := Subtype.val_injective
  frobenius := fun x => ⟨(concreteRationalPrime : concreteLogShellField) * x.1,
    actualLogShell_p_mul_mem x.2⟩
  frobenius_action := fun x => rfl
  frobenius_nontrivial := by
    refine ⟨⟨1, actualLogShell_one_mem⟩, ?_⟩
    intro h
    have hv := congrArg Subtype.val h
    dsimp at hv
    have hp1 : (concreteRationalPrime : concreteLogShellField) ≠ 1 := by
      intro hP
      have hnat : concreteRationalPrime = 1 := by exact_mod_cast hP
      exact (Fact.out : Nat.Prime concreteRationalPrime).one_lt.ne' hnat
    exact hp1 (by simpa using hv)


/-- The frozen local source log-shell card is realized by the actual integral
log-shell. -/
theorem sourceLogShellCard_realized :
    SourceLogShellCardRealized concreteLogShellField :=
  ⟨actualSourceLogShellCard⟩

/-- The frozen local source Frobenius-log-shell card is realized by the actual
integral log-shell and actual p-power action. -/
theorem sourceFrobeniusLogShellCard_realized :
    SourceFrobeniusLogShellCardRealized concreteLogShellField :=
  ⟨actualSourceFrobeniusLogShellCard⟩

/-- The full source log-shell/Frobenius card is inhabited by the actual object. -/
theorem sourceLogShellFrobeniusCard_nonempty (l : PrimeGeFive) :
    Nonempty (SourceLogShellFrobeniusCard l) :=
  ⟨actualSourceLogShellFrobeniusCard l⟩

end LeanFormal.IUT.SourceCardActual

end