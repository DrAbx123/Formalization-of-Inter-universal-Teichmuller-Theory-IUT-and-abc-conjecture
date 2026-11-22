import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithm
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmKernel
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmTorsionFinite
import LeanFormal.IUT.Foundations.LocalFields.IntegralUnitLogarithmOpenMap
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverseSharpRadius
import LeanFormal.IUT.Foundations.LocalFields.IntegralLogShellLattice
import LeanFormal.IUT.Foundations.LocalFields.UnscaledUnitLogLattice
import Mathlib.NumberTheory.Padics.ProperSpace
import Mathlib.GroupTheory.Index
import Mathlib.Tactic

/-!
# The actual p-adic logarithm on principal units of a local field

This module assembles the actual p-adic logarithm on the principal-unit
subgroup of a genuine nonarchimedean local field, reusing the tree's
constructed logarithm.  No logarithm is postulated: all analytic content is
the tree's analytic log on the actual principal units 1 + m_k.

## Contents

* (1) The principal-unit subgroup H = 1 + maximal ideal, the actual log
  homomorphism H -> K, its kernel T, its image L, and the genuine exact
  sequence 1 -> T -> H -> L -> 0 (H/T is isomorphic to L).
* (2) Torsion is contained in T; in fact T is exactly the finite-order locus
  of H (using the tree's proved full-unit kernel theorem).  The tree's sharp
  local inverse of the log on the radius p^(-1/(p-1)) is recorded, together
  with the reason it is not a global inverse.
* (3) The image L is the actual local logarithmic image: it is an additive
  subgroup, it is open and compact, it is contained in the tree's actual
  unscaled unit-log lattice, and, after the tree's log-shell scaling, it is
  contained in the actual scaled local log-shell.
* (4) Only cards are frozen for the data not available as actual source data:
  the normalization choice needed to extend the log to K^x, the source
  log-shell, and the Frobenius action on that shell.  No card is inhabited and
  no theorem consumes a card.

## Boundary

* The logarithm, principal units, log-shell and lattice are the tree's actual
  constructions; this file only assembles them and proves the exact-sequence,
  torsion, inverse and image-property statements.
* The concrete instance is the actual p-adic field Q_p (the degree-one
  completion).  No nonabelian, global Frobenioid, theta, q-pilot or Tate
  statement is made.
* The normalization choice extending the log to K^x, the IUT source log-shell
  and the Frobenius action on it are NOT constructed; they are frozen as cards
  only, with no fake log, no fake source and no unproved assumption.
-/

noncomputable section

set_option linter.unusedSectionVars false

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

section ActualLocalFieldLog

variable {K : Type*} [NormedField K] [CharZero K] [CompleteSpace K]
variable [IsUltrametricDist K] [ProperSpace K]

/-! ## 1. The actual log on the principal units -/

/-- The actual p-adic logarithm on a principal unit, as the analytic series
on u - 1; this is the tree's analytic log restricted to the principal units. -/
def principalUnitLog (u : principalUnits (K := K)) : K :=
  log1p (((u : (Integers K)ˣ).val : K) - 1)

theorem principalUnitLog_one :
    principalUnitLog (1 : principalUnits (K := K)) = 0 := by
  change log1p ((((1 : (Integers K)ˣ).val : K)) - 1) = 0
  rw [show (((1 : (Integers K)ˣ).val : K)) = 1 from by simp]
  rw [sub_self, LeanFormal.IUT.LocalFieldLogarithm.log1p_zero]

theorem principalUnitLog_mul (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    (u v : principalUnits (K := K)) :
    principalUnitLog (u * v) = principalUnitLog u + principalUnitLog v := by
  change log1p (((((u : (Integers K)ˣ) * (v : (Integers K)ˣ)).val : K)) - 1) =
    log1p (((u : (Integers K)ˣ).val : K) - 1) +
      log1p (((v : (Integers K)ˣ).val : K) - 1)
  exact LeanFormal.IUT.LocalFieldLogarithm.principalUnitLog_mul (p := p)
    (u : (Integers K)ˣ) (v : (Integers K)ˣ) u.property v.property

theorem principalUnitLog_inv (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    (u : principalUnits (K := K)) :
    principalUnitLog u⁻¹ = -principalUnitLog u := by
  have h := principalUnitLog_mul (K := K) p u u⁻¹
  rw [mul_inv_cancel, principalUnitLog_one] at h
  exact eq_neg_of_add_eq_zero_right h.symm

/-- The actual p-adic logarithm on principal units as a homomorphism into the
additive local field (written multiplicatively). -/
def principalUnitLogHom (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    principalUnits (K := K) →* Multiplicative K where
  toFun u := Multiplicative.ofAdd (principalUnitLog u)
  map_one' := by
    change principalUnitLog (1 : principalUnits (K := K)) = 0
    exact principalUnitLog_one
  map_mul' u v := by
    change principalUnitLog (u * v) = principalUnitLog u + principalUnitLog v
    exact principalUnitLog_mul (K := K) p u v

/-- The kernel T of the actual principal-unit logarithm. -/
def principalUnitLogKernel (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    Subgroup (principalUnits (K := K)) :=
  (principalUnitLogHom (K := K) p).ker

/-- The image L of the actual principal-unit logarithm, as an additive
subgroup of the local field. -/
def principalUnitLogImage (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] : AddSubgroup K where
  carrier := Set.range (principalUnitLog (K := K))
  zero_mem' := ⟨1, principalUnitLog_one⟩
  add_mem' := by
    rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
    exact ⟨u * v, principalUnitLog_mul (K := K) p u v⟩
  neg_mem' := by
    rintro _ ⟨u, rfl⟩
    exact ⟨u⁻¹, principalUnitLog_inv (K := K) p u⟩

/-- The genuine exact sequence 1 -> T -> H -> L -> 0: the quotient of the
principal units by the kernel of the log is isomorphic to the image. -/
def principalUnitLogQuotientEquivImage (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    (principalUnits (K := K)) ⧸ principalUnitLogKernel (K := K) p ≃*
      (principalUnitLogHom (K := K) p).range :=
  QuotientGroup.quotientKerEquivRange (principalUnitLogHom (K := K) p)

/-- The actual log is surjective onto its image by definition of the image. -/
theorem principalUnitLog_surjectiveOnImage (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    Function.Surjective (fun u : principalUnits (K := K) =>
      (⟨principalUnitLog u, Set.mem_range_self u⟩ :
        principalUnitLogImage (K := K) p)) := by
  intro x
  obtain ⟨u, hu⟩ := x.property
  exact ⟨u, Subtype.ext hu⟩

theorem principalUnitLog_eq_zero_of_mem_kernel (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    {u : principalUnits (K := K)} (hu : u ∈ principalUnitLogKernel (K := K) p) :
    principalUnitLog u = 0 := by
  have h' := MonoidHom.mem_ker.mp hu
  have h'' := congrArg Multiplicative.toAdd h'
  change principalUnitLog u = 0 at h''
  exact h''

/-! ## 2. Torsion in the kernel and the non-global inverse -/

/-- The kernel of the principal-unit log is exactly the finite-order locus of
the principal units: this uses the tree's proved full-unit kernel theorem. -/
theorem principalUnitLogKernel_mem_iff (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    (u : principalUnits (K := K)) :
    u ∈ principalUnitLogKernel (K := K) p ↔
      IsOfFinOrder (u : (Integers K)ˣ) := by
  change principalUnitLog u = 0 ↔ IsOfFinOrder (u : (Integers K)ˣ)
  unfold principalUnitLog
  rw [← LeanFormal.IUT.LocalFieldLogarithm.unitLog_eq_log1p (p := p)
    (u : (Integers K)ˣ) u.property]
  exact LeanFormal.IUT.LocalFieldLogarithm.unitLog_eq_zero_iff_isOfFinOrder
    (p := p) _

/-- Torsion is contained in the kernel of the actual log. -/
theorem principalUnitLog_torsion_le_kernel (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    (u : principalUnits (K := K))
    (hu : IsOfFinOrder (u : (Integers K)ˣ)) :
    u ∈ principalUnitLogKernel (K := K) p :=
  (principalUnitLogKernel_mem_iff (K := K) p u).mpr hu

theorem principalUnitLogKernel_eq_torsion_locus (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    (principalUnitLogKernel (K := K) p : Set (principalUnits (K := K))) =
      {u : principalUnits (K := K) | IsOfFinOrder (u : (Integers K)ˣ)} := by
  ext u
  exact principalUnitLogKernel_mem_iff (K := K) p u

theorem principalUnitLog_not_injective_of_nontrivialKernel (p : ℕ)
    [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    (h : ∃ u : principalUnits (K := K), u ≠ 1 ∧
      u ∈ principalUnitLogKernel (K := K) p) :
    ¬ Function.Injective (principalUnitLog (K := K)) := by
  rintro hinj
  obtain ⟨u, hune, huker⟩ := h
  apply hune
  apply hinj
  rw [principalUnitLog_eq_zero_of_mem_kernel (K := K) p huker,
    principalUnitLog_one]

/-! ## 3. The sharp local inverse of the actual log -/

/-- The valuation threshold 1/(p-1) of the sharp log inverse radius. -/
def sharpInverseValuationThreshold (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1)

/-- The sharp inverse radius p^(-1/(p-1)): the open ball on which the local
log is inverted by the tree's contraction argument. -/
def sharpInverseRadius (p : ℕ) : ℝ :=
  (p : ℝ) ^ (-(sharpInverseValuationThreshold p))

/-- The tree's sharp local inverse: on the closed ball of radius r below
p^(-1/(p-1)) the actual log is surjective. -/
theorem exists_log1p_preimage_on_sharp_radius (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    {r : ℝ} (hr : 0 ≤ r) (hrsharp : r < sharpInverseRadius p) {y : K}
    (hy : ‖y‖ ≤ r) :
    ∃ x : K, ‖x‖ ≤ r ∧ log1p x = y := by
  refine LeanFormal.IUT.LocalFieldLogarithm.exists_log1p_preimage_sharp
    (p := p) hr ?_ hy
  simpa [sharpInverseRadius, sharpInverseValuationThreshold] using hrsharp

/-- The sharp inverse radius is strictly smaller than one. -/
theorem sharpInverseRadius_lt_one (p : ℕ) [Fact p.Prime] :
    sharpInverseRadius p < 1 := by
  unfold sharpInverseRadius sharpInverseValuationThreshold
  have hp1 : (1 : ℝ) < (p : ℝ) := by
    exact_mod_cast (Fact.out : p.Prime).one_lt
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hexp : -(1 / ((p : ℝ) - 1)) < 0 := by
    have h : 0 < 1 / ((p : ℝ) - 1) := div_pos zero_lt_one hpos
    linarith
  exact Real.rpow_lt_one_of_one_lt_of_neg hp1 hexp

/-- The image of the principal-unit log contains the whole sharp inverse
ball: the tree's local inverse constructs the principal unit explicitly. -/
theorem principalUnitLogImage_contains_sharp_ball (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K]
    {r : ℝ} (hr : 0 ≤ r) (hrsharp : r < sharpInverseRadius p) {y : K}
    (hy : ‖y‖ ≤ r) :
    y ∈ (principalUnitLogImage (K := K) p : Set K) := by
  obtain ⟨x, hxr, hxlog⟩ := exists_log1p_preimage_on_sharp_radius
    (K := K) (p := p) hr hrsharp hy
  have hr_lt_one : r < 1 :=
    lt_trans hrsharp (sharpInverseRadius_lt_one (p := p))
  have hx_lt_one : ‖x‖ < 1 := lt_of_le_of_lt hxr hr_lt_one
  have hunit : ‖1 + x‖ = 1 :=
    LeanFormal.IUT.LocalFieldLogarithm.norm_one_add_of_norm_lt_one x hx_lt_one
  let u : (Integers K)ˣ := unitOfNormOne ⟨1 + x, hunit⟩
  have hu_val : ((u.val : K)) = 1 + x := rfl
  have hu_mem : u ∈ principalUnits (K := K) := by
    rw [mem_principalUnits_iff]
    change ‖(1 + x : K) - 1‖ < 1
    rw [add_sub_cancel_left]
    exact hx_lt_one
  refine ⟨⟨u, hu_mem⟩, ?_⟩
  change principalUnitLog ⟨u, hu_mem⟩ = y
  unfold principalUnitLog
  rw [hu_val, add_sub_cancel_left]
  exact hxlog



/-! ## 4. The image is the actual local log-shell -/

/-- The additive image of the principal-unit log is exactly the image of the
principal units under the tree's actual full-unit logarithm. -/
theorem principalUnitLogImage_eq_unitLog_image (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    (principalUnitLogImage (K := K) p : Set K) =
      unitLog (K := K) '' (principalUnits (K := K) : Set (Integers K)ˣ) := by
  ext x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨(u : (Integers K)ˣ), u.property,
      LeanFormal.IUT.LocalFieldLogarithm.unitLog_eq_log1p (p := p) _ u.property⟩
  · rintro ⟨u, hu, rfl⟩
    exact ⟨⟨u, hu⟩,
      (LeanFormal.IUT.LocalFieldLogarithm.unitLog_eq_log1p (p := p) u hu).symm⟩

/-- The principal units are compact: they are an open subgroup of the actual
compact integral unit group. -/
theorem isCompact_principalUnits :
    IsCompact (principalUnits (K := K) : Set (Integers K)ˣ) := by
  letI := compactSpace_units (K := K)
  have hclosed : IsClosed (principalUnits (K := K) : Set (Integers K)ˣ) :=
    Subgroup.isClosed_of_isOpen (principalUnits (K := K))
      (isOpen_principalUnits (K := K))
  exact hclosed.isCompact

/-- The image L of the principal-unit log is open in the local field. -/
theorem isOpen_principalUnitLogImage (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    IsOpen (principalUnitLogImage (K := K) p : Set K) := by
  rw [principalUnitLogImage_eq_unitLog_image (K := K) p]
  exact isOpenMap_unitLog (K := K) (p := p) (principalUnits (K := K))
    (isOpen_principalUnits (K := K))

/-- The image L of the principal-unit log is compact. -/
theorem isCompact_principalUnitLogImage (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    IsCompact (principalUnitLogImage (K := K) p : Set K) := by
  rw [principalUnitLogImage_eq_unitLog_image (K := K) p]
  exact (isCompact_principalUnits (K := K)).image (continuous_unitLog (p := p))

/-- The image L of the principal-unit log is contained in the actual unscaled
unit-log lattice. -/
theorem principalUnitLogImage_subset_unitLogLattice (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    (principalUnitLogImage (K := K) p : Set K) ⊆
      (unitLogLattice (K := K) (p := p) : Set K) := by
  intro x hx
  rw [coe_unitLogLattice_eq_range (K := K) (p := p)]
  rcases hx with ⟨u, rfl⟩
  exact ⟨(u : (Integers K)ˣ),
    LeanFormal.IUT.LocalFieldLogarithm.unitLog_eq_log1p (p := p) _ u.property⟩

/-- The image L of the principal-unit log is contained in the actual
Z_p-lattice log-shell. -/
theorem principalUnitLogImage_subset_integralLogShellLattice (p : ℕ)
    [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    (principalUnitLogImage (K := K) p : Set K) ⊆
      (integralLogShellLattice (K := K) (p := p) : Set K) := by
  intro x hx
  exact unitLogLattice_le_integralLogShellLattice (K := K) (p := p)
    (principalUnitLogImage_subset_unitLogLattice (K := K) p hx)

/-- After the tree's log-shell scaling, the image L lies in the actual scaled
local log-shell. -/
theorem principalUnitLogImage_scaled_subset_integralLogShell (p : ℕ)
    [Fact p.Prime] [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    ∀ x ∈ (principalUnitLogImage (K := K) p : Set K),
      (logShellScale p : K)⁻¹ * x ∈
        (integralLogShell (K := K) (p := p) : Set K) := by
  rintro x ⟨u, rfl⟩
  refine ⟨(u : (Integers K)ˣ), ?_⟩
  exact congrArg (fun t => (logShellScale p : K)⁻¹ * t)
    (LeanFormal.IUT.LocalFieldLogarithm.unitLog_eq_log1p (p := p)
      (u : (Integers K)ˣ) u.property)

/-- The actual scaled local log-shell is open and compact (tree theorems). -/
theorem integralLogShell_isOpen_and_isCompact (p : ℕ) [Fact p.Prime]
    [localNormedAlgebra : NormedAlgebra ℚ_[p] K] :
    IsOpen (integralLogShell (K := K) (p := p) : Set K) ∧
      IsCompact (integralLogShell (K := K) (p := p) : Set K) :=
  ⟨isOpen_integralLogShell (K := K) (p := p),
    isCompact_integralLogShell (K := K) (p := p)⟩

end ActualLocalFieldLog

/-! ## 5. Cards for the data that is not available as actual source data -/

section SourceCards

variable {K : Type*} [NormedField K]

/-- Frozen card for the normalization choice needed to extend the actual
logarithm from the principal units to all of K^x.  The log of a chosen
uniformizer is not determined by the analytic log, so extending it requires a
normalization choice; this card records that choice as data.  No inhabitant is
constructed and no theorem consumes the card. -/
structure LogExtensionNormalizationCard (K : Type*) [NormedField K] where
  /-- The chosen uniformizer. -/
  uniformizer : K
  /-- The chosen uniformizer is nonzero. -/
  uniformizer_ne_zero : uniformizer ≠ 0
  /-- The chosen uniformizer is a local parameter. -/
  uniformizer_norm_lt_one : ‖uniformizer‖ < 1
  /-- The normalization: the chosen value of the log on the uniformizer. -/
  chosenValueOnUniformizer : K

def LogExtensionNormalizationCardRealized (K : Type*) [NormedField K] : Prop :=
  Nonempty (LogExtensionNormalizationCard K)

/-- Frozen card for the IUT source log-shell: an open compact additive
subgroup of the local field.  No inhabitant is constructed and no theorem
consumes the card.  The actual local log image is verified separately to be
open, compact and contained in the actual log-shell/lattice. -/
structure SourceLogShellCard (K : Type*) [NormedField K] where
  /-- The source log-shell. -/
  shell : AddSubgroup K
  /-- It is open. -/
  shell_isOpen : IsOpen (shell : Set K)
  /-- It is compact. -/
  shell_isCompact : IsCompact (shell : Set K)

def SourceLogShellCardRealized (K : Type*) [NormedField K] : Prop :=
  Nonempty (SourceLogShellCard K)

/-- Frozen card for the Frobenius action on the source log-shell.  The tree
constructs the local log-shell but not its Frobenius action, so this action is
frozen as data only; no inhabitant is constructed and no theorem consumes it. -/
structure SourceFrobeniusLogShellCard (K : Type*) [NormedField K] where
  /-- The source log-shell. -/
  shell : AddSubgroup K
  /-- The Frobenius action on the local field. -/
  frobenius : K ≃+ K
  /-- The Frobenius action preserves the log-shell. -/
  frobenius_preserves_shell : ∀ x : K, x ∈ shell → frobenius x ∈ shell

def SourceFrobeniusLogShellCardRealized (K : Type*) [NormedField K] : Prop :=
  Nonempty (SourceFrobeniusLogShellCard K)

end SourceCards

/-! ## 6. The concrete local field Q_p -/

section PadicConcrete

variable (p : ℕ) [Fact p.Prime]

/-- The actual principal-unit log homomorphism at the concrete completion Q_p. -/
noncomputable def padicPrincipalUnitsLogHom :
    principalUnits (K := ℚ_[p]) →* Multiplicative ℚ_[p] :=
  principalUnitLogHom (K := ℚ_[p]) p

theorem padicPrincipalUnitLogKernel_mem_iff
    (u : principalUnits (K := ℚ_[p])) :
    u ∈ principalUnitLogKernel (K := ℚ_[p]) p ↔
      IsOfFinOrder (u : (Integers ℚ_[p])ˣ) :=
  principalUnitLogKernel_mem_iff (K := ℚ_[p]) p u

def padicPrincipalUnitLog_exact_sequence :
    (principalUnits (K := ℚ_[p])) ⧸ principalUnitLogKernel (K := ℚ_[p]) p ≃*
      (principalUnitLogHom (K := ℚ_[p]) p).range :=
  principalUnitLogQuotientEquivImage (K := ℚ_[p]) p

theorem padicPrincipalUnitLog_inverse_on_sharp_radius {r : ℝ} (hr : 0 ≤ r)
    (hrsharp : r < sharpInverseRadius p) {y : ℚ_[p]} (hy : ‖y‖ ≤ r) :
    ∃ x : ℚ_[p], ‖x‖ ≤ r ∧ log1p x = y :=
  exists_log1p_preimage_on_sharp_radius (K := ℚ_[p]) p hr hrsharp hy

theorem padicPrincipalUnitLogImage_isOpen :
    IsOpen (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) :=
  isOpen_principalUnitLogImage (K := ℚ_[p]) p

theorem padicPrincipalUnitLogImage_isCompact :
    IsCompact (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) :=
  isCompact_principalUnitLogImage (K := ℚ_[p]) p

theorem padicPrincipalUnitLogImage_subset_unitLogLattice :
    (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) ⊆
      (unitLogLattice (K := ℚ_[p]) (p := p) : Set ℚ_[p]) :=
  principalUnitLogImage_subset_unitLogLattice (K := ℚ_[p]) p

theorem padicPrincipalUnitLogImage_subset_integralLogShellLattice :
    (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) ⊆
      (integralLogShellLattice (K := ℚ_[p]) (p := p) : Set ℚ_[p]) :=
  principalUnitLogImage_subset_integralLogShellLattice (K := ℚ_[p]) p

theorem padicPrincipalUnitLogImage_scaled_subset_integralLogShell :
    ∀ x ∈ (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]),
      (logShellScale p : ℚ_[p])⁻¹ * x ∈
        (integralLogShell (K := ℚ_[p]) (p := p) : Set ℚ_[p]) :=
  principalUnitLogImage_scaled_subset_integralLogShell (K := ℚ_[p]) p

/-- The packaged log-shell properties of the actual principal-unit image at
the concrete completion Q_p: additive image, open, compact, contained in the
actual Z_p unit-log lattice and in the actual scaled log-shell. -/
theorem padicPrincipalUnitLogImage_isActualLogShell :
    IsOpen (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) ∧
      IsCompact (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) ∧
      (principalUnitLogImage (K := ℚ_[p]) p : Set ℚ_[p]) ⊆
        (unitLogLattice (K := ℚ_[p]) (p := p) : Set ℚ_[p]) := by
  exact ⟨padicPrincipalUnitLogImage_isOpen p,
    padicPrincipalUnitLogImage_isCompact p,
    padicPrincipalUnitLogImage_subset_unitLogLattice p⟩

end PadicConcrete

end Example36
end LeanFormal.IUT.IUTII.Frobenioid
