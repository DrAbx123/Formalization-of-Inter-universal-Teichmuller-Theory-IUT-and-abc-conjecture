import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlEmbeddingShellQuotientConsumer
import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlEmbeddingLatticeCokernel
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Comparison of the principal-unit-image quotient and the unit-log cokernel

This file constructs the actual additive comparison map

  (target principalUnitLogImage / Q_l shell image)
    -> (target unitLogLattice / Q_l shell image transported to the lattice)

from the inclusion of the principal-unit log image into the unit-log lattice.
It proves the comparison kernel is zero (injectivity), the exact image
description, the two different triviality criteria, and states the exact
residual for equality.

No cardinal or rank equality is asserted.
No theta spec is used.
-/

namespace ABCBridge.SourceQlEmbeddingShellQuotientComparison

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.SourceQlEmbeddingConsumer
open ABCBridge.SourceQlEmbeddingShellImageUpdate
open ABCBridge.SourceQlEmbeddingShellImageQuotient
open ABCBridge.SourceQlEmbeddingShellQuotientConsumer
open ABCBridge.SourceQlEmbeddingLatticeCokernel
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlQuotientComparisonPrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- Inclusion of the principal-unit log image into the target unit-log lattice. -/
noncomputable def sourceQlPrincipalImageToLattice :
    principalUnitLogImage (K := CommonPrimeCompletion place) l.value →+
      unitLogLattice (K := CommonPrimeCompletion place) (p := l.value) where
  toFun x :=
    ⟨x, principalUnitLogImage_subset_unitLogLattice
      (K := CommonPrimeCompletion place) l.value x.property⟩
  map_zero' := by ext; rfl
  map_add' x y := by ext; rfl

/-- The shell image transported into the target unit-log lattice. -/
noncomputable def sourceQlShellImageInLattice :
    AddSubgroup (unitLogLattice (K := CommonPrimeCompletion place) (p := l.value)) :=
  AddSubgroup.map (sourceQlPrincipalImageToLattice l place)
    (sourceQlEmbeddingShellImageUpdate l place)

/-- The comparison map from the principal-unit quotient to the lattice quotient. -/
noncomputable def sourceQlShellQuotientComparison :
    SourceQlEmbeddingShellImageQuotient l place →+
      (unitLogLattice (K := CommonPrimeCompletion place) (p := l.value) ⧸
        sourceQlShellImageInLattice l place) :=
  QuotientAddGroup.lift
    (sourceQlEmbeddingShellImageUpdate l place)
    ((QuotientAddGroup.mk' (sourceQlShellImageInLattice l place)).comp
      (sourceQlPrincipalImageToLattice l place))
    (by
      intro x hx
      change QuotientAddGroup.mk' (sourceQlShellImageInLattice l place)
        (sourceQlPrincipalImageToLattice l place x) = 0
      rw [QuotientAddGroup.eq_zero_iff]
      exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩)

@[simp] theorem sourceQlShellQuotientComparison_mk
    (x : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :
    sourceQlShellQuotientComparison l place
        (sourceQlEmbeddingShellImageQuotientProjection l place x) =
      QuotientAddGroup.mk' (sourceQlShellImageInLattice l place)
        (sourceQlPrincipalImageToLattice l place x) :=
  rfl

/-- The comparison map is injective: its kernel is zero. -/
theorem sourceQlShellQuotientComparison_ker :
    (sourceQlShellQuotientComparison l place).ker = ⊥ := by
  rw [AddSubgroup.eq_bot_iff]
  intro q hq
  induction q using QuotientAddGroup.induction_on with
  | H x =>
      have hx : x ∈ sourceQlEmbeddingShellImageUpdate l place := by
        have h0 : sourceQlShellQuotientComparison l place
            (sourceQlEmbeddingShellImageQuotientProjection l place x) = 0 := hq
        rw [sourceQlShellQuotientComparison_mk] at h0
        rw [QuotientAddGroup.eq_zero_iff] at h0
        rcases AddSubgroup.mem_map.mp h0 with ⟨y, hy, hxy⟩
        -- injectivity of the inclusion is needed to conclude x = y
        have hinj : Function.Injective (sourceQlPrincipalImageToLattice l place) := by
          intro a b hab
          apply Subtype.ext
          exact congrArg Subtype.val hab
        exact (hinj hxy).symm ▸ hy
      rw [← sourceQlEmbeddingShellImageQuotientProjection_eq_zero_iff]
      exact (sourceQlEmbeddingShellImageQuotientProjection_eq_zero_iff l place x).mpr hx

/-- The range of the comparison is the quotient of the principal-image range by
the transported shell image. -/
theorem sourceQlShellQuotientComparison_range :
    (sourceQlShellQuotientComparison l place).range =
      AddSubgroup.map
        (QuotientAddGroup.mk' (sourceQlShellImageInLattice l place))
        (sourceQlPrincipalImageToLattice l place).range := by
  apply AddSubgroup.ext
  intro z
  constructor
  · intro hz
    rcases AddMonoidHom.mem_range.mp hz with ⟨q, rfl⟩
    induction q using QuotientAddGroup.induction_on with
    | H x =>
        exact AddSubgroup.mem_map.mpr
          ⟨sourceQlPrincipalImageToLattice l place x,
            AddMonoidHom.mem_range.mpr ⟨x, rfl⟩, rfl⟩
  · intro hz
    rcases AddSubgroup.mem_map.mp hz with ⟨y, hy, rfl⟩
    rcases AddMonoidHom.mem_range.mp hy with ⟨x, rfl⟩
    exact AddMonoidHom.mem_range.mpr
      ⟨sourceQlEmbeddingShellImageQuotientProjection l place x, rfl⟩

/-- The principal-unit quotient is trivial exactly when the Q_l shell image is
the whole principal-unit log image. -/
theorem sourceQlShellQuotientComparison_domain_trivial_iff :
    Subsingleton (SourceQlEmbeddingShellImageQuotient l place) ↔
      sourceQlEmbeddingShellImageUpdate l place = ⊤ :=
  sourceQlEmbeddingShellImageQuotient_subsingleton_iff l place

/-- The lattice quotient is trivial exactly when the transported Q_l shell
image is the whole target unit-log lattice. -/
theorem sourceQlShellQuotientComparison_codomain_trivial_iff :
    Subsingleton
        (unitLogLattice (K := CommonPrimeCompletion place) (p := l.value) ⧸
          sourceQlShellImageInLattice l place) ↔
      sourceQlShellImageInLattice l place = ⊤ :=
  QuotientAddGroup.subsingleton_iff

/-- The transported shell image is the image of the principal shell image in the
lattice; it is not identified with the whole lattice without a principal-image
surjectivity statement. -/
theorem sourceQlShellImageInLattice_eq_map :
    sourceQlShellImageInLattice l place =
      AddSubgroup.map (sourceQlPrincipalImageToLattice l place)
        (sourceQlEmbeddingShellImageUpdate l place) := rfl

/-- Exact residual: the comparison is injective and its kernel is zero; the two
quotients have different triviality criteria unless the principal-unit image is
the whole target unit-log lattice.  No cardinal/rank claim. -/
theorem sourceQlShellQuotientComparison_exactResidual :
    (sourceQlShellQuotientComparison l place).ker = ⊥
      ∧
    ((Subsingleton (SourceQlEmbeddingShellImageQuotient l place)) ↔
      sourceQlEmbeddingShellImageUpdate l place = ⊤)
      ∧
    ((Subsingleton
        (unitLogLattice (K := CommonPrimeCompletion place) (p := l.value) ⧸
          sourceQlShellImageInLattice l place)) ↔
      sourceQlShellImageInLattice l place = ⊤) :=
  ⟨sourceQlShellQuotientComparison_ker l place,
    sourceQlShellQuotientComparison_domain_trivial_iff l place,
    sourceQlShellQuotientComparison_codomain_trivial_iff l place⟩

/-- The principal-image inclusion into the lattice is injective. -/
theorem sourceQlPrincipalImageToLattice_injective :
    Function.Injective (sourceQlPrincipalImageToLattice l place) := by
  intro x y h
  apply Subtype.ext
  exact congrArg Subtype.val h

/-- Membership in the transported shell image. -/
theorem sourceQlShellImageInLattice_mem_iff
    (z : unitLogLattice (K := CommonPrimeCompletion place) (p := l.value)) :
    z ∈ sourceQlShellImageInLattice l place ↔
      ∃ y : sourceQlEmbeddingShellImageUpdate l place,
        sourceQlPrincipalImageToLattice l place y = z :=
  AddSubgroup.mem_map

/-- The transported shell image is contained in the target unit-log lattice. -/
theorem sourceQlShellImageInLattice_le_top :
    sourceQlShellImageInLattice l place ≤ ⊤ := le_top

/-- The comparison map is additive. -/
theorem sourceQlShellQuotientComparison_add
    (x y : SourceQlEmbeddingShellImageQuotient l place) :
    sourceQlShellQuotientComparison l place (x + y) =
      sourceQlShellQuotientComparison l place x +
        sourceQlShellQuotientComparison l place y :=
  map_add (sourceQlShellQuotientComparison l place) x y

/-- The comparison map sends zero to zero. -/
theorem sourceQlShellQuotientComparison_zero :
    sourceQlShellQuotientComparison l place 0 = 0 :=
  map_zero (sourceQlShellQuotientComparison l place)

/-- Exact residual, compact form: injective comparison, distinct triviality
criteria, no cardinal/rank equality. -/
theorem sourceQlShellQuotientComparison_residual_compact :
    (sourceQlShellQuotientComparison l place).ker = ⊥
      ∧
    (Subsingleton (SourceQlEmbeddingShellImageQuotient l place) ↔
      sourceQlEmbeddingShellImageUpdate l place = ⊤)
      ∧
    (Subsingleton
        (unitLogLattice (K := CommonPrimeCompletion place) (p := l.value) ⧸
          sourceQlShellImageInLattice l place) ↔
      sourceQlShellImageInLattice l place = ⊤) :=
  sourceQlShellQuotientComparison_exactResidual l place


end

end ABCBridge.SourceQlEmbeddingShellQuotientComparison
