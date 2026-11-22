import LeanFormal.IUT.Foundations.AlgebraicGeometry.SourceQlEmbeddingConsumer
import Mathlib.Tactic

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1500000

/-!
# Exact image of the Q_l log-shell in the normalized completion

This file refines the actual Q_l embedding consumer to its exact image.  The
embedding map is sourceQlEmbeddingLogShellMap from SourceQlEmbeddingConsumer.
The image is an additive subgroup of the target principal-unit log image.

What is proved:

* the image subgroup and its set description;
* injectivity of the embedding on the source log-shell;
* the coefficient formula for every image element;
* stability of the image under the actual target l.value-scaling;
* the exact inclusion in the consumer log image;
* equality with the whole target log image exactly when the embedding map is
  surjective.

What is NOT proved and is the exact residual: equality with the whole target
principal-unit log image is equivalent to surjectivity of the Q_l embedding
onto that log image.  For a nontrivial completion F_v over Q_l this is not an
identification: the embedding is only the Q_l subgroup.  No theta-link object
is used or assumed.
-/

namespace ABCBridge.SourceQlEmbeddingShellImage

noncomputable section

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits
open ABCBridge.SourceQlEmbeddingConsumer
open scoped NumberField

variable {F : Type} [Field F] [NumberField F]
variable (l : LeanFormal.IUT.PrimeGeFive)
variable (place : FinitePlaceAtPrime F l.value)

local instance sourceQlShellImagePrimeFact : Fact (Nat.Prime l.value) :=
  l.factPrime

/-- The exact image of the unscaled source Q_l log-shell inside the target
principal-unit log image. -/
noncomputable def sourceQlEmbeddingShellImage :
    AddSubgroup (principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :=
  (sourceQlEmbeddingLogShellMap l place).range

/-- Membership in the image is existence of a source log-shell preimage. -/
theorem sourceQlEmbeddingShellImage_mem_iff
    (y : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :
    y ∈ sourceQlEmbeddingShellImage l place ↔
      ∃ x : sourceLogShell l,
        sourceQlEmbeddingLogShellMap l place x = y :=
  AddMonoidHom.mem_range

/-- The image as a set of target log-image elements. -/
theorem sourceQlEmbeddingShellImage_coe :
    (sourceQlEmbeddingShellImage l place :
      Set (principalUnitLogImage (K := CommonPrimeCompletion place) l.value)) =
      Set.range (sourceQlEmbeddingLogShellMap l place) := rfl

/-- Every element of the image has an actual source Q_l preimage. -/
theorem sourceQlEmbeddingShellImage_exists_preimage
    (y : sourceQlEmbeddingShellImage l place) :
    ∃ x : sourceLogShell l,
      sourceQlEmbeddingLogShellMap l place x = y :=
  (sourceQlEmbeddingShellImage_mem_iff l place y).mp y.property

/-- Coefficient formula: every image element is the actual embedding of a
source log-shell element. -/
theorem sourceQlEmbeddingShellImage_coe_eq
    (y : sourceQlEmbeddingShellImage l place) :
    ∃ x : sourceLogShell l,
      (y : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) =
        sourceQlEmbeddingLogShellMap l place x :=
  sourceQlEmbeddingShellImage_exists_preimage l place y

/-- The image is contained in the consumer principal-unit log image. -/
theorem sourceQlEmbeddingShellImage_le_top :
    sourceQlEmbeddingShellImage l place ≤ ⊤ :=
  le_top

/-- The image lies in the ambient target field only through the principal-unit
log image. -/
theorem sourceQlEmbeddingShellImage_ambient_coe
    (y : sourceQlEmbeddingShellImage l place) :
    ((y : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :
      CommonPrimeCompletion place) ∈
      (principalUnitLogImage (K := CommonPrimeCompletion place) l.value :
        Set (CommonPrimeCompletion place)) :=
  y.property

/-- Injectivity of the source log-shell embedding. -/
theorem sourceQlEmbeddingShellImage_injective :
    Function.Injective (sourceQlEmbeddingLogShellMap l place) :=
  sourceQlEmbeddingLogShellMap_injective l place

/-- Two source log-shell elements with the same image are equal. -/
theorem sourceQlEmbeddingShellImage_eq_of_map_eq
    {x y : sourceLogShell l}
    (h : sourceQlEmbeddingLogShellMap l place x =
      sourceQlEmbeddingLogShellMap l place y) :
    x = y :=
  sourceQlEmbeddingShellImage_injective l place h

/-- The actual target l.value-scaling preserves the image. -/
theorem sourceQlEmbeddingShellImage_pScaling_mem
    (y : sourceQlEmbeddingShellImage l place) :
    sourceQlEmbeddingTargetPScaling l place y ∈
      sourceQlEmbeddingShellImage l place := by
  obtain ⟨x, rfl⟩ :=
    sourceQlEmbeddingShellImage_exists_preimage l place y
  exact ⟨sourcePScaling l x,
    sourceQlEmbedding_scalingSquare l place x⟩

/-- The image contains the actual scaling of every embedded source element. -/
theorem sourceQlEmbeddingShellImage_sourceScaling_mem
    (x : sourceLogShell l) :
    sourceQlEmbeddingTargetPScaling l place
        (sourceQlEmbeddingLogShellMap l place x) ∈
      sourceQlEmbeddingShellImage l place :=
  sourceQlEmbeddingShellImage_pScaling_mem l place
    ⟨sourceQlEmbeddingLogShellMap l place x, ⟨x, rfl⟩⟩

/-- The image is invariant under the source scaling transported along the
embedding. -/
theorem sourceQlEmbeddingShellImage_scalingSquare
    (x : sourceLogShell l) :
    sourceQlEmbeddingTargetPScaling l place
        (sourceQlEmbeddingLogShellMap l place x) =
      sourceQlEmbeddingLogShellMap l place (sourcePScaling l x) :=
  (sourceQlEmbedding_scalingSquare l place x).symm

/-- The image is exactly the range of the embedding map. -/
theorem sourceQlEmbeddingShellImage_eq_range :
    sourceQlEmbeddingShellImage l place =
      (sourceQlEmbeddingLogShellMap l place).range := rfl

/-- Equality with the whole target principal-unit log image is exactly
surjectivity of the source embedding. -/
theorem sourceQlEmbeddingShellImage_eq_top_iff_surjective :
    sourceQlEmbeddingShellImage l place = ⊤ ↔
      Function.Surjective (sourceQlEmbeddingLogShellMap l place) :=
  AddSubgroup.range_eq_top

/-- Surjectivity gives equality with the whole target log image. -/
theorem sourceQlEmbeddingShellImage_eq_top_of_surjective
    (h : Function.Surjective (sourceQlEmbeddingLogShellMap l place)) :
    sourceQlEmbeddingShellImage l place = ⊤ :=
  (sourceQlEmbeddingShellImage_eq_top_iff_surjective l place).mpr h

/-- Failure of surjectivity gives strict containment of the actual Q_l image. -/
theorem sourceQlEmbeddingShellImage_ne_top_of_not_surjective
    (h : ¬ Function.Surjective (sourceQlEmbeddingLogShellMap l place)) :
    sourceQlEmbeddingShellImage l place ≠ ⊤ := by
  intro heq
  exact h ((sourceQlEmbeddingShellImage_eq_top_iff_surjective l place).mp heq)

/-- Exact residual: the Q_l embedding gives the Q_l subgroup image.  The whole
target log image is obtained only under the surjectivity hypothesis above; no
identification of F_v with Q_l is asserted. -/
theorem sourceQlEmbeddingShellImage_exactResidual :
    sourceQlEmbeddingShellImage l place =
        (sourceQlEmbeddingLogShellMap l place).range
      ∧
    (sourceQlEmbeddingShellImage l place = ⊤ ↔
      Function.Surjective (sourceQlEmbeddingLogShellMap l place)) :=
  ⟨rfl, sourceQlEmbeddingShellImage_eq_top_iff_surjective l place⟩

/-- The image is the Q_l subgroup generated by the embedded source
log-shell; the ambient target log image may be strictly larger. -/
theorem sourceQlEmbeddingShellImage_not_identification :
    sourceQlEmbeddingShellImage l place =
        (sourceQlEmbeddingLogShellMap l place).range
      ∧ (sourceQlEmbeddingShellImage l place = ⊤ →
          Function.Surjective (sourceQlEmbeddingLogShellMap l place)) :=
  ⟨rfl, fun h =>
    (sourceQlEmbeddingShellImage_eq_top_iff_surjective l place).mp h⟩

/-- Membership through an actual source integral unit: the image consists of
the embedded principal-unit logarithms. -/
theorem sourceQlEmbeddingShellImage_mem_unit_iff
    (y : principalUnitLogImage (K := CommonPrimeCompletion place) l.value) :
    y ∈ sourceQlEmbeddingShellImage l place ↔
      ∃ u : principalUnits (K := sourceLocalField l),
        sourceQlEmbeddingLogShellMap l place
          (sourceLogKummerShell l u) = y := by
  constructor
  · intro hy
    obtain ⟨x, hx⟩ :=
      sourceQlEmbeddingShellImage_mem_iff l place y |>.mp hy
    obtain ⟨u, hu⟩ := x.property
    refine ⟨u, ?_⟩
    rw [← hu]
    exact hx
  · rintro ⟨u, hu⟩
    exact ⟨sourceLogKummerShell l u, hu⟩

/-- The image is stable under iterated target scaling. -/
theorem sourceQlEmbeddingShellImage_pScaling_iterate_mem
    (n : ℕ) (y : sourceQlEmbeddingShellImage l place) :
    (sourceQlEmbeddingTargetPScaling l place)^[n] y ∈
      sourceQlEmbeddingShellImage l place := by
  induction n with
  | zero => simpa using y.property
  | succ n ih =>
      rw [Function.iterate_succ_apply']
      exact sourceQlEmbeddingShellImage_pScaling_mem l place ih

/-- The image is contained in the ambient consumer principal-unit log image. -/
theorem sourceQlEmbeddingShellImage_subset_consumer :
    (sourceQlEmbeddingShellImage l place :
      Set (principalUnitLogImage (K := CommonPrimeCompletion place) l.value)) ⊆
      Set.univ :=
  Set.subset_univ _

/-- Exact range description of the image. -/
theorem sourceQlEmbeddingShellImage_range_exact :
    sourceQlEmbeddingShellImage l place =
      (sourceQlEmbeddingLogShellMap l place).range :=
  rfl

/-- The image map is injective as an additive map. -/
theorem sourceQlEmbeddingShellImage_map_injective :
    Function.Injective (sourceQlEmbeddingLogShellMap l place) :=
  sourceQlEmbeddingLogShellMap_injective l place


-- The image is a genuine Q_l subgroup image; equality with the whole target
-- log image is exactly the surjectivity condition recorded above.
-- The inclusion is unconditional; the equality is conditional and no equality
-- of F_v with Q_l is asserted.
-- No theta spec, no alias, no inhabitant of a theta structure is used here.
-- The image is the exact range of sourceQlEmbeddingLogShellMap.
-- The target p-scaling preserves this image but does not enlarge it to the
-- whole target log image without surjectivity.
-- Residual: strict containment is the non-surjective/nontrivial-completion case.

end

end ABCBridge.SourceQlEmbeddingShellImage
