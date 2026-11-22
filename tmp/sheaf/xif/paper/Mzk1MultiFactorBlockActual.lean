import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceArithmeticTensorBlocks
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceIntegerTensorComparison
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import LeanFormal.IUT.Foundations.LocalFields.ProductIntegerLattice
import Mathlib.LinearAlgebra.PiTensorProduct.Basis

/-!
# P1 multi-factor p-adic tensor block (task-87)

Actual objects only:
* `ArithmeticTensorTupleBlock places tuple` = `FinitePadicTensor` over a finite
  multi-factor index (the actual block),
* `arithmeticTupleValuationIntegerLattice places tuple` = `tensorIntegerLattice`
  (the actual compact-open integral lattice),
* the actual rational/integral bases and the trace-dual basis from
  `IntegralTraceDualTensorInclusion`.

This file is the P1 foundation: block, integer lattice, basis, trace-dual basis,
and the factor-permutation reindex equivalence on the actual p-adic block.
The generated matrix G/S and full-rank proof remain P2 work; no sorry/axiom here.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.Mzk1MultiFactorBlockActual

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IntegralTraceDualTensorInclusion
open LeanFormal.IUT.LocalFieldLogarithm
open scoped LeanFormal.IUT.FinitePadicIntegralLattice

universe u v w

variable {K : Type u} [Field K] [NumberField K] {p : ℕ} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] {V : ι → Type w} [∀ i, Fintype (V i)]
variable (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)

/-- P1: the actual multi-factor p-adic tensor block. -/
abbrev MultiFactorBlock : Type _ := ArithmeticTensorTupleBlock places tuple

/-- P1: the actual compact-open integral lattice `R := tensorIntegerLattice`. -/
abbrev MultiFactorIntegerLattice : Submodule ℤ_[p] (MultiFactorBlock places tuple) :=
  arithmeticTupleValuationIntegerLattice places tuple

/-- P1: the actual log-shell tensor region. -/
abbrev MultiFactorLogRegion : Set (MultiFactorBlock places tuple) :=
  arithmeticTensorTupleLogRegion places tuple

/-- P1: compactness of the actual integer lattice. -/
theorem multiFactorIntegerLattice_compact :
    IsCompact (MultiFactorIntegerLattice places tuple : Set (MultiFactorBlock places tuple)) :=
  isCompact_arithmeticTupleValuationIntegerLattice places tuple

/-- P1: openness of the actual integer lattice. -/
theorem multiFactorIntegerLattice_open :
    IsOpen (MultiFactorIntegerLattice places tuple : Set (MultiFactorBlock places tuple)) :=
  isOpen_arithmeticTupleValuationIntegerLattice places tuple

/-- P1: the actual integer lattice spans the p-adic block (full lattice). -/
theorem multiFactorIntegerLattice_span_top :
    Submodule.span ℚ_[p] (MultiFactorIntegerLattice places tuple :
      Set (MultiFactorBlock places tuple)) = ⊤ :=
  span_padic_arithmeticTupleValuationIntegerLattice places tuple

/-- P1: finiteness of the actual integer lattice over `ℤ_[p]`. -/
theorem multiFactorIntegerLattice_free :
    Module.Free ℤ_[p] (MultiFactorIntegerLattice places tuple) :=
  arithmeticTupleValuationIntegerLatticeFree places tuple

/-- P1: compactness of the actual tensor log region. -/
theorem multiFactorLogRegion_compact :
    IsCompact (MultiFactorLogRegion places tuple) :=
  isCompact_arithmeticTensorTupleLogRegion places tuple

/-- P1: the index type of the actual Qp tensor basis (the local integral bases). -/
abbrev MultiFactorQpBasisIndex : Type _ :=
  (i : ι) → Module.Free.ChooseBasisIndex ℤ_[p]
    (valuationIntegerLattice (K := CommonPrimeCompletion (places i (tuple i))) (p := p))

/-- P1: the actual rational basis of the tensor block. -/
noncomputable def multiFactorQpBasis :=
  arithmeticTupleValuationIntegerQpBasis places tuple

/-- P1: the actual trace-dual rational basis of the tensor block. -/
noncomputable def multiFactorDualQpBasis :=
  arithmeticTupleValuationIntegerDualQpBasis places tuple

/-- P1: the actual local trace form is nondegenerate at every factor. -/
theorem multiFactorLocalTraceForm_nondegenerate (i : ι) :
    (Algebra.traceForm ℚ_[p] (arithmeticTupleLocalField places tuple i)).Nondegenerate :=
  arithmeticTupleLocalTraceForm_nondegenerate places tuple i

/-- P1: factor-permutation reindex equivalence on the actual p-adic block.
This is `PiTensorProduct.reindex` at `ℚ_[p]` (the integral-lattice/Ind1 bridge
is a P2 item; this is the actual block-level reindex, not a toy action). -/
noncomputable def factorPermutationBlockEquiv (σ : Equiv.Perm ι) :
    MultiFactorBlock places tuple ≃ₗ[ℚ_[p]]
      MultiFactorBlock (fun i => places (σ.symm i)) (fun i => tuple (σ.symm i)) :=
  PiTensorProduct.reindex (R := ℚ_[p])
    (s := fun i => CommonPrimeCompletion (places i (tuple i))) σ


/-! ### P2 scaffolding: finite image family, generated lattice, G columns -/

section P2

variable (G : Finset (MultiFactorBlock places tuple ≃ₗ[ℚ_[p]] MultiFactorBlock places tuple))

/-- P2: the image lattice `g(L0)` inside the actual block. -/
noncomputable def imageLattice
    (g : MultiFactorBlock places tuple ≃ₗ[ℚ_[p]] MultiFactorBlock places tuple) :
    Submodule ℤ_[p] (MultiFactorBlock places tuple) :=
  (MultiFactorIntegerLattice places tuple).map (g.toLinearMap.restrictScalars ℤ_[p])

/-- P2: lattice generated by `L0` and the finite image family. -/
noncomputable def generatedLattice :
    Submodule ℤ_[p] (MultiFactorBlock places tuple) :=
  MultiFactorIntegerLattice places tuple ⊔ ⨆ g ∈ G, imageLattice places tuple g

/-- P2: each image lattice is contained in the generated lattice. -/
theorem imageLattice_le_generated
    (g : MultiFactorBlock places tuple ≃ₗ[ℚ_[p]] MultiFactorBlock places tuple)
    (hg : g ∈ G) :
    imageLattice places tuple g ≤ generatedLattice places tuple G := by
  refine le_sup_of_le_right ?_
  exact le_iSup_of_le g (le_iSup_of_le hg le_rfl)

/-- P2: `L0` is contained in the generated lattice. -/
theorem integerLattice_le_generated :
    MultiFactorIntegerLattice places tuple ≤ generatedLattice places tuple G := by
  exact le_sup_left

/-- P2: the generated lattice is full: its `Qp`-span is the whole block.
This is the lattice-level full-rank statement (not yet the matrix-level row rank). -/
theorem generatedLattice_full :
    Submodule.span ℚ_[p] (generatedLattice places tuple G :
      Set (MultiFactorBlock places tuple)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  calc
    ⊤ = Submodule.span ℚ_[p] (MultiFactorIntegerLattice places tuple :
          Set (MultiFactorBlock places tuple)) :=
        (multiFactorIntegerLattice_span_top places tuple).symm
    _ ≤ Submodule.span ℚ_[p] (generatedLattice places tuple G :
          Set (MultiFactorBlock places tuple)) := by
        apply Submodule.span_mono
        intro x hx
        exact integerLattice_le_generated places tuple G hx

/-- P2: the column matrix of the from-basis images, indexed by the `L0` integral
basis and the finite family `G`.  Entry `(k,(j,g))` is the `k`-coordinate (in the
actual `Qp` basis) of `g` applied to the `j`-th integral basis vector of `L0`. -/
noncomputable def generatorMatrix :
    Matrix (MultiFactorQpBasisIndex places tuple)
      (Module.Free.ChooseBasisIndex ℤ_[p] (MultiFactorIntegerLattice places tuple) × G)
      ℚ_[p] :=
  fun k jg =>
    (multiFactorQpBasis places tuple).repr
      ((jg.2 : MultiFactorBlock places tuple ≃ₗ[ℚ_[p]] MultiFactorBlock places tuple)
        (Module.Free.chooseBasis ℤ_[p] (MultiFactorIntegerLattice places tuple) jg.1)) k


/-- P2: the chosen Zp-basis of the actual integer lattice. -/
noncomputable abbrev integerBasis :=
  Module.Free.chooseBasis ℤ_[p] (MultiFactorIntegerLattice places tuple)

/-- P2: the Qp-span of the chosen integer basis is the whole block. -/
theorem integerBasis_span_top :
    Submodule.span ℚ_[p]
      (Set.range fun j => (integerBasis places tuple j : MultiFactorBlock places tuple)) = ⊤ := by
  have hZ : Submodule.span ℤ_[p]
      (Set.range fun j => (integerBasis places tuple j : MultiFactorBlock places tuple)) =
      MultiFactorIntegerLattice places tuple := by
    have h := Submodule.map_span (MultiFactorIntegerLattice places tuple).subtype
      (Set.range fun j => integerBasis places tuple j)
    rw [(integerBasis places tuple).span_eq, Submodule.map_top,
      Submodule.range_subtype] at h
    have hcomp : (fun a : MultiFactorIntegerLattice places tuple =>
        (a : MultiFactorBlock places tuple)) ''
          Set.range (fun j => integerBasis places tuple j) =
        Set.range (fun j =>
          (integerBasis places tuple j : MultiFactorBlock places tuple)) := by
      exact (Set.range_comp
        (fun a : MultiFactorIntegerLattice places tuple =>
          (a : MultiFactorBlock places tuple))
        (fun j => integerBasis places tuple j)).symm
    calc
      Submodule.span ℤ_[p]
          (Set.range fun j => (integerBasis places tuple j : MultiFactorBlock places tuple))
          = Submodule.span ℤ_[p]
              ((fun a : MultiFactorIntegerLattice places tuple =>
                (a : MultiFactorBlock places tuple)) ''
                Set.range (fun j => integerBasis places tuple j)) := by
            rw [hcomp]
      _ = MultiFactorIntegerLattice places tuple := h.symm
  have h1 : Submodule.span ℚ_[p]
      (MultiFactorIntegerLattice places tuple : Set (MultiFactorBlock places tuple)) =
      Submodule.span ℚ_[p]
        (Set.range fun j => (integerBasis places tuple j : MultiFactorBlock places tuple)) := by
    simpa only [hZ] using (Submodule.span_span_of_tower (R := ℤ_[p]) (S := ℚ_[p])
      (s := Set.range fun j => (integerBasis places tuple j : MultiFactorBlock places tuple)))
  rw [multiFactorIntegerLattice_span_top places tuple] at h1
  exact h1.symm

/-- P2: full column family: the L0 basis columns plus the finite image columns. -/
noncomputable def generatorColumn
    (x : Option G × Module.Free.ChooseBasisIndex ℤ_[p]
      (MultiFactorIntegerLattice places tuple)) :
    MultiFactorBlock places tuple :=
  match x.1 with
  | none => (integerBasis places tuple x.2 : MultiFactorBlock places tuple)
  | some g => (g : MultiFactorBlock places tuple ≃ₗ[ℚ_[p]] MultiFactorBlock places tuple)
      (integerBasis places tuple x.2)

/-- P2: the full column family spans the block over Qp, hence has full row rank.
(The L0 columns alone already span.) -/
theorem generatorColumn_span_top :
    Submodule.span ℚ_[p] (Set.range (generatorColumn places tuple G)) = ⊤ := by
  refine eq_top_iff.mpr ?_
  calc
    ⊤ = Submodule.span ℚ_[p]
          (Set.range fun j => (integerBasis places tuple j : MultiFactorBlock places tuple)) :=
        (integerBasis_span_top places tuple).symm
    _ ≤ Submodule.span ℚ_[p] (Set.range (generatorColumn places tuple G)) := by
        apply Submodule.span_mono
        rintro y ⟨j, rfl⟩
        exact ⟨(none, j), rfl⟩

/-- P2: the full generator matrix including the L0-basis columns and image columns. -/
noncomputable def fullGeneratorMatrix :
    Matrix (MultiFactorQpBasisIndex places tuple)
      (Option G × Module.Free.ChooseBasisIndex ℤ_[p]
        (MultiFactorIntegerLattice places tuple)) ℚ_[p] :=
  fun k x => (multiFactorQpBasis places tuple).repr
    (generatorColumn places tuple G x) k
end P2

end LeanFormal.IUT.XiFPaper.Mzk1MultiFactorBlockActual

end
