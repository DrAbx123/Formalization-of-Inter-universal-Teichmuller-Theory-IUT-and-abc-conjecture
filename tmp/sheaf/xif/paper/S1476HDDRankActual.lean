import tmp.sheaf.xif.paper.S1215SourceSHEHDDCompatibilityActual
import tmp.sheaf.xif.paper.S1418HDDConsumerActual
import LeanFormal.IUT.Foundations.NumberField.LocalQParameter
import LeanFormal.IUT.Foundations.NumberField.PlaceCompletionCarrier
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.FreeModule.Finite.Basic
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.RingTheory.Valuation.ValuationSubring

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

/-!
# S1476: actual rank > 1 arithmetic vector bundle localization

S1418's exact first field for the S1215 fourth joint is
`S1215HDDLocalLattice`, whose `rank` is a natural number and whose
`lattice` is
`Theorem311Output I -> place -> Set (Fin rank -> localField v)`.
The S1402 dependent source supplies only one `Completion v` factor per
place, so the paper's rank-`>1` arithmetic-vector-bundle localization
(IUT III, Corollary 3.12, Step (xi-d); Card AV R3) was missing.

This file constructs the actual donor:

* the global free arithmetic vector bundle `O_Q^r`, with its
  `O_Q`-module of sections and the `O_Q`-linear completed integral
  localization `O_Q^r -> O_v^r` at every finite place;
* the local integral lattice `s1476LocalLattice r v`, the image of
  `O_v^r` in `K_v^r` under the completed-ring inclusion;
* its module structure: a linear equivalence with `O_v^r`, freeness, finite
  generation, `Module.finrank = r`, integrality of every coordinate, and
  fullness in `K_v^r`;
* the S1215 HDD local lattice of rank `2` obtained from the `r = 2`
  donor, and hence an inhabitant of S1418's exact first-field type.

The donor is actual: it uses the actual completed valuation rings
`CompletionIntegers v`, the actual completions `Completion v`, and the
actual ring of integers `O_Q`.  It is not rank-one (`rank = 2`), not an
arbitrary `Set` (the lattice is a `Submodule`, the range of an explicit
linear map), and no axiom, `sorry`, `True`, `PUnit` or rank-one
surrogate is introduced.

The donor lattice is independent of the `Theorem311Output` argument.  The
paper's HDD local lattice is attached to the output-dependent source image of
the S1402 dependent source; constructing that output-dependent family and
identifying it with the rank-`r` localization remains outside this file.
Thus this file closes the S1215 first-field *type* with an actual rank-2
local lattice and does not claim that the free donor is the paper's full HDD
arithmetic vector bundle.
-/

namespace LeanFormal.IUT.XiFPaper.S1476HDDRankActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1418HDDConsumerActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v

variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}

/-! ## 1. Global free arithmetic vector bundle -/

/-- Global sections of the free arithmetic vector bundle of rank `r` over
`O_Q`: the free `O_Q`-module `O_Q^r`. -/
abbrev S1476GlobalSections (r : Nat) : Type :=
  Fin r → NumberField.RingOfIntegers ℚ

/-- The actual rank-`r` arithmetic vector bundle over `O_Q`, with its
per-place completed integral localization.  This refines Card AV (which has
only a section carrier and a reading into the local ring) by retaining the
rank, the `O_Q`-module structure and the integral lattice
`Fin r → O_v` at every place. -/
structure S1476RankArithmeticVectorBundle (r : Nat) where
  total : Type
  [addCommGroup : AddCommGroup total]
  [module : Module (NumberField.RingOfIntegers ℚ) total]
  localization : ∀ v : NumberField.FinitePlace ℚ,
    total →ₗ[NumberField.RingOfIntegers ℚ] (Fin r → CompletionIntegers v)
  rank : Module.finrank (NumberField.RingOfIntegers ℚ) total = r

attribute [instance] S1476RankArithmeticVectorBundle.addCommGroup
attribute [instance] S1476RankArithmeticVectorBundle.module

/-- The completed integral localization of a global section: apply the
`O_Q → O_v` structure map coordinatewise. -/
noncomputable def s1476GlobalLocalization (r : Nat) (v : NumberField.FinitePlace ℚ) :
    S1476GlobalSections r →ₗ[NumberField.RingOfIntegers ℚ]
      (Fin r → CompletionIntegers v) :=
  LinearMap.pi (fun i =>
    (Algebra.linearMap (NumberField.RingOfIntegers ℚ) (CompletionIntegers v)).comp
      (LinearMap.proj i))

theorem s1476GlobalSections_finrank (r : Nat) :
    Module.finrank (NumberField.RingOfIntegers ℚ) (S1476GlobalSections r) = r := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-- The free arithmetic vector bundle of rank `r` over `O_Q`. -/
noncomputable def s1476FreeArithmeticVectorBundle (r : Nat) :
    S1476RankArithmeticVectorBundle r where
  total := S1476GlobalSections r
  localization := s1476GlobalLocalization r
  rank := s1476GlobalSections_finrank r

/-! ## 2. The actual integral local lattice -/

noncomputable def s1476IntegralMap (r : Nat) (v : NumberField.FinitePlace ℚ) :
    (Fin r → CompletionIntegers v) →ₗ[CompletionIntegers v]
      (Fin r → Completion v) :=
  LinearMap.pi (fun i =>
    (Algebra.linearMap (CompletionIntegers v) (Completion v)).comp
      (LinearMap.proj i))

@[simp] theorem s1476IntegralMap_apply (r : Nat) (v : NumberField.FinitePlace ℚ)
    (x : Fin r → CompletionIntegers v) (i : Fin r) :
    s1476IntegralMap r v x i = (x i : Completion v) := rfl

theorem s1476IntegralMap_injective (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Function.Injective (s1476IntegralMap r v) := by
  intro x y hxy
  funext i
  have h : ((x i : CompletionIntegers v) : Completion v) =
      ((y i : CompletionIntegers v) : Completion v) := by
    have := congrFun hxy i
    simpa using this
  exact Subtype.ext h

noncomputable def s1476LocalLattice (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Submodule (CompletionIntegers v) (Fin r → Completion v) :=
  LinearMap.range (s1476IntegralMap r v)

theorem s1476LocalLattice_eq_range (r : Nat) (v : NumberField.FinitePlace ℚ) :
    s1476LocalLattice r v = LinearMap.range (s1476IntegralMap r v) := rfl

theorem s1476LocalLattice_eq_map_top (r : Nat) (v : NumberField.FinitePlace ℚ) :
    s1476LocalLattice r v =
      (⊤ : Submodule (CompletionIntegers v)
        (Fin r → CompletionIntegers v)).map (s1476IntegralMap r v) := by
  rw [Submodule.map_top]
  rfl

noncomputable def s1476LocalLatticeEquiv (r : Nat) (v : NumberField.FinitePlace ℚ) :
    (Fin r → CompletionIntegers v) ≃ₗ[CompletionIntegers v]
      s1476LocalLattice r v :=
  LinearEquiv.ofInjective (s1476IntegralMap r v) (s1476IntegralMap_injective r v)

instance s1476LocalLatticeFree (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Module.Free (CompletionIntegers v) (s1476LocalLattice r v) :=
  Module.Free.of_equiv (s1476LocalLatticeEquiv r v)

instance s1476LocalLatticeFinite (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Module.Finite (CompletionIntegers v) (s1476LocalLattice r v) :=
  Module.Finite.equiv (s1476LocalLatticeEquiv r v)

theorem s1476LocalLattice_finrank (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Module.finrank (CompletionIntegers v) (s1476LocalLattice r v) = r := by
  rw [← (s1476LocalLatticeEquiv r v).finrank_eq,
    Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

theorem s1476LocalLattice_integral (r : Nat) (v : NumberField.FinitePlace ℚ)
    {x : Fin r → Completion v} (hx : x ∈ s1476LocalLattice r v) :
    ∀ i, x i ∈ (CompletionIntegers v : Set (Completion v)) := by
  rcases hx with ⟨y, rfl⟩
  intro i
  exact SetLike.coe_mem (y i)

/-- Every localized global section lies in the actual integral local lattice. -/
theorem s1476GlobalLocalization_mem_localLattice (r : Nat)
    (v : NumberField.FinitePlace ℚ) (x : S1476GlobalSections r) :
    (fun i => (s1476GlobalLocalization r v x i : Completion v)) ∈
      s1476LocalLattice r v :=
  ⟨s1476GlobalLocalization r v x, rfl⟩

theorem s1476Single_mem_span (r : Nat) (v : NumberField.FinitePlace ℚ) (i : Fin r) :
    (Pi.single i (1 : Completion v) : Fin r → Completion v) ∈
      Submodule.span (Completion v)
        (s1476LocalLattice r v : Set (Fin r → Completion v)) := by
  apply Submodule.subset_span
  refine ⟨Pi.single i (1 : CompletionIntegers v), ?_⟩
  funext j
  by_cases h : j = i
  · subst h
    rw [s1476IntegralMap_apply, Pi.single_eq_same, Pi.single_eq_same]
    exact map_one (algebraMap (CompletionIntegers v) (Completion v))
  · rw [s1476IntegralMap_apply, Pi.single_eq_of_ne' (Ne.symm h),
      Pi.single_eq_of_ne' (Ne.symm h)]
    exact map_zero (algebraMap (CompletionIntegers v) (Completion v))

theorem s1476LocalLattice_span_eq_top (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Submodule.span (Completion v)
      (s1476LocalLattice r v : Set (Fin r → Completion v)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  rw [← (Pi.basisFun (Completion v) (Fin r)).sum_repr x]
  apply Submodule.sum_mem
  intro i _
  apply Submodule.smul_mem
  rw [Pi.basisFun_apply]
  exact s1476Single_mem_span r v i

theorem s1476Ambient_finrank (r : Nat) (v : NumberField.FinitePlace ℚ) :
    Module.finrank (Completion v) (Fin r → Completion v) = r := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin]

/-! ## 3. Donor record -/

/-- The actual rank-`r` arithmetic-vector-bundle localization donor.  Its
`lattice v` is the completed integral local lattice `O_v^r ⊂ K_v^r`; the
remaining fields record integrality, the `O_v`-module structure, the rank
and fullness in the completed local field. -/
structure S1476ArithmeticVectorBundleLocalization (r : Nat) where
  lattice : (v : NumberField.FinitePlace ℚ) →
    Submodule (CompletionIntegers v) (Fin r → Completion v)
  integral : ∀ (v) {x}, x ∈ lattice v → ∀ i,
    x i ∈ (CompletionIntegers v : Set (Completion v))
  free : ∀ v, Module.Free (CompletionIntegers v) (lattice v)
  finite : ∀ v, Module.Finite (CompletionIntegers v) (lattice v)
  finrank : ∀ v, Module.finrank (CompletionIntegers v) (lattice v) = r
  full : ∀ v, Submodule.span (Completion v)
    (lattice v : Set (Fin r → Completion v)) = ⊤

/-- The actual donor, instantiated by the free rank-`r` arithmetic vector
bundle's completed integral local lattice. -/
noncomputable def s1476ActualLocalization (r : Nat) :
    S1476ArithmeticVectorBundleLocalization r where
  lattice := s1476LocalLattice r
  integral := fun v => s1476LocalLattice_integral r v
  free := fun v => s1476LocalLatticeFree r v
  finite := fun v => s1476LocalLatticeFinite r v
  finrank := fun v => s1476LocalLattice_finrank r v
  full := fun v => s1476LocalLattice_span_eq_top r v

/-- Package a rank-`r` arithmetic-vector-bundle localization donor as the
S1215 HDD local lattice: the same rank, and the local lattice at every
output and place. -/
noncomputable def S1476ArithmeticVectorBundleLocalization.toS1215
    {r : Nat} (D : S1476ArithmeticVectorBundleLocalization r)
    (I : Input Label Choice) : S1215HDDLocalLattice (I := I) where
  rank := r
  lattice := fun _ v =>
    (D.lattice v : Set (Fin r → (oneColumnStructure).localField v))

noncomputable def s1476S1215HDDLocalLattice (I : Input Label Choice) :
    S1215HDDLocalLattice (I := I) :=
  (s1476ActualLocalization 2).toS1215 (I := I)

@[simp] theorem s1476S1215HDDLocalLattice_rank (I : Input Label Choice) :
    (s1476S1215HDDLocalLattice (I := I)).rank = 2 := rfl

theorem s1476S1215HDDLocalLattice_rank_gt_one (I : Input Label Choice) :
    1 < (s1476S1215HDDLocalLattice (I := I)).rank := by
  rw [s1476S1215HDDLocalLattice_rank]
  norm_num

theorem s1476S1215HDDLocalLattice_lattice (I : Input Label Choice)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (s1476S1215HDDLocalLattice (I := I)).lattice o v =
      (s1476LocalLattice 2 v : Set (Fin 2 → (oneColumnStructure).localField v)) := rfl

theorem s1476S1215HDDLocalLattice_integral (I : Input Label Choice)
    (o : Theorem311Output I) (v : NumberField.FinitePlace ℚ)
    {x : Fin 2 → (oneColumnStructure).localField v}
    (hx : x ∈ (s1476S1215HDDLocalLattice (I := I)).lattice o v) :
    ∀ i, x i ∈ (CompletionIntegers v : Set (Completion v)) := by
  exact s1476LocalLattice_integral 2 v hx

theorem s1476S1215HDDLocalLattice_output_independent (I : Input Label Choice)
    (o o' : Theorem311Output I) :
    (s1476S1215HDDLocalLattice (I := I)).lattice o =
      (s1476S1215HDDLocalLattice (I := I)).lattice o' := rfl

theorem s1476S1215FirstField_inhabited (I : Input Label Choice) :
    Nonempty (S1215HDDLocalLattice (I := I)) :=
  ⟨s1476S1215HDDLocalLattice (I := I)⟩

/-- The exact first field recorded by S1418 is inhabited by the actual
rank-2 arithmetic vector bundle localization donor. -/
theorem s1476S1418FirstField_inhabited (I : Input Label Choice) :
    Nonempty (S1418HDDLocalLatticeRequired (I := I)) :=
  ⟨s1476S1215HDDLocalLattice (I := I)⟩

section Checks

#check S1476GlobalSections
#check S1476RankArithmeticVectorBundle
#check s1476GlobalLocalization
#check s1476FreeArithmeticVectorBundle
#check s1476GlobalSections_finrank
#check s1476GlobalLocalization_mem_localLattice
#check s1476IntegralMap
#check s1476LocalLattice
#check s1476LocalLatticeEquiv
#check s1476LocalLatticeFree
#check s1476LocalLatticeFinite
#check s1476LocalLattice_finrank
#check s1476LocalLattice_integral
#check s1476LocalLattice_span_eq_top
#check s1476ActualLocalization
#check S1476ArithmeticVectorBundleLocalization.toS1215
#check s1476S1215HDDLocalLattice
#check s1476S1215HDDLocalLattice_rank
#check s1476S1215HDDLocalLattice_rank_gt_one
#check s1476S1215HDDLocalLattice_lattice
#check s1476S1215HDDLocalLattice_integral
#check s1476S1215HDDLocalLattice_output_independent
#check s1476S1215FirstField_inhabited
#check s1476S1418FirstField_inhabited

end Checks

end LeanFormal.IUT.XiFPaper.S1476HDDRankActual

end