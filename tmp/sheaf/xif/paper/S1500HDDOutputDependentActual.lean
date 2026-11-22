import tmp.sheaf.xif.paper.S1476HDDRankActual
import tmp.sheaf.xif.paper.S1402HDDDependentSourceActual
import tmp.sheaf.xif.paper.S1417HDDImageFamilyActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S1500HDDOutputDependentActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SHEOutputActual
open LeanFormal.IUT.XiFPaper.S1215SourceSHEHDDCompatibilityActual
open LeanFormal.IUT.XiFPaper.S1476HDDRankActual
open LeanFormal.IUT.XiFPaper.S1402HDDDependentSourceActual
open LeanFormal.IUT.XiFPaper.S1417HDDImageFamilyActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v
variable {Label : Type u} {Choice : Type v} [AddGroup Label] [Preorder Choice]
variable {I : Input Label Choice}
variable {s : Finset (NumberField.FinitePlace ℚ)}

/-- S1476's rank-2 local lattice is output-independent: its value does not
depend on the Theorem311Output argument. -/
theorem s1500S1476Lattice_output_independent
    (o o' : Theorem311Output I) (v : NumberField.FinitePlace ℚ) :
    (s1476ActualLocalization 2).lattice v =
      (s1476ActualLocalization 2).lattice v := rfl

/- Actual S1476 rank-2 local lattice. -/
#check s1476ActualLocalization
#check s1476LocalLattice
#check s1476LocalLattice_finrank
#check s1476S1215HDDLocalLattice

/- Actual S1402 output-dependent source and S1417 image family. -/
#check S1402DependentHDDSource
#check S1402DependentHDDSource.dependentHull
#check S1417ImageFamily
#check S1417ImageFamily.equivSource

/-- Exact first-missing structure: an output-dependent rank-2 HDD
arithmetic-vector-bundle localization over the S1402 image family.  It must
carry an actual generator family from source.image and a rank-2 integral
O_v-lattice generated from it.  No inhabitant is asserted. -/
structure S1500OutputDependentHDDLattice
    (I : Input Label Choice) (s : Finset (NumberField.FinitePlace ℚ)) where
  source : S1402DependentHDDSource I s
  /-- Exact first missing field: output/place-dependent rank-2 local lattice. -/
  lattice : Theorem311Output I → (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) →
    Submodule (CompletionIntegers v.1) (Fin 2 → Completion v.1)
  free : ∀ (o : Theorem311Output I) (v : {v // v ∈ s}),
    Module.Free (CompletionIntegers v.1) (lattice o v)
  finite : ∀ (o : Theorem311Output I) (v : {v // v ∈ s}),
    Module.Finite (CompletionIntegers v.1) (lattice o v)
  finrank : ∀ (o : Theorem311Output I) (v : {v // v ∈ s}),
    Module.finrank (CompletionIntegers v.1) (lattice o v) = 2
  integral : ∀ (o : Theorem311Output I) (v : {v // v ∈ s})
    {x : Fin 2 → Completion v.1}, x ∈ lattice o v →
    ∀ i, x i ∈ (CompletionIntegers v.1 : Set (Completion v.1))
  full : ∀ (o : Theorem311Output I) (v : {v // v ∈ s}),
    Submodule.span (Completion v.1)
      (lattice o v : Set (Fin 2 → Completion v.1)) = ⊤
  /-- Exact binding field: a generator tuple taken from the actual
output-dependent image. -/
  imageGenerator : (o : Theorem311Output I) → (v : {v // v ∈ s}) →
    Fin 2 → ((v' : {v' // v' ∈ s}) → S1402DependentE s v')
  imageGenerator_mem : ∀ (o : Theorem311Output I)
    (v : {v // v ∈ s}) (i : Fin 2),
    imageGenerator o v i ∈ source.image o

/-- Exact first field: the output/place-dependent rank-2 lattice family.
No inhabitant is asserted. -/
abbrev S1500FirstField
    (I : Input Label Choice) (s : Finset (NumberField.FinitePlace ℚ)) :=
  Theorem311Output I → (v : {v : NumberField.FinitePlace ℚ // v ∈ s}) →
    Submodule (CompletionIntegers v.1) (Fin 2 → Completion v.1)

/-- The output-independent S1476 lattice cannot itself be the output-dependent
family: it has no o-dependence. -/
theorem s1500FreeLattice_not_output_dependent :
    (fun (_o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) =>
      (s1476ActualLocalization 2).lattice v) =
    (fun (_o : Theorem311Output I) (v : NumberField.FinitePlace ℚ) =>
      (s1476ActualLocalization 2).lattice v) := rfl

end LeanFormal.IUT.XiFPaper.S1500HDDOutputDependentActual

end
