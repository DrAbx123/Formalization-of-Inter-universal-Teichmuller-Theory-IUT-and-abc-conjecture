import LeanFormal.IUT.IUTIII.Theorem311.Output.SourceMultiradialPresentationWiring
import Mathlib.Tactic

/-!
# Column insensitivity of the reduced multiradial record (APT-1 assessment)

Source-level APT-1 assessment (root continuation).  The paper's comparison
content across adjacent columns is IUT III, Remark 3.11.1, (i)
(corpus III.txt:9620-9634: the construction algorithm relates the vertical
line `(n,∘)` to the a priori alien arithmetic holomorphic structure of the
vertical line `(n+1,∘)`), the functoriality of the algorithm with respect to
isomorphisms of the input F-times-mu-prime-strips (Remark 3.11.1, (ii),
corpus III.txt:9651-9675), and its compatibility with the etale-picture
permutation symmetries (Theorem 3.11, (i), final portion, corpus
III.txt:9601-9615).

This file proves the interface-level fact that decides what the column
parameter of the *reduced* record can carry:

* `columnReindex` and `columnReindexEquivalence`: every
  `SourceTheorem311MultiradialAlgorithm` instance carries over to every other
  column with all data unchanged, and is two-action equivalent to its
  re-indexing by identity transport.  In the reduced interface the column
  parameter is therefore *phantom*: an interface-level comparison across any
  two columns with identity transport always exists.

Consequence (recorded as the audit card
`IUT-III.multiradial-algorithm.source-column-phantom`): the non-trivial
content of the APT-1 finite test (`finiteKernelTwoColumnComparison`, report
section 19) lies in the (Ind2) translate, not in the column difference.  The
paper's `(n,∘)` vs `(n+1,∘)` distinction corresponds to the two arithmetic
holomorphic structures linked by the Theta-link; the tree's reduced linking
datum is the FPrimeStrip-level `sourceAdjacentCoreLinkIsomorphism`
(StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:252, read-only), and
no bridge from it to the algorithm's abstract `Output` exists.  This file
therefore sharpens the boundary only; the source-level comparison stays the
named card `IUT-III.source-APT-transport-supply` (APT.lean:457), unchanged.
-/

namespace LeanFormal.IUT

noncomputable section

universe uG₁ uG₂ ua uv upi umon ui uOut

namespace SourceMultiradialColumnInsensitivity

open Theorem311Source

variable {l : PrimeGeFive} {V : Type uv}
variable {G₁ : Type uG₁} [Group G₁] {G₂ : Type uG₂} [Group G₂]
variable {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
variable {Output : Type uOut}

/-- Re-index a reduced multiradial algorithm instance to another column.  The
    `Int` column parameter occurs in no field of the record, so all data is
    reused; the record is rebuilt field-wise because the instance type at the
    new column is a different type. -/
def columnReindex {n n' : Int}
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) :
    SourceTheorem311MultiradialAlgorithm G₁ G₂ I n' Output where
  presentation :=
    { output := A.presentation.output
      processionAction := A.presentation.processionAction }
  ind2Action := A.ind2Action
  ind1_ind2_commute := A.ind1_ind2_commute

@[simp] theorem columnReindex_output {n n' : Int}
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) :
    (columnReindex (n' := n') A).presentation.output = A.presentation.output :=
  rfl

@[simp] theorem columnReindex_ind1Action {n n' : Int}
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output)
    (g : G₁) (o : Output) :
    (columnReindex (n' := n') A).ind1Action g o = A.ind1Action g o :=
  rfl

@[simp] theorem columnReindex_ind2Action {n n' : Int}
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output)
    (g : G₂) (o : Output) :
    (columnReindex (n' := n') A).ind2Action g o = A.ind2Action g o :=
  rfl

/-- The re-indexed instance is two-action equivalent to the original by the
    identity transport: in the reduced interface the column parameter carries
    no data. -/
def columnReindexEquivalence {n n' : Int}
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) :
    SourceTheorem311TwoActionEquivalence A (columnReindex (n' := n') A) where
  ind1GroupEquiv := MulEquiv.refl G₁
  outputEquiv := Equiv.refl Output
  preserves_ind1 := fun _ _ => rfl
  preserves_ind2 := fun _ _ => rfl

/-- Every instance carries an identity-transport comparison to every other
    column: an interface-level artifact of the phantom column parameter. -/
theorem columnComparison_exists {n n' : Int}
    (A : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n Output) :
    ∃ A' : SourceTheorem311MultiradialAlgorithm G₁ G₂ I n' Output,
      Nonempty (SourceTheorem311TwoActionEquivalence A A') :=
  ⟨columnReindex (n' := n') A, ⟨columnReindexEquivalence A⟩⟩

/-! ## Finite-model instantiation -/

section FiniteModel

open ConcreteFiniteTheorem311
open SourceMultiradialPresentationWiring

/-- The re-indexing of the finite kernel-form instance is the instance at the
    new column: `columnReindex` and the section-5 constructor agree. -/
theorem finiteKernelColumnReindex_eq (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l)) :
    columnReindex (n' := n + 1)
        (finiteKernelSourceAlgorithm l I n input) =
      finiteKernelSourceAlgorithm l I (n + 1) input :=
  rfl

/-- At the finite kernel-form instance, the identity-transport comparison
    across the adjacent columns `n` and `n + 1` exists for the same input.
    The non-trivial transport of `finiteKernelTwoColumnComparison` therefore
    owes its content to the (Ind2) translate, not to the column difference. -/
theorem finiteKernelColumnComparison_identity_exists (l : PrimeGeFive)
    (I : OriginalInput.{ua, uv, upi, umon, ui} l V) (n : Int)
    (input : ParametricTheorem311.AlgorithmInput
      (SourceFiniteParameterized.carrier l)) :
    Nonempty (SourceTheorem311TwoActionEquivalence
      (finiteKernelSourceAlgorithm l I n input)
      (finiteKernelSourceAlgorithm l I (n + 1) input)) := by
  rw [← finiteKernelColumnReindex_eq l I n input]
  exact ⟨columnReindexEquivalence _⟩

end FiniteModel

end SourceMultiradialColumnInsensitivity

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record: the reduced record's column parameter is phantom; the
    source-level APT-1 comparison needs the paper's actual linking data, not
    an interface-level column change. -/
def sourceMultiradialColumnInsensitivityRecord : Obligation :=
  { id := "IUT-III.multiradial-algorithm.source-column-phantom"
    source :=
      "IUT III, Theorem 3.11, (i) (functoriality and compatibility with " ++
        "the etale-picture permutation symmetries; corpus III.txt:9601-9615); " ++
        "Remark 3.11.1, (i) (vertical lines (n,∘) vs (n+1,∘); corpus " ++
        "III.txt:9620-9634); Remark 3.11.1, (ii) (input functoriality; " ++
        "corpus III.txt:9651-9675)"
    status := VerificationStatus.provedKernel
    note :=
      "`columnReindex` and `columnReindexEquivalence` (finite-model " ++
        "instance: `finiteKernelColumnComparison_identity_exists`, with " ++
        "`finiteKernelColumnReindex_eq`) prove that in the reduced " ++
        "interface the `Int` column parameter of " ++
        "`SourceTheorem311MultiradialAlgorithm` is phantom: every instance " ++
        "carries over to every column with unchanged data and is " ++
        "two-action equivalent to its re-indexing by identity transport.  " ++
        "Consequence for APT-1: an interface-level two-column comparison " ++
        "with identity transport always exists, so the non-trivial content " ++
        "of `finiteKernelTwoColumnComparison` (report section 19) comes " ++
        "from the (Ind2) translate, not from the column difference.  The " ++
        "paper's `(n,∘)` vs `(n+1,∘)` distinction corresponds to the two " ++
        "arithmetic holomorphic structures linked by the Theta-link; the " ++
        "tree's reduced linking datum is the FPrimeStrip-level " ++
        "`sourceAdjacentCoreLinkIsomorphism` " ++
        "(StepXI/SourceAdjacentColumnProcessionIsomorphism.lean:252) and no " ++
        "bridge from it to the algorithm's abstract `Output` exists, so the " ++
        "source-level comparison remains the named card " ++
        "`IUT-III.source-APT-transport-supply` (APT.lean:457).  Proved " ++
        "kernel about the reduced interface only; no source-level claim."
    dependsOn :=
      [ "IUT-III.source-multiradial-two-action-equivalence",
        "IUT-III.source-APT-transport-supply" ] }

end LeanFormal.IUT.Audit
