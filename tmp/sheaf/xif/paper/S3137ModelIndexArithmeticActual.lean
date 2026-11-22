import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput
import LeanFormal.IUT.Audit.Status

/-! # S3137: model index arithmetic (from-scratch model, task-72)

INDEX_EQUIV/permutation/shift half of the model skeleton.  SourceTheorem311Index
is definitionally Int × Int (SourceOriginalInput.lean:39); horizontal/vertical
shifts are the production definitions.  Data + proofs only.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.S3137ModelIndexArithmeticActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.Audit

variable {l : PrimeGeFive}

/-- Model index = the paper source index (Int × Int). -/
abbrev ModelIndex : Type := SourceTheorem311Index

/-- Index equivalence half (constructible). -/
def modelIndexEquiv : ModelIndex ≃ SourceTheorem311Index :=
  Equiv.refl _

@[simp] theorem modelIndexEquiv_apply (p : ModelIndex) :
    modelIndexEquiv p = p :=
  rfl

@[simp] theorem modelIndexEquiv_symm_apply (p : SourceTheorem311Index) :
    modelIndexEquiv.symm p = p :=
  rfl

/-- Trivial permutation half (constructible). -/
def modelPermutation : Equiv.Perm ModelIndex :=
  Equiv.refl _

@[simp] theorem modelPermutation_apply (p : ModelIndex) :
    modelPermutation p = p :=
  rfl

/-- Horizontal lattice shift (production definition). -/
def modelHorizontalShift (p : ModelIndex) : ModelIndex := horizontalIndex p

/-- Vertical lattice shift (production definition). -/
def modelVerticalShift (p : ModelIndex) : ModelIndex := verticalIndex p

@[simp] theorem modelHorizontalShift_apply (p : ModelIndex) :
    modelHorizontalShift p = horizontalIndex p := rfl

@[simp] theorem modelVerticalShift_apply (p : ModelIndex) :
    modelVerticalShift p = verticalIndex p := rfl

/-- Re-export: a natural from-scratch model must align its arithmetic with the
initial data via OriginalInput.arithmetic_alignment; the index half above is
already the paper index up to refl. -/
theorem modelIndex_refl_aligns (p : ModelIndex) :
    modelIndexEquiv p = p := rfl

end LeanFormal.IUT.XiFPaper.S3137ModelIndexArithmeticActual

namespace LeanFormal.IUT.Audit

/-- INDEX: from-scratch model index arithmetic (constructible). -/
def S3137ModelIndexArithmeticRecord : Obligation :=
  { id := "INDEX.MODEL.from-scratch-index-arithmetic"
    source := "IUT I Definition 3.1; SourceOriginalInput.lean:39-46"
    status := VerificationStatus.interface
    note := "CONSTRUCTIBLE: SourceTheorem311Index := Int × Int (production); modelIndexEquiv = Equiv.refl; modelPermutation = Equiv.refl; modelHorizontalShift/modelVerticalShift = production horizontalIndex/verticalIndex. File S3137ModelIndexArithmeticActual EXIT0 + probe. Not a residual."
    dependsOn := ["S3137ModelIndexArithmeticActual"] }

end LeanFormal.IUT.Audit
