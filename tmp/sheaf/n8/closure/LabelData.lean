import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Data.Fintype.Card

/-!
# N8 label data — paper labels are finite sets with permutation automorphisms

Paper: IUT III corpus 544–570.  The labels are `S_{j+1} = {0, ..., j}` with
arbitrary permutation automorphisms; they are NOT an additive group.  The
production `[AddGroup Label]` index used by C0 is a separate object and is
compared to the label set only by an explicit transport obligation.

`LabelData` records a finite label set together with an arbitrary permutation
automorphism.  `ProcessionLabelData` adds the procession level and
`card = level + 1`.  `C0AdditiveLabelTransport` is the separate explicit
comparison between a C0 production additive index and a `LabelData` set; it
does not assert that the additive group is the paper label set.
-/

noncomputable section

namespace LeanFormal.IUT.N8Closure.LabelData

universe u

/-- A finite label set with an arbitrary permutation automorphism. -/
structure LabelData where
  /-- The finite label set. -/
  Labels : Type u
  /-- Finite cardinality. -/
  fintype : Fintype Labels
  /-- An arbitrary permutation automorphism (paper: no preferred one). -/
  permAction : Equiv.Perm Labels

attribute [instance] LabelData.fintype

/-- A procession label set: level `j`, labels `S_{j+1}`, cardinal `j+1`, and
an arbitrary permutation automorphism. -/
structure ProcessionLabelData where
  /-- Procession level `j`. -/
  level : Nat
  /-- The finite label set of the procession. -/
  labels : LabelData
  /-- Paper cardinality `card S_{j+1} = j + 1`. -/
  card_eq : Fintype.card labels.Labels = level + 1
  /-- Arbitrary permutation automorphism of the label set. -/
  permAction : Equiv.Perm labels.Labels

/-- C0 production additive index.  This is the index used by C0's
`[AddGroup Label]` signature; it is not identified with the paper label set. -/
structure C0ProductionAdditiveIndex where
  /-- The additive production index type. -/
  Index : Type u
  /-- The additive group structure used by C0. -/
  addGroup : AddGroup Index

attribute [instance] C0ProductionAdditiveIndex.addGroup

/-- Explicit C0 additive-index ↔ paper-label-set comparison obligation.
This is the only transport from the production additive index to the finite
label set; it is a plain equivalence, not an additive/group isomorphism, and
it does not replace `[AddGroup Label]` by the paper label set. -/
structure C0AdditiveLabelTransport (A : C0ProductionAdditiveIndex)
    (P : LabelData) where
  /-- Explicit comparison of the additive production index with the label set. -/
  indexEquiv : A.Index ≃ P.Labels

end LeanFormal.IUT.N8Closure.LabelData