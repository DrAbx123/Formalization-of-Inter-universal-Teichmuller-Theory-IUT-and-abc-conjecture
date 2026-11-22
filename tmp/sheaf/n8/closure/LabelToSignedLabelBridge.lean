/-
# LabelToSignedLabelBridge

Bridge from `ProcessionLabelData` (finite paper label set, card = level+1) to
the signed-label interval `SignedLabel l.value` (card = l.value).  The bridge
uses `Fintype.equivOfCardEq`, so it is an arbitrary equivalence, not a group
isomorphism and not an additive structure.
-/
import tmp.sheaf.n8.closure.LabelData
import LeanFormal.IUT.Foundations.Theta.SignedLabelEquiv

noncomputable section

namespace LeanFormal.IUT.N8Closure.LabelToSignedLabelBridge

open LeanFormal.IUT.N8Closure.LabelData
open LeanFormal.IUT

/-- The finite paper label set of a procession has card `level + 1`, hence card
`l.value` whenever `l.value = level + 1`. -/
theorem card_labels_eq_signedLabel
    (l : PrimeGeFive) (P : ProcessionLabelData)
    (hcard : l.value = P.level + 1) :
    Fintype.card P.labels.Labels = Fintype.card (SignedLabel l.value) := by
  rw [P.card_eq, SignedLabel.card_signedLabel, hcard]

/-- Arbitrary equivalence from the procession label set to signed labels. -/
def labelEquiv
    (l : PrimeGeFive) (P : ProcessionLabelData)
    (hcard : l.value = P.level + 1) :
    P.labels.Labels ≃ SignedLabel l.value :=
  Fintype.equivOfCardEq (card_labels_eq_signedLabel l P hcard)

@[simp] theorem labelEquiv_apply_card
    (l : PrimeGeFive) (P : ProcessionLabelData)
    (hcard : l.value = P.level + 1) :
    Fintype.card P.labels.Labels = l.value := by
  rw [P.card_eq, hcard]

/-- The exponent map `j ↦ (e j).1 ^ 2` attached to the bridge. -/
def exponentMap
    (l : PrimeGeFive) (P : ProcessionLabelData)
    (hcard : l.value = P.level + 1) :
    P.labels.Labels → Int := by
  intro j
  exact (labelEquiv l P hcard j).1 ^ 2

@[simp] theorem exponentMap_apply
    (l : PrimeGeFive) (P : ProcessionLabelData)
    (hcard : l.value = P.level + 1) (j : P.labels.Labels) :
    exponentMap l P hcard j = (labelEquiv l P hcard j).1 ^ 2 := rfl

#check card_labels_eq_signedLabel
#check labelEquiv
#check exponentMap
#print axioms labelEquiv
#print axioms exponentMap
end LeanFormal.IUT.N8Closure.LabelToSignedLabelBridge
end