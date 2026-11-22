import tmp.sheaf.xif.paper.Mzk1Section0PathCompositionActual

/-!
# Mzk1Section0PathLawActual — derived category laws for the Section-0 path model
(new theorems from the existing PathData asset: length additivity, append assoc/unit,
reverse-append). No copies/bookkeeping; no axiom/sorry.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 1000000

namespace LeanFormal.IUT.XiFPaper.Mzk1Section0PathLawActual

open LeanFormal.IUT.XiFPaper.Section0PathCompositionActual

universe u

variable {V E : Type*}

/-- Derived: length is additive under path concatenation. -/
theorem pdAppend_length (p q : PathData V E) (h : p.end_ = q.start) :
    pdLength (pdAppend p q h) = pdLength p + pdLength q := by
  cases p
  cases q
  simp [pdAppend, pdLength, List.length_append]

/-- Derived: concatenation is associative (with the induced endpoint proofs). -/
theorem pdAppend_assoc (p q r : PathData V E) (h1 : p.end_ = q.start)
    (h2 : q.end_ = r.start) :
    pdAppend (pdAppend p q h1) r (by simpa [pdAppend] using h2) =
      pdAppend p (pdAppend q r h2) (by simpa [pdAppend] using h1) := by
  cases p
  cases q
  cases r
  simp [pdAppend, List.append_assoc]

/-- Derived: appending the empty path on the right is the identity. -/
theorem pdAppend_nil_right (p : PathData V E) :
    pdAppend p (pdNil (E := E) p.end_) rfl = p := by
  cases p
  simp [pdAppend, pdNil]

/-- Derived: appending the empty path on the left is the identity. -/
theorem pdAppend_nil_left (p : PathData V E) :
    pdAppend (pdNil (E := E) p.start) p rfl = p := by
  cases p
  simp [pdAppend, pdNil]

/-- Derived: reversing a concatenation swaps the summands. -/
theorem pdReverse_append (p q : PathData V E) (h : p.end_ = q.start) :
    pdReverse (pdAppend p q h) =
      pdAppend (pdReverse q) (pdReverse p) (by simpa [pdReverse] using h.symm) := by
  cases p
  cases q
  simp [pdAppend, pdReverse, List.reverse_append]

#check pdAppend_length
#check pdAppend_assoc
#check pdAppend_nil_right
#check pdAppend_nil_left
#check pdReverse_append

end LeanFormal.IUT.XiFPaper.Mzk1Section0PathLawActual
end
