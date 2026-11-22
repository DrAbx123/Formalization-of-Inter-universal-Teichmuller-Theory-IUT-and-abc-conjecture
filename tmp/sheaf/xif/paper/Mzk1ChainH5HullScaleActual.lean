import tmp.sheaf.xif.paper.Mzk1H5HullBoundActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Mzk1ChainH5HullScaleActual — finite-list scaling closure for H5 hulls

Genuine new induction: if a point lies in an H5 hull, then scaling it successively
by any finite list of rational scalars (via the hull scale action) remains in the
hull.  Reuses the EXIT0 H5HullBound scale-membership law.
No new paper input; no closure; gate NOT PASSED; registry 14041. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1ChainH5HullScaleActual

open LeanFormal.IUT.XiFPaper.Mzk1H5HullBoundActual

/-- Finite-list scaling closure for an H5 hull. -/
theorem h5Hull_scaleFold_mem {C : Type*} (d : H5HullBound C) (as : List ℚ)
    {x : C} (hx : x ∈ d.hull) :
    as.foldl (fun y a => d.scale a y) x ∈ d.hull := by
  induction as generalizing x with
  | nil => simpa
  | cons a as ih =>
      simp only [List.foldl_cons]
      exact ih (d.scale_mem a hx)

/-- Scaling by a two-element list (explicit composition form). -/
theorem h5Hull_scale_two_mem {C : Type*} (d : H5HullBound C) (a b : ℚ)
    {x : C} (hx : x ∈ d.hull) :
    d.scale b (d.scale a x) ∈ d.hull :=
  h5Hull_scaleFold_mem d [a, b] hx

end LeanFormal.IUT.XiFPaper.Mzk1ChainH5HullScaleActual

end
