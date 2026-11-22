import tmp.sheaf.xif.paper.S2088GMapCancellationActual

/-! # S2091: direct scheme-level cancellation for cover-map structure maps

Specialization of `S2088_scheme_finiteEtale_cancel`: if `f ≫ h` is finite
etale and `h` is finite etale, then `f` is finite etale.  This is the
scheme-level statement needed for the cover-map comparison
`B.structureMap = g.map ≫ C.structureMap` after base change to schemes.

It does NOT by itself prove the stack-level `EtaleStackFiniteEtaleMorphism
(g.map)`: that still requires a presentation of `g.map` at each scheme point
of `C.source`.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2091SchemeDirectActual

open CategoryTheory
open AlgebraicGeometry
open LeanFormal.IUT.XiFPaper.S2088GMapCancellationActual

universe u
variable {X Y Z : Scheme.{u}}

/-- Direct scheme-level cancellation for a finite-etale right factor. -/
theorem S2091_scheme_finiteEtale_cancel_special
    (f : X ⟶ Y) (h : Y ⟶ Z)
    [IsFinite (f ≫ h)] [Etale (f ≫ h)] [IsFinite h] [Etale h] :
    IsFinite f ∧ Etale f := by
  haveI : LocallyOfFiniteType h := inferInstance
  haveI : FormallyUnramified h := inferInstance
  haveI : IsSeparated h := inferInstance
  exact ⟨(S2088_scheme_finiteEtale_cancel f h).2,
    (S2088_scheme_finiteEtale_cancel f h).1⟩

#print axioms S2091_scheme_finiteEtale_cancel_special

end LeanFormal.IUT.XiFPaper.S2091SchemeDirectActual

end
