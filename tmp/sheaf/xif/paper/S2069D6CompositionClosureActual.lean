import tmp.sheaf.xif.paper.S2062TwoPullbackPasteActual
import tmp.sheaf.xif.paper.S2048FiniteEtaleCompSchemeActual

/-! # S2069: S2046CompositionStatement and S2044CompositionClosure from S2062

S2062 supplies the unconditional composition of base-change presentations
(`Iut.EtaleStackBaseChangePresentation.comp`) and of scheme-representable
projections (`Iut.SchemeRepresentableMap.comp`).  Combined with the
scheme-level finite-etale composition `S2048_isFinite_and_etale_comp`, this
gives the D6(c) composition closure unconditionally.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option synthInstance.maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S2046FiniteEtaleAPIGapActual
open LeanFormal.IUT.XiFPaper.S2048FiniteEtaleCompSchemeActual

universe u

/-- Unconditional composition of representably finite-etale stack morphisms
over S1726K. -/
noncomputable def S2069CompositionStatement :
    S2046CompositionStatement := by
  intro W Y Z f g hf hg
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T q
    exact EtaleStackBaseChangePresentation.comp
      (Pg := hg.baseChange T q)
      (Pf := hf.baseChange (hg.baseChange T q).pullbackScheme
        (hg.baseChange T q).toSource)
  · intro T q
    let Pg := hg.baseChange T q
    let Pf := hf.baseChange Pg.pullbackScheme Pg.toSource
    have hf' : AlgebraicGeometry.IsFinite Pf.projection.left ∧
        AlgebraicGeometry.Etale Pf.projection.left :=
      hf.hasProperty Pg.pullbackScheme Pg.toSource
    have hg' : AlgebraicGeometry.IsFinite Pg.projection.left ∧
        AlgebraicGeometry.Etale Pg.projection.left :=
      hg.hasProperty T q
    haveI := hf'.1
    haveI := hf'.2
    haveI := hg'.1
    haveI := hg'.2
    have h := S2048_isFinite_and_etale_comp
      (f := Pf.projection.left) (g := Pg.projection.left)
    exact h

open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual

/-- Unconditional S2044CompositionClosure. -/
noncomputable def S2069CompositionClosure : S2044CompositionClosure := by
  intro X Y Z p q hp hq
  exact S2069CompositionStatement (W := X) (Y := Y) (Z := Z) p q hp hq

/-- D6(c): given only the iso-comma projection certificate, the structure map
is representably finite etale. -/
noncomputable def S2069D6FiniteEtaleOfToA
    (htoA : S2044ToAFiniteEtaleField)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) :=
  S2044FiniteEtaleOfClosure S2069CompositionClosure htoA

#print axioms S2069CompositionStatement
#print axioms S2069CompositionClosure
#print axioms S2069D6FiniteEtaleOfToA

end LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual

end
