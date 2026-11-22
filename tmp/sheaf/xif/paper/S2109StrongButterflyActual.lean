import tmp.sheaf.xif.paper.S2103StrongAssemblyActual
import tmp.sheaf.xif.paper.S2097BaseChangeButterflyActual

/-! # S2109: strong-input butterfly, replacing the refuted weak hG

S2108 used `S2094GPresentationConeEssSurj`, which S2100 refutes.  This file
uses only strong finite-etale structures on `g.map` (S2103 input) and the
actual pasted-square full data for those strong presentations.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2109StrongButterflyActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2094FullUniversalInputsActual
open LeanFormal.IUT.XiFPaper.S2097BaseChangeButterflyActual
open LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual

universe u

/-- Strong butterfly input: only big-square full property and pasted-square
full data for the strong presentations selected by a strong finite-etale
structure. -/
structure S2109StrongPastedFull
    (hg : S2103StrongCospanGMapFiniteEtale) : Type 1 where
  bigSquare : S2094BigSquareEssSurj
  pasted :
    forall (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
      (T : SchemeOverField S1726K)
      (ptA : Pseudofunctor.StrongTrans
        (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
      S2097PastedSquareFull f g T ptA
        ((hg A B C f g).baseChange T (S2086PointC f ptA)).toWeak

/-- Right-cancel plus the strong pasted data give the strong base-change
pullback. -/
noncomputable def S2109StrongBaseChangePullbackOfInputs
    (hRC : S2097RightCancelStatement)
    (hg : S2103StrongCospanGMapFiniteEtale)
    (h : S2109StrongPastedFull hg) :
    S2103StrongBaseChangePullback hg := by
  intro A B C f g T ptA
  let Pg := (hg A B C f g).baseChange T (S2086PointC f ptA)
  exact S2097BaseChangePullback_of_rightCancel f g T ptA Pg.toWeak
    hRC h.bigSquare (h.pasted A B C f g T ptA)

/-- D6(c) from right-cancel, strong pasted data, and the strong finite-etale
structure on every g.map. -/
noncomputable def S2109D6FiniteEtaleOfStrongInputs
    (hRC : S2097RightCancelStatement)
    (hg : S2103StrongCospanGMapFiniteEtale)
    (h : S2109StrongPastedFull hg)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (A := A) (B := B) (C := C) (f := f) (g := g) :=
  S2103D6FiniteEtaleOfStrongInputs hg
    (S2109StrongBaseChangePullbackOfInputs hRC hg h) f g

#print axioms S2109StrongBaseChangePullbackOfInputs
#print axioms S2109D6FiniteEtaleOfStrongInputs

end LeanFormal.IUT.XiFPaper.S2109StrongButterflyActual

end
