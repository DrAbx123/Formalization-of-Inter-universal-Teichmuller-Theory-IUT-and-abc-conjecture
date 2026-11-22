import tmp.sheaf.xif.paper.S2100GPresentationConeEssSurjActual
import tmp.sheaf.xif.paper.S2086ToAAssemblyActual

/-! # S2103: S2086 assembly with strong g-presentations

S2094GPresentationConeEssSurj is false (S2100).  The corrected input is a
strong finite-etale structure on every cover map `g.map`, giving strong
presentations.  The butterfly pullback is then demanded only for those strong
presentations.  No weak/universal claim over arbitrary presentations is made.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1852CoherentCoverActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual
open LeanFormal.IUT.XiFPaper.S2069D6CompositionClosureActual
open LeanFormal.IUT.XiFPaper.S2086ToAAssemblyActual
open LeanFormal.IUT.XiFPaper.S2100GPresentationConeEssSurjActual

universe u

/-- The strong finite-etale structure on every cover map. -/
def S2103StrongCospanGMapFiniteEtale : Type 1 :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    StrongEtaleStackFiniteEtaleMorphism g.map

/-- The corrected butterfly pullback, demanded only for the strong
presentations selected by the strong structure. -/
def S2103StrongBaseChangePullback
    (hg : S2103StrongCospanGMapFiniteEtale) : Type _ :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (T : SchemeOverField S1726K)
    (ptA : Pseudofunctor.StrongTrans
      (schemeRepresentableEtalePseudofunctor S1726K T) A.source.fiber),
    (S2086ToASquare f g T ptA
      ((hg A B C f g).baseChange T (S2086PointC f ptA)).toWeak).TwoPullbackWitness

/-- Strong inputs give `S2044ToAFiniteEtaleField`. -/
noncomputable def S2103ToAOfStrongInputs
    (hg : S2103StrongCospanGMapFiniteEtale)
    (h : S2103StrongBaseChangePullback hg) : S2044ToAFiniteEtaleField := by
  intro A B C f g
  refine { baseChange := ?_, hasProperty := ?_ }
  · intro T ptA
    let Pg := (hg A B C f g).baseChange T (S2086PointC f ptA)
    exact S2086ToAPresentation f g T ptA Pg.toWeak
      (h A B C f g T ptA)
  · intro T ptA
    exact (hg A B C f g).hasProperty T (S2086PointC f ptA)

/-- D6(c) finite etaleness from the strong inputs. -/
noncomputable def S2103D6FiniteEtaleOfStrongInputs
    (hg : S2103StrongCospanGMapFiniteEtale)
    (h : S2103StrongBaseChangePullback hg)
    {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S2043FirstMissingFiniteEtale (A := A) (B := B) (C := C) (f := f) (g := g) :=
  S2044FiniteEtaleOfClosure S2069CompositionClosure (S2103ToAOfStrongInputs hg h)

#print axioms S2103ToAOfStrongInputs
#print axioms S2103D6FiniteEtaleOfStrongInputs

end LeanFormal.IUT.XiFPaper.S2103StrongAssemblyActual

end
