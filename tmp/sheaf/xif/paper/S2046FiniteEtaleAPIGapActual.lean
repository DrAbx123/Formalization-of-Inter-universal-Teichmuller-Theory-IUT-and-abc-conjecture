import tmp.sheaf.xif.paper.S2044D6FiniteEtaleClosureActual
import tmp.sheaf.xif.paper.S1892PullbackFiniteEtaleActual

/-! # S2046: D6(c) finite-etale API gap and exact lemma list

The remaining `S2043FirstMissingFiniteEtale` is reduced here to three
explicit Type-valued API statements (not Prop/Nonempty gates):

1. 2-isomorphism invariance of representable finite etaleness;
2. composition closure (pasting of the two base-change 2-pullback squares);
3. representable finite etaleness of the iso-comma first projection `toA`.

These are exactly the lemmas absent from `Iut/Foundations/Orbicurve.lean`.
Mathlib already supplies the scheme-level `Etale` composition instance; the
missing part is the stack-presentation pasting and the geometric `toA`
certificate.  No witness or certificate is fabricated.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2046FiniteEtaleAPIGapActual

open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1955AssembleCDActual
open LeanFormal.IUT.XiFPaper.S1985SiteLiftNaturalityActual
open LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual
open LeanFormal.IUT.XiFPaper.S2042D6GeometricHalfActual
open LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual
open LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual

universe u
variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

/-- Missing API lemma 1: invariance under 2-isomorphism. -/
def S2046IsoInvarianceStatement : Type 1 :=
  ∀ {W Z : EtaleStackOverField S1726K} {f g : W.Hom Z},
    Iso f g → EtaleStackFiniteEtaleMorphism f →
      EtaleStackFiniteEtaleMorphism g

/-- Missing API lemma 2: composition closure. -/
def S2046CompositionStatement : Type 1 :=
  ∀ {W Y Z : EtaleStackOverField S1726K} (f : W.Hom Y) (g : Y.Hom Z),
    EtaleStackFiniteEtaleMorphism f → EtaleStackFiniteEtaleMorphism g →
      EtaleStackFiniteEtaleMorphism (Pseudofunctor.StrongTrans.vcomp f g)

/-- Missing API lemma 3: the geometric `toA` finite-etale certificate. -/
def S2046ToAStatement : Type 1 :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g)

/-- The three API lemmas give the remaining D6(c) certificate. -/
noncomputable def S2046FiniteEtaleOfAPI
    (hcomp : S2046CompositionStatement)
    (htoA : S2046ToAStatement) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) := by
  have hA : EtaleStackFiniteEtaleMorphism A.map := A.finiteEtale
  have hto : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g) :=
    htoA A B C f g
  have h := hcomp (W := S2042IsoCommaStackObj (f := f) (g := g))
    (Y := A.source) (Z := S1726Orbicurve.stack) (toA f g) A.map hto hA
  exact h

#print axioms S2046FiniteEtaleOfAPI

end LeanFormal.IUT.XiFPaper.S2046FiniteEtaleAPIGapActual

end
