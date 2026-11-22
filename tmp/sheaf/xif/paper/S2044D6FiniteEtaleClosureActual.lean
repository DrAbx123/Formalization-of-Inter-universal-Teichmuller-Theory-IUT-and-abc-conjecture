import tmp.sheaf.xif.paper.S2043D6StructureMapEqActual

/-! # S2044: D6(c) finite-etale data: exact closure reduction

`S2043FirstMissingFiniteEtale` is `EtaleStackFiniteEtaleMorphism (structureMap f g)`
with `structureMap f g = vcomp (toA f g) A.map`.  This file records the two
actual closure facts still missing and proves that they give the finite-etale
certificate:

1. `S2044ToAFiniteEtaleField`: the iso-comma first projection `toA f g` is
   representably finite etale;
2. `S2044CompositionClosure`: representable finite etaleness is closed under
   composition of stack morphisms (the pasting of two base-change squares).

Neither is in the tree: `EtaleStackRepresentableMorphismProperty` has no
composition or iso-invariance API, and no finite-etale certificate for the
iso-comma projection `toA` is constructed.  No fake certificate is introduced;
the final finiteEtale is only derived under the two explicitly named closure
fields.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual

open CategoryTheory
open CategoryTheory.Bicategory
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

universe u
variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

/-- Exact missing closure field 1: representable finite etaleness of the
iso-comma first projection. -/
def S2044ToAFiniteEtaleField : Type 1 :=
  ∀ (A B C : S1728Cover) (f : S1728CoverMap A C) (g : S1728CoverMap B C),
    EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g)

/-- Exact missing closure field 2: representable finite etaleness is closed
under composition of stack morphisms (pasting of base-change squares). -/
def S2044CompositionClosure : Type 1 :=
  ∀ {X Y Z : EtaleStackOverField S1726K}
    (p : X.Hom Y) (q : Y.Hom Z),
    EtaleStackFiniteEtaleMorphism p →
    EtaleStackFiniteEtaleMorphism q →
    EtaleStackFiniteEtaleMorphism
      (Pseudofunctor.StrongTrans.vcomp p q)

/-- The two closure fields give the remaining D6(c) finite-etale certificate
for `structureMap = toA ≫ A.map`. -/
noncomputable def S2044FiniteEtaleOfClosure
    (hcomp : S2044CompositionClosure)
    (htoA : S2044ToAFiniteEtaleField) :
    S2043FirstMissingFiniteEtale (f := f) (g := g) := by
  have hA : EtaleStackFiniteEtaleMorphism A.map :=
    A.finiteEtale
  have hto : EtaleStackFiniteEtaleMorphism
      (source := S2042IsoCommaStackObj (f := f) (g := g))
      (target := A.source) (toA f g) :=
    htoA A B C f g
  have h := hcomp (X := S2042IsoCommaStackObj (f := f) (g := g))
    (Y := A.source) (Z := S1726Orbicurve.stack) (toA f g) A.map hto hA
  exact h

#print axioms S2044FiniteEtaleOfClosure

end LeanFormal.IUT.XiFPaper.S2044D6FiniteEtaleClosureActual

end
