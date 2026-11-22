import tmp.sheaf.xif.paper.S2042D6GeometricHalfActual

/-! # S2043: D6(c) structureMap_eq' by bicategorical cancellation

Constructs `structureMap_eq' : Iso (toB ≫ B.map) (structureMap f g)` from
`f.commutes`, `g.commutes` and the iso-comma square `commutes f g`, using the
explicit bicategorical associator/whiskering isomorphisms.  The finite-etale
certificate for `structureMap = toA ≫ A.map` remains the exact missing
representable-finite-etale stability/closure field (no closure lemma for
`EtaleStackFiniteEtaleMorphism` is in the tree).

No fake finiteEtale and no weak TwoPullbackWitness is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual

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

universe u
variable {A B C : S1728Cover} {f : S1728CoverMap A C} {g : S1728CoverMap B C}

noncomputable def S2043WhiskerLeftIso {A B C : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) (g g' : Pseudofunctor.StrongTrans B C)
    (e : Iso g g') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f g') := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  exact @Bicategory.whiskerLeftIso Bicat _ A B C f g g' e

noncomputable def S2043WhiskerRightIso {A B C : EtaleStackPseudofunctor S1726K}
    (f f' : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (e : Iso f f') :
    Iso (Pseudofunctor.StrongTrans.vcomp f g) (Pseudofunctor.StrongTrans.vcomp f' g) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  exact @Bicategory.whiskerRightIso Bicat _ A B C f f' e g

noncomputable def S2043AssociatorIso {A B C D : EtaleStackPseudofunctor S1726K}
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C)
    (h : Pseudofunctor.StrongTrans C D) :
    Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp f g) h)
      (Pseudofunctor.StrongTrans.vcomp f (Pseudofunctor.StrongTrans.vcomp g h)) := by
  let Bicat := EtaleStackPseudofunctor S1726K
  letI : Bicategory Bicat := inferInstance
  exact @Bicategory.associator Bicat _ A B C D f g h

/-- `structureMap_eq'` by bicategorical cancellation. -/
noncomputable def S2043_structureMap_eq' :
    Iso (Pseudofunctor.StrongTrans.vcomp (toB f g) B.map) (structureMap f g) := by
  -- (toB ≫ B.map) <- (toB ≫ (g.map ≫ C.map)) <- ((toB ≫ g.map) ≫ C.map)
  let e1 : Iso (Pseudofunctor.StrongTrans.vcomp (toB f g)
      (Pseudofunctor.StrongTrans.vcomp g.map C.map))
      (Pseudofunctor.StrongTrans.vcomp (toB f g) B.map) :=
    S2043WhiskerLeftIso (toB f g) (Pseudofunctor.StrongTrans.vcomp g.map C.map)
      B.map (g.commutes)
  let e2 : Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp
      (toB f g) g.map) C.map)
      (Pseudofunctor.StrongTrans.vcomp (toB f g)
        (Pseudofunctor.StrongTrans.vcomp g.map C.map)) :=
    S2043AssociatorIso (toB f g) g.map C.map
  let e3 : Iso (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp
      (toA f g) f.map) C.map)
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp
        (toB f g) g.map) C.map) :=
    S2043WhiskerRightIso (Pseudofunctor.StrongTrans.vcomp (toA f g) f.map)
      (Pseudofunctor.StrongTrans.vcomp (toB f g) g.map) C.map (commutes f g)
  let e4 : Iso (Pseudofunctor.StrongTrans.vcomp (toA f g)
      (Pseudofunctor.StrongTrans.vcomp f.map C.map))
      (Pseudofunctor.StrongTrans.vcomp (Pseudofunctor.StrongTrans.vcomp
        (toA f g) f.map) C.map) :=
    (S2043AssociatorIso (toA f g) f.map C.map).symm
  let e5 : Iso (Pseudofunctor.StrongTrans.vcomp (toA f g) A.map)
      (Pseudofunctor.StrongTrans.vcomp (toA f g)
        (Pseudofunctor.StrongTrans.vcomp f.map C.map)) :=
    (S2043WhiskerLeftIso (toA f g) (Pseudofunctor.StrongTrans.vcomp f.map C.map)
      A.map (f.commutes)).symm
  exact e1.symm.trans (e2.symm.trans (e3.symm.trans (e4.symm.trans e5.symm)))

/-- The finite-etale certificate for `structureMap = toA ≫ A.map` is the exact
remaining D6(c) field; no closure/stability lemma for
`EtaleStackFiniteEtaleMorphism` under this iso-comma projection exists in the
tree.  This is recorded as a type, not asserted. -/
def S2043FirstMissingFiniteEtale : Type 1 :=
  EtaleStackFiniteEtaleMorphism
    (source := S2042IsoCommaStackObj (f := f) (g := g))
    (target := S1726Orbicurve.stack)
    (structureMap f g)

#print axioms S2043_structureMap_eq'

end LeanFormal.IUT.XiFPaper.S2043D6StructureMapEqActual

end
