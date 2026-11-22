import tmp.sheaf.xif.paper.S2424CoverCompositionActual
import tmp.sheaf.xif.paper.S2398HomOfStrongTransCompActual

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1641CoverMapCompositionActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2403RepresentableExamplesActual
open LeanFormal.IUT.XiFPaper.S2424CoverCompositionActual
namespace LeanFormal.IUT.XiFPaper.S2429CompositeAssemblyActual

/-- The exact dependent-cast composition lemma: transport of a vertical
composite along three fiber equalities is the vertical composite of the
transports. -/
def S2429CastComp : Prop :=
  forall {A B C : EtaleStackOverField S1726K}
    {S1 S2 S3 : SchemeOverField S1726K}
    (h1 : A.fiber = S1742YS (F := S1726K) S1)
    (h2 : B.fiber = S1742YS (F := S1726K) S2)
    (h3 : C.fiber = S1742YS (F := S1726K) S3)
    (f : A.Hom B) (g : B.Hom C),
    S2403CastHom h1 h3 (Pseudofunctor.StrongTrans.vcomp f g) =
      Pseudofunctor.StrongTrans.vcomp
        (S2403CastHom h1 h2 f) (S2403CastHom h2 h3 g)

/-- Exact composite map-iso/Mono obligation after the cast lemma. -/
def S2429CompositeAssemblyRequired
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) : Prop :=
  S2424CompositionRequired H


/-- General type-level cast-composition lemma: transporting a vertical composite
along three type equalities is the vertical composite of the transports. -/
theorem S2429CastComp_general
    {A B C X Y Z : EtaleStackPseudofunctor S1726K}
    (e1 : X = A) (e2 : Y = B) (e3 : Z = C)
    (f : Pseudofunctor.StrongTrans A B) (g : Pseudofunctor.StrongTrans B C) :
    (e1 ▸ e3 ▸ Pseudofunctor.StrongTrans.vcomp f g) =
      Pseudofunctor.StrongTrans.vcomp (e1 ▸ e2 ▸ f) (e2 ▸ e3 ▸ g) := by
  cases e1
  cases e2
  cases e3
  rfl

/-- The cast-composition lemma S2429CastComp. -/
theorem S2429CastComp_holds : S2429CastComp := by
  intro A B C S1 S2 S3 h1 h2 h3 f g
  exact S2429CastComp_general h1.symm h2.symm h3.symm f g


noncomputable def S2429CompositeMap
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) :
    H.R1.sourceScheme ⟶ H.R2.targetScheme :=
  H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)

def S2429CompositeMapIsoRequired
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) : Prop :=
  Nonempty (Iso
    (S2403CastHom H.R1.source_fiber_eq H.R2.target_fiber_eq
      (S1641CoverMapComp g1 g2).map)
    (S1742StrongTransOfHom (F := S1726K) (S2429CompositeMap H)))


theorem S2429MonoCastComp
    {S1 S2 S2' S3 : SchemeOverField S1726K}
    (a : S1 ⟶ S2) (b : S2' ⟶ S3) [Mono a] [Mono b]
    (h : S2 = S2') :
    Mono (a ≫ (h ▸ b)) := by
  cases h
  exact inferInstance

theorem S2429CompositeMap_mono
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) :
    Mono (S2429CompositeMap H) := by
  haveI : Mono H.R1.g0 := H.R1.mono
  haveI : Mono H.R2.g0 := H.R2.mono
  exact S2429MonoCastComp H.R1.g0 H.R2.g0 H.middle_eq

noncomputable def S2424CompositeOfMapIso
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2)
    (h : S2429CompositeMapIsoRequired H) :
    S2424CompositeRepresentable H where
  sourceScheme := H.R1.sourceScheme
  targetScheme := H.R2.targetScheme
  source_fiber_eq := H.R1.source_fiber_eq
  target_fiber_eq := H.R2.target_fiber_eq
  g0 := S2429CompositeMap H
  map_iso := h
  mono := S2429CompositeMap_mono H

theorem S2424CompositionRequired_of_mapIso
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2)
    (h : S2429CompositeMapIsoRequired H) :
    S2424CompositionRequired H :=
  ⟨S2424CompositeOfMapIso H h⟩


end LeanFormal.IUT.XiFPaper.S2429CompositeAssemblyActual
end