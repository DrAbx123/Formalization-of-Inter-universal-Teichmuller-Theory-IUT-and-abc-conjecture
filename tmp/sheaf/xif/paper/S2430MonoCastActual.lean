import tmp.sheaf.xif.paper.S2429CompositeAssemblyActual

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
open LeanFormal.IUT.XiFPaper.S2429CompositeAssemblyActual
namespace LeanFormal.IUT.XiFPaper.S2430MonoCastActual

/-- General Mono-cast-composition lemma.  If `a : S1 ⟶ S2` and `b : S2' ⟶ S3`
are monomorphisms, then the composite of `a` with the transport of `b` along an
arbitrary object equality `h : S2 = S2'` is again a monomorphism.

The object types `S1 S2 S2' S3` are arbitrary, and the equality `h` is an
ordinary hypothesis rather than a projection of a structure, so dependent
elimination of `h` is structural: `cases h` reduces the transported morphism to
`b` and the goal to `Mono (a ≫ b)`, which is Mathlib's `mono_comp` instance.
This is the Mono analogue of the type-generalization trick used for
`S2429CastComp_general`. -/
theorem S2430MonoCastComp_general
    {S1 S2 S2' S3 : SchemeOverField S1726K}
    (a : S1 ⟶ S2) (b : S2' ⟶ S3)
    (ha : Mono a) (hb : Mono b) (h : S2 = S2') :
    Mono (a ≫ (h ▸ b)) := by
  cases h
  haveI : Mono a := ha
  haveI : Mono b := hb
  infer_instance

/-- The composite scheme map attached to a composable pair of representable
cover maps is a monomorphism.

`S2429CompositeMap H = H.R1.g0 ≫ (H.middle_eq ▸ H.R2.g0)`; both factors are
monomorphisms (`H.R1.mono`, `H.R2.mono`) and the second one is only transported
along the arbitrary equality `H.middle_eq`, so the general Mono-cast lemma
applies. -/
theorem S2430CompositeMap_mono
    {A B C : S1728Cover} {g1 : S1728CoverMap A B} {g2 : S1728CoverMap B C}
    (H : S2424ComposableRepresentable g1 g2) :
    Mono (S2429CompositeMap H) := by
  unfold S2429CompositeMap
  exact S2430MonoCastComp_general H.R1.g0 H.R2.g0 H.R1.mono H.R2.mono H.middle_eq

end LeanFormal.IUT.XiFPaper.S2430MonoCastActual
end
