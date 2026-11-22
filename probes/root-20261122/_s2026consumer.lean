import tmp.sheaf.xif.paper.S2026EffectivityReassemblyActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.S2026Consumer

open CategoryTheory
open CategoryTheory.Bicategory
open scoped Pseudofunctor.StrongTrans
open Iut
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual.S1728Paper
open LeanFormal.IUT.XiFPaper.S1945SitePseudofunctorDataActual
open LeanFormal.IUT.XiFPaper.S1956IsoCommaStackActual
open LeanFormal.IUT.XiFPaper.S1891PullbackStackIsStackActual
open LeanFormal.IUT.XiFPaper.S2004IsoCommaEffectivityActual
open LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual

/-- The effectivity half is available for every cospan and every covering sieve. -/
example {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C)
    (S : LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual.Site)
    (R : Sieve S) (hR : R ∈ LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual.J S) :
    ((sitePseudofunctor f g).toDescentData
      (fun (i : R.arrows.category) => i.obj.hom)).EssSurj :=
  S2026IsoCommaEffectivity f g S R hR

/-- The stack condition, and the consumer S1891 existence form. -/
example {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1891IsoCommaStackExistsFor LeanFormal.IUT.XiFPaper.S2026EffectivityReassemblyActual.J
      A.source.fiber B.source.fiber C.source.fiber f.map g.map :=
  S1956IsoCommaStack_to_S1891 f g (S2026IsoCommaStack f g)

example {A B C : S1728Cover} (f : S1728CoverMap A C) (g : S1728CoverMap B C) :
    S1891IsoCommaStackCore f g :=
  S1956IsoCommaStack_core f g (S2026IsoCommaStack f g)

example : S2004EffectivityAll := S2026EffectivityAll

#print axioms S2026IsoCommaEffectivity
#print axioms S2026IsoCommaStack

end LeanFormal.IUT.XiFPaper.S2026Consumer