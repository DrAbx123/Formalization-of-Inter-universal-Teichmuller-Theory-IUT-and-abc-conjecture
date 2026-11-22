import tmp.sheaf.xif.paper.S2533CoverObjectMapActual
import tmp.sheaf.xif.paper.S1728CoverCategoryActual
import tmp.sheaf.xif.paper.S2535AdjoinRootAlgebraMapActual
import tmp.sheaf.xif.paper.S2518InvCoverMapActual
import tmp.sheaf.xif.paper.S2533CoverObjectMapActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36EtaleCoverFoundations

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S2482QiOrbicurveActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2533CoverObjectMapActual
open LeanFormal.IUT.XiFPaper.S1728CoverCategoryActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2534CoverHomMapActual

noncomputable def S2534AlgCoverMap {A B : CommAlgCat.FiniteEtale F}
    (f : A ⟶ B) :
    finiteEtaleAlgebraCover F B ⟶ finiteEtaleAlgebraCover F A := by
  apply ObjectProperty.homMk
  refine Over.homMk (Spec.map (CommRingCat.ofHom f.hom.hom)) ?_
  dsimp only [finiteEtaleAlgebraCover, finiteEtaleAlgebraStructureMap,
    FiniteEtaleCover.mk]
  change Spec.map (CommRingCat.ofHom f.hom.hom) ≫
    Spec.map (CommRingCat.ofHom (algebraMap F A.obj)) =
    Spec.map (CommRingCat.ofHom (algebraMap F B.obj))
  rw [← Spec.map_comp]
  rw [Spec.map_inj]
  apply CommRingCat.hom_ext
  apply AdjoinRoot.ringHom_ext
  · ext x
    simpa [CommRingCat.ofHom_comp, CommRingCat.hom_comp] using
      (S2535_commutes_adjoinRoot (f := f.hom.hom) x).symm
  · simpa [CommRingCat.ofHom_comp, CommRingCat.hom_comp] using
      (S2535_commutes_root (f := f.hom.hom)).symm

noncomputable def S2534CoverMap {A B : CommAlgCat.FiniteEtale F}
    (f : A ⟶ B) :
    Iut.OrbicurveFiniteEtaleCoverMap (S2533ObjectMap B) (S2533ObjectMap A) :=
  S2518InvCoverMap
    ((FiniteEtaleCover.pullback (S := Spec (CommRingCat.of F))
      (T := S2482AffineScheme) S2482AffineOver.hom).map
      (S2534AlgCoverMap f))

noncomputable def S2534QuotMap {A B : CommAlgCat.FiniteEtale F}
    (f : A ⟶ B) :
    S1728CoverMapClass (S2533ObjectMap B) (S2533ObjectMap A) :=
  Quot.mk _ (S2534CoverMap f)

#check S2534QuotMap
#print axioms S2534QuotMap
end LeanFormal.IUT.XiFPaper.S2534CoverHomMapActual
end