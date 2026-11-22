import tmp.sheaf.xif.paper.S2518InvCoverMapActual
noncomputable section
open CategoryTheory
open scoped Pseudofunctor.StrongTrans
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2480QiActual
open LeanFormal.IUT.XiFPaper.S1742TwoYonedaActual
open LeanFormal.IUT.XiFPaper.S2518InvCoverMapActual
open LeanFormal.IUT.XiFPaper.S2517RepresentableFiniteEtaleActual
open LeanFormal.IUT.XiFPaper.S2517InvObjActual
open LeanFormal.IUT.IUTII.Frobenioid.Example36.EtaleCoverFoundations
example (C : FiniteEtaleCover S2482AffineScheme) :
    S2518InvSchemeMap (𝟙 C) = 𝟙 (S2517CScheme C) := by
  apply CategoryTheory.Over.OverMorphism.ext
  rfl
example (S : Iut.SchemeOverField F) :
    S1742StrongTransOfHom (𝟙 S) = Pseudofunctor.StrongTrans.id (S1742YS S) := rfl
