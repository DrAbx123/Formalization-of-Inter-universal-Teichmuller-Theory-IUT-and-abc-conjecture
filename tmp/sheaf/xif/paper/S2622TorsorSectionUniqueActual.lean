import tmp.sheaf.xif.paper.S2621TorsorPresheafActual
noncomputable section
set_option autoImplicit false
set_option maxRecDepth 100000
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
set_option linter.unusedVariables false
namespace LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
structure S2622TorsorData extends S2619ActionGroupoidData (l := l) (F := F) where
  hfree : ∀ (V : (Iut.SchemeOverField F)ᵒᵖ)
    (M : V.unop ⟶ toS2619ActionGroupoidData.U) {g1 g2 : S2619G l},
    M ≫ (toS2619ActionGroupoidData.rho g1).hom =
      M ≫ (toS2619ActionGroupoidData.rho g2).hom → g1 = g2
lemma S2620_torsor_section_unique
    (D : S2622TorsorData (l := l) (F := F))
    (S : Iut.SchemeOverField F)
    (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S)
    (T : (Over S)ᵒᵖ) (g1 g2 : ZMod l.value)
    (h1 : (T.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g1).hom = T.unop.hom ≫ N)
    (h2 : (T.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g2).hom = T.unop.hom ≫ N) :
    g1 = g2 := by
  exact D.hfree (Opposite.op T.unop.left) (T.unop.hom ≫ M) (h1.trans h2.symm)
#print axioms S2620_torsor_section_unique
end LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
end
