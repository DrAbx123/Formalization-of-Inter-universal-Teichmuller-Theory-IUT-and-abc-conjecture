import tmp.sheaf.xif.paper.S2668D9ReductionActual
import tmp.sheaf.xif.paper.S2668FiberCoherenceActual
import tmp.sheaf.xif.paper.S2621TorsorPresheafActual

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S2670D9ConditionalActualAdapted

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
open LeanFormal.IUT.XiFPaper.S2668D9ReductionActual
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-- Nonempty-slice corrected torsor datum: freeness is only required over
nonempty slices, avoiding the vacuous empty-object obstruction of S2622. -/
structure S2670TorsorDataNonempty extends S2619ActionGroupoidData (l := l) (F := F) where
  hfree : ∀ (V : (Iut.SchemeOverField F)ᵒᵖ)
    (hV : Nonempty (CategoryTheory.Over.left (X := Spec F) V.unop))
    (M : V.unop ⟶ toS2619ActionGroupoidData.U) {g1 g2 : S2619G l},
    M ≫ (toS2619ActionGroupoidData.rho g1).hom =
      M ≫ (toS2619ActionGroupoidData.rho g2).hom → g1 = g2

lemma S2670_torsor_section_unique
    (D : S2670TorsorDataNonempty (l := l) (F := F))
    (S : Iut.SchemeOverField F)
    (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S)
    (T : (Over S)ᵒᵖ) (hT : Nonempty (CategoryTheory.Over.left (X := S) T.unop)) (g1 g2 : ZMod l.value)
    (h1 : (T.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g1).hom = T.unop.hom ≫ N)
    (h2 : (T.unop.hom ≫ M) ≫ (D.toS2619ActionGroupoidData.rho g2).hom = T.unop.hom ≫ N) :
    g1 = g2 :=
  D.hfree (Opposite.op ((CategoryTheory.Over.left (X := Spec F) T.unop))) hT (T.unop.hom ≫ M) (h1.trans h2.symm)

/-- Explicit effectivity input for D9: every covering sieve descent datum is
effective.  This is the only remaining non-formal input. -/
def S2670EssSurjInput (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u}) : Prop :=
  ∀ {S : Iut.SchemeOverField F} (R : Sieve S)
    (hR : R ∈ Iut.SchemeOverField.etaleTopology F S),
    (fib.toDescentData (fun (f : R.arrows.category) => f.obj.hom)).EssSurj

/-- Conditional D9 IsStack: hom-presheaf sheaf conditions + explicit effectivity. -/
theorem S2670D9IsStack
    (fib : LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u})
    (hsheaf : ∀ {S : Iut.SchemeOverField F}
      (M N : fib.obj (LocallyDiscrete.mk (Opposite.op S))),
      Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
        (fib.presheafHom M N))
    (hess : S2670EssSurjInput fib) :
    fib.IsStack (Iut.SchemeOverField.etaleTopology F) :=
  (S2668D9IsStack_iff fib).mpr ⟨hsheaf, hess⟩

#check S2670TorsorDataNonempty
#check S2670_torsor_section_unique
#check S2670D9IsStack
#print axioms S2670D9IsStack
end LeanFormal.IUT.XiFPaper.S2670D9ConditionalActualAdapted
end
