import tmp.sheaf.xif.paper.S2668FiberCoherenceActual
import tmp.sheaf.xif.paper.S2665TorsorSheafActual
import Mathlib.CategoryTheory.Sites.SheafOfTypes

/-!
# S2669: the action-groupoid fiber pseudofunctor is a prestack

For a free action-groupoid datum `D : S2622TorsorData`, the concrete
pseudofunctor `F = S2668FiberPseudofunctor D.toS2619ActionGroupoidData` sends
`V` to the action groupoid of `S2619Hom D V` under the `rho`-action.  This
file proves descent of morphisms (Mathlib's `Pseudofunctor.IsPrestack`) for
this pseudofunctor with respect to the etale topology on `SchemeOverField F`.

The proof compares, componentwise by the identity, the universe lift of the
presheaf of morphisms with the torsor section presheaf `S2620TorsorPresheaf`,
whose sheaf property is `S2620_G_torsor_isSheaf`.  The comparison is a
natural isomorphism because each section type is a subsingleton
(`S2665TorsorPresheaf_subsingleton`), so naturality is immediate.
-/

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2669D9PrestackActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2620RepresentableSheafActual
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
open LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
open LeanFormal.IUT.XiFPaper.S2665TorsorSheafActual
open LeanFormal.IUT.XiFPaper.S2668FiberCoherenceActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]
variable (D : S2622TorsorData (l := l) (F := F))

/-- The concrete pseudofunctor of action-groupoid fibers attached to `D`. -/
abbrev S2669FiberPF (D : S2622TorsorData (l := l) (F := F)) :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u} :=
  S2668FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData

/-- The object of the fiber over `S` attached to a section `M : S ⟶ D.U`. -/
noncomputable def S2669Mo (S : Iut.SchemeOverField F)
    (M : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    S2619FiberAt (l := l) (F := F) D.toS2619ActionGroupoidData (Opposite.op S) :=
  ⟨CategoryTheory.SingleObj.star (S2619G l), M⟩

/-- The section underlying an object of the fiber.  We use the structure projection
`.snd` rather than `ActionCategory.back`: the latter needs to synthesize a
`MulAction` instance for the projected datum `D.toS2619ActionGroupoidData`, and
that instance is not found, while the projection is definitionally the same map. -/
noncomputable def S2669FiberBack {V : (Iut.SchemeOverField F)ᵒᵖ}
    (M : (S2669FiberPF (l := l) (F := F) D).obj (LocallyDiscrete.mk V)) :
    S2619Hom (l := l) (F := F) D.toS2619ActionGroupoidData V := M.snd

/-- The underlying section of `S2669Mo` is `M`. -/
@[simp]
lemma S2669Mo_snd (S : Iut.SchemeOverField F)
    (M : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    (S2669Mo (l := l) (F := F) D S M).snd = M := rfl

/-- `S2669FiberBack` of `S2669Mo` is the section it was built from. -/
@[simp]
lemma S2669FiberBack_Mo (S : Iut.SchemeOverField F)
    (M : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    S2669FiberBack (l := l) (F := F) D (S2669Mo (l := l) (F := F) D S M) = M := rfl

/-- After the universe lift, the presheaf of morphisms of the fiber pseudofunctor
is the torsor section presheaf.  The components are the identity: both sides are
the same subtype of `ZMod l.value`.  Naturality is automatic because the target
section type is a subsingleton. -/
noncomputable def S2669PresheafHomULiftIso (S : Iut.SchemeOverField F)
    (M N : (S2669FiberPF (l := l) (F := F) D).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    ((S2669FiberPF (l := l) (F := F) D).presheafHom M N) ⋙ uliftFunctor.{u+1, 0} ≅
      S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2669FiberBack (l := l) (F := F) D M) (S2669FiberBack (l := l) (F := F) D N) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T T' f
    haveI : Subsingleton
        ((S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
          (S2669FiberBack (l := l) (F := F) D M)
          (S2669FiberBack (l := l) (F := F) D N)).obj T') :=
      S2665TorsorPresheaf_subsingleton (l := l) (F := F) D S
        (S2669FiberBack (l := l) (F := F) D M)
        (S2669FiberBack (l := l) (F := F) D N) T'
    ext x
    exact Subsingleton.elim _ _)

/-- **Descent of morphisms for the fiber pseudofunctor**: for any two objects of
the fiber over `S`, the presheaf of morphisms between them is a sheaf for the
slice etale topology. -/
theorem S2669FiberPresheafHom_isSheaf (S : Iut.SchemeOverField F)
    (M N : (S2669FiberPF (l := l) (F := F) D).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    Presheaf.IsSheaf (S2620Slice (F := F) S)
      ((S2669FiberPF (l := l) (F := F) D).presheafHom M N) := by
  have hQ : Presheaf.IsSheaf (S2620Slice (F := F) S)
      (S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2669FiberBack (l := l) (F := F) D M)
        (S2669FiberBack (l := l) (F := F) D N)) :=
    S2620_G_torsor_isSheaf D S
      (S2669FiberBack (l := l) (F := F) D M)
      (S2669FiberBack (l := l) (F := F) D N)
  have hQ' : Presieve.IsSheaf (S2620Slice (F := F) S)
      (S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2669FiberBack (l := l) (F := F) D M)
        (S2669FiberBack (l := l) (F := F) D N)) :=
    (isSheaf_iff_isSheaf_of_type (J := S2620Slice (F := F) S) _).mp hQ
  have hU : Presieve.IsSheaf (S2620Slice (F := F) S)
      (((S2669FiberPF (l := l) (F := F) D).presheafHom M N) ⋙
        uliftFunctor.{u+1, 0}) :=
    Presieve.isSheaf_iso (S2620Slice (F := F) S)
      (S2669PresheafHomULiftIso (l := l) (F := F) D S M N).symm hQ'
  have hP : Presieve.IsSheaf (S2620Slice (F := F) S)
      ((S2669FiberPF (l := l) (F := F) D).presheafHom M N) :=
    (Presieve.isSheaf_comp_uliftFunctor_iff (S2620Slice (F := F) S)).mp hU
  exact (isSheaf_iff_isSheaf_of_type (J := S2620Slice (F := F) S) _).mpr hP

/-- The statement requested for the objects `Mo`, `No` attached to sections
`M N : S ⟶ D.U`. -/
theorem S2669FiberPresheafHom_isSheaf_Mo (S : Iut.SchemeOverField F)
    (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    Presheaf.IsSheaf (S2620Slice (F := F) S)
      ((S2669FiberPF (l := l) (F := F) D).presheafHom
        (S2669Mo (l := l) (F := F) D S M)
        (S2669Mo (l := l) (F := F) D S N)) :=
  S2669FiberPresheafHom_isSheaf (l := l) (F := F) D S _ _

/-- **The action-groupoid fiber pseudofunctor is a prestack** for the etale
topology: descent of morphisms holds for all fibers. -/
theorem S2669FiberIsPrestack :
    (S2669FiberPF (l := l) (F := F) D).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) :=
  ⟨fun {S} M N => S2669FiberPresheafHom_isSheaf (l := l) (F := F) D S M N⟩

/-- The target sheaf statement with the concrete pseudofunctor and the objects
`Mo`, `No` written out. -/
example (S : Iut.SchemeOverField F)
    (M N : S2621Hom (l := l) (F := F) D.toS2619ActionGroupoidData S) :
    Presheaf.IsSheaf (S2620Slice (F := F) S)
      ((S2668FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).presheafHom
        (S2669Mo (l := l) (F := F) D S M)
        (S2669Mo (l := l) (F := F) D S N)) :=
  S2669FiberPresheafHom_isSheaf_Mo (l := l) (F := F) D S M N

/-- The prestack target with the concrete pseudofunctor and the etale topology
written out. -/
example :
    (S2668FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) :=
  S2669FiberIsPrestack (l := l) (F := F) D

#print axioms S2669Mo
#print axioms S2669FiberBack
#print axioms S2669PresheafHomULiftIso
#print axioms S2669FiberPresheafHom_isSheaf
#print axioms S2669FiberPresheafHom_isSheaf_Mo
#print axioms S2669FiberIsPrestack

end LeanFormal.IUT.XiFPaper.S2669D9PrestackActual
end
