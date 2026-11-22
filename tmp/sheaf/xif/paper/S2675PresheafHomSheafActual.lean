import tmp.sheaf.xif.paper.S2667FiberCoherenceActual
import tmp.sheaf.xif.paper.S2665TorsorSheafActual

/-!
# S2675: descent of morphisms for the actual S2667 fiber pseudofunctor

For a free action-groupoid datum `D : S2622TorsorData` on `SchemeOverField F`,
the actual fiber pseudofunctor of S2667 sends `V` to the action groupoid of
sections `V.unop ⟶ D.U` and a slice morphism `h` to pullback along `h`.
Its presheaf of morphisms between two objects of the fiber over `S` is
identified, after the universe lift, with the torsor section presheaf of
S2620/S2621 (the "old orientation" presheaf whose sheaf property is S2665's
`S2620_G_torsor_isSheaf`).

The identification is componentwise the identity: both presheaves have the same
underlying subtype of `ZMod l.value`.  Naturality is automatic because the
torsor section types are subsingletons by freeness of the action.  The sheaf
property is then transferred to the actual (unlifted) presheaf of morphisms via
`Presieve.isSheaf_comp_uliftFunctor_iff`.
-/

noncomputable section
open CategoryTheory
open LeanFormal.IUT
open scoped CategoryTheory.Bicategory
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2675PresheafHomSheafActual

open LeanFormal.IUT.XiFPaper.S2619ActionGroupoidFiberSkeleton
open LeanFormal.IUT.XiFPaper.S2620RepresentableSheafActual
open LeanFormal.IUT.XiFPaper.S2621TorsorPresheafActual
open LeanFormal.IUT.XiFPaper.S2622TorsorSectionUniqueActual
open LeanFormal.IUT.XiFPaper.S2665TorsorSheafActual
open LeanFormal.IUT.XiFPaper.S2667FiberCoherenceActual

universe u
variable {l : PrimeGeFive} {F : Type u} [Field F]

/-- The actual S2667 fiber pseudofunctor attached to a free action-groupoid datum. -/
abbrev S2675FiberPF (D : S2622TorsorData (l := l) (F := F)) :
    LocallyDiscrete (Iut.SchemeOverField F)ᵒᵖ ⥤ᵖ Cat.{0, u} :=
  S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData

/-- The section of the base `V` underlying an object of the actual fiber over `V`.
We use the structure projection `.snd` rather than `ActionCategory.back`, which
would need the `MulAction` instance of the projected datum. -/
noncomputable def S2675FiberBack (D : S2622TorsorData (l := l) (F := F))
    {V : (Iut.SchemeOverField F)ᵒᵖ}
    (M : (S2675FiberPF (l := l) (F := F) D).obj (LocallyDiscrete.mk V)) :
    S2619Hom (l := l) (F := F) D.toS2619ActionGroupoidData V := M.snd

variable (D : S2622TorsorData (l := l) (F := F))

/-- **Identification up to universe lift.**  The universe lift of the presheaf of
morphisms of the actual S2667 fiber pseudofunctor is the old-orientation torsor
section presheaf of S2620/S2621.  The components are the identity; naturality
holds because the target sections are subsingletons. -/
noncomputable def S2675PresheafHomIso (S : Iut.SchemeOverField F)
    (M N : (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    ((S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).presheafHom M N) ⋙
        uliftFunctor.{u+1, 0} ≅
      S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2675FiberBack (l := l) (F := F) D M)
        (S2675FiberBack (l := l) (F := F) D N) :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro T T' f
    haveI : Subsingleton
        ((S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
          (S2675FiberBack (l := l) (F := F) D M)
          (S2675FiberBack (l := l) (F := F) D N)).obj T') :=
      S2665TorsorPresheaf_subsingleton (l := l) (F := F) D S
        (S2675FiberBack (l := l) (F := F) D M)
        (S2675FiberBack (l := l) (F := F) D N) T'
    ext x
    exact Subsingleton.elim _ _)

/-- **Descent of morphisms for the actual S2667 fiber pseudofunctor.**  For any
two objects of the fiber over `S`, the presheaf of morphisms between them is a
sheaf for the slice etale topology. -/
theorem S2675PresheafHom_isSheaf (S : Iut.SchemeOverField F)
    (M N : (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      ((S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).presheafHom M N) := by
  change Presheaf.IsSheaf (S2620Slice (F := F) S)
    ((S2675FiberPF (l := l) (F := F) D).presheafHom M N)
  have hQ : Presheaf.IsSheaf (S2620Slice (F := F) S)
      (S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2675FiberBack (l := l) (F := F) D M)
        (S2675FiberBack (l := l) (F := F) D N)) :=
    S2620_G_torsor_isSheaf D S
      (S2675FiberBack (l := l) (F := F) D M)
      (S2675FiberBack (l := l) (F := F) D N)
  have hQ' : Presieve.IsSheaf (S2620Slice (F := F) S)
      (S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2675FiberBack (l := l) (F := F) D M)
        (S2675FiberBack (l := l) (F := F) D N)) :=
    (isSheaf_iff_isSheaf_of_type (J := S2620Slice (F := F) S) _).mp hQ
  have hU : Presieve.IsSheaf (S2620Slice (F := F) S)
      (((S2675FiberPF (l := l) (F := F) D).presheafHom M N) ⋙
        uliftFunctor.{u+1, 0}) :=
    Presieve.isSheaf_iso (S2620Slice (F := F) S)
      (S2675PresheafHomIso (l := l) (F := F) D S M N).symm hQ'
  have hP : Presieve.IsSheaf (S2620Slice (F := F) S)
      ((S2675FiberPF (l := l) (F := F) D).presheafHom M N) :=
    (Presieve.isSheaf_comp_uliftFunctor_iff (S2620Slice (F := F) S)).mp hU
  exact (isSheaf_iff_isSheaf_of_type (J := S2620Slice (F := F) S) _).mpr hP

/-- **The actual S2667 fiber pseudofunctor is a prestack** for the etale topology:
descent of morphisms holds for all fibers. -/
theorem S2675FiberIsPrestack :
    (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) :=
  ⟨fun {S} M N => S2675PresheafHom_isSheaf (l := l) (F := F) D S M N⟩

/-- The requested sheaf statement written literally with the S2667 pseudofunctor
and the slice etale topology. -/
example (S : Iut.SchemeOverField F)
    (M N : (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    Presheaf.IsSheaf ((Iut.SchemeOverField.etaleTopology F).over S)
      ((S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).presheafHom M N) :=
  S2675PresheafHom_isSheaf (l := l) (F := F) D S M N

/-- The S2619 presheaf-hom sheaf goal instantiated at the actual S2667 pseudofunctor. -/
example (S : Iut.SchemeOverField F)
    (M N : (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    S2619PresheafHomSheafGoal (F := F)
      (fib := S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData)
      (S := S) M N :=
  S2675PresheafHom_isSheaf (l := l) (F := F) D S M N

/-- The identification with the old-orientation torsor presheaf, written literally
with the S2667 pseudofunctor and up to the universe lift. -/
example (S : Iut.SchemeOverField F)
    (M N : (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).obj
      (LocallyDiscrete.mk (Opposite.op S))) :
    ((S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).presheafHom M N) ⋙
        uliftFunctor.{u+1, 0} ≅
      S2620TorsorPresheaf (l := l) (F := F) D.toS2619ActionGroupoidData S
        (S2675FiberBack (l := l) (F := F) D M)
        (S2675FiberBack (l := l) (F := F) D N) :=
  S2675PresheafHomIso (l := l) (F := F) D S M N

/-- The prestack conclusion written literally with the S2667 pseudofunctor. -/
example :
    (S2667FiberPseudofunctor (l := l) (F := F) D.toS2619ActionGroupoidData).IsPrestack
      (Iut.SchemeOverField.etaleTopology F) :=
  S2675FiberIsPrestack (l := l) (F := F) D

#check S2675PresheafHomIso
#check S2675PresheafHom_isSheaf
#check S2675FiberIsPrestack
#print axioms S2675PresheafHomIso
#print axioms S2675PresheafHom_isSheaf
#print axioms S2675FiberIsPrestack

end LeanFormal.IUT.XiFPaper.S2675PresheafHomSheafActual
end
