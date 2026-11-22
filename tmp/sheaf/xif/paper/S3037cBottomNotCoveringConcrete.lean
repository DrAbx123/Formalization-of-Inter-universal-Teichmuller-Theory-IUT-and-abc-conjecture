import tmp.sheaf.xif.paper.S3037bBottomNotCovering
import tmp.sheaf.xif.paper.S2811IsPrestackActual
import Mathlib.AlgebraicGeometry.Limits
noncomputable section
open CategoryTheory Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3026NonemptyEtaleSite
open LeanFormal.IUT.XiFPaper.S3037NonemptyHne
open LeanFormal.IUT.XiFPaper.S3037BottomNotCovering
open LeanFormal.IUT.XiFPaper.S2811IsPrestackActual
namespace LeanFormal.IUT.XiFPaper.S3037cBottomNotCoveringConcrete

abbrev K : Type := S2844D6F6BaseChangeActual.K

noncomputable def S3037cX (U : S3026NonemptyScheme) : Iut.SchemeOverField K :=
  Over.mk (coprod.desc U.obj.hom U.obj.hom)

noncomputable def S3037cInl (U : S3026NonemptyScheme) :
    U.obj ⟶ S3037cX U :=
  Over.homMk coprod.inl (by
    change coprod.inl ≫ coprod.desc U.obj.hom U.obj.hom = U.obj.hom
    exact coprod.inl_desc _ _)

noncomputable def S3037cInr (U : S3026NonemptyScheme) :
    U.obj ⟶ S3037cX U :=
  Over.homMk coprod.inr (by
    change coprod.inr ≫ coprod.desc U.obj.hom U.obj.hom = U.obj.hom
    exact coprod.inr_desc _ _)

theorem S3037cInl_ne_inr (U : S3026NonemptyScheme)
    (hU : Nonempty U.obj.left) : S3037cInl U ≠ S3037cInr U := by
  obtain ⟨x⟩ := hU
  intro h
  have hx := congrArg (fun f : U.obj ⟶ S3037cX U => f.left x) h
  exact AlgebraicGeometry.inl_ne_inr _ _ x x hx

theorem S3037_bottom_not_covering_concrete
    (U : S3026NonemptyScheme) :
    ((⊥ : Sieve U) ∉ S3026NonemptySite U) := by
  apply S3037_bottom_not_mem_of_nonsubsingleton U
    (yoneda.obj (S3037cX U))
    (S2811_yoneda_isSheaf K (S3037cX U))
  intro hsub
  exact S3037cInl_ne_inr U U.property
    (hsub.elim (S3037cInl U) (S3037cInr U))

#check S3037cX
#check S3037cInl_ne_inr
/-- Bottom is not covering on the nonempty site. -/
theorem S3037BottomNotCovering :
    ∀ U : S3026NonemptyScheme, ((⊥ : Sieve U) ∉ S3026NonemptySite U) :=
  S3037_bottom_not_covering_concrete

/-- The hne hypothesis for the nonempty site is ACTUAL. -/
theorem S3037Hne_actual : S3037Hne :=
  S3037_hne_of_bottom_not_covering S3037BottomNotCovering

#check S3037_bottom_not_covering_concrete
#check S3037BottomNotCovering
#check S3037Hne_actual
#print axioms S3037Hne_actual
#print axioms S3037_bottom_not_covering_concrete

end LeanFormal.IUT.XiFPaper.S3037cBottomNotCoveringConcrete