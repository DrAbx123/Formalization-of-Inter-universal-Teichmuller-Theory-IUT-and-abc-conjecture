import tmp.sheaf.xif.paper.S3050ConnectedSite
import tmp.sheaf.xif.paper.S3057bValLemmas
noncomputable section
set_option maxHeartbeats 4000000
open CategoryTheory
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3050ConnectedSite
open LeanFormal.IUT.XiFPaper.S3057bValLemmas
namespace LeanFormal.IUT.XiFPaper.S3057ConnectedHomSheaf

abbrev K : Type := S3050ConnectedSite.K

/-- hne on the connected site. -/
def S3057Hne : Prop :=
  ∀ (S : S3050ConnectedScheme) (T : Over S) (R : Sieve T),
    R ∈ S3050ConnectedSite.over S T → Nonempty R.arrows.category

/-- Separatedness of the restricted hom presheaf, assuming every covering sieve has an index. -/
theorem S3057_homForm_separated
    (hne : S3057Hne)
    (S : S3050ConnectedScheme)
    (M N : S3050Q.obj { as := Opposite.op S }) :
    Presheaf.IsSeparated (S3050ConnectedSite.over S) (S3050Q.presheafHom M N) := by
  intro T R hR x y hxy
  obtain ⟨i0⟩ := hne S T R hR
  have hval : x.val = y.val := by
    have h := hxy i0.obj.left i0.obj.hom i0.property
    have hx : (((S3050Q.presheafHom M N).map i0.obj.hom.op) x).val = x.val := by
      exact presheafHom_map_val M N i0.obj.hom x
    have hy : (((S3050Q.presheafHom M N).map i0.obj.hom.op) y).val = y.val := by
      exact presheafHom_map_val M N i0.obj.hom y
    have h' := congrArg (fun z => z.val) h
    rw [hx, hy] at h'
    exact h'
  exact Subtype.ext hval

#check S3057Hne
#check S3057_homForm_separated
#print axioms S3057_homForm_separated

end LeanFormal.IUT.XiFPaper.S3057ConnectedHomSheaf