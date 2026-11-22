import tmp.sheaf.xif.paper.S3076QPrimeMapCompActual

noncomputable section
open CategoryTheory
open CategoryTheory.Limits
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3069QPrimeTorsorStack
open LeanFormal.IUT.XiFPaper.S3075QPrimeAssembly
open LeanFormal.IUT.XiFPaper.S3049TorsorFiberCategory
open LeanFormal.IUT.XiFPaper.S3048StackificationQPrime
open LeanFormal.IUT.XiFPaper.S3076QPrimeMapCompActual

namespace LeanFormal.IUT.XiFPaper.S3076CompReverseProbeAdapted
set_option maxHeartbeats 4000000

abbrev C : Type 1 := Iut.SchemeOverField S2994A6K

variable {U V W : LocallyDiscrete Cᵒᵖ}
variable (f : U ⟶ V) (g : V ⟶ W)
variable (P : S3048SignTorsorFiber U)

theorem S3076CompToB_toA :
    S3076CompToB f g P ≫ S3076CompToA f g P =
      𝟙 (S3076CompA f g P) := by
  apply pullback.hom_ext
    (f := S3076CompE P)
    (g := S3076CompG g ≫ S3076CompF f)
  · simp only [S3076CompToA, S3076CompToB, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.assoc]
    simp only [pullback.lift_fst, pullback.lift_snd]
    simp [pullback.condition]
  · simp only [S3076CompToA, S3076CompToB, pullback.lift_fst_assoc,
      pullback.lift_snd_assoc, Category.assoc]
    simp only [pullback.lift_fst, pullback.lift_snd]
    simp [pullback.condition]

end LeanFormal.IUT.XiFPaper.S3076CompReverseProbeAdapted
