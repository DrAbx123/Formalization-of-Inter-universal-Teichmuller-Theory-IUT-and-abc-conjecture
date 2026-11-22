import tmp.sheaf.xif.paper.S3088FamilyConstructionActual
import tmp.sheaf.xif.paper.BaseQFamilyActual
import LeanFormal.IUT.IUTIII.Corollary312.ArithmeticQPilotLogVolume

noncomputable section
open scoped BigOperators
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S3088FamilyConstructionActual
open LeanFormal.IUT.XiFPaper.S3087GenericSourceHodgeFamilyAttempt
open LeanFormal.IUT.XiFPaper.BaseQFamilyActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
open LeanFormal.IUT.ArithmeticQPilotLogVolume
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000000

namespace LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt

variable {V : Type} [Nonempty V]
variable (T : SourceNativeInitialThetaData.{0} fiveLabel)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- The actual weighted native q product. -/
noncomputable def S3094WeightedQProduct : Real :=
  ∏ b : Bad (nativePlaceSelection T),
    Real.exp (nativeBadLocalWeight T b *
      Real.log ‖(nativeBaseQFamily T b).q‖)

theorem S3094WeightedQProduct_pos : 0 < S3094WeightedQProduct (T := T) := by
  unfold S3094WeightedQProduct
  exact Finset.prod_pos (fun b _ => Real.exp_pos _)

noncomputable def S3094Packet : FiniteThetaPacket fiveLabel :=
  FiniteThetaPacket.ofQ (l := fiveLabel) (S3094WeightedQProduct (T := T))
    (S3094WeightedQProduct_pos (T := T))

noncomputable def S3094Theater (i : SourceTheorem311Index) :
    HodgeTheater.{0, 0, 0, 0} fiveLabel V where
  arithmetic := T.arithmetic
  primeStrip := S3087Strip V i.1 i.2
  thetaPacket := S3094Packet (T := T)

theorem S3094Theater_injective : Function.Injective (S3094Theater (V := V) T) := by
  intro i j h
  let v0 : V := Classical.choice ‹Nonempty V›
  have hprojHEq : HEq ((S3094Theater (V := V) T i).primeStrip.proj v0)
      ((S3094Theater (V := V) T j).primeStrip.proj v0) :=
    congr_arg_heq (fun T : HodgeTheater.{0, 0, 0, 0} fiveLabel V =>
      T.primeStrip.proj v0) h
  have hproj : (S3094Theater (V := V) T i).primeStrip.proj v0 =
      (S3094Theater (V := V) T j).primeStrip.proj v0 := eq_of_heq hprojHEq
  have h01 := DFunLike.congr_fun hproj
    (Multiplicative.ofAdd ((0 : Int), (1 : Int)))
  have h10 := DFunLike.congr_fun hproj
    (Multiplicative.ofAdd ((1 : Int), (0 : Int)))
  have hn : i.1 = j.1 := by
    have h01' : Multiplicative.ofAdd
        (sourceHaarActualShearAddEquiv i.1 i.2 ((0 : Int), (1 : Int))) =
        Multiplicative.ofAdd
          (sourceHaarActualShearAddEquiv j.1 j.2 ((0 : Int), (1 : Int))) := h01
    have h := congrArg (fun x => (Multiplicative.toAdd x).1) h01'
    simpa [sourceHaarActualShearAddEquiv] using h
  have hm : i.2 = j.2 := by
    have h10' : Multiplicative.ofAdd
        (sourceHaarActualShearAddEquiv i.1 i.2 ((1 : Int), (0 : Int))) =
        Multiplicative.ofAdd
          (sourceHaarActualShearAddEquiv j.1 j.2 ((1 : Int), (0 : Int))) := h10
    have h := congrArg (fun x => (Multiplicative.toAdd x).2) h10'
    simpa [sourceHaarActualShearAddEquiv] using h
  exact Prod.ext hn hm

noncomputable def S3094TheaterLink (i j : SourceTheorem311Index) :
    HodgeTheaterLink (S3094Theater (V := V) T i) (S3094Theater (V := V) T j) where
  primeStripEquiv := S3088StripEquiv V i j
  theta_q_eq := rfl
  theta_scale_eq := fun j => rfl

theorem S3094TheaterLink_ext {i j : SourceTheorem311Index}
    {L M : HodgeTheaterLink (S3094Theater (V := V) T i) (S3094Theater (V := V) T j)}
    (h : L.primeStripEquiv = M.primeStripEquiv) : L = M := by
  cases L; cases M; simp only at h; congr

theorem S3094TheaterLink_refl (i : SourceTheorem311Index) :
    S3094TheaterLink (V := V) T i i =
      HodgeTheaterLink.refl (S3094Theater (V := V) T i) := by
  refine S3094TheaterLink_ext (V := V) (T := T) ?_
  exact S3088StripEquiv_self V i

theorem S3094TheaterLink_symm (i j : SourceTheorem311Index) :
    HodgeTheaterLink.symm (S3094TheaterLink (V := V) T i j) =
      S3094TheaterLink (V := V) T j i := by
  refine S3094TheaterLink_ext (V := V) (T := T) ?_
  exact S3088StripEquiv_symm V i j

theorem S3094TheaterLink_trans (i j k : SourceTheorem311Index) :
    HodgeTheaterLink.trans (S3094TheaterLink (V := V) T i j)
        (S3094TheaterLink (V := V) T j k) =
      S3094TheaterLink (V := V) T i k := by
  refine S3094TheaterLink_ext (V := V) (T := T) ?_
  exact S3088StripEquiv_trans V i j k

noncomputable def S3094Family :
    SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} fiveLabel V where
  index := SourceTheorem311Index
  theater := S3094Theater (V := V) T
  distinct := S3094Theater_injective (V := V) T
  link := S3094TheaterLink (V := V) T
  link_refl := S3094TheaterLink_refl (V := V) T
  link_symm := S3094TheaterLink_symm (V := V) T
  link_trans := S3094TheaterLink_trans (V := V) T
  permutation := Equiv.refl SourceTheorem311Index
  permutationLink := fun i => HodgeTheaterLink.refl (S3094Theater (V := V) T i)
  permutation_naturality := by
    intro i j
    change HodgeTheaterLink.trans (S3094TheaterLink (V := V) T i j)
        (HodgeTheaterLink.refl (S3094Theater (V := V) T j)) =
      HodgeTheaterLink.trans (HodgeTheaterLink.refl (S3094Theater (V := V) T i))
        (S3094TheaterLink (V := V) T i j)
    rw [HodgeTheaterLink.trans_refl, HodgeTheaterLink.refl_trans]

theorem S3094Family_q (i : SourceTheorem311Index) :
    ((S3094Family (V := V) T).theater i).thetaPacket.q =
      S3094WeightedQProduct (T := T) := by
  rfl

#check S3094WeightedQProduct
#check S3094Family
#check S3094Family_q
#print axioms S3094Family
#print axioms S3094Family_q

end LeanFormal.IUT.XiFPaper.S3094ActualQFamilyAttempt
end
