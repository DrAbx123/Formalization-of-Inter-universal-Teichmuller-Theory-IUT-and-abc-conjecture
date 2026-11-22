import tmp.sheaf.xif.paper.S3087GenericSourceHodgeFamilyAttempt
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

noncomputable section
open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S3087GenericSourceHodgeFamilyAttempt
open LeanFormal.IUT.XiFPaper.S2678PaperUnconditionalHcompActual
set_option relaxedAutoImplicit false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 16000

namespace LeanFormal.IUT.XiFPaper.S3088FamilyConstructionActual

variable (V : Type) [Nonempty V]

/-- Generic shear-strip equivariance. -/
noncomputable def S3088StripEquiv (i j : SourceTheorem311Index) :
    FPrimeStripEquiv (S3087Strip V i.1 i.2) (S3087Strip V j.1 j.2) where
  isoPi := fun _ => MulEquiv.refl _
  isoG := fun _ =>
    (sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
      (sourceHaarActualShearMulEquiv j.1 j.2)
  isoMon := fun _ => MulEquiv.refl _
  compatProj := by
    intro v
    ext x
    change sourceHaarActualShearMulEquiv j.1 j.2 x =
      ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv j.1 j.2))
        (sourceHaarActualShearMulEquiv i.1 i.2 x)
    simp [MulEquiv.trans_apply]
  compatAction := by
    intro v g x
    rfl
  compatDegree := by
    intro v x
    rfl

/-- Componentwise extensionality for the generic strip equivalences. -/
theorem S3088StripEquiv_ext
    {F F' : FPrimeStrip.{0, 0, 0} V}
    {phi psi : FPrimeStripEquiv F F'}
    (hPi : forall v, phi.isoPi v = psi.isoPi v)
    (hG : forall v, phi.isoG v = psi.isoG v)
    (hMon : forall v, phi.isoMon v = psi.isoMon v) : phi = psi := by
  cases phi
  cases psi
  simp only at hPi hG hMon
  congr
  all_goals first
    | exact funext hPi
    | exact funext hG
    | exact funext hMon

theorem S3088StripEquiv_self (i : SourceTheorem311Index) :
    S3088StripEquiv V i i = FPrimeStripEquiv.refl (S3087Strip V i.1 i.2) := by
  refine S3088StripEquiv_ext (V := V) ?_ ?_ ?_
  · intro v; rfl
  · intro v; exact MulEquiv.symm_trans_self _
  · intro v; rfl

theorem S3088StripEquiv_symm (i j : SourceTheorem311Index) :
    FPrimeStripEquiv.symm (S3088StripEquiv V i j) = S3088StripEquiv V j i := by
  refine S3088StripEquiv_ext (V := V) ?_ ?_ ?_
  · intro v; rfl
  · intro v
    ext x
    change ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv j.1 j.2)).symm x =
      ((sourceHaarActualShearMulEquiv j.1 j.2).symm.trans
        (sourceHaarActualShearMulEquiv i.1 i.2)) x
    rw [MulEquiv.symm_trans_apply, MulEquiv.trans_apply]
    rfl
  · intro v; rfl

theorem S3088StripEquiv_trans (i j k : SourceTheorem311Index) :
    FPrimeStripEquiv.trans (S3088StripEquiv V i j) (S3088StripEquiv V j k) =
      S3088StripEquiv V i k := by
  refine S3088StripEquiv_ext (V := V) ?_ ?_ ?_
  · intro v; rfl
  · intro v
    ext x
    change ((sourceHaarActualShearMulEquiv j.1 j.2).symm.trans
        (sourceHaarActualShearMulEquiv k.1 k.2))
        (((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
          (sourceHaarActualShearMulEquiv j.1 j.2)) x) =
      ((sourceHaarActualShearMulEquiv i.1 i.2).symm.trans
        (sourceHaarActualShearMulEquiv k.1 k.2)) x
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  · intro v; rfl

/-- Generic Hodge-theater link. -/
noncomputable def S3088TheaterLink
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (i j : SourceTheorem311Index) :
    HodgeTheaterLink (S3087Theater V A i) (S3087Theater V A j) where
  primeStripEquiv := S3088StripEquiv V i j
  theta_q_eq := rfl
  theta_scale_eq := by
    intro j
    rfl

/-- Extensionality for generic theater links. -/
theorem S3088TheaterLink_ext
    {A : InitialThetaArithmeticData.{0} fiveLabel}
    {i j : SourceTheorem311Index}
    {L M : HodgeTheaterLink (S3087Theater V A i) (S3087Theater V A j)}
    (h : L.primeStripEquiv = M.primeStripEquiv) : L = M := by
  cases L
  cases M
  simp only at h
  congr

/-- Generic distinctness: evaluate at a chosen base place. -/
theorem S3088Theater_injective
    (A : InitialThetaArithmeticData.{0} fiveLabel) :
    Function.Injective (S3087Theater V A) := by
  intro i j h
  let v0 : V := Classical.choice ‹Nonempty V›
  have hprojHEq : HEq ((S3087Theater V A i).primeStrip.proj v0)
      ((S3087Theater V A j).primeStrip.proj v0) :=
    congr_arg_heq (fun T : HodgeTheater.{0, 0, 0, 0} fiveLabel V =>
      T.primeStrip.proj v0) h
  have hproj : (S3087Theater V A i).primeStrip.proj v0 =
      (S3087Theater V A j).primeStrip.proj v0 := eq_of_heq hprojHEq
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

/-- Generic link refl. -/
theorem S3088TheaterLink_refl
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (i : SourceTheorem311Index) :
    S3088TheaterLink V A i i = HodgeTheaterLink.refl (S3087Theater V A i) := by
  refine S3088TheaterLink_ext V ?_
  exact S3088StripEquiv_self V i

/-- Generic link symmetry. -/
theorem S3088TheaterLink_symm
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (i j : SourceTheorem311Index) :
    HodgeTheaterLink.symm (S3088TheaterLink V A i j) =
      S3088TheaterLink V A j i := by
  refine S3088TheaterLink_ext V ?_
  exact S3088StripEquiv_symm V i j

/-- Generic link transitivity. -/
theorem S3088TheaterLink_trans
    (A : InitialThetaArithmeticData.{0} fiveLabel)
    (i j k : SourceTheorem311Index) :
    HodgeTheaterLink.trans (S3088TheaterLink V A i j)
        (S3088TheaterLink V A j k) =
      S3088TheaterLink V A i k := by
  refine S3088TheaterLink_ext V ?_
  exact S3088StripEquiv_trans V i j k

/-- Generic source Hodge theater family over any nonempty V. -/
noncomputable def S3088Family
    (A : InitialThetaArithmeticData.{0} fiveLabel) :
    SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} fiveLabel V where
  index := SourceTheorem311Index
  theater := S3087Theater V A
  distinct := S3088Theater_injective V A
  link := S3088TheaterLink V A
  link_refl := S3088TheaterLink_refl V A
  link_symm := S3088TheaterLink_symm V A
  link_trans := S3088TheaterLink_trans V A
  permutation := Equiv.refl SourceTheorem311Index
  permutationLink := fun i => HodgeTheaterLink.refl (S3087Theater V A i)
  permutation_naturality := by
    intro i j
    change HodgeTheaterLink.trans (S3088TheaterLink V A i j)
        (HodgeTheaterLink.refl (S3087Theater V A j)) =
      HodgeTheaterLink.trans (HodgeTheaterLink.refl (S3087Theater V A i))
        (S3088TheaterLink V A i j)
    rw [HodgeTheaterLink.trans_refl, HodgeTheaterLink.refl_trans]

#check S3088Family
#check S3087FamilyTarget
#print axioms S3088Family

end LeanFormal.IUT.XiFPaper.S3088FamilyConstructionActual
end