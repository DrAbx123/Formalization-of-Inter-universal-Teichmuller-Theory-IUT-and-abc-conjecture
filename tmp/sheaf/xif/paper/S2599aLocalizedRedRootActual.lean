import tmp.sheaf.xif.paper.S2598bHsepSplitActual
import tmp.sheaf.xif.paper.S2581S2543ParamsActual
import tmp.sheaf.xif.paper.S2667PermBarCycleActual
import tmp.sheaf.xif.paper.S2539AbstractRedRootActual
import tmp.sheaf.xif.paper.S2597RootSetEquivActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual
attribute [local instance] Ideal.Quotient.field

abbrev O : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev OL : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.C
abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S
abbrev K : Type := LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual.S1720Field
abbrev L10 : Type := LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057FiveDivisionField
abbrev f : R10[X] := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'
abbrev p : Ideal R10 := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10
abbrev P : Ideal T10 := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W

local instance hp : p.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10_max

local instance hPprime : P.IsPrime :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_prime_self

local instance hPover : P.LiesOver p :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_lies_p10_self

local instance hPmax : P.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual.P10_isMaximal_self

local instance hPfield : Field (T10 ⧸ P) := Ideal.Quotient.field P
local instance hPdomain : IsDomain (T10 ⧸ P) := Ideal.Quotient.isDomain P

instance S2599a_instIC : IsIntegralClosure T10 R10 L10 :=
  LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S2537_isIntegralClosure

lemma f_natDegree_ne_zero : f.natDegree ≠ 0 := by
  rw [show f.natDegree = 12 from
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_natDegree]
  norm_num

noncomputable def toS (x : f.rootSet L10) : f.rootSet T10 :=
  LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS
    (R := R10) (S := T10) (L := L10) f
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    f_natDegree_ne_zero x

noncomputable def localizedRedRoot :
    f.rootSet L10 →
      (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.fbar f p).rootSet
        (T10 ⧸ P) :=
  fun x => LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.redRoot
    (f := f) (p := p) (P := P)
    (hmonic := LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic)
    (toS x)

theorem localizedRedRoot_injective : Function.Injective localizedRedRoot := by
  intro x y hxy
  apply LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS_injective
    (R := R10) (S := T10) (L := L10) f
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    f_natDegree_ne_zero
  exact (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.redRoot_injective
    (f := f) (p := p) (P := P)
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit) hxy

theorem card_rootSet_T10 : Fintype.card (f.rootSet T10) = f.natDegree :=
  LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.card_rootSet_eq
    (f := f) (p := p) (P := P)
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit

theorem card_rootSet_L10 : Fintype.card (f.rootSet L10) = f.natDegree := by
  classical
  have hsepK : (f.map (algebraMap R10 K)).Separable := by
    have hfK : f.map (algebraMap R10 K) =
        Polynomial.C ((5 : K)⁻¹) *
          LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5F :=
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_map_scalar
    rw [hfK]
    have hu : IsUnit (Polynomial.C ((5 : K)⁻¹)) := by
      rw [Polynomial.isUnit_C, isUnit_iff_ne_zero]
      exact inv_ne_zero (by norm_num)
    exact Polynomial.Separable.unit_mul hu
      LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual.S2057Psi5F_separable
  have hsep_g : (f.map (algebraMap R10 L10)).Separable := by
    have h := hsepK.map (f := algebraMap K L10)
    simpa only [Polynomial.map_map, IsScalarTower.algebraMap_eq R10 K L10] using h
  have hmapid : (f.map (algebraMap R10 L10)).map (algebraMap L10 L10) =
      f.map (algebraMap R10 L10) := by
    rw [Polynomial.map_map]
    simp
  have hg_ne : f.map (algebraMap R10 L10) ≠ 0 :=
    Polynomial.map_monic_ne_zero
      LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
  have hsplit_g : (f.map (algebraMap R10 L10)).Splits :=
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit
  have hsplit_g' : ((f.map (algebraMap R10 L10)).map (algebraMap L10 L10)).Splits := by
    rw [hmapid]
    exact hsplit_g
  have hcard : Fintype.card ((f.map (algebraMap R10 L10)).rootSet L10) =
      (f.map (algebraMap R10 L10)).natDegree :=
    LeanFormal.IUT.XiFPaper.S2533LocalizedDedekindActual.nonmonic_card_rootSet
      (f.map (algebraMap R10 L10)) hg_ne hsep_g hsplit_g'
  have hset : f.rootSet L10 = (f.map (algebraMap R10 L10)).rootSet L10 := by
    simp only [Polynomial.rootSet_def, Polynomial.aroots_def]
    rw [hmapid]
  have hdeg : (f.map (algebraMap R10 L10)).natDegree = f.natDegree :=
    Polynomial.natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective R10 L10) f
  calc Fintype.card (f.rootSet L10)
      = Fintype.card ((f.map (algebraMap R10 L10)).rootSet L10) :=
        Fintype.card_congr (Equiv.setCongr hset)
    _ = (f.map (algebraMap R10 L10)).natDegree := hcard
    _ = f.natDegree := hdeg

theorem localizedRedRoot_bijective : Function.Bijective localizedRedRoot := by
  have hcomp : localizedRedRoot =
      (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.redRoot
        (f := f) (p := p) (P := P)
        LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic) ∘ toS := rfl
  rw [hcomp]
  exact (LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual.redRoot_bijective
    (f := f) (p := p) (P := P)
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep
    LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit).comp
    (LeanFormal.IUT.XiFPaper.S2597RootSetEquivActual.toS_bijective
      (R := R10) (S := T10) (L := L10) f
      LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic
      f_natDegree_ne_zero card_rootSet_T10 card_rootSet_L10)

#check localizedRedRoot
#check localizedRedRoot_injective
#check card_rootSet_T10
#check card_rootSet_L10
#check localizedRedRoot_bijective
#print axioms localizedRedRoot_injective
#print axioms card_rootSet_T10
#print axioms card_rootSet_L10
#print axioms localizedRedRoot_bijective

end LeanFormal.IUT.XiFPaper.S2599aLocalizedRedRootActual
end
