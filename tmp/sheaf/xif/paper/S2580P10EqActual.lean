import tmp.sheaf.xif.paper.S2577Away10FbarActual
import tmp.sheaf.xif.paper.S2661P10Actual
import tmp.sheaf.xif.paper.S2664P10MaxActual

noncomputable section
open Polynomial
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
open LeanFormal.IUT.XiFPaper.S2661P10Actual

namespace LeanFormal.IUT.XiFPaper.S2580P10EqActual

abbrev O : Type := S2565ConcreteIntegralClosureCActual.C
abbrev R10 : Type := S2537ConcreteLocalizationActual.R

theorem p10_eq_self :
    S2661P10Actual.p10 S2577Away10FbarActual.W =
      S2577Away10FbarActual.p10 := by
  haveI hpR : (S2661P10Actual.p10 S2577Away10FbarActual.W).IsMaximal :=
    S2661P10Actual.p10_isMaximal S2577Away10FbarActual.W
  have hker : (S2577Away10FbarActual.p10).IsPrime :=
    RingHom.ker_isPrime S2577Away10FbarActual.φ10
  have hle : S2661P10Actual.p10 S2577Away10FbarActual.W ≤
      S2577Away10FbarActual.p10 := by
    rw [S2661P10Actual.p10, Ideal.map_le_iff_le_comap]
    intro a ha
    rw [Ideal.mem_comap]
    change S2577Away10FbarActual.φ10
      (algebraMap S2661P10Actual.A10 S2661P10Actual.R10 a) = 0
    rw [show S2577Away10FbarActual.φ10
        (algebraMap S2661P10Actual.A10 S2661P10Actual.R10 a) =
        S2577Away10FbarActual.g a by
      rw [← RingHom.comp_apply, S2577Away10FbarActual.φ10_comp_algebraMap]]
    have hq : Ideal.Quotient.mk S2577Away10FbarActual.W.p a = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.mpr ha
    simp [S2577Away10FbarActual.g, hq]
  exact Ideal.IsMaximal.eq_of_le hpR hker.ne_top hle

#check p10_eq_self
#print axioms p10_eq_self
end LeanFormal.IUT.XiFPaper.S2580P10EqActual
end