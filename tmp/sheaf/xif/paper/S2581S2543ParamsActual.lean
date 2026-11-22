import tmp.sheaf.xif.paper.S2580P10EqActual
import tmp.sheaf.xif.paper.S2665P10FintypeActual
import tmp.sheaf.xif.paper.S2664P10MaxActual

noncomputable section
set_option maxHeartbeats 8000000
open Polynomial
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2577Away10FbarActual
open LeanFormal.IUT.XiFPaper.S2580P10EqActual
open LeanFormal.IUT.XiFPaper.S2661P10Actual
open LeanFormal.IUT.XiFPaper.S2663P10PrimeActual
open LeanFormal.IUT.XiFPaper.S2665P10FintypeActual

namespace LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual

abbrev R10 : Type := S2537ConcreteLocalizationActual.R
abbrev T10 : Type := S2537ConcreteLocalizationActual.S

noncomputable instance fintype_quot_p10 :
    Fintype (R10 ⧸ S2577Away10FbarActual.p10) :=
  Fintype.ofEquiv (ZMod 613) S2577Away10FbarActual.e.symm

instance decEq_quot_p10 : DecidableEq (R10 ⧸ S2577Away10FbarActual.p10) :=
  Classical.decEq _

theorem P10_lies_p10_self :
    (S2663P10PrimeActual.P10 S2577Away10FbarActual.W).LiesOver
      S2577Away10FbarActual.p10 := by
  have h := S2663P10PrimeActual.P10_lies_p10 S2577Away10FbarActual.W
  rwa [S2580P10EqActual.p10_eq_self] at h

theorem P10_isMaximal_self :
    (S2663P10PrimeActual.P10 S2577Away10FbarActual.W).IsMaximal :=
  S2664P10MaxActual.P10_isMaximal S2577Away10FbarActual.W

theorem P10_prime_self :
    (S2663P10PrimeActual.P10 S2577Away10FbarActual.W).IsPrime :=
  S2663P10PrimeActual.P10_prime S2577Away10FbarActual.W

#check fintype_quot_p10
#check decEq_quot_p10
#check P10_lies_p10_self
#check P10_isMaximal_self
#check P10_prime_self
#print axioms P10_lies_p10_self
end LeanFormal.IUT.XiFPaper.S2581S2543ParamsActual
end