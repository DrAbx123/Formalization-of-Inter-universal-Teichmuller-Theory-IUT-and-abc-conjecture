import tmp.sheaf.xif.paper.S2580P10EqActual
import tmp.sheaf.xif.paper.S2665P10FintypeActual
import tmp.sheaf.xif.paper.S2598bHsepSplitActual
import tmp.sheaf.xif.paper.S2548ConcreteCycleTypeActual

noncomputable section
set_option maxHeartbeats 16000000
set_option maxRecDepth 100000
open Polynomial NumberField

namespace LeanFormal.IUT.XiFPaper.S2667PermBarCycleActual
attribute [local instance] Ideal.Quotient.field

abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S

theorem P10_lies_S2577 :
    (LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W).LiesOver
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10 := by
  have h := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10_lies_p10
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W
  rwa [LeanFormal.IUT.XiFPaper.S2580P10EqActual.p10_eq_self] at h

theorem fbar10_monic :
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10.Monic := by
  unfold LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10
  exact LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10'_monic.map
    (Ideal.Quotient.mk LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10)

theorem factorDegrees_filter_irreducible {k : Type} [Field k] {g : k[X]}
    (hg : g.Monic) (hirr : Irreducible g) (hdeg : g.natDegree = 12) :
    (LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees g).filter
      (fun n => n ≠ 1) = ({12} : Multiset ℕ) := by
  classical
  unfold LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
    Monic.normalize_eq_self hg]
  simp [hdeg]

local instance hp10 : LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10.IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10_max
local instance hP10 : (LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W).IsPrime :=
  LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10_prime
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W
local instance hP10over : (LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W).LiesOver
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10 := P10_lies_S2577
local instance hP10max : (LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W).IsMaximal :=
  LeanFormal.IUT.XiFPaper.S2664P10MaxActual.P10_isMaximal
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W

local instance fintypeR10p : Fintype
    (LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.A10 ⧸
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10) :=
  Fintype.ofEquiv (ZMod 613)
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.e.symm
local instance fintypeT10P : Fintype (T10 ⧸
    LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W) :=
  LeanFormal.IUT.XiFPaper.S2665P10FintypeActual.P10_fintype
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W
local instance decR10p : DecidableEq
    (LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.A10 ⧸
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10) :=
  Classical.decEq _
local instance decT10P : DecidableEq (T10 ⧸
    LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
      LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W) :=
  Classical.decEq _

theorem permBar_cycleType_twelve :
    (LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual.permBar
      (f := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10')
      (p := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10)
      (P := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
        LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W)).cycleType =
      ({12} : Multiset ℕ) := by
  classical
  have hcyc :=
    LeanFormal.IUT.XiFPaper.S2548ConcreteCycleTypeActual.concrete_permBar_cycleType
      (f := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.f10')
      (p := LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.p10)
      (P := LeanFormal.IUT.XiFPaper.S2663P10PrimeActual.P10
        LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.W)
      (hmonic := LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hmonic)
      (hsep := LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsep)
      (hsplit := LeanFormal.IUT.XiFPaper.S2598bHsepSplitActual.S2598b_hsplit)
  rw [hcyc]
  exact factorDegrees_filter_irreducible fbar10_monic
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10_irreducible
    LeanFormal.IUT.XiFPaper.S2577Away10FbarActual.fbar10_natDegree

#check permBar_cycleType_twelve
#print axioms permBar_cycleType_twelve

end LeanFormal.IUT.XiFPaper.S2667PermBarCycleActual
end
