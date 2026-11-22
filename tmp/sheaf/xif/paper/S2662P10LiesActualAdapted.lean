import tmp.sheaf.xif.paper.S2661P10Actual
import tmp.sheaf.xif.paper.S2588FbarIrreducibleActual

noncomputable section
set_option maxHeartbeats 8000000

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual
open LeanFormal.IUT.XiFPaper.S2584PrimeDegreeOneActual
open LeanFormal.IUT.XiFPaper.S2661P10Actual

namespace LeanFormal.IUT.XiFPaper.S2662P10LiesActualAdapted

abbrev O : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.C
abbrev OL : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.C
abbrev R10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.R
abbrev T10 : Type := LeanFormal.IUT.XiFPaper.S2537ConcreteLocalizationActual.S
abbrev SC : Type := LeanFormal.IUT.XiFPaper.S2565ConcreteIntegralClosureCActual.S

noncomputable def P0 (W : S2584PrimeDegreeOneWitness) : Ideal OL :=
  W.P.comap (algebraMap OL SC)

theorem P0_prime (W : S2584PrimeDegreeOneWitness) : (P0 W).IsPrime :=
  Ideal.comap_isPrime (algebraMap OL SC) W.P W.P_prime

theorem P0_lies (W : S2584PrimeDegreeOneWitness) :
    (P0 W).LiesOver W.p := by
  refine ⟨?_.symm⟩
  ext x
  rw [Ideal.mem_under, Ideal.mem_comap, ← RingHom.comp_apply]
  rw [show (algebraMap OL SC).comp (algebraMap O OL) = algebraMap O SC from
    IsScalarTower.algebraMap_eq O OL SC]
  rw [show (algebraMap O SC) x ∈ W.P ↔ x ∈ W.p from ?_]
  · rfl
  · have h := W.P_liesOver_p.over
    rw [Ideal.mem_under] at h
    exact h

#check P0
#check P0_prime
#check P0_lies

end LeanFormal.IUT.XiFPaper.S2662P10LiesActualAdapted
end
