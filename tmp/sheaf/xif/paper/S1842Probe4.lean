import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Noetherian.Basic

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.defProp false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1842Probe

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual

attribute [local instance] S1779PointClosureAlgebra

section General

variable {X Y : Type} [CommRing X] [CommRing Y]
  [Algebra X Y] [Module.Finite X Y] [Algebra.Etale X Y] [IsNoetherianRing X]

example : IsClopen (Module.support X Y) := by
  haveI : Module.FinitePresentation X Y := Module.finitePresentation_of_finite X Y
  haveI : Module.Flat X Y := inferInstance
  have hlc : IsLocallyConstant (fun p : PrimeSpectrum X => Module.rankAtStalk Y p) :=
    Module.isLocallyConstant_rankAtStalk
  have hsupp : Module.support X Y =
      {p : PrimeSpectrum X | Module.rankAtStalk Y p = 0}ᶜ := by
    ext p
    rw [Set.mem_compl_iff, Set.mem_setOf_eq, Module.rankAtStalk_eq_zero_iff_notMem_support,
      not_not]
  rw [hsupp]
  exact (hlc.isClopen_fiber 0).compl

end General

end LeanFormal.IUT.XiFPaper.S1842Probe
