import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Module
import Mathlib.RingTheory.Spectrum.Prime.Topology
import Mathlib.RingTheory.Finiteness.ModuleFinitePresentation
import Mathlib.RingTheory.Noetherian.Basic
import Mathlib.Algebra.Module.LocalizedModule.Basic

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

lemma support_isClopen : IsClopen (Module.support X Y) := by
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

lemma exists_idempotent_support_eq_basicOpen :
    ∃ e : X, IsIdempotentElem e ∧ Module.support X Y = PrimeSpectrum.basicOpen e :=
  PrimeSpectrum.isClopen_iff.mp support_isClopen

lemma one_sub_e_smul_one_eq_zero {e : X} (he : IsIdempotentElem e)
    (hsupp : Module.support X Y = PrimeSpectrum.basicOpen e) :
    (1 - e) • (1 : Y) = 0 := by
  have hsub : Module.support X Y ⊆ PrimeSpectrum.zeroLocus ({1 - e} : Set X) := by
    rw [hsupp, PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  have hsingle : Subsingleton (LocalizedModule.Away (1 - e) Y) :=
    LocalizedModule.subsingleton_iff_support_subset.mpr hsub
  obtain ⟨r, hr, hry⟩ := (LocalizedModule.subsingleton_iff).mp hsingle (1 : Y)
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff r (1 - e)).mp hr
  rw [← hn] at hry
  rcases n with _ | n
  · simp only [pow_zero, one_smul] at hry
    rw [hry, smul_zero]
  · rw [IsIdempotentElem.pow_succ_eq n he.one_sub] at hry
    simpa using hry

end General

end LeanFormal.IUT.XiFPaper.S1842Probe
