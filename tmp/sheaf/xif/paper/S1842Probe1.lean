import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
import Mathlib.RingTheory.Spectrum.Prime.Module
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

variable {X Y : CommAlgCat.FiniteEtale.{0} S1779R} (f : X ⟶ Y)

example : IsNoetherianRing S1779R := by infer_instance

example : IsNoetherianRing (X : Type) := by
  haveI : Module.Finite S1779R (X : Type) := X.property.left
  exact IsNoetherianRing.of_finite S1779R (X : Type)

example : True := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower S1779R (X : Type) (Y : Type) :=
    IsScalarTower.of_algebraMap_eq' (by
      ext r
      exact (f.hom.hom.commutes r).symm)
  haveI : Module.Finite S1779R (Y : Type) := Y.property.left
  haveI : Module.Finite S1779R (X : Type) := X.property.left
  haveI : Module.Finite (X : Type) (Y : Type) := by
    -- try transitivity
    exact Module.Finite.of_restrictScalars_finite S1779R (X : Type) (Y : Type) |>.mp ?_
  trivial

end LeanFormal.IUT.XiFPaper.S1842Probe
