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

example : True := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r = f.hom.hom ((algebraMap S1779R (X : Type)) r)
    exact (f.hom.hom.commutes r).symm
  haveI : Module.Finite S1779R (Y : Type) := Y.property.left
  haveI : Module.Finite S1779R (X : Type) := X.property.left
  haveI : Module.Finite (X : Type) (Y : Type) :=
    Module.Finite.of_restrictScalars_finite S1779R (X : Type) (Y : Type)
  haveI : IsNoetherianRing S1779R := by infer_instance
  haveI : IsNoetherianRing (X : Type) :=
    IsNoetherianRing.of_finite S1779R (X : Type)
  haveI : Module.FinitePresentation (X : Type) (Y : Type) :=
    Module.finitePresentation_of_finite (X : Type) (Y : Type)
  haveI : Algebra.FinitePresentation (X : Type) (Y : Type) := inferInstance
  haveI : Algebra.FormallyUnramified S1779R (X : Type) := inferInstance
  haveI : Algebra.FormallyEtale S1779R (Y : Type) := inferInstance
  haveI : Algebra.FormallyEtale (X : Type) (Y : Type) :=
    Algebra.FormallyEtale.of_restrictScalars (R := S1779R) (A := (X : Type)) (B := (Y : Type))
  haveI : Algebra.Etale (X : Type) (Y : Type) :=
    ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat (X : Type) (Y : Type) := inferInstance
  haveI : Module.Projective (X : Type) (Y : Type) :=
    Module.Flat.projective_of_finitePresentation
  have hfree : Module.freeLocus (X : Type) (Y : Type) = Set.univ :=
    Module.freeLocus_eq_univ_iff.mpr inferInstance
  trivial

end LeanFormal.IUT.XiFPaper.S1842Probe
