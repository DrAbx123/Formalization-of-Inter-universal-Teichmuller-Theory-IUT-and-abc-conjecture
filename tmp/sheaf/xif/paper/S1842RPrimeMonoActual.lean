/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors / S1842

# S1842: the missing field 4 at the closed point (0,0) of Spec R'

S1835 reduced the fourth field of the six-field fibre functor to

  S1835BCPreservesEpis : Functor.PreservesEpimorphisms S1835BC.op

and proved that the concrete sufficient form

  S1835BCInjectiveOnMonos

(for every mono f : X ⟶ Y of finite etale R'-algebras, the induced map
Omega (x)_{R'} X -> Omega (x)_{R'} Y is injective) implies field 4 verbatim.

This file attacks exactly that statement.  It proves, unconditionally:

* for every morphism f : X ⟶ Y of finite etale R'-algebras, the codomain Y
  is a *finite etale X-algebra* (S1842EtaleOfHom), hence flat and projective
  over X;
* the support Module.support X Y is clopen, and is cut out by an idempotent
  e : X (S1842SupportClopen, S1842ExistsIdempotentSupport);
* if e is such an idempotent, then (1 - e) • (1 : Y) = 0
  (S1842OneSubESmulOne);
* the tensor cancellation
  (Omega (x)_{R'} X) (x)_X Y ≃ Omega (x)_{R'} Y
  (S1842Cancel) and its compatibility with the unit map
  (S1842Cancel_tmul_one);
* consequently, if Y is faithfully flat over X, then
  Omega (x)_{R'} X -> Omega (x)_{R'} Y is injective
  (S1842Injective_of_faithfullyFlat).

The exact remaining input is isolated as

  S1842MonoFaithfullyFlat:
  for every mono f : X ⟶ Y of finite etale R'-algebras, Y is faithfully
  flat over X (with the X-algebra structure induced by f).

This is the algebraic core of field 4.  It is not hidden, weakened, or assumed:
S1842BCInjectiveOnMonos_of_monoFaithfullyFlat and
S1842BCPreservesEpis_of_monoFaithfullyFlat derive the literal S1835 targets
from it.  Equivalently, the missing content is the statement that a
monomorphism of finite etale R'-algebras is injective (then flatness of
Y/X, proved here, gives faithful flatness by the standard criterion).  The
support and idempotent lemmas above are the precise place where the present
proof stops: they show that a non-injective mono would have a nontrivial
idempotent 1 - e in its kernel, but turning this into a contradiction needs
the missing faithful-flat/injectivity statement.

No sorry, admit, new axiom, Shrink, ULift or PUnit occurs here.
-/

import tmp.sheaf.xif.paper.S1835FiberRPrimeActual
import Mathlib.RingTheory.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RingTheory.Flat.FaithfullyFlat.Algebra
import Mathlib.RingTheory.Etale.Basic
import Mathlib.RingTheory.Smooth.Flat
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
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace LeanFormal.IUT.XiFPaper.S1842RPrimeMonoActual

open CategoryTheory CategoryTheory.Limits
open scoped TensorProduct
open LeanFormal.IUT.XiFPaper.S1726OrbicurveFPrimeActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual
open LeanFormal.IUT.XiFPaper.S1779CorrectFiniteEtaleTargetActual.S1779FiniteEtaleClosure
open LeanFormal.IUT.XiFPaper.S1830G2G3RPrimeActual
open LeanFormal.IUT.XiFPaper.S1835FiberRPrimeActual

attribute [local instance] S1779PointClosureAlgebra

/-! ## 1. Tensor cancellation and faithful flatness

The following section is stated for an arbitrary commutative base R, an
arbitrary R-algebra Omega, and an R-algebra map X -> Y.  It is the abstract
form of the computation used at R = R', Omega = AlgebraicClosure F'. -/

section TensorCancellation

variable {R Omega X Y : Type} [CommRing R] [CommRing Omega] [Algebra R Omega]
  [CommRing X] [Algebra R X] [CommRing Y] [Algebra R Y] [Algebra X Y]
  [IsScalarTower R X Y]

/-- Make Omega (x)_R X an X-module through the right factor. -/
local instance : Algebra X (Omega ⊗[R] X) := Algebra.TensorProduct.rightAlgebra

/-- Make X (x)_R Omega an X-module through the left factor. -/
local instance : Algebra X (X ⊗[R] Omega) := Algebra.TensorProduct.leftAlgebra

/-- **Tensor cancellation**:
(Omega (x)_R X) (x)_X Y ≃ Omega (x)_R Y. -/
noncomputable def S1842Cancel :
    (Omega ⊗[R] X) ⊗[X] Y ≃ₗ[R] Omega ⊗[R] Y :=
  (TensorProduct.congr (R := X)
      (Algebra.TensorProduct.commRight R X Omega).symm.toLinearEquiv
      (LinearEquiv.refl X Y)).restrictScalars R ≪≫ₗ
    (TensorProduct.comm X (X ⊗[R] Omega) Y).restrictScalars R ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R X X Y Omega).restrictScalars R ≪≫ₗ
    (TensorProduct.comm R Y Omega)

/-- The cancellation sends (omega (x) x) (x) y to omega (x) (x • y). -/
theorem S1842Cancel_tmul_one (m : Omega ⊗[R] X) :
    S1842Cancel (R := R) (Omega := Omega) (X := X) (Y := Y) (m ⊗ₜ[X] (1 : Y)) =
      Algebra.TensorProduct.map (AlgHom.id R Omega) (IsScalarTower.toAlgHom R X Y) m := by
  induction m using TensorProduct.induction_on with
  | zero => simp
  | add m n hm hn =>
    rw [TensorProduct.add_tmul, map_add, hm, hn, map_add]
  | tmul omega x =>
    simp [S1842Cancel, TensorProduct.AlgebraTensorModule.cancelBaseChange_tmul,
      Algebra.smul_def]

/-- If Y is faithfully flat over X, then the base change map
Omega (x)_R X -> Omega (x)_R Y is injective. -/
theorem S1842Injective_of_faithfullyFlat [Module.FaithfullyFlat X Y] :
    Function.Injective (fun m : Omega ⊗[R] X =>
      Algebra.TensorProduct.map (AlgHom.id R Omega) (IsScalarTower.toAlgHom R X Y) m) := by
  intro m n hmn
  have hsub : (Algebra.TensorProduct.map (AlgHom.id R Omega)
      (IsScalarTower.toAlgHom R X Y)) (m - n) = 0 := by
    rw [map_sub, sub_eq_zero.mpr hmn]
  have h0 : S1842Cancel (R := R) (Omega := Omega) (X := X) (Y := Y)
      ((m - n) ⊗ₜ[X] (1 : Y)) = 0 := by
    rw [S1842Cancel_tmul_one, hsub]
  have h1 : (m - n) ⊗ₜ[X] (1 : Y) = 0 := by
    have := congrArg (S1842Cancel (R := R) (Omega := Omega) (X := X) (Y := Y)).symm h0
    simpa using this
  have h2 : (1 : Y) ⊗ₜ[X] (m - n) = 0 := by
    have := congrArg (TensorProduct.comm X (Omega ⊗[R] X) Y) h1
    simpa using this
  have hzero : m - n = 0 :=
    Module.FaithfullyFlat.tensorProduct_mk_injective (A := X) (B := Y)
      (M := Omega ⊗[R] X) (by simpa using h2)
  exact sub_eq_zero.mp hzero

end TensorCancellation

/-! ## 2. The exact remaining input and field 4 -/

/-- **The exact first missing input of field 4.**  A mono of finite etale
R'-algebras is faithfully flat (equivalently, injective) as an algebra map.
This is stated with the X-algebra structure induced by f. -/
def S1842MonoFaithfullyFlat : Prop :=
  ∀ {X Y : CommAlgCat.FiniteEtale.{0} S1779R} (f : X ⟶ Y), Mono f →
    letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
    Module.FaithfullyFlat (X : Type) (Y : Type)

/-- **The concrete S1835 target from the missing faithful-flatness input.** -/
theorem S1842BCInjectiveOnMonos_of_monoFaithfullyFlat
    (h : S1842MonoFaithfullyFlat) : S1835BCInjectiveOnMonos := by
  intro X Y f hf
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r =
      f.hom.hom ((algebraMap S1779R (X : Type)) r)
    exact (f.hom.hom.commutes r).symm
  haveI : Module.FaithfullyFlat (X : Type) (Y : Type) := h f hf
  have hmap : IsScalarTower.toAlgHom S1779R (X : Type) (Y : Type) = f.hom.hom := by
    ext x
    rfl
  have hinj := S1842Injective_of_faithfullyFlat (R := S1779R) (Omega := S1835Omega)
    (X := X) (Y := Y)
  rw [hmap] at hinj
  exact hinj

/-- **Field 4** (S1835BCPreservesEpis) from the missing faithful-flatness
input, through S1835's concrete form. -/
theorem S1842BCPreservesEpis_of_monoFaithfullyFlat
    (h : S1842MonoFaithfullyFlat) : S1835BCPreservesEpis :=
  S1835BCPreservesEpis_of_injectiveOnMonos
    (S1842BCInjectiveOnMonos_of_monoFaithfullyFlat h)

/-- The same conclusion in the form consumed by S1835's six-field assembly. -/
theorem S1842PreservesEpis_of_monoFaithfullyFlat
    (h : S1842MonoFaithfullyFlat) :
    Functor.PreservesEpimorphisms (S1835Fiber) :=
  S1835PreservesEpis_of (S1842BCPreservesEpis_of_monoFaithfullyFlat h)

/-- **The exact first missing input**, named for the DAG. -/
def S1842FirstMissing : Prop := S1842MonoFaithfullyFlat

/-! ## 3. Unconditional algebra of a morphism of finite etale R'-algebras

For every f : X ⟶ Y in CommAlgCat.FiniteEtale R', the codomain Y is a
finite etale X-algebra.  This uses Mathlib's restriction-of-scalars lemma for
formally etale maps, the finiteness of Y over R', and Noetherianity of X. -/

/-- Y is a finite etale X-algebra, hence flat and projective over X. -/
theorem S1842EtaleOfHom {X Y : CommAlgCat.FiniteEtale.{0} S1779R} (f : X ⟶ Y) :
    letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
    Algebra.Etale (X : Type) (Y : Type) := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r =
      f.hom.hom ((algebraMap S1779R (X : Type)) r)
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
    Algebra.FormallyEtale.of_restrictScalars (R := S1779R)
      (A := (X : Type)) (B := (Y : Type))
  exact ⟨inferInstance, inferInstance⟩

/-- The support of Y over X is clopen. -/
theorem S1842SupportClopen {X Y : CommAlgCat.FiniteEtale.{0} S1779R} (f : X ⟶ Y) :
    letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
    IsClopen (Module.support (X : Type) (Y : Type)) := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r =
      f.hom.hom ((algebraMap S1779R (X : Type)) r)
    exact (f.hom.hom.commutes r).symm
  haveI : Module.Finite S1779R (Y : Type) := Y.property.left
  haveI : Module.Finite S1779R (X : Type) := X.property.left
  haveI : Module.Finite (X : Type) (Y : Type) :=
    Module.Finite.of_restrictScalars_finite S1779R (X : Type) (Y : Type)
  haveI : IsNoetherianRing S1779R := by infer_instance
  haveI : IsNoetherianRing (X : Type) :=
    IsNoetherianRing.of_finite S1779R (X : Type)
  haveI : Algebra.Etale (X : Type) (Y : Type) := S1842EtaleOfHom f
  haveI : Module.FinitePresentation (X : Type) (Y : Type) :=
    Module.finitePresentation_of_finite (X : Type) (Y : Type)
  haveI : Module.Flat (X : Type) (Y : Type) := inferInstance
  have hlc : IsLocallyConstant
      (fun p : PrimeSpectrum (X : Type) => Module.rankAtStalk (Y : Type) p) :=
    Module.isLocallyConstant_rankAtStalk
  have hsupp : Module.support (X : Type) (Y : Type) =
      {p : PrimeSpectrum (X : Type) | Module.rankAtStalk (Y : Type) p = 0}ᶜ := by
    ext p
    rw [Set.mem_compl_iff, Set.mem_setOf_eq,
      Module.rankAtStalk_eq_zero_iff_notMem_support, not_not]
  rw [hsupp]
  exact (hlc.isClopen_fiber 0).compl

/-- The support idempotent. -/
theorem S1842ExistsIdempotentSupport {X Y : CommAlgCat.FiniteEtale.{0} S1779R}
    (f : X ⟶ Y) :
    letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
    ∃ e : (X : Type), IsIdempotentElem e ∧
      Module.support (X : Type) (Y : Type) = PrimeSpectrum.basicOpen e := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  exact PrimeSpectrum.isClopen_iff.mp (S1842SupportClopen f)

/-- If e cuts out the support, then 1 - e annihilates the unit of Y. -/
theorem S1842OneSubESmulOne {X Y : CommAlgCat.FiniteEtale.{0} S1779R}
    (f : X ⟶ Y) :
    letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
    ∀ (e : (X : Type)), IsIdempotentElem e →
      Module.support (X : Type) (Y : Type) = PrimeSpectrum.basicOpen e →
      (1 - e) • (1 : (Y : Type)) = 0 := by
  letI : Algebra (X : Type) (Y : Type) := f.hom.hom.toRingHom.toAlgebra
  haveI : IsScalarTower S1779R (X : Type) (Y : Type) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change (algebraMap S1779R (Y : Type)) r =
      f.hom.hom ((algebraMap S1779R (X : Type)) r)
    exact (f.hom.hom.commutes r).symm
  haveI : Module.Finite S1779R (Y : Type) := Y.property.left
  haveI : Module.Finite S1779R (X : Type) := X.property.left
  haveI : Module.Finite (X : Type) (Y : Type) :=
    Module.Finite.of_restrictScalars_finite S1779R (X : Type) (Y : Type)
  haveI : IsNoetherianRing S1779R := by infer_instance
  haveI : IsNoetherianRing (X : Type) :=
    IsNoetherianRing.of_finite S1779R (X : Type)
  haveI : Algebra.Etale (X : Type) (Y : Type) := S1842EtaleOfHom f
  intro e he hsupp
  have hsub : Module.support (X : Type) (Y : Type) ⊆
      PrimeSpectrum.zeroLocus ({1 - e} : Set (X : Type)) := by
    rw [hsupp, PrimeSpectrum.basicOpen_eq_zeroLocus_of_isIdempotentElem e he]
  have hsingle : Subsingleton (LocalizedModule.Away (1 - e) (Y : Type)) :=
    LocalizedModule.subsingleton_iff_support_subset.mpr hsub
  obtain ⟨r, hr, hry⟩ := (LocalizedModule.subsingleton_iff).mp hsingle (1 : (Y : Type))
  obtain ⟨n, hn⟩ := (Submonoid.mem_powers_iff r (1 - e)).mp hr
  rw [← hn] at hry
  rcases n with _ | n
  · simp only [pow_zero, one_smul] at hry
    rw [hry, smul_zero]
  · rw [IsIdempotentElem.pow_succ_eq n he.one_sub] at hry
    simpa using hry

/-! ## 4. Status and axiom audit -/

/-- The exact first missing statement, for the DAG. -/
def S1842Status : Prop := S1842MonoFaithfullyFlat

/-- The unconditional X-algebra facts are available; the missing input is
exactly faithful flatness of a mono. -/
theorem S1842Status_implies_field4 (h : S1842Status) : S1835BCPreservesEpis :=
  S1842BCPreservesEpis_of_monoFaithfullyFlat h

#check S1842Cancel
#check S1842Cancel_tmul_one
#check S1842Injective_of_faithfullyFlat
#check S1842MonoFaithfullyFlat
#check S1842BCInjectiveOnMonos_of_monoFaithfullyFlat
#check S1842BCPreservesEpis_of_monoFaithfullyFlat
#check S1842PreservesEpis_of_monoFaithfullyFlat
#check S1842EtaleOfHom
#check S1842SupportClopen
#check S1842ExistsIdempotentSupport
#check S1842OneSubESmulOne
#check S1842FirstMissing
#check S1842Status
#check S1842Status_implies_field4

#print axioms S1842Cancel
#print axioms S1842Cancel_tmul_one
#print axioms S1842Injective_of_faithfullyFlat
#print axioms S1842BCInjectiveOnMonos_of_monoFaithfullyFlat
#print axioms S1842BCPreservesEpis_of_monoFaithfullyFlat
#print axioms S1842PreservesEpis_of_monoFaithfullyFlat
#print axioms S1842EtaleOfHom
#print axioms S1842SupportClopen
#print axioms S1842ExistsIdempotentSupport
#print axioms S1842OneSubESmulOne
#print axioms S1842Status_implies_field4

end LeanFormal.IUT.XiFPaper.S1842RPrimeMonoActual
