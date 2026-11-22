/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# S2049: exact local-CFT interfaces for P1

This file is the Lean part of the S2049 inventory.  It does **not** construct the
maximal unramified extension and it does **not** assume that one exists.  It
records the exact P1 carrier as a structure and constructs everything that is
constructible from Mathlib v4.32.2 alone:

* the profinite integers as Mathlib's profinite completion of Multiplicative Int,
  with its canonical dense map from Int;
* the normalized valuation L^× →* Multiplicative Int of a nonarchimedean local
  field, together with its unit kernel characterization;
* from a *given* P1 carrier (maximal unramified extension plus topological
  identification of its Galois group with Zhat), the unramified local Artin map,
  its Frobenius, and the normalization/unit theorems.

The structure field galEquiv is the missing mathematical object; no inhabitant
is fabricated.  P2 (cyclotomic/torsion identification) and P3 (norm limitation,
local existence, transfer compatibility) are recorded in
coord/reports/S2049-local-cft-inventory.md; their existing exact interfaces are
S2027's localArtinTorsion and S2024's LocalReciprocityData.transfer_compat.

The proof of normalizedValuation_eq_one_iff is adapted from the private
localFieldUnitValuation_eq_one_iff in
LeanFormal.IUT.IUTII.Kummer.LocalFieldRigidity (Apache-2.0), and is exposed
here as a public reusable interface.
-/
import Mathlib.NumberTheory.LocalField.Basic
import Mathlib.RingTheory.Valuation.Integral
import Mathlib.RingTheory.Valuation.RamificationGroup
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion
import Mathlib.GroupTheory.Torsion
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.AbsoluteGaloisGroup

noncomputable section

open scoped WithZero
open ValuativeRel

namespace LeanFormal.IUT.XiFPaper.S2049LocalCFTInventory

universe u

/-! ## 1. The profinite integers Zhat and the canonical map Int to Zhat -/

/-- Mathlib's profinite completion of Int, written multiplicatively.  This is
the target of the unramified local Artin map.  It is a genuine ProfiniteGrp
(hence a compact totally disconnected topological group); no new axiom or
structure is introduced. -/
abbrev Zhat : Type :=
  ProfiniteGrp.ProfiniteCompletion.completion (GrpCat.of (Multiplicative ℤ))

/-- The canonical map Int to Zhat, i.e. Mathlib's dense embedding eta.  It sends
1 to the topological generator of Zhat. -/
def zhatOfInt : Multiplicative ℤ →* Zhat :=
  (ProfiniteGrp.ProfiniteCompletion.eta (GrpCat.of (Multiplicative ℤ))).hom

/-- The image of Int is dense in Zhat; this is Mathlib's
ProfiniteCompletion.denseRange. -/
theorem denseRange_zhatOfInt : DenseRange zhatOfInt :=
  ProfiniteGrp.ProfiniteCompletion.denseRange (GrpCat.of (Multiplicative ℤ))

/-- The class of 1 : Int in Zhat, the topological generator. -/
def zhatGenerator : Zhat := zhatOfInt (Multiplicative.ofAdd 1)

/-! ## 2. The normalized valuation of a nonarchimedean local field -/

variable (L : Type u) [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L]

/-- The normalized valuation L^× →* Multiplicative Int of a nonarchimedean local
field.  It is the composite of the valuation with Mathlib's
IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt and the canonical
identification (WithZero M)^× ≃* M. -/
noncomputable def normalizedValuation : Lˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    ((Units.map
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).toMonoidWithZeroHom.toMonoidHom).comp
      (Units.map (ValuativeRel.valuation L).toMonoidWithZeroHom.toMonoidHom))

/-- The kernel of the normalized valuation is exactly the integral unit group:
v(u) = 1 iff valuation L u = 1.  This is the public form of the unit-kernel
computation used by the tree's Kummer rigidity file. -/
theorem normalizedValuation_eq_one_iff (u : Lˣ) :
    normalizedValuation L u = 1 ↔ ValuativeRel.valuation L (u : L) = 1 := by
  let valueGroupValue : (ValueGroupWithZero L)ˣ :=
    Units.map (ValuativeRel.valuation L).toMonoidWithZeroHom.toMonoidHom u
  let integerValue : (WithZero (Multiplicative ℤ))ˣ :=
    Units.map
      (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).toMonoidWithZeroHom.toMonoidHom
      valueGroupValue
  change WithZero.unitsWithZeroEquiv integerValue = 1 ↔ _
  constructor
  · intro h
    have integerValue_eq_one : integerValue = 1 :=
      WithZero.unitsWithZeroEquiv.injective (by simpa only [map_one] using h)
    have valueGroupValue_eq_one : valueGroupValue = 1 := by
      apply (Units.map_injective
        (f := (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).toMonoidWithZeroHom.toMonoidHom)
        (IsNonarchimedeanLocalField.valueGroupWithZeroIsoInt L).injective)
      simpa only [integerValue, map_one] using integerValue_eq_one
    exact congrArg Units.val valueGroupValue_eq_one
  · intro h
    have valueGroupValue_eq_one : valueGroupValue = 1 := Units.ext h
    have integerValue_eq_one : integerValue = 1 := by
      change Units.map _ valueGroupValue = 1
      rw [valueGroupValue_eq_one, map_one]
    simpa only [map_one] using congrArg WithZero.unitsWithZeroEquiv integerValue_eq_one

/-! ## 3. The exact P1 carrier and the unramified local Artin map -/

/-- A precise maximal-unramified predicate for an intermediate field Lur of a
fixed algebraic closure.  It says that Lur is the fixed field of the inertia
subgroup of some valuation subring A of AlgebraicClosure L whose valuation ring
pulls back to the valuation ring of L.  This is the standard inertia-field
characterization of the maximal unramified extension; it is a real predicate, not
a free propositional field. -/
def IsMaximalUnramified (Lur : IntermediateField L (AlgebraicClosure L)) : Prop :=
  ∃ A : ValuationSubring (AlgebraicClosure L),
    (∀ x : L, algebraMap L (AlgebraicClosure L) x ∈ A ↔
      ValuativeRel.valuation L x ≤ 1) ∧
    Lur = IntermediateField.fixedField
      ((A.inertiaSubgroup L).map (A.decompositionSubgroup L).subtype)
/-- **The exact P1 carrier.**  A maximal unramified extension Lur of L
inside a fixed algebraic closure, together with a *topological* group
isomorphism Gal(Lur/L) ≃ₜ* Zhat.

No field of this structure is inhabited in this file.  Constructing an
inhabitant is exactly P1; the rest of this file shows that, once an inhabitant
is supplied, the unramified local Artin map and its normalization follow
formally.  This is the interface downstream P1 should target. -/
structure UnramifiedGaloisData where
  /-- The maximal unramified extension, as an intermediate field. -/
  Lur : IntermediateField L (AlgebraicClosure L)
  /-- The precise maximal-unramified property of Lur. -/
  isMaximalUnramified : IsMaximalUnramified L Lur
  /-- The topological identification with the profinite integers. -/
  galEquiv : Gal(Lur/L) ≃ₜ* Zhat

namespace UnramifiedGaloisData

variable {L : Type u} [Field L] [ValuativeRel L] [TopologicalSpace L]
  [IsNonarchimedeanLocalField L] (d : UnramifiedGaloisData L)

/-- The arithmetic Frobenius: the preimage of the topological generator
1 in Zhat under the P1 identification. -/
noncomputable def frobenius : Gal(d.Lur/L) :=
  d.galEquiv.symm zhatGenerator

/-- The unramified local Artin map L^× →* Gal(Lur/L), defined as the
normalized valuation followed by the canonical map Int to Zhat and the inverse
of the P1 identification.  Its image is the dense cyclic subgroup generated by
frobenius; it is not claimed to be surjective (the source L^× is not compact). -/
noncomputable def artin : Lˣ →* Gal(d.Lur/L) :=
  d.galEquiv.symm.toMonoidHom.comp (zhatOfInt.comp (normalizedValuation L))

/-- The defining square of the unramified local Artin map. -/
theorem galEquiv_artin (x : Lˣ) :
    d.galEquiv (d.artin x) = zhatOfInt (normalizedValuation L x) := by
  change d.galEquiv (d.galEquiv.symm (zhatOfInt (normalizedValuation L x))) = _
  rw [ContinuousMulEquiv.apply_symm_apply]

/-- Units of the valuation ring have trivial unramified Artin symbol. -/
theorem artin_unit {u : Lˣ} (hu : ValuativeRel.valuation L (u : L) = 1) :
    d.artin u = 1 := by
  apply d.galEquiv.injective
  rw [galEquiv_artin, (normalizedValuation_eq_one_iff L u).mpr hu, map_one, map_one]

/-- A uniformizer (an element of normalized valuation 1) maps to the
arithmetic Frobenius.  This is the standard normalization
rec_ur(pi) = Frob of the unramified local Artin map. -/
theorem artin_uniformizer {π : Lˣ}
    (hπ : normalizedValuation L π = Multiplicative.ofAdd 1) :
    d.artin π = d.frobenius := by
  apply d.galEquiv.injective
  rw [galEquiv_artin, hπ]
  exact (ContinuousMulEquiv.apply_symm_apply d.galEquiv zhatGenerator).symm

end UnramifiedGaloisData

/-- **The exact P1 proposition.**  P1 is precisely the existence of the P1
carrier: a maximal unramified extension together with its topological
identification with Zhat.  This is stated, not inhabited. -/
def P1ExactMissing : Prop := Nonempty (UnramifiedGaloisData L)

/-! ## 4. Axiom probes -/

#print axioms denseRange_zhatOfInt
#print axioms normalizedValuation_eq_one_iff
#print axioms UnramifiedGaloisData.galEquiv_artin
#print axioms UnramifiedGaloisData.artin_unit
#print axioms UnramifiedGaloisData.artin_uniformizer

end LeanFormal.IUT.XiFPaper.S2049LocalCFTInventory