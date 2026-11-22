/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2493UnitScalingActual
import tmp.sheaf.xif.paper.S2540AbstractPermBarActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

/-!
# S2493b: unit scaling invariance for `fbar`, `permBar` and `cycleType`

`S2540AbstractPermBarActual` attaches to `f : R[X]`, a maximal ideal `p` of `R`
with finite residue field and a maximal ideal `P` of `S` lying over `p`, the
`q`-Frobenius permutation

  `permBar f p P : Equiv.Perm ((fbar f p).rootSet (S ⧸ P))`

of the root set of the reduction `fbar f p` in `S ⧸ P`.  The localized S2427
argument needs this object only up to scaling `f` by a unit `u : R`.

Main results:

* `fbar_C_mul_unit`: `fbar (C u * f) p = C (mk p u) * fbar f p`, no hypothesis on `u`.
* `rootSet_fbar_C_mul_unit`: for a unit `u` the two root sets coincide.
* `castPerm`: transport of a permutation along an equality of subtypes.
* `castPerm_permBar`: `permBar` is compatible with that transport.
* `cycleType_C_mul_unit`: the cycle type of `permBar` is unchanged.

Note on `factorDegrees`: `S2167DedekindFrobCycleActual.factorDegrees` is declared
for `{K : Type}` (universe 0), while `R ⧸ p` here lives in `Type u`; the scaling
lemma `factorDegrees_C_mul_unit` of S2493 therefore cannot be transported to this
abstract setting as it stands.  A universe-0 specialization is required.

No `sorry`, `axiom`, `native_decide` or `opaque` is used; the axiom footprint of
each declaration is printed at the end of the file.
-/

noncomputable section
set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option linter.unusedSectionVars false
open Polynomial NumberField
attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2493bPermBarScalingActual

open LeanFormal.IUT.XiFPaper.S2539AbstractRedRootActual
open LeanFormal.IUT.XiFPaper.S2540AbstractPermBarActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2493UnitScalingActual

variable {R S K L : Type*}
  [CommRing R] [CommRing S] [IsDomain R] [IsDomain S] [Field K] [Field L]
  [Algebra R K] [Algebra K L] [Algebra R L] [Algebra S L] [Algebra R S]
  [IsScalarTower R K L] [IsScalarTower R S L] [IsFractionRing R K]
  [FaithfulSMul R L] [IsIntegralClosure S R L]
  (f : R[X]) (p : Ideal R) [hp : p.IsMaximal]
  (P : Ideal S) [hP : P.IsPrime] [hPover : P.LiesOver p] [hPmax : P.IsMaximal]
  [Fintype (R ⧸ p)] [Fintype (S ⧸ P)]

/-! Decidable equality on the residue fields is used noncomputably only, to state
`Equiv.Perm.cycleType`; it is not part of the mathematical content. -/
local instance decidableEqQuotientR : DecidableEq (R ⧸ p) := Classical.decEq _
local instance decidableEqQuotientS : DecidableEq (S ⧸ P) := Classical.decEq _

/-! ## Task 2: reduction of `C u * f` -/

/-- Reduction modulo `p` commutes with multiplication by a constant. -/
lemma fbar_C_mul_unit {u : R} :
    fbar (C u * f) p = C (Ideal.Quotient.mk p u) * fbar f p := by
  simp [fbar, Polynomial.map_mul]

/-! ## Task 3: transport of permutations along an equality of subtypes -/

/-- Transport a permutation across an equality of subtypes.  We use
`Equiv.setCongr` (rather than `Equiv.cast`) because it preserves the underlying
element definitionally, which is what makes `castPerm_permBar` a `rfl`-level
statement. -/
noncomputable def castPerm {α : Type*} {s t : Set α} (h : s = t) (σ : Equiv.Perm s) :
    Equiv.Perm t :=
  (Equiv.setCongr h).permCongr σ

/-! ## Root sets are unchanged by unit scaling -/

/-- Scaling a polynomial by a nonzero constant does not change its root set. -/
lemma rootSet_C_mul_of_ne_zero {T U : Type*} [CommRing T] [IsDomain T] [CommRing U]
    [IsDomain U] [Algebra T U] [Module.IsTorsionFree T U] (Q : T[X]) {c : T} (hc : c ≠ 0) :
    (C c * Q).rootSet U = Q.rootSet U := by
  classical
  rw [rootSet_def, rootSet_def]
  rw [aroots_C_mul (p := Q) (a := c) hc]

/-- The root set of the reduction is unchanged when `f` is scaled by a unit. -/
lemma rootSet_fbar_C_mul_unit {u : R} (hu : IsUnit u) :
    (fbar (C u * f) p).rootSet (S ⧸ P) = (fbar f p).rootSet (S ⧸ P) := by
  have hc : Ideal.Quotient.mk p u ≠ 0 := (RingHom.isUnit_map (Ideal.Quotient.mk p) hu).ne_zero
  rw [fbar_C_mul_unit (f := f) (p := p) (u := u)]
  exact rootSet_C_mul_of_ne_zero (fbar f p) hc

/-! ## Task 4: `permBar` is natural in the root set -/

/-- Transporting `permBar (C u * f)` along the root set equality recovers
`permBar f`: both act on the underlying element by `y ↦ y ^ Nat.card (R ⧸ p)`. -/
lemma castPerm_permBar {u : R}
    (h : (fbar (C u * f) p).rootSet (S ⧸ P) = (fbar f p).rootSet (S ⧸ P)) :
    castPerm h (permBar (f := C u * f) p P) = permBar (f := f) p P := by
  ext y
  rfl

/-! ## Task 5: cycle types are invariant under relabelling

`Mathlib` has `Equiv.permCongr` and `Equiv.Perm.cycleType`, but neither
`Equiv.permCongr_cycleType` nor `Equiv.Perm.cycleType_permCongr` exists in this
snapshot, so the cross-type statement is proved here by the cycle decomposition
of `Equiv.Perm.cycle_induction_on`. -/

/-- Relabelling preserves disjointness of permutations. -/
theorem permCongr_disjoint {α β : Type*} {e : α ≃ β} {σ τ : Equiv.Perm α}
    (h : Equiv.Perm.Disjoint σ τ) :
    Equiv.Perm.Disjoint (e.permCongr σ) (e.permCongr τ) := by
  rw [Equiv.Perm.disjoint_iff_eq_or_eq] at h ⊢
  intro y
  rcases h (e.symm y) with h1 | h2
  · left; simp [Equiv.permCongr_apply, h1]
  · right; simp [Equiv.permCongr_apply, h2]

/-- Relabelling preserves being a cycle. -/
theorem permCongr_isCycle {α β : Type*} {e : α ≃ β} {σ : Equiv.Perm α}
    (hσ : σ.IsCycle) : (e.permCongr σ).IsCycle := by
  obtain ⟨x, hx, h⟩ := hσ
  refine ⟨e x, ?_, ?_⟩
  · intro hc
    apply hx
    have h1 : e (σ x) = e x := by
      simpa [Equiv.permCongr_apply] using hc
    exact e.injective h1
  · intro y hy
    have hz : σ (e.symm y) ≠ e.symm y := by
      intro hzy
      apply hy
      rw [Equiv.permCongr_apply, hzy, Equiv.apply_symm_apply]
    obtain ⟨n, hn⟩ := h hz
    refine ⟨n, ?_⟩
    have hmap : e.permCongr (σ ^ n) = (e.permCongr σ) ^ n := by
      simpa using map_zpow (Equiv.permCongrHom e) σ n
    calc
      ((e.permCongr σ) ^ n) (e x) = e.permCongr (σ ^ n) (e x) := by rw [hmap]
      _ = e ((σ ^ n) x) := by simp [Equiv.permCongr_apply]
      _ = e (e.symm y) := by rw [hn]
      _ = y := by simp

/-- Relabelling transports supports. -/
theorem permCongr_support {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support = σ.support.map e.toEmbedding := by
  ext y
  simp only [Equiv.Perm.mem_support, Finset.mem_map, Equiv.coe_toEmbedding]
  constructor
  · intro hy
    refine ⟨e.symm y, ?_, e.apply_symm_apply y⟩
    intro h
    apply hy
    rw [Equiv.permCongr_apply, h, Equiv.apply_symm_apply]
  · rintro ⟨x, hx, rfl⟩
    rw [Equiv.permCongr_apply, Equiv.symm_apply_apply]
    simpa using hx

/-- Relabelling preserves the cardinality of the support. -/
theorem permCongr_card_support {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).support.card = σ.support.card := by
  rw [permCongr_support]
  exact Finset.card_map _

/-- The cycle type of a permutation is invariant under relabelling. -/
theorem permCongr_cycleType {α β : Type*} [Fintype α] [DecidableEq α] [Fintype β]
    [DecidableEq β] (e : α ≃ β) (σ : Equiv.Perm α) :
    (e.permCongr σ).cycleType = σ.cycleType := by
  induction σ using Equiv.Perm.cycle_induction_on with
  | base_one => simpa using map_one (Equiv.permCongrHom e)
  | base_cycles σ hσ =>
      rw [(permCongr_isCycle (e := e) hσ).cycleType, hσ.cycleType,
        permCongr_card_support e σ]
  | induction_disjoint σ τ hd hc hσ hτ =>
      rw [Equiv.permCongr_mul, hd.cycleType_mul, (permCongr_disjoint (e := e) hd).cycleType_mul,
        hσ, hτ]

/-- `castPerm` does not change the cycle type. -/
theorem castPerm_cycleType {α : Type*} {s t : Set α} [Fintype s] [DecidableEq s] [Fintype t]
    [DecidableEq t] (h : s = t) (σ : Equiv.Perm s) :
    (castPerm h σ).cycleType = σ.cycleType :=
  permCongr_cycleType (Equiv.setCongr h) σ

/-- Unit scaling does not change the cycle type of the `q`-Frobenius permutation. -/
theorem cycleType_C_mul_unit {u : R} (hu : IsUnit u) :
    (permBar (f := C u * f) p P).cycleType = (permBar (f := f) p P).cycleType := by
  have h := rootSet_fbar_C_mul_unit (f := f) (p := p) (P := P) hu
  rw [← castPerm_permBar (f := f) (p := p) (P := P) (u := u) h]
  rw [castPerm_cycleType]

/-! ## Axiom footprint -/

#print axioms fbar_C_mul_unit
#print axioms rootSet_C_mul_of_ne_zero
#print axioms rootSet_fbar_C_mul_unit
#print axioms castPerm_permBar
#print axioms permCongr_cycleType
#print axioms castPerm_cycleType
#print axioms cycleType_C_mul_unit

/-! ## Task 1: API probe

`Equiv.setCongr`, `Equiv.cast`, `Equiv.cast_apply`, `Equiv.permCongr_apply` and
`Equiv.Perm.cycle_induction_on` are the API used below.  The two names
`Equiv.permCongr_cycleType` and `Equiv.Perm.cycleType_permCongr` do NOT exist in
this Mathlib snapshot (`#check` reports `unknown constant` for both), so
`permCongr_cycleType` below is proved from `Equiv.Perm.cycle_induction_on`
instead. -/

#check Equiv.setCongr
#check Equiv.cast
#check Equiv.cast_apply
#check Equiv.permCongr_apply
#check Equiv.Perm.cycle_induction_on

end LeanFormal.IUT.XiFPaper.S2493bPermBarScalingActual
end
