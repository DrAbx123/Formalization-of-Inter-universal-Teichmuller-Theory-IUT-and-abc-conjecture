/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# S2500: the bridge from the honest Frobenius root/pair cycle type to the
actual S2480 cycle-type target

The main result is

  S2132FrobInducesPairCycleType  ->  S2480FirstMissing

(equivalently S2167ConcreteTarget -> S2480FirstMissing), and, through the
current S2480 identification S2480FirstMissing_iff_target, the matrix-range
target S2480Target.

## Proof route

1. S2132FrobInduces_iff turns the hypothesis into the root cycle-type form
   S2132FrobInducesRootCycleType.
2. Polynomial.Gal.restrict_surjective lifts the splitting-field automorphism
   sigma_L to an absolute Galois element sigma_K.  The canonical roots
   equivalence Polynomial.Gal.rootsEquivRoots and
   AlgEquiv.restrictNormal_commutes show that the root permutations are
   conjugate, hence have the same cycle type.
3. S2500Psi_eq identifies the S2056 root set with the root set of
   S2057Psi5F over the algebraic closure; S2500RootEquiv transports the cycle
   type to the S2056 root permutation used by S2480RootPerm.
4. S2480FirstMissing is exactly the resulting root-cycle statement, and
   S2480FirstMissing_iff_target converts it to the matrix-range target
   S2480Target (which itself uses S2480PairMatrix_cycleType).

The cycle-type transport uses the compiled lemma S2132cycleType_permCongr.
S2427RootPermCycleActual currently has no olean, and the S2345 integral-root
transport is not needed on this route.

The file was not compiled in the authoring session; it is intended for the
parent's serial lake env lean pass.  IMPORTANT: S2480CycleTypeRepairActual.lean
was updated at 04:38 (the current olean is older); recompile S2480 first.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Polynomial
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual

namespace LeanFormal.IUT.XiFPaper.S2500TargetBridgeActual

/-! ## 1. psi_5 over F' and over the algebraic closure -/

/-- The actual odd 5-division polynomial over F'. -/
abbrev S2500p : S1720Field[X] := S2057Psi5F

/-- The algebraic closure of F' used by S2056/S2480. -/
abbrev S2500K : Type := S2056K

/-- psi_5 splits over the algebraic closure. -/
local instance S2500FactSplits :
    Fact ((S2500p.map (algebraMap S1720Field S2500K)).Splits) :=
  ⟨IsAlgClosed.splits _⟩

/-- The polynomial identity identifying the S2056 polynomial over the closure
with the base change of the S2057 polynomial over F'. -/
theorem S2500Psi_eq :
    S2056W.preΨ (5 : ℤ) = S2500p.map (algebraMap S1720Field S2500K) := by
  change (((S1667Curve.map (algebraMap ℚ S1720Field)).map
      (algebraMap S1720Field S2500K)).preΨ (5 : ℤ)) =
    (((S1667Curve.preΨ (5 : ℤ)).map (algebraMap ℚ S1720Field)).map
      (algebraMap S1720Field S2500K))
  simp only [WeierstrassCurve.map_preΨ]

/-- Membership in the twelve S2056 roots is membership in the root set of the
S2057 polynomial over the closure. -/
theorem S2500RootMem_iff (x : S2500K) :
    x ∈ S2056RootFinset ↔ x ∈ S2500p.rootSet S2500K := by
  rw [S2056RootFinset, Multiset.mem_toFinset,
    Polynomial.mem_roots S2056W_preΨ_ne_zero, Polynomial.IsRoot.def,
    Polynomial.mem_rootSet', S2500Psi_eq]
  constructor
  · intro hx
    refine ⟨S2056W_preΨ_ne_zero, ?_⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, S2500Psi_eq]
    exact hx
  · rintro ⟨_, hx⟩
    rw [Polynomial.aeval_def, ← Polynomial.eval_map, S2500Psi_eq] at hx
    exact hx

/-- The S2056 root set is the root set of S2057Psi5F over the closure. -/
noncomputable def S2500RootEquiv : S2056Root ≃ S2500p.rootSet S2500K :=
  Equiv.subtypeEquivRight S2500RootMem_iff

@[simp] theorem S2500RootEquiv_coe (x : S2056Root) :
    (S2500RootEquiv x).1 = x.1 := rfl

@[simp] theorem S2500RootEquiv_symm_coe (y : S2500p.rootSet S2500K) :
    (S2500RootEquiv.symm y).1 = y.1 := rfl

/-! ## 2. Lifting a splitting-field automorphism to the absolute Galois group -/

/-- The canonical equivalence between the roots of psi_5 in its splitting
field and in the algebraic closure. -/
noncomputable def S2500RootsEquiv :
    S2500p.rootSet S2132L ≃ S2500p.rootSet S2500K :=
  Polynomial.Gal.rootsEquivRoots S2500p S2500K

@[simp] theorem S2500RootsEquiv_coe (y : S2500p.rootSet S2132L) :
    (S2500RootsEquiv y).1 = algebraMap S2132L S2500K y.1 := rfl

/-- The action of a splitting-field automorphism on the roots in the splitting
field. -/
noncomputable def S2500RootPermL (σ : Polynomial.Gal S2500p) :
    Equiv.Perm (S2500p.rootSet S2132L) :=
  MulAction.toPermHom (Polynomial.Gal S2500p) (S2500p.rootSet S2132L) σ

/-- This action is the S2132 root permutation. -/
theorem S2500RootPermL_eq (σ : Polynomial.Gal S2500p) :
    S2500RootPermL σ = S2132DivisionRootEquiv σ := by
  apply Equiv.ext
  intro x
  apply Subtype.ext
  rfl

/-- The action of an absolute Galois element on the roots in the closure,
through the restriction to the splitting field. -/
noncomputable def S2500RootPermK (σ : S1725AbsoluteGalois) :
    Equiv.Perm (S2500p.rootSet S2500K) :=
  MulAction.toPermHom (Polynomial.Gal S2500p) (S2500p.rootSet S2500K)
    (Polynomial.Gal.restrict S2500p S2500K σ)

/-- The underlying value of the root action in the closure is the Galois
action itself. -/
theorem S2500RootPermK_coe (σ : S1725AbsoluteGalois)
    (x : S2500p.rootSet S2500K) :
    (S2500RootPermK σ x).1 = σ x.1 := by
  change ((Polynomial.Gal.restrict S2500p S2500K σ • x :
    S2500p.rootSet S2500K) : S2500K) = σ x.1
  exact Polynomial.Gal.restrict_smul S2500p S2500K σ x

/-- A lift of sigma_L along the restriction map has the conjugate root
permutation on the closure. -/
theorem S2500RootPermK_eq_permCongr (σ_L : Polynomial.Gal S2500p)
    (σ_K : S1725AbsoluteGalois)
    (h : Polynomial.Gal.restrict S2500p S2500K σ_K = σ_L) :
    S2500RootsEquiv.permCongr (S2500RootPermL σ_L) = S2500RootPermK σ_K := by
  ext x
  apply Subtype.ext
  have hx : algebraMap S2132L S2500K ((S2500RootsEquiv.symm x).1) = x.1 := by
    have h' := congrArg Subtype.val (Equiv.apply_symm_apply S2500RootsEquiv x)
    simpa [S2500RootsEquiv_coe] using h'
  have hL : (S2500RootsEquiv.permCongr (S2500RootPermL σ_L) x).1 =
      algebraMap S2132L S2500K (σ_L ((S2500RootsEquiv.symm x).1)) := by
    rw [Equiv.permCongr_apply, S2500RootsEquiv_coe]
    congr 1
    simpa [S2500RootPermL_eq]
  have hR : (S2500RootPermK σ_K x).1 = σ_K x.1 :=
    S2500RootPermK_coe σ_K x
  have hcomm : algebraMap S2132L S2500K (σ_L ((S2500RootsEquiv.symm x).1)) =
      σ_K (algebraMap S2132L S2500K ((S2500RootsEquiv.symm x).1)) := by
    have hc := AlgEquiv.restrictNormal_commutes (F := S1720Field)
      (K₁ := S2500K) (K₂ := S2500K) (E := S2132L) σ_K
      ((S2500RootsEquiv.symm x).1)
    have hrestr : σ_K.restrictNormal S2132L = σ_L := by
      simpa using h
    simpa [hrestr] using hc
  calc
    (S2500RootsEquiv.permCongr (S2500RootPermL σ_L) x).1
        = algebraMap S2132L S2500K (σ_L ((S2500RootsEquiv.symm x).1)) := hL
    _ = σ_K (algebraMap S2132L S2500K ((S2500RootsEquiv.symm x).1)) := hcomm
    _ = σ_K x.1 := by simp [hx]
    _ = (S2500RootPermK σ_K x).1 := hR.symm

/-- The cycle-type transport from the splitting-field root action to the S2056
root permutation used by S2480. -/
theorem S2500RootEquiv_transport (σ : S1725AbsoluteGalois) :
    S2480RootPerm σ = S2500RootEquiv.symm.permCongr (S2500RootPermK σ) := by
  ext x
  apply Subtype.ext
  simp [S2480RootPerm_apply, S2056RootMap, S2500RootEquiv_symm_coe,
    S2500RootPermK_coe, S2500RootEquiv_coe]

/-! ## 3. The bridge -/

/-- The root cycle-type form of the hypothesis gives an absolute Galois element
whose S2056 root permutation has cycle type (10, 2). -/
theorem S2500RootCycleType_lift (h : S2132FrobInducesRootCycleType) :
    ∃ σ_K : S1725AbsoluteGalois,
      (S2480RootPerm σ_K).cycleType = ({10, 2} : Multiset ℕ) := by
  classical
  obtain ⟨σ_L, hσ⟩ := h
  obtain ⟨σ_K, hK⟩ :=
    Polynomial.Gal.restrict_surjective S2500p S2500K σ_L
  refine ⟨σ_K, ?_⟩
  have hKroot : (S2500RootPermK σ_K).cycleType =
      ({10, 2} : Multiset ℕ) := by
    have hperm := S2500RootPermK_eq_permCongr σ_L σ_K hK
    rw [← hperm, S2132cycleType_permCongr, S2500RootPermL_eq, hσ]
    decide
  rw [S2500RootEquiv_transport, S2132cycleType_permCongr]
  exact hKroot

/-- The root/pair cycle-type target implies the S2480 first-missing target
(the absolute-closure root-cycle statement). -/
theorem S2500TargetBridge (h : S2132FrobInducesPairCycleType) :
    S2480FirstMissing := by
  obtain ⟨σ_K, hσ⟩ :=
    S2500RootCycleType_lift ((S2132FrobInduces_iff).mpr h)
  change ∃ σ : S1725AbsoluteGalois,
    (S2480RootPerm σ).cycleType = ({10, 2} : Multiset ℕ)
  exact ⟨σ_K, hσ⟩

/-- The same bridge lands directly on the actual matrix-range target
S2480Target. -/
theorem S2500TargetBridge_target (h : S2132FrobInducesPairCycleType) :
    S2480Target :=
  S2480FirstMissing_iff_target.mp (S2500TargetBridge h)

/-- The S2167 name of the hypothesis gives the same first-missing bridge. -/
theorem S2500TargetBridge_S2167 (h : S2167ConcreteTarget) :
    S2480FirstMissing :=
  S2500TargetBridge h

/-- The S2167 name of the hypothesis gives the matrix-range target. -/
theorem S2500TargetBridge_S2167_target (h : S2167ConcreteTarget) :
    S2480Target :=
  S2500TargetBridge_target h

/-! ## 4. Axiom footprint -/

#print axioms S2500Psi_eq
#print axioms S2500RootMem_iff
#print axioms S2500RootEquiv
#print axioms S2500RootsEquiv
#print axioms S2500RootPermL
#print axioms S2500RootPermL_eq
#print axioms S2500RootPermK
#print axioms S2500RootPermK_coe
#print axioms S2500RootPermK_eq_permCongr
#print axioms S2500RootEquiv_transport
#print axioms S2500RootCycleType_lift
#print axioms S2500TargetBridge
#print axioms S2500TargetBridge_target
#print axioms S2500TargetBridge_S2167
#print axioms S2500TargetBridge_S2167_target

end LeanFormal.IUT.XiFPaper.S2500TargetBridgeActual

end
