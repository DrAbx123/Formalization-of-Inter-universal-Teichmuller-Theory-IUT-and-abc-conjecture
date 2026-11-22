/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import tmp.sheaf.xif.paper.S1720SourceArithmeticActual
import tmp.sheaf.xif.paper.S1725SourceTorsionFPrimeActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1906RankTwoTorsionActual
import tmp.sheaf.xif.paper.S1667AdmissibleCurveActual
import Mathlib.FieldTheory.PolynomialGaloisGroup

/-!
# S2502: root-permutation cycle-type transport from the S2132 splitting field
to the absolute closure

## Purpose

S2132FrobInducesPairCycleType (S2132) is stated on the actual splitting field
L = S2057FiveDivisionField of the odd 5-division polynomial psi_5 over
F' = S1720Field:

  there is sigma : Gal(L / F') such that the induced permutation of the twelve
  roots of psi_5 has cycle type (10, 2).

S2480FirstMissing (S2480) is stated on the absolute Galois group
Gal(F'-bar / F') and on the twelve S2056 roots of prePsi_5 in the algebraic
closure.  This file closes the transport between the two statements.

## What is proved here

1. S2502_prePsi_eq: the polynomial prePsi_5 over the algebraic closure is the
   base change of the S2057 polynomial over F'.  This is the only place where
   the actual curve data are used; the proof rewrites S2056W through
   S1720Curve.curve to the double base change of S1667Curve and applies
   Mathlib's WeierstrassCurve.map_prePsi on both sides.
2. S2502RootMem_iff and S2502RootEquiv: the rootSet of psi_5 over the
   algebraic closure is literally the S2056 root finset, so the S2056 roots
   and the rootSet are canonically equivalent.
3. S2502RootPermAC: the permutation of the rootSet of psi_5 over the algebraic
   closure induced by an absolute Galois element, realised through Mathlib's
   Polynomial.Gal.galAction.  Its underlying value is the Galois action
   (S2502RootPermAC_apply_val).
4. S2502cycleType_transport: every rho : Gal(L / F') is the restriction of
   some sigma : Gal(F'-bar / F') (Polynomial.Gal.restrict_surjective, using
   that the algebraic closure is normal over F'), and along the canonical
   equivalence roots in L = roots in the algebraic closure the cycle types of
   rho and sigma agree (S2132cycleType_permCongr).
5. S2502FirstMissing_of_frobInduces, S2502frobInduces_of_firstMissing and the
   equivalence S2502FirstMissing_iff_frobInduces: the S2132 splitting-field
   statement is equivalent to the S2480 absolute-closure root-cycle target.
   The passage to the matrix/pair formulation is exactly S2480's
   S2480PairMatrix_cycleType, which identifies the cycle type of the matrix
   action pairPermHom (rho_5(sigma)) on the twelve S2009 pairs with the cycle
   type of the S2056 root permutation of sigma.

## Exact missing

The transport itself is closed.  The remaining input of the whole route is
S2132FrobInducesPairCycleType itself: the arithmetic Dedekind--Frobenius
statement that the Frobenius at a prime of F' above 29 has root cycle type
(10, 2).  It is recorded below as S2502ExactMissing and is not inhabited here.

S2345RootSetEquivActual is the integral-root bridge of the Dedekind side of the
route (it has a compiled olean, so it is imported and its value lemma is
re-exported below).  S2427RootPermCycleActual has no olean at the time of
writing, so the identical cycle-type invariance is taken from the compiled
S2132cycleType_permCongr.

No sorry, admit, axiom, opaque declaration, True/PUnit gate or native_decide
is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

namespace LeanFormal.IUT.XiFPaper.S2502RootTransportActual

open Polynomial
open NumberField
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S1906RankTwoTorsionActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2345RootSetEquivActual

/-! ## 0. The S2345 integral-root bridge (recorded for the Dedekind side) -/

section S2345Bridge

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

/-- The S2345 identification of an integral root with its image in the ambient
number field.  This is the bridge used by the Dedekind--Frobenius side
(S2427/S2440); it is recorded here because the S2132 root permutation is
stated on the ambient field. -/
theorem S2502s2345RootSetEquiv_apply (f : (RingOfIntegers K)[X]) (hmonic : f.Monic)
    (a : f.rootSet (RingOfIntegers L)) :
    ((s2345RootSetEquiv (K := K) (L := L) f hmonic a).1 : L) =
      algebraMap (RingOfIntegers L) L a.1 :=
  s2345RootSetEquiv_apply (K := K) (L := L) f hmonic a

end S2345Bridge

/-! ## 1. prePsi_5 over the algebraic closure -/

/-- The odd 5-division polynomial over the algebraic closure of F' is the base
change of the actual S2057 polynomial over F'. -/
theorem S2502_prePsi_eq :
    S2056W.preΨ (5 : ℤ) =
      S2057Psi5F.map (algebraMap S1720Field S2056K) := by
  change (S1667Curve.baseChange S2056K).preΨ (5 : ℤ) =
    (((S1667Curve.preΨ (5 : ℤ)).map (algebraMap ℚ S1720Field)).map
      (algebraMap S1720Field S2056K))
  rw [WeierstrassCurve.baseChange_preΨ]
  simp [S2057Psi5F, S2057Psi5Q]

/-! ## 2. The twelve roots in the algebraic closure are the S2056 roots -/

/-- The root set of psi_5 over the algebraic closure is the S2056 root
finset. -/
theorem S2502RootMem_iff (x : S2056K) :
    x ∈ S2056RootFinset ↔ x ∈ S2057Psi5F.rootSet S2056K := by
  rw [S2056RootFinset, Multiset.mem_toFinset,
    Polynomial.mem_roots S2056W_preΨ_ne_zero, Polynomial.IsRoot.def,
    Polynomial.mem_rootSet', ← S2502_prePsi_eq]
  rw [Polynomial.aeval_def, ← Polynomial.eval_map, ← S2502_prePsi_eq]
  constructor
  · intro hx
    exact ⟨S2056W_preΨ_ne_zero, hx⟩
  · rintro ⟨_, hx⟩
    exact hx

/-- The canonical equivalence between the roots of psi_5 over the algebraic
closure and the S2056 root type. -/
noncomputable def S2502RootEquiv :
    (S2057Psi5F.rootSet S2056K) ≃ S2056Root :=
  (Equiv.subtypeEquivRight S2502RootMem_iff).symm

@[simp] theorem S2502RootEquiv_apply_val (x : S2057Psi5F.rootSet S2056K) :
    (S2502RootEquiv x).1 = x.1 := rfl

/-! ## 3. The Galois permutation of the roots in the algebraic closure -/

/-- The algebraic closure is algebraically closed, so psi_5 splits there. -/
local instance S2502Splits :
    Fact ((S2057Psi5F.map (algebraMap S1720Field S2056K)).Splits) :=
  ⟨IsAlgClosed.splits (S2057Psi5F.map (algebraMap S1720Field S2056K))⟩

/-- The permutation of the roots of psi_5 over the algebraic closure induced by
an absolute Galois element, through the canonical action of the Galois group of
psi_5 on its roots. -/
noncomputable def S2502RootPermAC (σ : S1725AbsoluteGalois) :
    Equiv.Perm (S2057Psi5F.rootSet S2056K) :=
  Polynomial.Gal.galActionHom S2057Psi5F S2056K
    (Polynomial.Gal.restrict S2057Psi5F S2056K σ)

/-- The Galois action on the roots is the evaluation of the represented
permutation. -/
theorem S2502RootPermAC_apply (σ : S1725AbsoluteGalois)
    (x : S2057Psi5F.rootSet S2056K) :
    S2502RootPermAC σ x =
      Polynomial.Gal.restrict S2057Psi5F S2056K σ • x := rfl

/-- The underlying value of the represented root permutation is the Galois
action. -/
theorem S2502RootPermAC_apply_val (σ : S1725AbsoluteGalois)
    (x : S2057Psi5F.rootSet S2056K) :
    (S2502RootPermAC σ x).1 = σ x.1 := by
  rw [S2502RootPermAC_apply]
  exact Polynomial.Gal.restrict_smul (p := S2057Psi5F) (E := S2056K) σ x

/-- The root permutation over the algebraic closure corresponds to the S2056
root permutation under the canonical root equivalence. -/
theorem S2502RootEquiv_apply_rootPermAC (σ : S1725AbsoluteGalois)
    (x : S2057Psi5F.rootSet S2056K) :
    S2502RootEquiv (S2502RootPermAC σ x) =
      S2480RootPerm σ (S2502RootEquiv x) := by
  apply Subtype.ext
  rw [S2502RootEquiv_apply_val, S2480RootPerm_apply]
  change (S2502RootPermAC σ x).1 = σ (S2502RootEquiv x).1
  rw [S2502RootPermAC_apply_val, S2502RootEquiv_apply_val]

/-- The cycle type of the root permutation over the algebraic closure equals
the cycle type of the S2056 root permutation. -/
theorem S2502cycleType_rootPermAC (σ : S1725AbsoluteGalois) :
    (S2502RootPermAC σ).cycleType = (S2480RootPerm σ).cycleType := by
  have hconj : S2502RootEquiv.permCongr (S2502RootPermAC σ) = S2480RootPerm σ := by
    ext x
    rw [Equiv.permCongr_apply, S2502RootEquiv_apply_rootPermAC, Equiv.apply_symm_apply]
  rw [← hconj, S2132cycleType_permCongr]

/-! ## 4. Restriction of an absolute Galois element to the splitting field -/

/-- The represented permutation of the roots over the algebraic closure is the
conjugate, along the canonical identification of the roots of psi_5 in the
splitting field and in the algebraic closure, of the permutation induced by the
restriction of sigma to the splitting field. -/
theorem S2502RootPermAC_eq (σ : S1725AbsoluteGalois) :
    S2502RootPermAC σ =
      (Polynomial.Gal.rootsEquivRoots (p := S2057Psi5F) (E := S2056K)).permCongr
        (S2132DivisionRootEquiv
          (Polynomial.Gal.restrict S2057Psi5F S2056K σ)) := by
  ext x
  rw [Equiv.permCongr_apply, S2502RootPermAC_apply]
  rw [Polynomial.Gal.smul_def]
  have hinner : (Polynomial.Gal.restrict S2057Psi5F S2056K σ •
        (Polynomial.Gal.rootsEquivRoots (p := S2057Psi5F) (E := S2056K)).symm x) =
      S2132DivisionRootEquiv (Polynomial.Gal.restrict S2057Psi5F S2056K σ)
        ((Polynomial.Gal.rootsEquivRoots (p := S2057Psi5F) (E := S2056K)).symm x) := by
    apply Subtype.ext
    rfl
  rw [hinner]

/-- Every F'-automorphism of the splitting field is the restriction of an
absolute Galois element, and the two root permutations have the same cycle
type. -/
theorem S2502cycleType_transport (ρ : S2132L ≃ₐ[S1720Field] S2132L) :
    ∃ σ : S1725AbsoluteGalois,
      (S2480RootPerm σ).cycleType =
        Equiv.Perm.cycleType (S2132DivisionRootEquiv ρ) := by
  obtain ⟨σ, hσ⟩ :=
    Polynomial.Gal.restrict_surjective (p := S2057Psi5F) (E := S2056K) ρ
  refine ⟨σ, ?_⟩
  rw [← S2502cycleType_rootPermAC σ, S2502RootPermAC_eq σ,
    S2132cycleType_permCongr, hσ]

/-! ## 5. The transport theorems -/

/-- The honest S2132 splitting-field cycle-type statement implies the actual
S2480 absolute-closure root-cycle target. -/
theorem S2502FirstMissing_of_frobInduces
    (h : S2132FrobInducesPairCycleType) : S2480FirstMissing := by
  rw [S2480FirstMissing_iff_target, S2480Target_iff_exists_sigma]
  obtain ⟨ρ, hρ⟩ := S2132FrobInduces_iff.mpr h
  obtain ⟨σ, hσ⟩ := S2502cycleType_transport ρ
  refine ⟨σ, ?_⟩
  rw [S2480PairMatrix_cycleType σ]
  exact hσ.trans (hρ.trans (by decide))

/-- The S2480 absolute-closure root-cycle target implies the honest S2132
splitting-field cycle-type statement. -/
theorem S2502frobInduces_of_firstMissing
    (h : S2480FirstMissing) : S2132FrobInducesPairCycleType := by
  have hroot : ∃ σ : S1725AbsoluteGalois,
      (S2480RootPerm σ).cycleType = ({10, 2} : Multiset ℕ) := by
    have h' := S2480FirstMissing_iff_target.mp h
    rw [S2480Target_iff_exists_sigma] at h'
    obtain ⟨σ, hσ⟩ := h'
    exact ⟨σ, by rwa [S2480PairMatrix_cycleType σ] at hσ⟩
  obtain ⟨σ, hσ⟩ := hroot
  have hsplit :
      Equiv.Perm.cycleType
        (S2132DivisionRootEquiv (Polynomial.Gal.restrict S2057Psi5F S2056K σ)) =
        (S2480RootPerm σ).cycleType := by
    rw [← S2502cycleType_rootPermAC σ, S2502RootPermAC_eq σ,
      S2132cycleType_permCongr]
  refine S2132FrobInduces_iff.mp
    ⟨Polynomial.Gal.restrict S2057Psi5F S2056K σ, ?_⟩
  rw [hsplit, hσ]
  decide

/-- **The root-permutation cycle-type transport.**  The honest splitting-field
statement of S2132 is equivalent to the absolute-closure root-cycle target of
S2480. -/
theorem S2502FirstMissing_iff_frobInduces :
    S2480FirstMissing ↔ S2132FrobInducesPairCycleType :=
  ⟨S2502frobInduces_of_firstMissing, S2502FirstMissing_of_frobInduces⟩

/-- The root-cycle statement on Gal(L/F') is equivalent to the root-cycle
statement on the absolute Galois group. -/
theorem S2502RootCycleType_iff :
    S2480RootCycleTypeRequired ↔ S2132FrobInducesRootCycleType := by
  constructor
  · intro h
    have htarget : S2480Target := S2480Target_iff_rootCycle.mpr h
    have hmiss : S2480FirstMissing := S2480FirstMissing_iff_target.mpr htarget
    exact S2132FrobInduces_iff.mpr (S2502frobInduces_of_firstMissing hmiss)
  · intro h
    have hmiss : S2480FirstMissing :=
      S2502FirstMissing_of_frobInduces (S2132FrobInduces_iff.mp h)
    exact S2480Target_iff_rootCycle.mp (S2480FirstMissing_iff_target.mp hmiss)

/-! ## 6. Exact missing input -/

/-- The remaining arithmetic input of the whole cycle-type route: the actual
Dedekind--Frobenius statement that an F'-automorphism of the splitting field of
psi_5 has root cycle type (10, 2).  This is not proved in this file; the file
proves that it is exactly equivalent to the S2480 target. -/
def S2502ExactMissing : Prop := S2132FrobInducesPairCycleType

/-- The exact missing input gives the S2480 first missing statement. -/
theorem S2502FirstMissing_of_exactMissing (h : S2502ExactMissing) :
    S2480FirstMissing :=
  S2502FirstMissing_of_frobInduces h

/-- The exact missing input is definitionally the S2132 statement. -/
theorem S2502ExactMissing_iff :
    S2502ExactMissing ↔ S2132FrobInducesPairCycleType :=
  Iff.rfl

/-! ## 7. Axiom footprint -/

#print axioms S2502s2345RootSetEquiv_apply
#print axioms S2502_prePsi_eq
#print axioms S2502RootMem_iff
#print axioms S2502RootEquiv
#print axioms S2502RootPermAC
#print axioms S2502RootPermAC_apply_val
#print axioms S2502RootEquiv_apply_rootPermAC
#print axioms S2502cycleType_rootPermAC
#print axioms S2502RootPermAC_eq
#print axioms S2502cycleType_transport
#print axioms S2502FirstMissing_of_frobInduces
#print axioms S2502frobInduces_of_firstMissing
#print axioms S2502FirstMissing_iff_frobInduces
#print axioms S2502ExactMissing_iff

end LeanFormal.IUT.XiFPaper.S2502RootTransportActual

end
