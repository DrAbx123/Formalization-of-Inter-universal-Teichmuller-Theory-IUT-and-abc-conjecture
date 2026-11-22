/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2540Mod613CertificateActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2520RootCycleTransferActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
import tmp.sheaf.xif.paper.S2487DedekindCertificateActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual

/-!
# S2541: Dedekind--Frobenius cycle types at an actual residue-degree-one prime

## What this file is asked to do, and what is actually true

The task is to assemble the S2470 irreducible-residue Dedekind theorem at an
actual residue-degree-one prime so as to produce

  S2132FrobInducesPairCycleType,

conditional only on the residue certificate/data, using
S2470_residueIrreducible_rootTwelveCycle, S2520, S2481 and S2487.

**That derivation is mathematically impossible, and this file proves the
obstruction.**  The S2470 theorem produces an F'-automorphism whose
permutation of the twelve roots has cycle type {12}.  The canonical
root-to-pair bijection S2056RootPairEquiv is Galois-equivariant
(S2056Psi5RootsActual), so the induced permutation of the twelve pairs also has
cycle type {12}.  The S2132 target asks for cycle type {2, 10}.  Cycle type
is a conjugacy invariant, so no {12}-element can be a witness of the target:
the powers of a 12-cycle have cycle types {}, {2,2,2,2,2,2}, {3,3,3,3},
{4,4,4}, {6,6}, {12}, and never {2, 10}.

The two D5 arithmetic inputs must therefore not be confused:

* the irreducible reduction at a residue-degree-one prime (the mod-613
  certificate of S2540/S2481) gives the twelve-cycle, hence, together with the
  root-to-range transport S2470RootToRangeTransport, the pair-transitivity
  input S2440TwelveCycleInputRequired (not the cycle-type input);
* S2132FrobInducesPairCycleType needs a two-factor residue certificate:
  an irreducible quadratic times an irreducible degree-ten factor over the
  residue field of F' at the prime, together with the Dedekind--Frobenius
  comparison there.  The mod-29 factorization of the paper is over F_29,
  while 29 is inert in Q(sqrt(-3)) contained in F', so a prime of F' above 29
  has residue degree two and the relative Frobenius there has cycle type
  {5,5}, not {2,10} (this is the S2167/S2470 subtlety).

## What is proved unconditionally here

1. S2541_rootTwelveCycle: the S2470 theorem applied to actual residue data at
   the residue-degree-one prime 613 yields an F'-automorphism with root cycle
   type {12}.
2. S2541_rootSet_model_eq, S2541RootEquiv, S2541_permCongr_rootPerm,
   S2541_rootCycleType_eq_divisionRoot: the root cycle type of an integral
   model of a nonzero F'-multiple of psi_5 and the cycle type of the induced
   permutation S2132DivisionRootEquiv sigma of the actual roots in the
   five-division field agree.  This is the model-to-splitting-field transport
   that the S2470 route previously lacked on the cycle-type side.
3. S2541_pairTwelveCycle: the S2470 witness has pair cycle type {12}.
4. S2541_twelveCycle_not_pairTen: a twelve-cycle on the roots can never
   induce cycle type {2,10} on the pairs (the obstruction).
5. S2541RangeCycleType_of_frobInduces: S2132FrobInducesPairCycleType gives the
   actual range cycle-type input S2203RangeCycleTypeRequired S1982Basis (via
   S2520 and S2480).
6. S2541FrobInduces_of_dedekindAt: the honest conditional assembly: actual
   two-factor residue data at a residue-degree-one prime together with the
   Dedekind--Frobenius comparison at that prime give
   S2132FrobInducesPairCycleType.
7. S2541D5LargeImageFive_of_exactMissing and
   S2541D5LargeImageFive_of_bothExactMissing: the D5 large-image target from
   the S2132 cycle-type input plus the twelve-cycle/pair-transitivity route.

## Exact missing (reported, not proved)

* S2540IrreducibleRequired (S2540): the concrete finite-field certificate that
  2^36 psi_5 is irreducible modulo 613.  This is the finite part of the
  twelve-cycle route.  It is a plain Prop with no inhabitant in the tree
  (S2540ProbeDecide proposes a decide proof; it is not compiled here).
* S2470RootToRangeTransport (S2470): the model-to-range transport for the
  twelve-cycle/pair-transitivity route.
* S2541S2132ExactMissing: actual two-factor residue data at a residue-degree-one
  prime together with S2541DedekindFrobeniusAt, i.e. the Dedekind--Frobenius
  comparison at that prime.  No such two-factor residue data is in the tree.
  The general comparison is the corrected Dedekind--Frobenius theorem
  (S2217 DedekindFrobeniusCycleTypeTheoremCorrected); S2454/S2491 contain a
  raw/normalized proof, but their oleans are not in the compiled import graph,
  and the S2487 literal statement DedekindFrobeniusCycleTypeTheorem is refuted
  by S2217.

No sorry, admit, axiom, True/PUnit gate, or native_decide is used.  Every
conditional theorem is labelled _of_... and is not announced as the actual
target.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2541DedekindCycleActual

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual
open LeanFormal.IUT.XiFPaper.S2540Mod613CertificateActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S2487DedekindCertificateActual

/-- The model root set carries the classical decidable equality.  This is the
same instance that the `letI := Classical.decEq _` inside `rootCycleType` uses,
so that `rootCycleType` and an explicitly written `Equiv.Perm.cycleType` on the
model roots are definitionally the same object. -/
noncomputable instance S2541ModelRootSetDecEq (priority := 2000)
    (f : (RingOfIntegers S1720Field)[X]) :
    DecidableEq ((f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
      S2057FiveDivisionField) :=
  Classical.decEq _

/-! ## 1. The actual residue-degree-one prime at 613 -/

/-- A prime of O_{F'} is a residue-degree-one prime above the rational prime
q if it lies over (q) and has inertia degree one over Z. -/
def S2541ResidueDegreeOne (q : Nat) (p : Ideal (RingOfIntegers S1720Field)) : Prop :=
  p.LiesOver (Ideal.span ({(q : Int)} : Set Int)) ∧ p.inertiaDeg Int = 1

/-- The actual residue-degree-one prime above 613 supplied by S2481. -/
abbrev S2541ResidueDegreeOneAt613 (p : Ideal (RingOfIntegers S1720Field)) : Prop :=
  S2541ResidueDegreeOne 613 p

/-- The concrete finite-field certificate of the twelve-cycle route: the actual
integer model of 2^36 psi_5 is irreducible modulo 613 (S2540).  This is the
exact finite missing input; the residue-degree-one prime above 613 is the S2481
input, and S2541_sourceSplitsAt613 records the S2481 splitting. -/
abbrev S2541Mod613Certificate : Prop := S2540IrreducibleRequired

/-- The source field F' splits completely at 613 (S2481), the
Dedekind--Kummer input for a residue-degree-one prime above 613. -/
theorem S2541_sourceSplitsAt613 :
    (S2481HZ.map (Int.castRingHom (ZMod 613))).Splits :=
  S2481HMod613_splits

/-- The quadratic factor of the corrected mod-29 certificate is irreducible
(S2487, S2216).  Note that this is a mod-29 statement over F_29; it is not a
relative factor-degree statement over a residue field of F'. -/
theorem S2541_quadraticIrreducible : S2167QuadraticIrreducible :=
  S2487QuadraticIrreducible

/-- The degree-ten factor of the corrected mod-29 certificate is irreducible
(S2487, S2126). -/
theorem S2541_tenIrreducible : S2167TenIrreducible :=
  S2487TenIrreducible

/-- The actual residue data at the residue-degree-one prime 613: the S2470
residue data together with the residue-degree-one condition at 613. -/
def S2541ActualResidueData613 : Type :=
  {D : S2470ActualResidueData // S2541ResidueDegreeOneAt613 D.p}

/-- **The S2470 irreducible-residue Dedekind theorem at the actual
residue-degree-one prime.**  The residue data at 613 produce an
F'-automorphism of the actual five-division field whose permutation of the
twelve roots of the model has cycle type {12}. -/
theorem S2541_rootTwelveCycle (D : S2541ActualResidueData613) :
    ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
      rootCycleType S1720Field S2057FiveDivisionField D.1.f D.1.f_splits σ =
        ({12} : Multiset Nat) :=
  D.1.rootTwelveCycle

/-! ## 2. Transport from an integral model to the actual roots -/

/-- The root set in the five-division field of an integral model f of a
nonzero F'-multiple of the actual psi_5 is the root set of psi_5 itself. -/
theorem S2541_rootSet_model_eq
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F) :
    (f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
        S2057FiveDivisionField =
      S2057Psi5F.rootSet S2057FiveDivisionField := by
  obtain ⟨c, hc, hf⟩ := hpsi
  ext x
  simp only [Polynomial.mem_rootSet']
  have hcmap : algebraMap S1720Field S2057FiveDivisionField c ≠ 0 := by
    intro h
    exact hc ((algebraMap S1720Field S2057FiveDivisionField).injective (by simpa using h))
  constructor
  · rintro ⟨hne, hzero⟩
    rw [hf, Polynomial.map_mul, Polynomial.map_C] at hne
    rw [hf, Polynomial.aeval_mul, Polynomial.aeval_C] at hzero
    refine ⟨?_, ?_⟩
    · intro h0
      exact hne (by rw [h0, mul_zero])
    · exact (mul_eq_zero.mp hzero).resolve_left hcmap
  · rintro ⟨hne, hzero⟩
    rw [hf, Polynomial.map_mul, Polynomial.map_C, Polynomial.aeval_mul, Polynomial.aeval_C]
    refine ⟨?_, ?_⟩
    · intro h0
      rcases mul_eq_zero.mp h0 with h1 | h1
      · exact hcmap h1
      · exact hne h1
    · rw [hzero, mul_zero]

/-- The canonical identification of the model roots with the actual roots of
psi_5 in the five-division field. -/
noncomputable def S2541RootEquiv
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F) :
    (f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
        S2057FiveDivisionField ≃
      S2057Psi5F.rootSet S2057FiveDivisionField :=
  Equiv.setCongr (S2541_rootSet_model_eq f hpsi)

/-- The value of the root permutation on the model roots: the Galois action on
the underlying element. -/
theorem S2541_rootPerm_apply
    (f : (RingOfIntegers S1720Field)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    (x : (f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
      S2057FiveDivisionField) :
    ((rootPerm S1720Field S2057FiveDivisionField f hsplit σ x).1 : S2057FiveDivisionField) =
      σ • x.1 := rfl

/-- The root permutation on the model roots is the permutation
S2132DivisionRootEquiv sigma of the actual roots under the canonical
identification. -/
theorem S2541_permCongr_rootPerm
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F)
    (hsplit : (f.map (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)) :
    (S2541RootEquiv f hpsi).permCongr
        (rootPerm S1720Field S2057FiveDivisionField f hsplit σ) =
      S2132DivisionRootEquiv σ := by
  ext x
  apply Subtype.ext
  rw [Equiv.permCongr_apply]
  have hval : ∀ y : (f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
        S2057FiveDivisionField,
      (((S2541RootEquiv f hpsi) y).1 : S2057FiveDivisionField) = y.1 := fun y => rfl
  have hsym : ∀ y : S2057Psi5F.rootSet S2057FiveDivisionField,
      ((((S2541RootEquiv f hpsi).symm y)).1 : S2057FiveDivisionField) = y.1 := fun y => rfl
  rw [hval, S2541_rootPerm_apply, AlgEquiv.smul_def, hsym]
  rfl

/-- **The model-to-splitting-field cycle-type transport.**  The cycle type of
the integral model roots equals the cycle type of the induced permutation of
the actual roots (equivalently of the twelve pairs). -/
theorem S2541_rootPerm_cycleType_eq_divisionRoot
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F)
    (hsplit : (f.map (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)) :
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ).cycleType =
      Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) := by
  classical
  rw [← S2541_permCongr_rootPerm f hpsi hsplit σ]
  exact (S2132cycleType_permCongr (S2541RootEquiv f hpsi)
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ)).symm

/-- **The model-to-splitting-field cycle-type transport, root-cycle form.** -/
theorem S2541_rootCycleType_eq_divisionRoot
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F)
    (hsplit : (f.map (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)) :
    rootCycleType S1720Field S2057FiveDivisionField f hsplit σ =
      Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) :=
  S2541_rootPerm_cycleType_eq_divisionRoot f hpsi hsplit σ

/-! ## 3. The twelve-cycle on the pairs and the {12} versus {2,10} obstruction -/

/-- The pair cycle type of an F'-automorphism is its root cycle type under the
cardinality identification of the twelve roots with the twelve pairs. -/
theorem S2541_pairCycleType_eq (σ : S2132L ≃ₐ[S1720Field] S2132L) :
    (S2132DivisionRootPairEquiv.permCongr (S2132DivisionRootEquiv σ)).cycleType =
      (S2132DivisionRootEquiv σ).cycleType := by
  classical
  exact S2132cycleType_permCongr S2132DivisionRootPairEquiv (S2132DivisionRootEquiv σ)

/-- **The S2470 witness has pair cycle type {12}.** -/
theorem S2541_pairTwelveCycle (D : S2541ActualResidueData613) :
    ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
      (S2132DivisionRootPairEquiv.permCongr (S2132DivisionRootEquiv σ)).cycleType =
        ({12} : Multiset Nat) := by
  obtain ⟨σ, hσ⟩ := S2541_rootTwelveCycle D
  refine ⟨σ, ?_⟩
  rw [S2541_pairCycleType_eq σ,
    ← S2541_rootCycleType_eq_divisionRoot D.1.f D.1.f_psi5 D.1.f_splits σ]
  exact hσ

/-- **Obstruction.**  A twelve-cycle on the roots induces a twelve-cycle on the
pairs; it can never induce cycle type {2, 10}.  Hence the irreducible-residue
theorem at 613 cannot produce a witness of S2132FrobInducesPairCycleType. -/
theorem S2541_twelveCycle_not_pairTen (σ : S2132L ≃ₐ[S1720Field] S2132L)
    (h12 : (S2132DivisionRootEquiv σ).cycleType = ({12} : Multiset Nat)) :
    ¬ (S2132DivisionRootPairEquiv.permCongr (S2132DivisionRootEquiv σ)).cycleType =
        ({2, 10} : Multiset Nat) := by
  intro h210
  rw [S2541_pairCycleType_eq σ, h12] at h210
  have hne : ({12} : Multiset Nat) ≠ ({2, 10} : Multiset Nat) := by
    intro h
    have hcard := congrArg (fun m : Multiset Nat => m.card) h
    rw [Multiset.card_singleton, Multiset.card_pair] at hcard
    omega
  exact hne h210

/-- Every witness of the S2132 target has root cycle type {2, 10}. -/
theorem S2541_rootCycleType_of_s2132 (h : S2132FrobInducesPairCycleType) :
    ∃ σ : S2132L ≃ₐ[S1720Field] S2132L,
      (S2132DivisionRootEquiv σ).cycleType = ({2, 10} : Multiset Nat) :=
  S2132FrobInduces_iff.mpr h

/-! ## 4. The honest two-factor residue data and the conditional S2132 assembly -/

/-- Actual residue factorization data at an actual residue-degree-one prime of
F': an integral model f of a nonzero F'-multiple of psi_5, a maximal prime p
of O_{F'} of residue degree one above q, a prime P of the actual five-division
field above it, and the two-factor reduction certificate: g2 irreducible of
degree two, g10 irreducible of degree ten, and fbar f p = g2 * g10. -/
structure S2541TwoFactorResidueData where
  q : Nat
  f : (RingOfIntegers S1720Field)[X]
  p : Ideal (RingOfIntegers S1720Field)
  P : Ideal (RingOfIntegers S2057FiveDivisionField)
  p_max : p.IsMaximal
  [P_prime : P.IsPrime]
  [P_lies : P.LiesOver p]
  residueDegreeOne : S2541ResidueDegreeOne q p
  f_monic : f.Monic
  f_sep : (fbar f p).Separable
  f_splits : (f.map (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  f_psi5 : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F
  g2 : ((RingOfIntegers S1720Field) ⧸ p)[X]
  g10 : ((RingOfIntegers S1720Field) ⧸ p)[X]
  g2_monic : g2.Monic
  g2_irreducible : Irreducible g2
  g2_degree : g2.natDegree = 2
  g10_monic : g10.Monic
  g10_irreducible : Irreducible g10
  g10_degree : g10.natDegree = 10
  factor_eq : fbar f p = g2 * g10

/-- The exact two-factor residue certificate carried by the data. -/
def S2541TwoFactorCertificate (D : S2541TwoFactorResidueData) : Prop :=
  D.g2.Monic ∧ Irreducible D.g2 ∧ D.g2.natDegree = 2 ∧
  D.g10.Monic ∧ Irreducible D.g10 ∧ D.g10.natDegree = 10 ∧
  fbar D.f D.p = D.g2 * D.g10

/-- The data are the two-factor residue certificate. -/
theorem S2541TwoFactorCertificate_of_data (D : S2541TwoFactorResidueData) :
    S2541TwoFactorCertificate D :=
  ⟨D.g2_monic, D.g2_irreducible, D.g2_degree, D.g10_monic, D.g10_irreducible,
    D.g10_degree, D.factor_eq⟩

/-- The Dedekind--Frobenius comparison at the actual prime: some
F'-automorphism of the actual five-division field has root cycle type {2, 10}
on the roots of the model.  This is exactly what the Dedekind--Frobenius
theorem supplies from the two-factor reduction certificate
S2541TwoFactorCertificate; it is the exact arithmetic missing input of the
{2,10} route. -/
def S2541DedekindFrobeniusAt (D : S2541TwoFactorResidueData) : Prop :=
  ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
    rootCycleType S1720Field S2057FiveDivisionField D.f D.f_splits σ =
      ({2, 10} : Multiset Nat)

/-- **Conditional assembly.**  Actual two-factor residue data at an actual
residue-degree-one prime, together with the Dedekind--Frobenius comparison at
that prime, produce S2132FrobInducesPairCycleType.  The comparison is the only
arithmetic input beyond the residue certificate S2541TwoFactorCertificate; the
model-to-splitting-field transport is proved in Section 2. -/
theorem S2541FrobInduces_of_dedekindAt (D : S2541TwoFactorResidueData)
    (h : S2541DedekindFrobeniusAt D) : S2132FrobInducesPairCycleType := by
  obtain ⟨σ, hσ⟩ := h
  refine S2132FrobInduces_iff.mp ⟨σ, ?_⟩
  rw [← S2541_rootCycleType_eq_divisionRoot D.f D.f_psi5 D.f_splits σ]
  exact hσ

/-! ## 5. The range cycle-type form and the D5 assembly -/

/-- The S2132 cycle-type input gives the actual range cycle type
S2203RangeCycleTypeRequired S1982Basis (via S2520 and S2480). -/
theorem S2541RangeCycleType_of_frobInduces (h : S2132FrobInducesPairCycleType) :
    S2203RangeCycleTypeRequired S1982Basis :=
  S2480FirstMissing_iff_target.mp (S2520S2480FirstMissing_of_S2132 h)

/-- Exact missing arithmetic inputs of the twelve-cycle / pair-transitivity
half: S2470 residue data and the model-to-range transport. -/
def S2541TwelveCycleExactMissing : Prop :=
  S2470ResidueCertificateRequired ∧ S2470RootToRangeTransport

/-- Exact missing arithmetic input of the S2132 cycle-type half: actual
two-factor residue data at a residue-degree-one prime together with the
Dedekind--Frobenius comparison there. -/
def S2541S2132ExactMissing : Prop :=
  ∃ D : S2541TwoFactorResidueData, S2541DedekindFrobeniusAt D

/-- The twelve-cycle exact missing input gives pair transitivity (S2470). -/
theorem S2541PairTransitive_of_exactMissing (h : S2541TwelveCycleExactMissing) :
    S2203RangePairTransitiveRequired S1982Basis :=
  S2470Target_of_residueData_and_transport (Classical.choice h.1) h.2

/-- The S2132 exact missing input gives S2132FrobInducesPairCycleType. -/
theorem S2541S2132_of_exactMissing (h : S2541S2132ExactMissing) :
    S2132FrobInducesPairCycleType := by
  obtain ⟨D, hD⟩ := h
  exact S2541FrobInduces_of_dedekindAt D hD

/-- The D5 large-image target from the S2132 cycle-type input and the
twelve-cycle/pair-transitivity route. -/
theorem S2541D5LargeImageFive_of_exactMissing
    (hp : S2541TwelveCycleExactMissing) (hc : S2132FrobInducesPairCycleType) :
    S1987D5LargeImageFive :=
  S2470D5LargeImageFive_of_residueData_transport_cycle
    (Classical.choice hp.1) hp.2 (S2541RangeCycleType_of_frobInduces hc)

/-- The D5 large-image target from both exact missing arithmetic inputs. -/
theorem S2541D5LargeImageFive_of_bothExactMissing
    (hp : S2541TwelveCycleExactMissing) (hc : S2541S2132ExactMissing) :
    S1987D5LargeImageFive :=
  S2541D5LargeImageFive_of_exactMissing hp (S2541S2132_of_exactMissing hc)

/-! ## 6. Axiom footprint -/

#print axioms S2541_sourceSplitsAt613
#print axioms S2541_rootTwelveCycle
#print axioms S2541_quadraticIrreducible
#print axioms S2541_tenIrreducible
#print axioms S2541_rootSet_model_eq
#print axioms S2541_rootPerm_apply
#print axioms S2541_permCongr_rootPerm
#print axioms S2541_rootPerm_cycleType_eq_divisionRoot
#print axioms S2541_rootCycleType_eq_divisionRoot
#print axioms S2541_pairCycleType_eq
#print axioms S2541_pairTwelveCycle
#print axioms S2541_twelveCycle_not_pairTen
#print axioms S2541_rootCycleType_of_s2132
#print axioms S2541TwoFactorCertificate_of_data
#print axioms S2541FrobInduces_of_dedekindAt
#print axioms S2541RangeCycleType_of_frobInduces
#print axioms S2541PairTransitive_of_exactMissing
#print axioms S2541S2132_of_exactMissing
#print axioms S2541D5LargeImageFive_of_exactMissing
#print axioms S2541D5LargeImageFive_of_bothExactMissing

end LeanFormal.IUT.XiFPaper.S2541DedekindCycleActual

end

