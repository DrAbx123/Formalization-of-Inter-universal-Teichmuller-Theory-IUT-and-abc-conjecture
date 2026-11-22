/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2487DedekindCertificateActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual

/-!
# S2530: the Dedekind--Frobenius factor-degree / cycle-type theorem for S2132

The paper input S2132FrobInducesPairCycleType is the arithmetic statement that
the Frobenius at a prime above 29 acts on the twelve pairs `{+-P}` of nonzero
5-torsion points with cycle type `(10, 2)`, because the odd 5-division
polynomial reduces modulo 29 as an irreducible quadratic times an irreducible
degree-ten factor.  The mathematical engine behind this is the classical
Dedekind--Frobenius theorem:

> if `f` is a monic integral polynomial, separable modulo a prime `p`, and it
> splits in a finite Galois extension `L/K`, then the permutation of the roots
> of `f` induced by an arithmetic Frobenius at a prime `P` above `p` has cycle
> type equal to the multiset of degrees of the irreducible factors of `f mod p`
> (with the linear factors removed, since Mathlib's cycle type omits fixed
> points).

## Status of this file (NOT compiled, per instruction)

This file is a consolidation and an audit.  It does **not** claim a compiled
proof of the general theorem.  It does the following.

1. It records the exact missing statement of the general theorem as
   `S2530DedekindFrobeniusCycleTypeRequired` (definitionally the corrected
   Dedekind--Frobenius cycle-type theorem of S2217), together with the
   orbit-size form `S2530DedekindFrobeniusOrbitSizeRequired`.

2. It proves the *irreducible-residue* special case from the already compiled
   S2470 theorem `S2470_residueIrreducible_rootTwelveCycle`: if the reduction
   is irreducible of degree twelve and has twelve roots in the residue field,
   then the corrected factor-degree conclusion holds (the factor-degree
   multiset is `{12}` and the filter does nothing).

3. It proves the non-arithmetic transport missing from the S2132 assembly:
   if an integral model `f` is a nonzero `K`-multiple of the actual
   `S2057Psi5F`, then the cycle type of a Galois automorphism on the roots of
   the model equals the cycle type of the same automorphism on the roots of
   `S2057Psi5F` (`S2530cycleType_divisionRootEquiv_eq_rootCycleType`).

4. It gives the conditional assembly: the exact missing general theorem plus a
   concrete residue datum `S2530ResidueData` (an integral monic model of a
   nonzero multiple of `psi_5`, a prime of `F'`, a prime of the splitting
   field above it, and factor degrees `{2, 10}`) implies
   `S2132FrobInducesPairCycleType`.

5. It audits S2487/S2167: the literal (uncorrected) theorem
   `DedekindFrobeniusCycleTypeTheorem` is *false* by
   `s2167_literal_statement_false` (counterexample `f = X`).  Hence
   `S2487DedekindMissing` is refuted and `S2487FirstMissing_of_dedekind` is
   vacuous.  The honest missing statement is the corrected one.

## Important cross-reference (not imported here because it has no olean)

A full candidate proof of exactly the missing theorem exists on disk in
`tmp/sheaf/xif/paper/S2445D5FinalActual.lean`, as
`s2445_dedekindFrobeniusCycleTypeTheoremCorrected : DedekindFrobeniusCycleTypeTheoremCorrected`
and `s2445_S2217Missing : S2217Missing`.  All of its imports are compiled
(S2425, S2408, S2428, S2440, S2339, S2217), but S2445 itself was never
compiled and has no log; it should therefore be compiled and repaired before
being treated as evidence.  `S2491CycleComputationActual` has a parallel
attempt but imports `S2427RootPermCycleActual`, which
`coord/reports/S2445-d5-status.md` records as containing `sorryAx`; it must not
be used.

## What is NOT done here

No `sorry`, `admit`, `axiom`, `True`, `PUnit` or `native_decide` is used and no
conditional object is announced as actual.  The general theorem is a plain
`Prop` (`S2530DedekindFrobeniusCycleTypeRequired`) with no inhabitant in this
file.  The concrete arithmetic residue datum `S2530ActualResidueRequired` is
also a plain `Prop` with no inhabitant.  The declaration
`S2530FrobInducesPairCycleType_of_residueData` is explicitly conditional on
both.

## Exact missing (summary)

* General theorem: `S2530DedekindFrobeniusCycleTypeRequired`, equivalently
  `S2217Missing`; the candidate proof is S2445D5FinalActual.
* Concrete arithmetic input: `S2530ActualResidueRequired`, i.e. a
  `S2530ResidueData`.  This is the honest residue certificate at a prime of
  `F'` (the `ZMod 29` computation in S2132/S2487 is not by itself an
  `F'`-level factorization, and the integral model of `psi_5` is not monic as
  an integer polynomial).
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

open Polynomial NumberField

attribute [local instance] Ideal.Quotient.field

namespace LeanFormal.IUT.XiFPaper.S2530DedekindCycleActual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2487DedekindCertificateActual

/-! ## 1. The exact statements of the missing general theorem -/

/-- The exact missing general theorem of this file: the corrected
Dedekind--Frobenius cycle-type theorem of S2217.  For a finite Galois
extension of number fields `L/K`, a monic integral polynomial `f` that is
separable modulo a maximal prime `p` and splits in `L`, and a prime `P` of
`O_L` above `p`, there is an arithmetic Frobenius at `P` whose root permutation
has cycle type equal to the multiset of irreducible factor degrees of
`f mod p`, with the linear factors removed.

This is the statement whose candidate proof is
`s2445_dedekindFrobeniusCycleTypeTheoremCorrected` in S2445D5FinalActual. -/
def S2530DedekindFrobeniusCycleTypeRequired : Prop :=
  LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.DedekindFrobeniusCycleTypeTheoremCorrected

/-- The same statement is definitionally the S2217 corrected theorem. -/
theorem S2530DedekindFrobeniusCycleTypeRequired_iff :
    S2530DedekindFrobeniusCycleTypeRequired ↔
      LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.DedekindFrobeniusCycleTypeTheoremCorrected :=
  Iff.rfl

/-- The orbit-size form of the missing theorem: the cycle type together with
the fixed points equals the full factor-degree multiset.  This is the form
called `S2217Missing` in S2217 (and proved in the candidate S2445). -/
def S2530DedekindFrobeniusOrbitSizeRequired : Prop :=
  LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.S2217Missing

/-- The orbit-size form is definitionally `S2217Missing`. -/
theorem S2530DedekindFrobeniusOrbitSizeRequired_iff :
    S2530DedekindFrobeniusOrbitSizeRequired ↔
      LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.S2217Missing :=
  Iff.rfl

/-! ## 2. The S2487/S2167 literal statement is false

S2487 defines `S2487DedekindMissing` as the *literal* S2167 theorem
`DedekindFrobeniusCycleTypeTheorem`, which compares Mathlib's cycle type
(omitting fixed points) with the full factor-degree multiset (including linear
factors).  S2217 kernel-refutes that literal statement.  Consequently
`S2487FirstMissing_of_dedekind` is vacuous, and the corrected statement above
is the honest one. -/

/-- The literal S2167 statement is false (S2217, counterexample `f = X`). -/
theorem S2530LiteralStatement_false :
    ¬ LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual.DedekindFrobeniusCycleTypeTheorem :=
  s2167_literal_statement_false

/-- The S2487 missing statement is refuted: it is exactly the literal S2167
statement. -/
theorem S2530S2487Missing_false : ¬ S2487DedekindMissing := by
  unfold S2487DedekindMissing
  exact s2167_literal_statement_false

/-- The S2167 first missing is refuted, because its first component is the
literal S2167 statement. -/
theorem S2530S2167FirstMissing_false : ¬ S2167FirstMissing := by
  intro h
  unfold S2167FirstMissing at h
  exact s2167_literal_statement_false h.1

/-! ## 3. General factor-degree lemmas -/

/-- The factor-degree multiset of a monic irreducible polynomial is the
singleton of its degree.  This is the `factorDegrees_X` argument of S2217 in
general form. -/
theorem S2530factorDegrees_irreducible {k : Type*} [Field k] {g : k[X]}
    (hg : g.Monic) (hirr : Irreducible g) :
    factorDegrees g = ({g.natDegree} : Multiset ℕ) := by
  classical
  unfold factorDegrees
  rw [UniqueFactorizationMonoid.normalizedFactors_irreducible hirr,
    Monic.normalize_eq_self hg]
  simp

/-- For a monic irreducible polynomial of degree twelve, the corrected
factor-degree multiset is `{12}`. -/
theorem S2530factorDegrees_filter_irreducible {k : Type*} [Field k] {g : k[X]}
    (hg : g.Monic) (hirr : Irreducible g) (hdeg : g.natDegree = 12) :
    (factorDegrees g).filter (fun n => n ≠ 1) = ({12} : Multiset ℕ) := by
  rw [S2530factorDegrees_irreducible hg hirr, hdeg, Multiset.filter_singleton]
  simp

/-! ## 4. The irreducible-residue case, from the actual S2470 theorem

S2470 proves, unconditionally and kernel checked, that in the irreducible
residue case an arithmetic Frobenius has a twelve-cycle on the roots.  We
recover from it the corrected factor-degree conclusion, which is the
specialisation of the general theorem to a single irreducible factor of degree
twelve.  This is the part of the general theorem that is already actual in the
tree. -/

section IrreducibleCase

variable {K L : Type*} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

local instance : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

local instance : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass

/-- **Irreducible-residue case of the general theorem.**  If the reduction of
the monic integral polynomial `f` at `P` is irreducible of degree twelve and
has twelve roots in the residue field, then some arithmetic Frobenius at `P`
has root cycle type equal to the corrected factor-degree multiset.  Proved
from `S2470_residueIrreducible_rootTwelveCycle` plus the factor-degree
computation; no general Dedekind--Frobenius comparison is used. -/
theorem S2530ResidueIrreducible_cycleTypeCorrected
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (hirr : Irreducible (fbar f p))
    (hdeg : (fbar f p).natDegree = 12)
    (hcard : Fintype.card ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) = 12) :
    ∃ σ : Gal(L/K), IsArithFrobAt (RingOfIntegers K) σ P ∧
      rootCycleType K L f hsplit σ =
        (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) := by
  obtain ⟨σ, hσ, hcyc⟩ :=
    S2470_residueIrreducible_rootTwelveCycle f p P hmonic hsep hsplit hirr hcard
  refine ⟨σ, hσ, ?_⟩
  rw [hcyc]
  rw [S2530factorDegrees_filter_irreducible
    (s2397Fbar_monic f p P hmonic) hirr hdeg]
  simp

end IrreducibleCase

/-! ## 5. Scaling transport of root sets and root cycle types

The Dedekind--Frobenius theorem is stated for a monic integral polynomial `f`.
The S2132 target is stated for the actual rational polynomial `S2057Psi5F`.  An
integral model satisfies `f.map (algebraMap O_K K) = C c * S2057Psi5F` for some
`c ≠ 0`; scaling by a nonzero constant does not change the root set, and the
Galois action is the same.  This section proves that transport, so that the
factor-degree conclusion for the model can be read on the actual roots. -/

/-- Scaling a polynomial by a nonzero constant does not change its root set. -/
theorem S2530rootSet_eq_of_eq_smul
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    {p q : K[X]} {c : K} (hc : c ≠ 0) (hq : q = C c * p) :
    q.rootSet A = p.rootSet A := by
  classical
  have hcA : algebraMap K A c ≠ 0 := by
    intro h
    have h1 : (1 : A) = 0 := by
      calc
        (1 : A) = algebraMap K A (c * c⁻¹) := by
          rw [mul_inv_cancel₀ hc, map_one]
        _ = algebraMap K A c * algebraMap K A c⁻¹ := by rw [map_mul]
        _ = 0 := by rw [h, zero_mul]
    exact one_ne_zero h1
  ext x
  rw [Polynomial.mem_rootSet', Polynomial.mem_rootSet']
  constructor
  · rintro ⟨hqne, hx⟩
    refine ⟨?_, ?_⟩
    · intro hp0
      apply hqne
      rw [hq, Polynomial.map_mul, Polynomial.map_C, hp0]
      simp
    · rw [hq, Polynomial.aeval_mul, Polynomial.aeval_C] at hx
      exact (mul_eq_zero.mp hx).resolve_left hcA
  · rintro ⟨hpne, hx⟩
    refine ⟨?_, ?_⟩
    · rw [hq, Polynomial.map_mul, Polynomial.map_C]
      exact mul_ne_zero (Polynomial.C_ne_zero.mpr hcA) hpne
    · rw [hq, Polynomial.aeval_mul, Polynomial.aeval_C, hx]
      simp

/-- The equivalence of root sets induced by scaling by a nonzero constant. -/
noncomputable def S2530rootSetEquiv
    {K A : Type*} [Field K] [CommRing A] [IsDomain A] [Algebra K A]
    {p q : K[X]} {c : K} (hc : c ≠ 0) (hq : q = C c * p) :
    q.rootSet A ≃ p.rootSet A :=
  Equiv.subtypeEquivRight
    (fun x => (Set.ext_iff.mp (S2530rootSet_eq_of_eq_smul (K := K) (A := A) hc hq)) x)

/-- The underlying value of the Galois root permutation `rootPerm` is the
Galois action. -/
theorem S2530rootPerm_apply_val
    {K L : Type*} [Field K] [Field L] [Algebra K L]
    (f : (RingOfIntegers K)[X])
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (σ : Gal(L/K))
    (x : (f.map (algebraMap (RingOfIntegers K) K)).rootSet L) :
    (rootPerm K L f hsplit σ x).1 = σ x.1 := by
  simp only [rootPerm, MulAction.toPermHom_apply, MulAction.toPerm_apply,
    Polynomial.rootSet.coe_smul, AlgEquiv.smul_def]

/-- **The model-to-psi_5 transport at the level of permutations.**  For the
actual splitting field `L = S2057FiveDivisionField` over `K = S1720Field`, an
integral model `f` of a nonzero `K`-multiple of `S2057Psi5F` gives a
conjugacy between the model root permutation of a Galois automorphism and the
S2132 root permutation `S2132DivisionRootEquiv`. -/
theorem S2530permCongr_rootPerm_eq_divisionRootEquiv
    (f : (RingOfIntegers S1720Field)[X])
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F) :
    (S2530rootSetEquiv (K := S1720Field) (A := S2057FiveDivisionField) hc hq).permCongr
        (rootPerm S1720Field S2057FiveDivisionField f hsplit σ) =
      S2132DivisionRootEquiv σ := by
  ext x
  apply Subtype.ext
  rw [Equiv.permCongr_apply]
  change
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ
      ((S2530rootSetEquiv (K := S1720Field) (A := S2057FiveDivisionField) hc hq).symm x)).1
      = (S2132DivisionRootEquiv σ x).1
  rw [S2530rootPerm_apply_val]
  rfl

/-- **The model-to-psi_5 transport at the level of cycle types.**  The cycle
type of `S2132DivisionRootEquiv σ` on the twelve psi_5 roots is the root cycle
type of `σ` on the roots of the integral model `f`. -/
theorem S2530cycleType_divisionRootEquiv_eq_rootCycleType
    (f : (RingOfIntegers S1720Field)[X])
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field))
    {c : S1720Field} (hc : c ≠ 0)
    (hq : f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F) :
    Equiv.Perm.cycleType (S2132DivisionRootEquiv σ) =
      rootCycleType S1720Field S2057FiveDivisionField f hsplit σ := by
  rw [← S2530permCongr_rootPerm_eq_divisionRootEquiv f hsplit σ hc hq]
  rw [S2132cycleType_permCongr]
  rfl

/-! ## 6. The concrete residue datum for the (10, 2) cycle type -/

/-- Concrete arithmetic residue datum for the S2132 target: an integral monic
model `f` of a nonzero `F'`-multiple of the actual `S2057Psi5F`, a maximal
prime `p` of `O_F'`, a prime `P` of the actual 5-division field above `p`, and
the corrected factor-degree multiset `{2, 10}` at `p`.  This is the honest
arithmetic input still missing; the `ZMod 29` certificate of S2132/S2487 is
not by itself such a datum (the residue degree at `29` in `F'` is not one, and
the integer model of `psi_5` is not monic). -/
structure S2530ResidueData where
  f : (RingOfIntegers S1720Field)[X]
  p : Ideal (RingOfIntegers S1720Field)
  P : Ideal (RingOfIntegers S2057FiveDivisionField)
  [p_max : p.IsMaximal]
  [P_prime : P.IsPrime]
  [P_lies : P.LiesOver p]
  f_monic : f.Monic
  f_sep : (fbar f p).Separable
  f_splits : (f.map
    (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  f_psi5 : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F
  fbar_degrees : (factorDegrees (fbar f p)).filter (fun n => n ≠ 1) =
    ({2, 10} : Multiset ℕ)

section ConcreteAssembly

local instance : MulSemiringAction
    Gal(S2057FiveDivisionField/S1720Field) (RingOfIntegers S2057FiveDivisionField) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers S1720Field)
    S1720Field S2057FiveDivisionField (RingOfIntegers S2057FiveDivisionField)

local instance : SMulCommClass
    Gal(S2057FiveDivisionField/S1720Field)
    (RingOfIntegers S1720Field) (RingOfIntegers S2057FiveDivisionField) :=
  LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass

/-- **Conditional Dedekind--Frobenius output at the concrete residue datum.**
If the exact missing general theorem holds, then an arithmetic Frobenius at the
chosen prime of the splitting field has root cycle type `{2, 10}` on the model
`f`. -/
theorem S2530ResidueData.exists_frobenius_rootCycleType
    (D : S2530ResidueData)
    (h : S2530DedekindFrobeniusCycleTypeRequired) :
    ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
      IsArithFrobAt (RingOfIntegers S1720Field) σ D.P ∧
      rootCycleType S1720Field S2057FiveDivisionField D.f D.f_splits σ =
        ({2, 10} : Multiset ℕ) := by
  letI : D.p.IsMaximal := D.p_max
  haveI : D.P.IsPrime := D.P_prime
  haveI : D.P.LiesOver D.p := D.P_lies
  obtain ⟨σ, H, hcyc⟩ :=
    h (K := S1720Field) (L := S2057FiveDivisionField)
      D.f D.p D.P D.f_monic D.f_sep D.f_splits
  exact ⟨σ, H, hcyc.trans D.fbar_degrees⟩

/-- **Conditional assembly of the S2132 root-cycle target.**  The exact
missing general theorem plus the concrete residue datum gives an
`F'`-automorphism of the actual splitting field whose action on the twelve
psi_5 roots has cycle type `(10, 2)`. -/
theorem S2530ResidueData.frobInducesRootCycleType
    (D : S2530ResidueData)
    (h : S2530DedekindFrobeniusCycleTypeRequired) :
    S2132FrobInducesRootCycleType := by
  obtain ⟨σ, H, hcyc⟩ := D.exists_frobenius_rootCycleType h
  obtain ⟨c, hc, hq⟩ := D.f_psi5
  refine ⟨σ, ?_⟩
  rw [S2530cycleType_divisionRootEquiv_eq_rootCycleType
    (f := D.f) (hsplit := D.f_splits) (σ := σ) (c := c) hc hq]
  exact hcyc

/-- **Conditional assembly of the S2132 pair-cycle target.**  The general
Dedekind--Frobenius theorem plus the concrete residue datum implies the actual
`S2132FrobInducesPairCycleType`. -/
theorem S2530ResidueData.frobInduces
    (D : S2530ResidueData)
    (h : S2530DedekindFrobeniusCycleTypeRequired) :
    S2132FrobInducesPairCycleType :=
  S2132FrobInduces_iff.mp (D.frobInducesRootCycleType h)

end ConcreteAssembly

/-! ## 7. Exact missing statements -/

/-- The exact missing arithmetic residue datum: the existence of a
`S2530ResidueData`. -/
def S2530ActualResidueRequired : Prop := Nonempty S2530ResidueData

/-- **Conditional main assembly.**  The general Dedekind--Frobenius theorem and
the concrete residue datum imply the S2132 target.  Neither hypothesis is
proved in this file. -/
theorem S2530FrobInducesPairCycleType_of_residueData
    (h : S2530DedekindFrobeniusCycleTypeRequired)
    (hD : S2530ActualResidueRequired) :
    S2132FrobInducesPairCycleType :=
  S2530ResidueData.frobInduces hD.some h

/-- The exact missing statement of this file: the corrected general
Dedekind--Frobenius theorem (together with the concrete residue datum, which is
stated separately as `S2530ActualResidueRequired`). -/
def S2530ExactMissing : Prop := S2530DedekindFrobeniusCycleTypeRequired

/-- The exact missing statement is the corrected S2217 theorem. -/
theorem S2530ExactMissing_iff :
    S2530ExactMissing ↔
      LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual.DedekindFrobeniusCycleTypeTheoremCorrected :=
  Iff.rfl

/-- The exact missing arithmetic input of the concrete assembly. -/
def S2530ExactArithmeticMissing : Prop := S2530ActualResidueRequired

/-! ## 8. Axiom footprint -/

#print axioms S2530DedekindFrobeniusCycleTypeRequired_iff
#print axioms S2530DedekindFrobeniusOrbitSizeRequired_iff
#print axioms S2530LiteralStatement_false
#print axioms S2530S2487Missing_false
#print axioms S2530S2167FirstMissing_false
#print axioms S2530factorDegrees_irreducible
#print axioms S2530factorDegrees_filter_irreducible
#print axioms S2530ResidueIrreducible_cycleTypeCorrected
#print axioms S2530rootSet_eq_of_eq_smul
#print axioms S2530rootSetEquiv
#print axioms S2530rootPerm_apply_val
#print axioms S2530permCongr_rootPerm_eq_divisionRootEquiv
#print axioms S2530cycleType_divisionRootEquiv_eq_rootCycleType
#print axioms S2530ResidueData.exists_frobenius_rootCycleType
#print axioms S2530ResidueData.frobInducesRootCycleType
#print axioms S2530ResidueData.frobInduces
#print axioms S2530FrobInducesPairCycleType_of_residueData

end LeanFormal.IUT.XiFPaper.S2530DedekindCycleActual

end
