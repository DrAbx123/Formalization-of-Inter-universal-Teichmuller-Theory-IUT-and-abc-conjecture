/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2203D5RangeActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S1942PrePsiFiveActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual

/-!
# S2471: the actual range cycle-type target and the exact Dedekind-Frobenius gap

## The target

  S2471Target := S2203RangeCycleTypeRequired S1982Basis
    = HasCycleType102
        (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

with E' = S1720Curve over the actual number field F' = S1720Field, the actual
rank-two basis S1982Basis of E'[5], and HasCycleType102 the existence of a
matrix in the range whose action on the twelve pairs {+-v} has cycle type
(10, 2) (S2009).

## Audit of the candidate bridge files (2026-11-03)

* S2445D5FinalActual.lean (the claimed unconditional Dedekind-Frobenius
  orbit-size proof) does NOT compile: EXIT=1 with errors at lines 72, 82, 129,
  132/153, 171, 227, 266, 289, 291, 348, 361.  Its #print axioms output contains
  sorryAx.  It cannot be consumed.
* S2461CycleTypeFinalActual.lean does NOT compile either: EXIT=1 with errors
  (Finset.insert unknown, missing HSMul GL2 V2 instances,
  S1894MatrixRep_acts argument order, change failures).  The stale olean is
  stale indeed.
* The mod-29 datum of S2056/S2132 has a false integer-model field
  (S2132NoIntegerModel).  What is true and proved is S2132CorrectedProduct:
  4*(x^2+6x+12)*f is the reduction of the integer model S2132Psi5Z = 2^36 psi_5,
  and f is irreducible over ZMod 29 (S2126).  Since 2^36 = 24 mod 29 and
  4/24 = 5, the actual psi_5 modulo 29 is 5*(x^2+6x+12)*f, so the actual factor
  degrees at 29 are {2,10}.  BUT the Dedekind-Frobenius factorization at a prime
  of F' above 29 is over the residue field of F'; 29 is inert in Q(sqrt(-3))
  (contained in F' by the S1687/S1993 analysis), so that residue field has even
  degree and the factor degrees there are not {2,10}.

## What is proved here

1. The target is definitionally the range statement, and it is equivalent to
   the existence of an absolute Galois element whose mod-5 matrix has pair
   cycle type (10, 2).
2. The corrected mod-29 product of S2132 is restated for the actual integral
   model S2132Psi5Z = 2^36 psi_5, and the degree-ten factor is irreducible
   over ZMod 29 (S2126).

## Exact first missing

The target is not proved.  The remaining inputs are

* S2471Psi5Z_mapRequired: the finite identity S2132Psi5Z.map Q
  = C (2^36) * S2057Psi5Q (the base change of the integral model is
  2^36 times the actual 5-division polynomial; no integral model of psi_5
  itself exists, S2132NoIntegerModel);
* DedekindFrobeniusCycleTypeTheoremCorrected (S2217, stated but not proved);
* S2471ResidueFactorizationRequired: a prime q of F' and a factorization of
  the reduction of psi_5 over the residue field of q with factor degrees (2,10).
  External computation: q = 1249 is prime, q = 1 mod 4, S1687H has six
  distinct roots mod q, and psi_5 factors as an irreducible quadratic times an
  irreducible degree-ten factor mod q.  Passing from these checks to a prime
  of F' with residue field F_1249 additionally needs the S1993/S2005 bridge
  identifying the splitting field of S1687H with the S1687 field and its
  compositum with Q(i) with F'; that bridge (S1993SplittingFieldH_eq) is not
  closed.  No Lean certificate is produced here.
* the S2461-style transport from the Dedekind-Frobenius root permutation to
  the matrix range element, which is not available in compiled form.

No sorry, admit, axiom, True/PUnit gate or native_decide is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2471CycleTypeFinalActual

open Polynomial
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S1942PrePsiFiveActual
open LeanFormal.IUT.XiFPaper.S1667AdmissibleCurveActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual

/-! ## 1. The exact target -/

/-- The actual range cycle-type target at the selected rank-two basis. -/
def S2471Target : Prop := S2203RangeCycleTypeRequired S1982Basis

/-- The target unfolded. -/
theorem S2471Target_iff_range :
    S2471Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The target is the existence of an absolute Galois element whose mod-5 matrix
has pair cycle type (10, 2). -/
theorem S2471Target_iff_exists_sigma :
    S2471Target ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) := by
  rw [S2471Target_iff_range]
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩, hc⟩

/-! ## 2. The actual integral model of psi_5 -/

/-- The actual integral model of the odd 5-division polynomial: the S2132
integer polynomial, equal to 2^36 * psi_5 when base changed to Q. -/
def S2471Psi5Z : ℤ[X] := S2132Psi5Z

/-- The exact model identity (the first finite missing input): the base change
of S2471Psi5Z to Q is 2^36 times the actual 5-division polynomial
S2057Psi5Q = S1667Curve.prePsi 5.  No integral model of psi_5 itself exists
(S2132NoIntegerModel). -/
def S2471Psi5Z_mapRequired : Prop :=
  S2471Psi5Z.map (Int.castRingHom ℚ) = C (2 ^ 36 : ℚ) * S2057Psi5Q

/-! ## 3. The actual mod-29 factorization (restated from S2132/S2126) -/

/-- The corrected mod-29 product of S2132: the reduction of the actual integral
model is 4*(x^2+6x+12)*f, with f the irreducible degree-ten polynomial of
S2126. -/
theorem S2471Mod29_correctedProduct :
    S2132F2Z.map (Int.castRingHom (ZMod 29)) *
        S2132F10Z.map (Int.castRingHom (ZMod 29)) =
      S2471Psi5Z.map (Int.castRingHom (ZMod 29)) := by
  exact S2132CorrectedProduct

/-- The degree-ten factor is irreducible over ZMod 29 (S2126). -/
theorem S2471Mod29_ten_irreducible : Irreducible S2132Factor10 :=
  S2132Factor10_irreducible

/-! ## 4. Exact first missing -/

/-- The finite-field factorization part of the first missing: at some prime q
that splits completely in F', the reduction of the actual psi_5 has an
irreducible quadratic and an irreducible degree-ten factor.  (q = 1249 is an
external witness; no Lean certificate is produced here.) -/
def S2471ResidueFactorizationRequired : Prop :=
  ∃ q : ℕ, Nat.Prime q ∧ q % 4 = 1 ∧
    ∃ g2 g10 : (ZMod q)[X],
      Irreducible g2 ∧ Irreducible g10 ∧
      g2.natDegree = 2 ∧ g10.natDegree = 10 ∧
      g2 * g10 = S2471Psi5Z.map (Int.castRingHom (ZMod q))

/-- The arithmetic part: the corrected Dedekind-Frobenius cycle-type theorem. -/
def S2471DedekindFrobeniusRequired : Prop :=
  DedekindFrobeniusCycleTypeTheoremCorrected

/-- The exact first missing for the target: the model identity, the
Dedekind-Frobenius bridge and the finite residue-field factorization
certificate. -/
def S2471FirstMissing : Prop :=
  S2471Psi5Z_mapRequired ∧ S2471DedekindFrobeniusRequired ∧
    S2471ResidueFactorizationRequired

/-- The first missing projects to the model identity. -/
theorem S2471ModelIdentity_of_firstMissing (h : S2471FirstMissing) :
    S2471Psi5Z_mapRequired := h.1

/-- The first missing projects to the arithmetic theorem. -/
theorem S2471DedekindFrobenius_of_firstMissing (h : S2471FirstMissing) :
    S2471DedekindFrobeniusRequired := h.2.1

/-- The first missing projects to the residue-field factorization. -/
theorem S2471ResidueFactorization_of_firstMissing (h : S2471FirstMissing) :
    S2471ResidueFactorizationRequired := h.2.2

#print axioms S2471Target_iff_range
#print axioms S2471Target_iff_exists_sigma
#print axioms S2471Mod29_correctedProduct
#print axioms S2471Mod29_ten_irreducible
#print axioms S2471ModelIdentity_of_firstMissing
#print axioms S2471DedekindFrobenius_of_firstMissing
#print axioms S2471ResidueFactorization_of_firstMissing

end LeanFormal.IUT.XiFPaper.S2471CycleTypeFinalActual

end
