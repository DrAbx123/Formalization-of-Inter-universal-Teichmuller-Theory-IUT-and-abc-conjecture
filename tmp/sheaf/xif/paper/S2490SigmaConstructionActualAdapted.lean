/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2132FrobCycleActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2217DedekindFrobTheoremActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
import tmp.sheaf.xif.paper.S2442QE5DegreeOrderSubagentActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual

/-!
# S2490: the actual sigma-construction attempt for pair cycle type (10, 2)

## Target

  S2490Target := S2480FirstMissing
    = exists sigma : S1725AbsoluteGalois,
        (pairPermHom
          (galoisLTorsionMatrixRepresentation S1987Five S1982Basis sigma)).cycleType
        = {10, 2}.

## Status: BLOCKED; no inhabitant of S2480FirstMissing is produced

This file reduces the target to the exact missing arithmetic and formal inputs,
and proves the parts that are currently available.  It is intentionally a
*conditional* construction: it does not postulate, axiomatise or fake any of the
missing lemmas, and it does not announce a conditional object as actual.

Proved here (from the actual, already compiled modules S2480, S2056, S2132,
S2167, S2217, S2440, S2442, S2057):

* S2490Target is the target of S2480 and is basis-independent (S1894);
* the permutation of the twelve actual roots of psi_5 and the permutation of the
  twelve actual pairs {+-P} induced by the same sigma have the same cycle type
  (S2056RootPairEquiv_equivariant);
* the corrected Dedekind--Frobenius cycle-type theorem (S2217) applied to an
  actual monic integral model f of a nonzero multiple of psi_5 at a prime P
  with factor degrees {2, 10} gives an arithmetic Frobenius on the actual
  5-division field whose root cycle type is exactly (10, 2).

Not proved here (exact missing chain, in order):

1. **Dedekind--Frobenius cycle comparison.**
   DedekindFrobeniusCycleTypeTheoremCorrected (S2217).  S2445D5FinalActual
   contains a kernel-level proof script of this theorem, but no .olean exists
   for it in the current build; S2217 itself only states the theorem.

2. **The actual arithmetic datum.**
   S2490DedekindData: a monic integral model f of a nonzero multiple of
   S2057Psi5F, a maximal prime p of O_{F'}, a prime P of the actual
   5-division field above p, separability of fbar f p, and
   factorDegrees (fbar f p) = {2, 10}.
   The concrete finite candidate is p = 1249.  External computation (not Lean):
   * S1687H splits completely mod 1249, and 1249 = 1 mod 4, so X^2 + 1 splits;
   * the resultant of S1687H and X^2 + 1 is 876 mod 1249, so 1249 is unramified
     in F' (the product defining F' has no repeated root mod 1249); hence 1249
     splits completely in F';
   * S2132Psi5Z mod 1249 factors as
       415 * (X^2 - 332X - 89) *
         (X^10 + 570X^9 - 432X^8 - 410X^7 - 72X^6 + 242X^5
            + 369X^4 - 85X^3 - 37X^2 + 166X + 580),
     with both factors irreducible of degrees 2 and 10.
   The model S2132Psi5Z is not monic: its leading coefficient is 2^36 * 5.
   Passing to the monic model f scales the roots by a constant c; since
   1249 does not divide 2 * 5, c is a unit at the prime above 1249, so the
   reduction has the same factor degrees 2 + 10.
   The product identity is S2490Mod1249ProductRequired; the irreducibility of
   the degree-ten factor is S2490Mod1249TenIrreducible.  Neither is proved in
   Lean in the tree.
   (Warning: q = 61 is NOT suitable: S1687H and X^2 + 1 share the roots
   +-11 mod 61, so 61 is ramified in F'.  q = 97 is completely split and
   unramified but the actual S2132Psi5Z reduction there is 4+4+4, not 2+10.)

3. **The splitting-field to absolute-closure transport.**
   S2490SplittingToRootCycle.  The Dedekind theorem produces sigma on the
   splitting field L = S2057FiveDivisionField.  The target requires sigma in
   S1725AbsoluteGalois and the cycle type on S2056Root (roots in the algebraic
   closure).  The missing formal steps are:
   * choose e : L ->_alg[F'] AlgebraicClosure F' (IsAlgClosed.lift);
   * extend e.comp sigma from e.fieldRange to an endomorphism of the
     algebraic closure using
     IsAlgClosed.surjective_restrictDomain_of_isAlgebraic;
   * turn this endomorphism into an equivalence using
     Algebra.IsAlgebraic.algHom_bijective and AlgEquiv.ofBijective;
   * identify the root sets of psi_5 in L and in the algebraic closure along e,
     and use Equiv.Perm.cycleType_permCongr.
   None of this pipeline is assembled in the tree.

4. **The pair/root to matrix-pair bridge.**
   S2490PairMatrixCycleType: for every sigma,
     (pairPermHom (matrix sigma)).cycleType = (S2490PairPerm sigma).cycleType.
   Mathematically this is the S2132/S2172/S2180/S2186/S1894 composition already
   written in the (unverified/stale) S2461 and in the scratch S2480v1
   (S2480PairMatrix_cycleType).  It is not available in the compiled S2480,
   which only states the existential sigma form.

5. **The projective alternative.**
   If one does not use a prime that splits completely in F', the Q-to-F'
   transport needs the linear-disjointness/projective bridge of S2442:
   S2442Psi5ProjectiveBridge and S2442CorrectedDomainComparison.  Both are
   unproved.  S2442 also refutes the old degree-480 target; the degree of the
   psi5 splitting field is 240 under the projective bridge, not 480.

No sorry, admit, axiom, True/PUnit gate, native_decide, or renamed hypothesis is
used.  All unconditional theorems below depend only on the standard axioms.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2490SigmaConstructionActualAdapted

open Polynomial
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2442QE5DegreeOrderSubagentActual
open LeanFormal.IUT.XiFPaper.S2289QE5DegreeActual

attribute [local instance] Ideal.Quotient.field

/-! ## 1. The target -/

/-- The actual target: inhabit S2480FirstMissing. -/
abbrev S2490Target : Prop := S2480FirstMissing

/-- The target unfolded: an actual absolute Galois element whose mod-5 matrix
acts on the twelve pairs with cycle type (10, 2). -/
theorem S2490Target_iff_sigma :
    S2490Target ↔ ∃ σ : S1725AbsoluteGalois,
      (pairPermHom
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
          ({10, 2} : Multiset ℕ) :=
  Iff.rfl

/-- The target at an arbitrary rank-two basis, by the S1894 change-of-basis
conjugacy already used in S2480.  This is the only place where a basis choice
can be moved; it does not produce the element. -/
theorem S2490Target_at_any_basis (b : S1725TorsionBasis S1987Five) :
    S2490Target ↔ HasCycleType102
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five b).range :=
  S2480FirstMissing_iff_target.trans (S2480Target_iff_basis b)

/-! ## 2. The root and pair permutations of an absolute Galois element -/

/-- The permutation of the twelve actual roots of psi_5 induced by sigma. -/
noncomputable def S2490RootPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Root :=
  Equiv.ofBijective (S2056RootMap σ)
    (Finite.injective_iff_bijective.mp (by
      intro x y h
      apply Subtype.ext
      exact σ.injective (congrArg Subtype.val h)))

@[simp] theorem S2490RootPerm_apply (σ : S1725AbsoluteGalois) (x : S2056Root) :
    S2490RootPerm σ x = S2056RootMap σ x := rfl

/-- The permutation of the twelve actual pairs {+-P} induced by sigma. -/
noncomputable def S2490PairPerm (σ : S1725AbsoluteGalois) : Equiv.Perm S2056Pair :=
  Equiv.ofBijective (S2056PairMap σ)
    (Finite.injective_iff_bijective.mp (by
      intro S T hST
      have hf : Function.Injective (S2056NonzeroTorsionMap σ) :=
        S2056NonzeroTorsionMap_injective σ
      have himg : S.1.image (S2056NonzeroTorsionMap σ) =
          T.1.image (S2056NonzeroTorsionMap σ) := congrArg Subtype.val hST
      apply Subtype.ext
      exact (Finset.image_inj hf).mp himg))

@[simp] theorem S2490PairPerm_apply (σ : S1725AbsoluteGalois) (S : S2056Pair) :
    S2490PairPerm σ S = S2056PairMap σ S := rfl

/-- **The canonical root-to-pair bijection is Galois-equivariant, hence the
root and pair permutations of the same sigma have the same cycle type.** -/
theorem S2490RootPair_cycleType (σ : S1725AbsoluteGalois) :
    (S2490RootPerm σ).cycleType = (S2490PairPerm σ).cycleType := by
  have hconj : S2056RootPairEquiv.permCongr (S2490RootPerm σ) = S2490PairPerm σ := by
    ext x
    have happ : S2056RootPairEquiv (S2056RootPairEquiv.symm x) = x :=
      Equiv.apply_symm_apply _ x
    change S2056RootPairEquiv (S2056RootMap σ (S2056RootPairEquiv.symm x)) =
      S2056PairMap σ x
    rw [S2056RootPairEquiv_equivariant]
    change S2056PairMap σ (S2056RootPairEquiv (S2056RootPairEquiv.symm x)) =
      S2056PairMap σ x
    rw [happ]
  rw [← hconj, S2132cycleType_permCongr]

/-- The pair-cycle form of the target: some sigma acts on the twelve actual
pairs {+-P} with cycle type (10, 2). -/
def S2490PairCycleWitness : Prop :=
  ∃ σ : S1725AbsoluteGalois,
    (S2490PairPerm σ).cycleType = ({10, 2} : Multiset ℕ)

/-- The root-cycle form of the target: some sigma acts on the twelve actual
roots of psi_5 with cycle type (10, 2). -/
def S2490RootCycleWitness : Prop :=
  ∃ σ : S1725AbsoluteGalois,
    (S2490RootPerm σ).cycleType = ({10, 2} : Multiset ℕ)

/-- The root-cycle and pair-cycle forms are equivalent. -/
theorem S2490RootCycle_iff_pairCycle :
    S2490RootCycleWitness ↔ S2490PairCycleWitness := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (S2490RootPair_cycleType σ).symm.trans hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (S2490RootPair_cycleType σ).trans hσ⟩

/-! ## 3. The actual Dedekind--Frobenius datum -/

/-- The separability predicate for the reduction, with the maximality proof
passed explicitly so that the residue-field instance is available inside the
definition. -/
def S2490SeparableFbar (f : (RingOfIntegers S1720Field)[X])
    (p : Ideal (RingOfIntegers S1720Field)) (hp : p.IsMaximal) : Prop :=
  letI : p.IsMaximal := hp
  (fbar f p).Separable

/-- The factor-degree predicate for the reduction, with the maximality proof
passed explicitly. -/
def S2490FactorDegreesEq (f : (RingOfIntegers S1720Field)[X])
    (p : Ideal (RingOfIntegers S1720Field)) (hp : p.IsMaximal) : Prop :=
  letI : p.IsMaximal := hp
  factorDegrees (fbar f p) = ({2, 10} : Multiset ℕ)

/-- The exact arithmetic datum fed to S2217.  The model f is an integral monic
polynomial whose base change to F' is a nonzero scalar multiple of the actual
odd 5-division polynomial S2057Psi5F.  The prime P lies above p, and the
factor-degree multiset of the reduction is {2, 10}. -/
structure S2490DedekindData where
  f : (RingOfIntegers S1720Field)[X]
  p : Ideal (RingOfIntegers S1720Field)
  P : Ideal (RingOfIntegers S2057FiveDivisionField)
  p_max : p.IsMaximal
  P_prime : P.IsPrime
  P_lies : P.LiesOver p
  f_monic : f.Monic
  f_sep : S2490SeparableFbar f p p_max
  f_splits : (f.map
    (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  f_eq : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
      C c * S2057Psi5F
  factorDegrees_eq : S2490FactorDegreesEq f p p_max

/-- The arithFrobAt API of S2167 applied to the datum: at the prime P there is
an actual arithmetic Frobenius sigma on the actual 5-division field.  This is
the existence half; the cycle-type half is the Dedekind theorem below. -/
theorem S2490_frobenius_exists (D : S2490DedekindData) :
    ∃ σ : S2057FiveDivisionField ≃ₐ[S1720Field] S2057FiveDivisionField,
      IsArithFrobAt (RingOfIntegers S1720Field) σ D.P := by
  letI : D.p.IsMaximal := D.p_max
  letI : D.P.IsPrime := D.P_prime
  letI : D.P.LiesOver D.p := D.P_lies
  letI : D.P.IsMaximal := P_isMaximal D.p D.P
  letI : NumberField S2057FiveDivisionField :=
    NumberField.of_module_finite (K := S1720Field)
  exact S2167FrobeniusExists S1720Field S2057FiveDivisionField D.P

/-- **S2217 applied to the actual datum.**  The corrected Dedekind--Frobenius
cycle-type theorem gives an arithmetic Frobenius on the actual 5-division field
with root cycle type (10, 2).  This is the only arithmetic input of the file;
the theorem is a hypothesis, not a proved fact. -/
theorem S2490_rootCycle_of_dedekindData
    (hDF : DedekindFrobeniusCycleTypeTheoremCorrected)
    (D : S2490DedekindData) :
    ∃ σ : S2057FiveDivisionField ≃ₐ[S1720Field] S2057FiveDivisionField,
      rootCycleType S1720Field S2057FiveDivisionField D.f D.f_splits σ =
        ({10, 2} : Multiset ℕ) := by
  letI : D.p.IsMaximal := D.p_max
  letI : D.P.IsPrime := D.P_prime
  letI : D.P.LiesOver D.p := D.P_lies
  letI : NumberField S2057FiveDivisionField :=
    NumberField.of_module_finite (K := S1720Field)
  have hsep : (fbar D.f D.p).Separable := by
    simpa [S2490SeparableFbar] using D.f_sep
  have hfac : factorDegrees (fbar D.f D.p) = ({2, 10} : Multiset ℕ) := by
    simpa [S2490FactorDegreesEq] using D.factorDegrees_eq
  obtain ⟨σ, -, hcyc⟩ :=
    hDF (K := S1720Field) (L := S2057FiveDivisionField)
      (f := D.f) (p := D.p) (P := D.P) D.f_monic hsep D.f_splits
  refine ⟨σ, ?_⟩
  rw [hcyc, hfac]
  decide

/-! ## 4. The exact mod-1249 finite certificate (stated, not proved) -/

/-- The irreducible quadratic X^2 - 332X - 89 over ZMod 1249. -/
def S2490Mod1249Quad : (ZMod 1249)[X] :=
  X ^ 2 - C (332 : ZMod 1249) * X - C (89 : ZMod 1249)

/-- The degree-ten factor
X^10 + 570X^9 - 432X^8 - 410X^7 - 72X^6 + 242X^5 + 369X^4 - 85X^3 - 37X^2 + 166X + 580
over ZMod 1249. -/
def S2490Mod1249Ten : (ZMod 1249)[X] :=
  C (580 : ZMod 1249) + C (166 : ZMod 1249) * X - C (37 : ZMod 1249) * X ^ 2 -
    C (85 : ZMod 1249) * X ^ 3 + C (369 : ZMod 1249) * X ^ 4 +
    C (242 : ZMod 1249) * X ^ 5 - C (72 : ZMod 1249) * X ^ 6 -
    C (410 : ZMod 1249) * X ^ 7 - C (432 : ZMod 1249) * X ^ 8 +
    C (570 : ZMod 1249) * X ^ 9 + X ^ 10

/-- The exact scalar 415 = 2^36 * 5 mod 1249 is the reduction of the leading
coefficient of S2132Psi5Z. -/
def S2490Mod1249Scalar : ZMod 1249 := 415

/-- The concrete mod-1249 product certificate.  This is a finite polynomial
identity over ZMod 1249; it is verified externally (all coefficients match), but
no Lean proof is included in this uncompiled file. -/
def S2490Mod1249ProductRequired : Prop :=
  C S2490Mod1249Scalar * S2490Mod1249Quad * S2490Mod1249Ten =
    S2132Psi5Z.map (Int.castRingHom (ZMod 1249))

/-- The remaining finite micro-input: the explicit degree-ten factor is
irreducible over ZMod 1249.  Verified externally; not proved in Lean here. -/
def S2490Mod1249TenIrreducible : Prop :=
  Irreducible S2490Mod1249Ten

/-- The finite certificate conjunction. -/
def S2490Mod1249CertificateRequired : Prop :=
  S2490Mod1249ProductRequired ∧ S2490Mod1249TenIrreducible

/-! ## 5. The exact transport gaps -/

/-- **Missing transport 1 (splitting field to absolute closure).**
An automorphism of the actual 5-division field with root cycle type (10, 2)
produces an absolute Galois element whose permutation of the roots in the
algebraic closure has the same cycle type. -/
def S2490SplittingToRootCycle : Prop :=
  ∀ (f : (RingOfIntegers S1720Field)[X])
    (hmonic : f.Monic)
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : S2057FiveDivisionField ≃ₐ[S1720Field] S2057FiveDivisionField),
    rootCycleType S1720Field S2057FiveDivisionField f hsplit σ =
      ({10, 2} : Multiset ℕ) →
    S2490RootCycleWitness

/-- **Missing transport 2 (root/pair permutation to matrix pair action).**
The cycle type of the intrinsic Galois pair permutation equals the cycle type
of the pair action of the mod-5 matrix in the selected basis, for every sigma.
This is the S2480v1 S2480PairMatrix_cycleType statement; it is not in the
compiled S2480. -/
def S2490PairMatrixCycleType : Prop :=
  ∀ σ : S1725AbsoluteGalois,
    (pairPermHom
      (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis σ)).cycleType =
      (S2490PairPerm σ).cycleType

/-- The pair-cycle witness is exactly the target once the pair/matrix bridge is
available. -/
theorem S2490Target_iff_pairCycle
    (hpm : S2490PairMatrixCycleType) :
    S2490Target ↔ S2490PairCycleWitness := by
  constructor
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (hpm σ).symm.trans hσ⟩
  · rintro ⟨σ, hσ⟩
    exact ⟨σ, (hpm σ).trans hσ⟩

/-- The Dedekind datum and the first transport give the intrinsic pair-cycle
witness (using the proved root/pair cycle-type identity). -/
theorem S2490PairCycleWitness_of_dedekindData
    (hDF : DedekindFrobeniusCycleTypeTheoremCorrected)
    (D : S2490DedekindData)
    (htrans : S2490SplittingToRootCycle) :
    S2490PairCycleWitness := by
  obtain ⟨σL, hσL⟩ := S2490_rootCycle_of_dedekindData hDF D
  obtain ⟨σ, hσ⟩ := htrans D.f D.f_monic D.f_splits σL hσL
  exact ⟨σ, (S2490RootPair_cycleType σ).symm.trans hσ⟩

/-! ## 6. The conditional construction -/

/-- **Conditional construction.**  The Dedekind datum and the two named
transport gaps produce the actual target.  No inhabitant of any of the three
inputs is asserted. -/
theorem S2490FirstMissing_of_inputs
    (hDF : DedekindFrobeniusCycleTypeTheoremCorrected)
    (D : S2490DedekindData)
    (htrans : S2490SplittingToRootCycle)
    (hpm : S2490PairMatrixCycleType) :
    S2490Target :=
  (S2490Target_iff_pairCycle hpm).mpr
    (S2490PairCycleWitness_of_dedekindData hDF D htrans)

/-- The exact missing package, with actual witnesses for the arithmetic datum. -/
structure S2490ExactMissing where
  dedekind : DedekindFrobeniusCycleTypeTheoremCorrected
  data : S2490DedekindData
  splittingTransport : S2490SplittingToRootCycle
  pairMatrix : S2490PairMatrixCycleType

/-- The exact missing package would inhabit the target. -/
theorem S2490FirstMissing_of_exactMissing (h : S2490ExactMissing) :
    S2490Target :=
  S2490FirstMissing_of_inputs h.dedekind h.data h.splittingTransport h.pairMatrix

/-! ## 7. The S2442 projective bridge and the degree correction -/

/-- The precise S2442 projective-bridge input, as a named missing proposition. -/
def S2490ProjectiveBridgeMissing : Prop :=
  S2442Psi5ProjectiveBridgeRequired

/-- Under the S2442 projective bridge, the degree of the psi5 splitting field
is 240, not 480.  This is why the Q-level degree-480 route cannot be used to
transport a (10, 2) cycle type. -/
theorem S2490Degree_eq_240 (D : S2442Psi5ProjectiveBridge) :
    Module.finrank ℚ s2289QE5 = 240 :=
  S2442Degree_eq_240 D

/-- The corrected projective domain comparison is the S2442 replacement for the
old (refuted) matrix-kernel restriction data. -/
def S2490CorrectedDomainComparison : Prop :=
  S2442CorrectedDomainComparison S1982Basis

/-! ## 8. Axiom footprint of the proved declarations -/

#print axioms S2490Target_iff_sigma
#print axioms S2490Target_at_any_basis
#print axioms S2490RootPair_cycleType
#print axioms S2490RootCycle_iff_pairCycle
#print axioms S2490_frobenius_exists
#print axioms S2490_rootCycle_of_dedekindData
#print axioms S2490Target_iff_pairCycle
#print axioms S2490PairCycleWitness_of_dedekindData
#print axioms S2490FirstMissing_of_inputs
#print axioms S2490FirstMissing_of_exactMissing
#print axioms S2490Degree_eq_240

end LeanFormal.IUT.XiFPaper.S2490SigmaConstructionActualAdapted

end
