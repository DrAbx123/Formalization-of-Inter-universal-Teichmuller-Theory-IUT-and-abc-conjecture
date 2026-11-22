/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
-/
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2445D5LargeImageChainActual
import tmp.sheaf.xif.paper.S2449D5FinalStatusActual
import tmp.sheaf.xif.paper.S2375RangePairTransitiveActual
import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual
import tmp.sheaf.xif.paper.S2364D5GroupRouteActual
import tmp.sheaf.xif.paper.S2186PairBijectiveActual
import tmp.sheaf.xif.paper.S2172AffineBasisLiftActual
import tmp.sheaf.xif.paper.S2229RangeTransitivityActual
import tmp.sheaf.xif.paper.S2243RangeCompatibilityActual
import tmp.sheaf.xif.paper.S2440RootPermCycleCleanActual
import tmp.sheaf.xif.paper.S2339FbarFactorsActual
import tmp.sheaf.xif.paper.S2408FiberSizesActual
import tmp.sheaf.xif.paper.S2167DedekindFrobCycleActual
import tmp.sheaf.xif.paper.S2345RootSetEquivActual
import tmp.sheaf.xif.paper.S2057DedekindFrobBridgeActual
import tmp.sheaf.xif.paper.S2056Psi5RootsActual
import tmp.sheaf.xif.paper.S2180BasisCompatiblePairActual
import tmp.sheaf.xif.paper.S1894D5LargeImageActual
import tmp.sheaf.xif.paper.S2132D5FactorizationActual
import tmp.sheaf.xif.paper.S2397RootFactorMapActual

/-!
# S2470: the actual pair-transitivity target and the Dedekind--Frobenius route

The target of this file is the actual proposition

  S2470Target := S2203RangePairTransitiveRequired S1982Basis
    = PairTransitive
        (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))

of the paper's D5 large-image input, i.e. the twelve-pair transitivity of the
actual mod-5 Galois range of the actual curve E' over F'.

## Status

The target is **not proved** and no inhabitant of it is produced.  Nothing
below is a sorry, axiom, True/PUnit gate, native_decide, or a renamed
hypothesis; every declaration is an actual Lean object, and the missing
statements are plain Props without inhabitants.

## What is proved here

1. The target is *definitionally* the S2203/S2375/S2378/S2445/S2449
   formulations of the pair-transitivity half of the D5 input
   (S2470Target_iff_S2375, S2470Target_iff_S2378, S2470Target_iff_S2445,
   and the affine/Galois forms S2470Target_iff_affine,
   S2470Target_iff_galois).

2. The sufficient inputs already kernel checked in the tree are re-exported for
   the final target: the twelve-cycle input S2440TwelveCycleInputRequired
   (S2470Target_of_twelveCycle), the SL_2 containment
   S1725ImageTail S1987Five S1982Basis (S2470Target_of_imageTail), the frozen
   S1987 large-image target (S2470Target_of_largeImage), the whole-range
   statement S2378RangeTopRequired (S2470Target_of_rangeTop).  Together with
   the cycle-type hypothesis they give the D5 endpoint
   (S2470D5LargeImageFive_of_target_and_cycle).

3. **New: the Dedekind--Frobenius irreducible-residue theorem.**
   S2470_residueIrreducible_rootTwelveCycle proves, for an arbitrary finite
   Galois extension of number fields L/K, an integral monic polynomial f that
   splits in L, a maximal prime p and a prime P above it: if the reduction
   fbar f p is irreducible and has exactly twelve roots in the residue field
   of L, then some arithmetic Frobenius at P (for the canonical action of
   Gal(L/K) on O_L) has root permutation of cycle type {12}.

   The interest of this theorem is that it is *sharper than the general
   Dedekind--Frobenius theorem of S2217/S2167*: the general orbit-size
   comparison is still missing in the tree (S2217Missing), but in the
   irreducible case the Frobenius transitivity on the root set is already
   kernel checked (S2339FrobTransitive), and the cycle-type transport
   permBar to rootPerm is S2440RootPermCycleCleanActual.  Consequently the
   *only* arithmetic input of the mod-13 route is the finite-field
   irreducibility of the reduction, not the general Dedekind--Frobenius
   comparison.

4. The exact residue data needed for the actual curve are packaged as
   S2470ActualResidueData: an integral model f of a nonzero rational multiple
   of the actual S2057Psi5F, a prime ideal p of O_{F'}, a prime P of the
   actual 5-division field above p, and the irreducibility of fbar f p of
   degree twelve.  S2470ActualResidueData.rootTwelveCycle derives from such
   data a Gal(F'/F')-element with twelve-cycle root permutation.

5. **The exact remaining gap is isolated as S2470RootToRangeTransport.**  It
   is the statement that a twelve-cycle on the roots of an integral model of
   psi_5 at a prime produces a twelve-cycle in the actual mod-5 matrix range
   (equivalently, that the Dedekind--Frobenius root permutation transports to
   the matrix pair action along the S2180/S2186 basis-compatible pair
   identification).  Given this transport the residue data do prove the
   target (S2470Target_of_residueData_and_transport).

## Exact first missing (summary)

* For the target itself: S2470Target (equivalently S2375ExactFirstMissing,
  S2378ExactFirstMissing, S2445RangePairTransitive).  No equivalent smaller
  statement is proved in the tree.

* For the arithmetic mod-13/Dedekind--Frobenius route investigated here: the
  conjunction of
  (a) S2470ActualResidueData (the concrete prime with irreducible degree-twelve
      reduction of an integral model of the actual psi_5), and
  (b) S2470RootToRangeTransport (transport of the root cycle type to the
      matrix pair action).
  Item (a) contains the finite-field certificate of the S1987 report
  (irreducibility of 2^36 * psi_5 mod 13, recorded below as
  S2470Mod13Certificate), which is not formalized in the tree; the tree only
  formalizes a mod-29 factorization (S2126/S2132), and even that only
  conditionally (S2132FirstMissing).  Item (b) is a formalization gap, not an
  arithmetic one: the affine/projective-to-pair identifications S2172/S2180/
  S2186 are kernel checked, but the composition with the Dedekind--Frobenius
  root permutation is not.

* A subtlety of the mod-13 route over F' (recorded in S2167 for 29 and
  repeated here): the certificate in the S1987 report is a Q-level statement,
  while 13 is not inert in the source field in general; a prime of F' above 13
  has residue degree > 1 whenever 13 splits partially, and the relative
  Frobenius is then a proper power of the Q-Frobenius.  Hence the mod-13
  certificate must be applied to a prime whose residue degree is one (or at a
  different prime), and the linear-disjointness/restriction transport from the
  Q-level to F' is itself not formalized (S2167 records the same phenomenon at
  29).  No numerical value of the residue degree at 13 is asserted here.
-/

noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2166AffinePairCorrespondenceActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2218RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual
open LeanFormal.IUT.XiFPaper.S2449D5FinalStatusActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual
open LeanFormal.IUT.XiFPaper.S2217DedekindFrobTheoremActual
open LeanFormal.IUT.XiFPaper.S2339FbarFactorsActual
open LeanFormal.IUT.XiFPaper.S2440RootPermCycleCleanActual
open LeanFormal.IUT.XiFPaper.S2397RootFactorMapActual
open LeanFormal.IUT.XiFPaper.S2229RangeTransitivityActual
open LeanFormal.IUT.XiFPaper.S2243RangeCompatibilityActual
open LeanFormal.IUT.XiFPaper.S2132D5FactorizationActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual

/-! ## 0. The canonical action of Gal(L/K) on O_L

The Dedekind--Frobenius interface of Mathlib is parameterized by a
`MulSemiringAction Gal(L/K) (RingOfIntegers L)` and an `SMulCommClass`.  The
transport lemmas of S2440RootPermCycleCleanActual use the canonical action
`IsIntegralClosure.MulSemiringAction`; the named definitions below expose that
same action as a local instance so that the Frobenius witnesses produced here
have exactly the type expected by those lemmas. -/

/-- The canonical action of Gal(L/K) on the ring of integers of L. -/
noncomputable def S2470RingOfIntegersAction {K L : Type*} [Field K] [Field L]
    [Algebra K L] [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] : MulSemiringAction Gal(L/K) (RingOfIntegers L) :=
  IsIntegralClosure.MulSemiringAction (RingOfIntegers K) K L (RingOfIntegers L)

attribute [local instance] S2470RingOfIntegersAction

/-- The canonical `SMulCommClass` of the action on the ring of integers (S2381). -/
noncomputable def S2470RingOfIntegersSMulComm {K L : Type*} [Field K] [Field L]
    [Algebra K L] [NumberField K] [NumberField L] [FiniteDimensional K L]
    [IsGalois K L] : SMulCommClass Gal(L/K) (RingOfIntegers K) (RingOfIntegers L) :=
  LeanFormal.IUT.XiFPaper.S2381SmulCommActual.S2381_smulCommClass

attribute [local instance] S2470RingOfIntegersSMulComm

/-! ## 1. The target and its equivalent formulations -/

/-- The actual target of this file: pair transitivity of the actual mod-5 range
at the selected basis S1982Basis. -/
def S2470Target : Prop := S2203RangePairTransitiveRequired S1982Basis

/-- The target unfolded. -/
theorem S2470Target_unfolded :
    S2470Target ↔
      PairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The target is the S2375 exact first missing. -/
theorem S2470Target_iff_S2375 : S2470Target ↔ S2375ExactFirstMissing := Iff.rfl

/-- The target is the S2378 exact first missing. -/
theorem S2470Target_iff_S2378 : S2470Target ↔ S2378ExactFirstMissing := Iff.rfl

/-- The target is the S2445 integrated pair-transitivity proposition. -/
theorem S2470Target_iff_S2445 : S2470Target ↔ S2445RangePairTransitive := Iff.rfl

/-- The target is the S2203 range hypothesis at S1982Basis. -/
theorem S2470Target_iff_S2203 :
    S2470Target ↔ S2203RangePairTransitiveRequired S1982Basis := Iff.rfl

/-- The target is the actual affine-pair transitivity of S2218. -/
theorem S2470Target_iff_affine :
    S2470Target ↔ S2218RangeAffinePairTransitiveRequired S1982Basis :=
  (S2218RangeAffinePairTransitiveRequired_iff S1982Basis).symm

/-- The target is the actual Galois transitivity of S2229. -/
theorem S2470Target_iff_galois :
    S2470Target ↔ S2229GaloisPairTransitive S1982Basis :=
  (S2375GaloisPairTransitive_iff_range).symm

/-- The pair-transitivity half of the S2449 exact first missing is the target. -/
theorem S2470Target_of_S2449 (h : S2449D5ExactFirstMissing) : S2470Target := h.1

/-- The target and the cycle-type hypothesis together are the S2449 exact
first missing. -/
theorem S2449_of_target_and_cycle (h : S2470Target)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) : S2449D5ExactFirstMissing :=
  ⟨h, hcycle⟩

/-- The pair-transitivity component of S2364's exact first missing is the
target. -/
theorem S2470Target_of_S2364 (h : S2364ExactFirstMissing) : S2470Target := h.2

/-! ## 2. The sufficient inputs of the tree, re-exported -/

/-- The twelve-cycle input implies the target (S2440). -/
theorem S2470Target_of_twelveCycle (h : S2440TwelveCycleInputRequired) :
    S2470Target :=
  S2440RangePairTransitive_of_twelveCycle h

/-- The SL_2 containment at the selected basis implies the target (S2440). -/
theorem S2470Target_of_imageTail (h : S1725ImageTail S1987Five S1982Basis) :
    S2470Target :=
  S2440RangePairTransitive_of_imageTail h

/-- The frozen S1987 large-image target implies the target (S2440). -/
theorem S2470Target_of_largeImage (h : S1987D5LargeImageFive) : S2470Target :=
  S2440RangePairTransitive_of_largeImage h

/-- The whole-range statement implies the target (S2378). -/
theorem S2470Target_of_rangeTop (h : S2378RangeTopRequired) : S2470Target :=
  S2378PairTransitive_of_rangeTop h

/-- Target plus cycle type give the D5 large-image endpoint (S2203/S2132). -/
theorem S2470D5LargeImageFive_of_target_and_cycle (hpair : S2470Target)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) : S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle hpair

/-- Target plus cycle type give the exact SL_2 containment at the basis
(S2364). -/
theorem S2470ImageTail_of_target_and_cycle (hpair : S2470Target)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1725ImageTail S1987Five S1982Basis :=
  S2364RangeImageTail_of_hypotheses S1982Basis hcycle hpair

/-! ## 3. Dedekind--Frobenius: irreducible residue implies a twelve-cycle -/

section DedekindFrobenius

variable {K L : Type} [Field K] [Field L] [Algebra K L]
  [NumberField K] [NumberField L] [FiniteDimensional K L] [IsGalois K L]

/-- **Frobenius existence for the canonical action.**  For a finite Galois
extension of number fields L/K and a prime P of O_L with finite residue field,
there is an arithmetic Frobenius at P for the canonical action
`IsIntegralClosure.MulSemiringAction` of Gal(L/K) on O_L. -/
theorem S2470_frobeniusExists
    (P : Ideal (RingOfIntegers L)) [P.IsPrime] [Finite (RingOfIntegers L ⧸ P)] :
    ∃ σ : Gal(L/K), IsArithFrobAt (RingOfIntegers K) σ P := by
  haveI : Algebra.IsInvariant (RingOfIntegers K) (RingOfIntegers L) Gal(L/K) :=
    Algebra.isInvariant_of_isGalois (RingOfIntegers K) K L (RingOfIntegers L)
  exact IsArithFrobAt.exists_of_isInvariant (RingOfIntegers K) Gal(L/K) P

/-- **Dedekind--Frobenius in the irreducible case.**  Let L/K be a finite
Galois extension of number fields, f an integral monic polynomial over K that
splits in L, p a maximal ideal of O_K and P a prime of O_L above p.  If the
reduction fbar f p (over the residue field at p) is separable and irreducible
and has exactly twelve roots in the residue field of L, and L contains the
roots of f, then some arithmetic Frobenius at P has, on the twelve roots of f,
a root permutation of cycle type {12}.  (The root count follows from
separability and natDegree fbar = 12 by the standard counting theorem; it is
kept as a hypothesis to avoid any dependence on a chosen Field structure on the
residue ring.)

No general Dedekind--Frobenius orbit-size theorem is used: the transitivity of
the residue Frobenius on the roots of an irreducible factor is S2339's
kernel-checked theorem, and the transport of the residue permutation to the
Galois root permutation is S2440RootPermCycleCleanActual. -/
theorem S2470_residueIrreducible_rootTwelveCycle
    (f : (RingOfIntegers K)[X]) (p : Ideal (RingOfIntegers K)) [hp : p.IsMaximal]
    (P : Ideal (RingOfIntegers L)) [hP : P.IsPrime] [hPover : P.LiesOver p]
    (hmonic : f.Monic) (hsep : (fbar f p).Separable)
    (hsplit : (f.map (algebraMap (RingOfIntegers K) L)).Splits)
    (hirr : Irreducible (fbar f p))
    (hcard : Fintype.card ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) = 12) :
    ∃ σ : Gal(L/K), IsArithFrobAt (RingOfIntegers K) σ P ∧
      rootCycleType K L f hsplit σ = ({12} : Multiset ℕ) := by
  classical
  haveI hPmax : P.IsMaximal := P_isMaximal p P
  have hmonicbar : (fbar f p).Monic := s2397Fbar_monic f p P hmonic
  haveI : Nontrivial ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)) :=
    Fintype.one_lt_card_iff_nontrivial.mp (by omega)
  have htrans : ∀ x y : ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P)),
      ∃ n : ℕ, (permBar (f := f) p P ^ n) x = y := by
    intro x y
    have hx : (Polynomial.aeval x.1) (fbar f p) = 0 :=
      (Polynomial.Monic.mem_rootSet hmonicbar).mp x.2
    have hy : (Polynomial.aeval y.1) (fbar f p) = 0 :=
      (Polynomial.Monic.mem_rootSet hmonicbar).mp y.2
    obtain ⟨n, hn⟩ := s2339FrobTransitive f p P hmonic hsep hsplit hmonicbar hirr
      dvd_rfl hx hy
    refine ⟨n, ?_⟩
    have hval : ∀ (m : ℕ),
        ((permBar (f := f) p P ^ m) x).1 = (frobBar p P)^[m] x.1 := by
      intro m
      induction m with
      | zero => simp
      | succ m ih =>
          rw [pow_succ']
          exact (congrArg (frobBar p P) ih).trans
            (Function.iterate_succ_apply' (f := frobBar p P) m x.1).symm
    apply Subtype.ext
    rw [hval n]
    exact hn
  have hcycleOn : (permBar (f := f) p P).IsCycleOn
      (Set.univ : Set ((fbar f p).rootSet ((RingOfIntegers L) ⧸ P))) := by
    refine ⟨?_, ?_⟩
    · rw [Set.bijOn_univ]
      exact Equiv.bijective _
    · intro x _ y _
      obtain ⟨n, hn⟩ := htrans x y
      exact ⟨(n : ℤ), by rwa [zpow_natCast]⟩
  have hsupport : (permBar (f := f) p P).support = Finset.univ := by
    ext y
    rw [Equiv.Perm.mem_support]
    simp only [Finset.mem_univ, iff_true]
    exact hcycleOn.apply_ne Set.nontrivial_univ (Set.mem_univ y)
  have hcycle : (permBar (f := f) p P).IsCycle := by
    rw [Equiv.Perm.isCycle_iff_exists_isCycleOn]
    exact ⟨Set.univ, Set.nontrivial_univ, hcycleOn, fun x _ => Set.mem_univ x⟩
  have hcycleType : (permBar (f := f) p P).cycleType = ({12} : Multiset ℕ) := by
    rw [hcycle.cycleType, hsupport, Finset.card_univ, hcard]
  obtain ⟨σ, hσ⟩ := S2470_frobeniusExists (K := K) (L := L) P
  refine ⟨σ, hσ, ?_⟩
  rw [← s2440_permBar_cycleType_eq_rootCycleType (K := K) (L := L) f p P hsplit
    hmonic hsep σ hσ]
  convert hcycleType

end DedekindFrobenius

/-! ## 4. The residue data for the actual curve -/

/-- The actual 5-division field over F' is a number field. -/
instance S2470FiveDivisionFieldNumberField : NumberField S2057FiveDivisionField :=
  NumberField.of_module_finite S1720Field S2057FiveDivisionField

/-- The concrete residue data needed by the Dedekind--Frobenius route for the
actual curve: an integral model f of a nonzero F'-multiple of the actual odd
5-division polynomial S2057Psi5F, a maximal prime p of O_{F'}, a prime P of the
actual 5-division field above p, and the irreducibility of the reduction of f
at p of degree twelve.  This is the exact arithmetic input still missing. -/
structure S2470ActualResidueData where
  f : (RingOfIntegers S1720Field)[X]
  p : Ideal (RingOfIntegers S1720Field)
  P : Ideal (RingOfIntegers S2057FiveDivisionField)
  p_max : p.IsMaximal
  [P_prime : P.IsPrime]
  [P_lies : P.LiesOver p]
  f_monic : f.Monic
  f_sep : (fbar f p).Separable
  f_splits : (f.map
    (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits
  f_psi5 : ∃ c : S1720Field, c ≠ 0 ∧
    f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F
  fbar_irreducible : Irreducible (fbar f p)
  fbar_degree : (fbar f p).natDegree = 12
  fbar_card : Fintype.card ((fbar f p).rootSet
    ((RingOfIntegers S2057FiveDivisionField) ⧸ P)) = 12

/-- **The residue data produce a twelve-cycle on the roots of the model.** -/
theorem S2470ActualResidueData.rootTwelveCycle (D : S2470ActualResidueData) :
    ∃ σ : Gal(S2057FiveDivisionField/S1720Field),
      rootCycleType S1720Field S2057FiveDivisionField D.f D.f_splits σ =
        ({12} : Multiset ℕ) := by
  letI : D.p.IsMaximal := D.p_max
  haveI : D.P.IsPrime := D.P_prime
  haveI : D.P.LiesOver D.p := D.P_lies
  obtain ⟨σ, -, hσ⟩ := S2470_residueIrreducible_rootTwelveCycle
    (K := S1720Field) (L := S2057FiveDivisionField)
    D.f D.p D.P D.f_monic D.f_sep D.f_splits D.fbar_irreducible D.fbar_card
  exact ⟨σ, hσ⟩

/-! ## 5. The exact remaining transport gap -/

/-- **The remaining formalization gap of the mod-13/DF route.**  A twelve-cycle
of an F'-automorphism of the actual 5-division field on the roots of an
integral model of a nonzero multiple of psi_5 produces a twelve-cycle in the
actual mod-5 matrix range, i.e. the S2440 twelve-cycle input.

Mathematically this is true: the twelve roots are the x-coordinates of the
twelve pairs {+-P} (S2056RootPairEquiv), the Galois action on pairs is the
matrix action in the S1982 basis (S2172/S2180/S2186/S1894), and conjugate
permutations have equal cycle type.  What is missing is the formalized
composition: the Dedekind--Frobenius root permutation lives on the roots of an
integral model inside the 5-division field, while S2056RootRootPerm acts on the
roots in the algebraic closure; the two root sets and their Galois actions are
not identified in the tree, and S2056RootPairEquiv is only proved for
automorphisms of the algebraic closure. -/
def S2470RootToRangeTransport : Prop :=
  ∀ (f : (RingOfIntegers S1720Field)[X]) (hmonic : f.Monic)
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)),
    (∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) = C c * S2057Psi5F) →
    rootCycleType S1720Field S2057FiveDivisionField f hsplit σ =
        ({12} : Multiset ℕ) →
    S2440TwelveCycleInputRequired

/-- **The residue data and the transport imply the target.**  This is a
conditional theorem: neither hypothesis is proved in the tree. -/
theorem S2470Target_of_residueData_and_transport (D : S2470ActualResidueData)
    (htrans : S2470RootToRangeTransport) : S2470Target := by
  obtain ⟨σ, hσ⟩ := D.rootTwelveCycle
  exact S2440RangePairTransitive_of_twelveCycle
    (htrans D.f D.f_monic D.f_splits σ D.f_psi5 hσ)

/-- The residue data and the transport give the D5 endpoint, given the
cycle-type hypothesis. -/
theorem S2470D5LargeImageFive_of_residueData_transport_cycle
    (D : S2470ActualResidueData) (htrans : S2470RootToRangeTransport)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) : S1987D5LargeImageFive :=
  S2470D5LargeImageFive_of_target_and_cycle
    (S2470Target_of_residueData_and_transport D htrans) hcycle

/-! ## 6. The exact first missing statements -/

/-- The exact first missing of the target: the target itself.  No equivalent
smaller statement is proved in the tree. -/
def S2470ExactFirstMissing : Prop := S2470Target

/-- The exact first missing is definitionally the target. -/
theorem S2470ExactFirstMissing_iff : S2470ExactFirstMissing ↔ S2470Target :=
  Iff.rfl

/-- The exact first missing is the S2375 exact first missing. -/
theorem S2470ExactFirstMissing_iff_S2375 :
    S2470ExactFirstMissing ↔ S2375ExactFirstMissing := Iff.rfl

/-- The concrete arithmetic input still missing: there exist an integral model
f of a nonzero multiple of the actual psi_5, a maximal prime p of O_{F'}, and a
prime P of the actual 5-division field above p at which the reduction of f is
separable and irreducible of degree twelve. -/
def S2470ResidueCertificateRequired : Prop := Nonempty S2470ActualResidueData

/-- The finite-field certificate of the S1987 report, in the integer model of
S2132: 2^36 * psi_5 is irreducible modulo 13.  This is a plain Prop with no
inhabitant in the tree; even it would not by itself give the target, since the
identification of the integer model with S2057Psi5Q (S2132FirstMissing) and
the residue-field transport are separate. -/
def S2470Mod13Certificate : Prop :=
  Irreducible (S2132Psi5Z.map (Int.castRingHom (ZMod 13)))

/-- The conjunction of the concrete residue certificate and the transport is
sufficient for the target. -/
theorem S2470Target_of_certificate_and_transport
    (hcert : S2470ResidueCertificateRequired) (htrans : S2470RootToRangeTransport) :
    S2470Target :=
  S2470Target_of_residueData_and_transport (Classical.choice hcert) htrans

/-! ## 7. Axiom footprint -/

#print axioms S2470Target_unfolded
#print axioms S2470Target_iff_S2375
#print axioms S2470Target_iff_S2378
#print axioms S2470Target_iff_S2445
#print axioms S2470Target_iff_affine
#print axioms S2470Target_iff_galois
#print axioms S2470Target_of_S2449
#print axioms S2449_of_target_and_cycle
#print axioms S2470Target_of_twelveCycle
#print axioms S2470Target_of_imageTail
#print axioms S2470Target_of_largeImage
#print axioms S2470Target_of_rangeTop
#print axioms S2470D5LargeImageFive_of_target_and_cycle
#print axioms S2470ImageTail_of_target_and_cycle
#print axioms S2470_residueIrreducible_rootTwelveCycle
#print axioms S2470FiveDivisionFieldNumberField
#print axioms S2470ActualResidueData.rootTwelveCycle
#print axioms S2470Target_of_residueData_and_transport
#print axioms S2470D5LargeImageFive_of_residueData_transport_cycle
#print axioms S2470ExactFirstMissing_iff
#print axioms S2470Target_of_certificate_and_transport

end LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual

end
