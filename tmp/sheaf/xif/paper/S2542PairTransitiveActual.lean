/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2440RangePairTransitiveSubagentActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
import tmp.sheaf.xif.paper.S2510AbsoluteLiftActual
import tmp.sheaf.xif.paper.S2520RootCycleTransferActual
import tmp.sheaf.xif.paper.S2378ActualPairTransitiveActual

/-!
# S2542: the actual mod-5 range pair-transitivity target

## The target

  S2542Target := S2203RangePairTransitiveRequired S1982Basis
    = PairTransitive
        (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis)),

the twelve-pair transitivity of the actual mod-5 Galois range of the actual
curve E' = S1720Curve over the actual number field F' = S1720Field, at the
actual rank-two basis S1982Basis of E'[5].

## Status of the target: NOT PROVED

Nothing in this file or in the consumed S2440, S2470, S2480, S2481, S2510,
S2520 chain produces an inhabitant of the target, and no other file in the
current tree is known to do so.  The exact first missing statement is the
target itself:

  S2542ExactFirstMissing := S2542Target,

definitionally S2375ExactFirstMissing, S2378ExactFirstMissing,
S2445RangePairTransitive and S2470Target.

## The three sufficient inputs re-exported here

1. S1725ImageTail S1987Five S1982Basis, the literal SL_2(F_5) containment at
   the selected basis, equivalent to the frozen S1987D5LargeImageFive
   (S2440RangePairTransitive_of_imageTail, S2542Target_of_imageTail).
2. S2440TwelveCycleInputRequired, a single element of the actual range whose
   permutation of the twelve pairs is a 12-cycle
   (S2440RangePairTransitive_of_twelveCycle, S2542Target_of_twelveCycle).
3. S2378RangeTopRequired, the stronger statement range = top
   (S2378PairTransitive_of_rangeTop, S2542Target_of_rangeTop).

None of the three is inhabited in the tree.  Under the independent (10, 2)
cycle-type input, the target is equivalent to the SL_2 containment
(S2440RangePairTransitive_iff_imageTail_of_cycleType102); without that input
no equivalence of the target with any of the three is claimed.

## New in this file: the cycle-type dictionary between the range and psi_5 roots

Using the matrix/root cycle-type equality of S2480/S2501, we prove the full
cycle-type dictionary S2542RangeCycleType_iff_rootCycleType: a multiset c is
realised in the actual mod-5 range if and only if it is realised by an
absolute Galois permutation of the twelve psi_5-roots.  Using the absolute
lift/restriction of S2510 and the cycle-type transfer of S2520, we prove
S2542RootCycleType_iff_divisionRootCycleType: this is in turn equivalent to c
being realised by an F'-automorphism of the actual psi_5 splitting field
S2132L.  In particular the twelve-cycle input is exactly the splitting-field
12-cycle statement (S2542RootCycleTwelve_iff_twelveCycleInput,
S2542DivisionRootCycleTwelve_iff_rootCycleTwelve,
S2542DivisionRootCycleTwelve_iff_twelveCycleInput).  Thus one exact arithmetic
form of the mod-13/Dedekind--Frobenius route is the splitting-field 12-cycle
statement, which suffices for the target; S2470 supplies the
Dedekind--Frobenius 12-cycle theorem and S2520 the root-cycle transfer, while
the remaining arithmetic input is the residue datum and transport recorded in
Section 4.

## The arithmetic residue route

The residue data plus the root-to-range transport of S2470 imply the target
(S2542Target_of_arithmeticResidueRoute, S2542Target_of_certificate_and_transport);
neither S2470ResidueCertificateRequired nor S2470RootToRangeTransport is
inhabited.  S2481 proves the complementary residue-degree-one statement at 613
(S2542Mod613SourceSplits) and states the finite irreducibility certificate as
a plain Prop (S2542Mod613Certificate); the certificate itself is not proved,
and even it would not by itself produce the root-to-range transport.

## Verification status

This file is written but NOT compiled (the parent build coordinator runs the
serial build).  No sorry, admit, axiom, True/PUnit gate, native_decide or
renamed hypothesis is used: every declaration is an ordinary definition or
theorem, the three sufficient inputs occur only as hypotheses or as the missing
endpoints, and no conditional statement is announced as actual.  The intended
axiom footprint of every declaration below is propext, Classical.choice and
Quot.sound only.
-/

noncomputable section

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2542PairTransitiveActual

open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S2009DicksonActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S2364D5GroupRouteActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2445D5LargeImageChainActual
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual
open LeanFormal.IUT.XiFPaper.S2510AbsoluteLiftActual
open LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual

/-! ## 1. The target and its equivalent formulations -/

/-- The actual pair-transitivity target: transitivity of the actual mod-5
Galois range at S1982Basis on the twelve pairs of nonzero 5-torsion points. -/
def S2542Target : Prop := S2203RangePairTransitiveRequired S1982Basis

/-- The target unfolded. -/
theorem S2542Target_unfolded :
    S2542Target ↔
      PairTransitive
        (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range :=
  Iff.rfl

/-- The target is literally the S2203 range hypothesis at S1982Basis. -/
theorem S2542Target_iff_S2203 :
    S2542Target ↔ S2203RangePairTransitiveRequired S1982Basis :=
  Iff.rfl

/-- The target is the S2375 exact first missing. -/
theorem S2542Target_iff_S2375 : S2542Target ↔ S2375ExactFirstMissing :=
  Iff.rfl

/-- The target is the S2378 exact first missing. -/
theorem S2542Target_iff_S2378 : S2542Target ↔ S2378ExactFirstMissing :=
  Iff.rfl

/-- The target is the S2445 integrated pair-transitivity proposition. -/
theorem S2542Target_iff_S2445 : S2542Target ↔ S2445RangePairTransitive :=
  Iff.rfl

/-- The target is the S2470 target. -/
theorem S2542Target_iff_S2470 : S2542Target ↔ S2470Target :=
  Iff.rfl

/-- The exact first missing statement of the pair-transitivity half: the
target itself. -/
def S2542ExactFirstMissing : Prop := S2542Target

/-- The exact first missing is definitionally the target. -/
theorem S2542ExactFirstMissing_iff :
    S2542ExactFirstMissing ↔ S2542Target :=
  Iff.rfl

/-- The exact first missing is the S2375 exact first missing. -/
theorem S2542ExactFirstMissing_iff_S2375 :
    S2542ExactFirstMissing ↔ S2375ExactFirstMissing :=
  S2542ExactFirstMissing_iff.trans S2542Target_iff_S2375

/-- The exact first missing is the S2470 target. -/
theorem S2542ExactFirstMissing_iff_S2470 :
    S2542ExactFirstMissing ↔ S2470Target :=
  S2542ExactFirstMissing_iff.trans S2542Target_iff_S2470

/-! ## 2. The three sufficient inputs -/

/-- **The SL_2(F_5) containment at S1982Basis implies the target** (S2440). -/
theorem S2542Target_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) : S2542Target :=
  S2440RangePairTransitive_of_imageTail h

/-- **The frozen S1987 large-image target implies the target** (S2440). -/
theorem S2542Target_of_largeImage
    (h : S1987D5LargeImageFive) : S2542Target :=
  S2440RangePairTransitive_of_largeImage h

/-- **A 12-cycle in the actual range implies the target** (S2440). -/
theorem S2542Target_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2542Target :=
  S2440RangePairTransitive_of_twelveCycle h

/-- **range = top implies the target** (S2378). -/
theorem S2542Target_of_rangeTop
    (h : S2378RangeTopRequired) : S2542Target :=
  S2378PairTransitive_of_rangeTop h

/-- The three sufficient inputs, packaged. -/
theorem S2542Target_of_sufficient_inputs :
    (S1725ImageTail S1987Five S1982Basis → S2542Target) ∧
      (S2440TwelveCycleInputRequired → S2542Target) ∧
        (S2378RangeTopRequired → S2542Target) :=
  ⟨S2542Target_of_imageTail, S2542Target_of_twelveCycle,
    S2542Target_of_rangeTop⟩

/-- **Under the (10, 2) cycle-type input, the target is exactly the SL_2
containment** (S2440/S2364). -/
theorem S2542Target_iff_imageTail_of_cycleType102
    (h102 : S2203RangeCycleTypeRequired S1982Basis) :
    S2542Target ↔ S1725ImageTail S1987Five S1982Basis :=
  S2440RangePairTransitive_iff_imageTail_of_cycleType102 h102

/-! ## 3. Cycle-type dictionary between the actual range and the psi_5 roots -/

/-- **Every cycle type realised in the actual mod-5 range is realised by an
absolute Galois permutation of the twelve psi_5-roots, and conversely**, by
the matrix/root cycle-type equality of S2480/S2501. -/
theorem S2542RangeCycleType_iff_rootCycleType (c : Multiset ℕ) :
    (∃ h ∈ (S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis).range,
        (pairPermHom h).cycleType = c) ↔
      (∃ sigma : S1725AbsoluteGalois,
        (S2501RootPerm sigma).cycleType = c) := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨sigma, rfl⟩ := MonoidHom.mem_range.mp hh
    refine ⟨sigma, ?_⟩
    rwa [← S2501PairMatrix_cycleType sigma]
  · rintro ⟨sigma, hsigma⟩
    refine ⟨S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis sigma,
      MonoidHom.mem_range.mpr ⟨sigma, rfl⟩, ?_⟩
    rwa [S2501PairMatrix_cycleType sigma]

/-- **Every cycle type realised by an absolute Galois permutation of the
twelve psi_5-roots is realised by an F'-automorphism of the actual psi_5
splitting field, and conversely**, by the S2510 lift/restriction and the S2520
cycle-type transfer. -/
theorem S2542RootCycleType_iff_divisionRootCycleType (c : Multiset ℕ) :
    (∃ sigma : S1725AbsoluteGalois,
        (S2501RootPerm sigma).cycleType = c) ↔
      (∃ tau : S2132L ≃ₐ[S1720Field] S2132L,
        Equiv.Perm.cycleType (S2132DivisionRootEquiv tau) = c) := by
  constructor
  · rintro ⟨sigma, hsigma⟩
    refine ⟨S2510Restrict sigma, ?_⟩
    rw [S2520cycleType_eq (S2510Restrict sigma) sigma
      (fun x => (S2510Restrict_apply sigma x).symm)]
    exact hsigma
  · rintro ⟨tau, htau⟩
    obtain ⟨sigma, hsigma⟩ := S2510_exists_lift tau
    refine ⟨sigma, ?_⟩
    rwa [← S2520cycleType_eq tau sigma hsigma]

/-- The twelve-cycle input in root-cycle form: an absolute Galois element whose
permutation of the twelve psi_5-roots over the algebraic closure is a
12-cycle.  This is stated with S2501RootPerm (definitionally S2480RootPerm). -/
def S2542RootCycleTwelveRequired : Prop :=
  ∃ sigma : S1725AbsoluteGalois,
    (S2501RootPerm sigma).cycleType = ({12} : Multiset ℕ)

/-- The same statement with S2480RootPerm. -/
theorem S2542RootCycleTwelve_iff_s2480RootCycle :
    S2542RootCycleTwelveRequired ↔
      ∃ sigma : S1725AbsoluteGalois,
        (S2480RootPerm sigma).cycleType = ({12} : Multiset ℕ) := by
  constructor
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma, ?_⟩
    rwa [S2501RootPerm_eq_s2480] at hsigma
  · rintro ⟨sigma, hsigma⟩
    refine ⟨sigma, ?_⟩
    rwa [← S2501RootPerm_eq_s2480] at hsigma

/-- **The S2440 twelve-cycle input is exactly the root 12-cycle statement**,
specialising the cycle-type dictionary at `{12}`. -/
theorem S2542RootCycleTwelve_iff_twelveCycleInput :
    S2542RootCycleTwelveRequired ↔ S2440TwelveCycleInputRequired :=
  (S2542RangeCycleType_iff_rootCycleType ({12} : Multiset ℕ)).symm

/-- The splitting-field form of the twelve-cycle input: an F'-automorphism of
the actual psi_5 splitting field S2132L whose permutation of the twelve roots
is a 12-cycle. -/
def S2542DivisionRootCycleTwelveRequired : Prop :=
  ∃ tau : S2132L ≃ₐ[S1720Field] S2132L,
    Equiv.Perm.cycleType (S2132DivisionRootEquiv tau) = ({12} : Multiset ℕ)

/-- **The splitting-field 12-cycle statement is exactly the closure root
12-cycle statement**, specialising the cycle-type dictionary at `{12}`. -/
theorem S2542DivisionRootCycleTwelve_iff_rootCycleTwelve :
    S2542DivisionRootCycleTwelveRequired ↔ S2542RootCycleTwelveRequired :=
  (S2542RootCycleType_iff_divisionRootCycleType ({12} : Multiset ℕ)).symm

/-- **The S2440 twelve-cycle input is exactly the splitting-field 12-cycle
statement.** -/
theorem S2542DivisionRootCycleTwelve_iff_twelveCycleInput :
    S2542DivisionRootCycleTwelveRequired ↔ S2440TwelveCycleInputRequired :=
  S2542DivisionRootCycleTwelve_iff_rootCycleTwelve.trans
    S2542RootCycleTwelve_iff_twelveCycleInput

/-- The splitting-field 12-cycle statement implies the target. -/
theorem S2542Target_of_divisionRootCycleTwelve
    (h : S2542DivisionRootCycleTwelveRequired) : S2542Target :=
  S2542Target_of_twelveCycle
    (S2542DivisionRootCycleTwelve_iff_twelveCycleInput.mp h)

/-! ## 4. The arithmetic residue route (S2470) and the mod-613 residue fact
(S2481) -/

/-- The arithmetic residue package sufficient for the target: a degree-twelve
irreducible residue datum for the actual psi_5 together with the root-to-range
transport.  Neither component is inhabited. -/
def S2542ArithmeticResidueRoute : Prop :=
  S2470ResidueCertificateRequired ∧ S2470RootToRangeTransport

/-- **The residue data plus the root-to-range transport imply the target**
(S2470). -/
theorem S2542Target_of_arithmeticResidueRoute
    (h : S2542ArithmeticResidueRoute) : S2542Target :=
  S2470Target_of_residueData_and_transport (Classical.choice h.1) h.2

/-- The certificate-plus-transport form of the residue route. -/
theorem S2542Target_of_certificate_and_transport
    (hcert : S2470ResidueCertificateRequired)
    (htrans : S2470RootToRangeTransport) : S2542Target :=
  S2470Target_of_certificate_and_transport hcert htrans

/-- The finite mod-13 irreducibility certificate of the S1987 report, a plain
Prop with no inhabitant (S2470). -/
def S2542Mod13Certificate : Prop := S2470Mod13Certificate

/-- The mod-613 irreducibility certificate used by the S2481 route, a plain
Prop with no inhabitant. -/
def S2542Mod613Certificate : Prop := S2481ResidueCertificate

/-- The actual residue-degree-one fact proved in S2481: the integer model of
the defining polynomial of F' splits completely modulo 613. -/
theorem S2542Mod613SourceSplits :
    (S2481HZ.map (Int.castRingHom (ZMod 613))).Splits :=
  S2481HMod613_splits

/-! ## 5. Consumers -/

/-- **Target plus the (10, 2) cycle-type input give the S1987 D5 large-image
target** (S2203). -/
theorem S2542D5LargeImageFive_of_target_and_cycle
    (hpair : S2542Target)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1987D5LargeImageFive :=
  S2203D5LargeImageFive_of_rangeHypotheses S1982Basis hcycle hpair

/-- **Target plus the S2480 (10, 2) root-cycle target give the S1987 D5
large-image target** (S2480). -/
theorem S2542D5LargeImageFive_of_target_and_S2480
    (hpair : S2542Target) (hcycle : S2480Target) :
    S1987D5LargeImageFive :=
  S2480D5LargeImageFive_of_firstMissing_and_pair
    (S2480FirstMissing_iff_target.mpr hcycle) hpair

/-- With the (10, 2) cycle-type input, the target gives the SL_2 containment
at S1982Basis (S2364). -/
theorem S2542ImageTail_of_target_and_cycle
    (hpair : S2542Target)
    (hcycle : S2203RangeCycleTypeRequired S1982Basis) :
    S1725ImageTail S1987Five S1982Basis :=
  S2364RangeImageTail_of_hypotheses S1982Basis hcycle hpair

/-- **The S2132 (10, 2) Frobenius-cycle input plus the target give the S1987
D5 large-image target** (S2520/S2480). -/
theorem S2542D5LargeImageFive_of_S2132_and_target
    (hcycle : S2132FrobInducesPairCycleType) (hpair : S2542Target) :
    S1987D5LargeImageFive :=
  S2480D5LargeImageFive_of_firstMissing_and_pair
    (S2520S2480FirstMissing_of_S2132 hcycle) hpair

/-- **The two arithmetic inputs give the S1987 D5 large-image target**: the
S2132 (10, 2) Frobenius cycle type and the splitting-field 12-cycle statement
for pair transitivity. -/
theorem S2542D5LargeImageFive_of_S2132_and_divisionRootCycleTwelve
    (hcycle : S2132FrobInducesPairCycleType)
    (hpair : S2542DivisionRootCycleTwelveRequired) :
    S1987D5LargeImageFive :=
  S2542D5LargeImageFive_of_S2132_and_target hcycle
    (S2542Target_of_divisionRootCycleTwelve hpair)

/-! ## 6. Axiom footprint -/

#print axioms S2542Target_unfolded
#print axioms S2542Target_iff_S2375
#print axioms S2542Target_iff_S2378
#print axioms S2542Target_iff_S2445
#print axioms S2542Target_iff_S2470
#print axioms S2542ExactFirstMissing_iff_S2375
#print axioms S2542Target_of_imageTail
#print axioms S2542Target_of_largeImage
#print axioms S2542Target_of_twelveCycle
#print axioms S2542Target_of_rangeTop
#print axioms S2542Target_of_sufficient_inputs
#print axioms S2542Target_iff_imageTail_of_cycleType102
#print axioms S2542RangeCycleType_iff_rootCycleType
#print axioms S2542RootCycleType_iff_divisionRootCycleType
#print axioms S2542RootCycleTwelve_iff_s2480RootCycle
#print axioms S2542RootCycleTwelve_iff_twelveCycleInput
#print axioms S2542DivisionRootCycleTwelve_iff_rootCycleTwelve
#print axioms S2542DivisionRootCycleTwelve_iff_twelveCycleInput
#print axioms S2542Target_of_divisionRootCycleTwelve
#print axioms S2542Target_of_arithmeticResidueRoute
#print axioms S2542Target_of_certificate_and_transport
#print axioms S2542Mod613SourceSplits
#print axioms S2542D5LargeImageFive_of_target_and_cycle
#print axioms S2542D5LargeImageFive_of_target_and_S2480
#print axioms S2542ImageTail_of_target_and_cycle
#print axioms S2542D5LargeImageFive_of_S2132_and_target
#print axioms S2542D5LargeImageFive_of_S2132_and_divisionRootCycleTwelve

end LeanFormal.IUT.XiFPaper.S2542PairTransitiveActual

end
