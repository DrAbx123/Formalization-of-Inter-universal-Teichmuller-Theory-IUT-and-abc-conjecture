/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: LeanFormal contributors
-/
import tmp.sheaf.xif.paper.S2470PairTransitiveFinalActual
import tmp.sheaf.xif.paper.S2480CycleTypeRepairActual
import tmp.sheaf.xif.paper.S2481PairTransitiveHardActual
import tmp.sheaf.xif.paper.S2501MatrixPairEquivActual
import tmp.sheaf.xif.paper.S2510AbsoluteLiftActual
import tmp.sheaf.xif.paper.S2520RootCycleTransferActual

/-!
# S2532: the actual pair-transitivity target at `S1982Basis`

## The target

  `S2532Target := S2203RangePairTransitiveRequired S1982Basis`
    = `PairTransitive
        (range (galoisLTorsionMatrixRepresentation S1987Five S1982Basis))`.

## Status: BLOCKED, no unconditional inhabitant

None of the three sufficient inputs available in the tree is proved:

* `S1725ImageTail S1987Five S1982Basis` (the `SL_2(F_5)` containment),
* `S2440TwelveCycleInputRequired` (a 12-cycle in the actual range),
* `S2378RangeTopRequired` (`range = top`).

This file does not assert the target; it contains no sorry, axiom, opaque
placeholder, `True`/`PUnit` gate, or renamed hypothesis.  It records:

1. the target is definitionally the S2470/S2375/S2440/S2481 target;
2. each of the three sufficient inputs implies the target (unconditional
   bridges, from the compiled S2440/S2470);
3. under the paper's other missing input, the `(10, 2)` cycle type, the
   target is *equivalent* to the large-image tail `S1725ImageTail`
   (S2440), hence the large-image statement is the exact remaining input on
   that route and cannot be replaced by a smaller one;
4. **new**: the former Dedekind--Frobenius transport gap
   `S2470RootToRangeTransport` is closed unconditionally
   (`S2532RootToRangeTransport`).  A twelve-cycle on the roots of any
   integral model `f` of a nonzero multiple of `psi_5` is lifted to the
   absolute Galois group by S2510, transported to the roots in the algebraic
   closure by S2520, and identified with the matrix pair action by
   S2480/S2501.  The root set of `f` over `F'` is the root set of
   `psi_5` because `f` is a nonzero scalar multiple of `psi_5`.
   Consequently the concrete residue datum `S2470ActualResidueData` implies
   the twelve-cycle input and the target, and the only remaining input of this
   route is the concrete arithmetic datum
   `S2532ResidueCertificateRequired = Nonempty S2470ActualResidueData`:
   an integral model `f` of a nonzero multiple of `psi_5`, a maximal prime
   `p` of `O_{F'}`, and a prime `P` of the actual 5-division field above
   `p` such that the reduction of `f` at `p` is separable and irreducible
   of degree twelve.  That datum is not formalized in the tree.

The mod-29 factorization of S2132 is a `{2, 10}` factorization, and the
mod-613 computation of S2481 proves only that the source field `F'` splits
completely at 613; neither supplies a degree-twelve irreducible reduction of
`psi_5`.  Hence no unconditional inhabitant of the target is produced.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2532PairTransitiveActual

open Polynomial NumberField
open LeanFormal.IUT.XiFPaper.S2470PairTransitiveFinalActual
open LeanFormal.IUT.XiFPaper.S2480CycleTypeRepairActual
open LeanFormal.IUT.XiFPaper.S2481PairTransitiveHardActual
open LeanFormal.IUT.XiFPaper.S2501MatrixPairEquivActual
open LeanFormal.IUT.XiFPaper.S2510AbsoluteLiftActual
open LeanFormal.IUT.XiFPaper.S2520RootCycleTransferActual
open LeanFormal.IUT.XiFPaper.S2440RangePairTransitiveSubagentActual
open LeanFormal.IUT.XiFPaper.S2375RangePairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2378ActualPairTransitiveActual
open LeanFormal.IUT.XiFPaper.S2449D5FinalStatusActual
open LeanFormal.IUT.XiFPaper.S2203D5RangeActual
open LeanFormal.IUT.XiFPaper.S1987D5LargeImageFiveActual
open LeanFormal.IUT.XiFPaper.S1982D5FiveActual
open LeanFormal.IUT.XiFPaper.S1725SourceTorsionFPrimeActual
open LeanFormal.IUT.XiFPaper.S1720SourceArithmeticActual
open LeanFormal.IUT.XiFPaper.S2057DedekindFrobBridgeActual
open LeanFormal.IUT.XiFPaper.S2132FrobCycleActual
open LeanFormal.IUT.XiFPaper.S2056Psi5RootsActual
open LeanFormal.IUT.XiFPaper.S2167DedekindFrobCycleActual

/-! ## 1. The target and its equivalent names -/

/-- The actual target: pair transitivity of the mod-5 matrix range at the
selected rank-two basis `S1982Basis`. -/
def S2532Target : Prop := S2203RangePairTransitiveRequired S1982Basis

/-- The target is definitionally the S2470 target. -/
theorem S2532Target_iff_S2470 : S2532Target ↔ S2470Target := Iff.rfl

/-- The target is definitionally the S2375 exact first missing. -/
theorem S2532Target_iff_S2375 : S2532Target ↔ S2375ExactFirstMissing := Iff.rfl

/-- The target is definitionally the S2440 exact first missing. -/
theorem S2532Target_iff_S2440 : S2532Target ↔ S2440ExactFirstMissing := Iff.rfl

/-- The target is definitionally the S2481 target. -/
theorem S2532Target_iff_S2481 : S2532Target ↔ S2481Target := Iff.rfl

/-! ## 2. The three sufficient inputs of the tree -/

/-- The `SL_2(F_5)` containment at `S1982Basis` implies the target. -/
theorem S2532Target_of_imageTail
    (h : S1725ImageTail S1987Five S1982Basis) : S2532Target :=
  S2470Target_of_imageTail h

/-- A twelve-cycle in the actual range implies the target. -/
theorem S2532Target_of_twelveCycle
    (h : S2440TwelveCycleInputRequired) : S2532Target :=
  S2470Target_of_twelveCycle h

/-- The large-image statement of S1987 implies the target. -/
theorem S2532Target_of_largeImage
    (h : S1987D5LargeImageFive) : S2532Target :=
  S2470Target_of_largeImage h

/-- Full range implies the target. -/
theorem S2532Target_of_rangeTop
    (h : S2378RangeTopRequired) : S2532Target :=
  S2470Target_of_rangeTop h

/-- The S2449 exact first missing contains the target. -/
theorem S2532Target_of_S2449
    (h : S2449D5ExactFirstMissing) : S2532Target :=
  S2470Target_of_S2449 h

/-! ## 3. The exact form under the paper's cycle-type input -/

/-- Under the `(10, 2)` cycle-type input, the target is *equivalent* to the
large-image tail at the selected basis.  This is the exact statement of what
remains on this route: the large-image containment. -/
theorem S2532Target_iff_imageTail_of_cycleType102
    (h102 : S2203RangeCycleTypeRequired S1982Basis) :
    S2532Target ↔ S1725ImageTail S1987Five S1982Basis :=
  S2440RangePairTransitive_iff_imageTail_of_cycleType102 h102

/-- Under the cycle-type input, the target is equivalent to the frozen S1987
large-image target itself. -/
theorem S2532Target_iff_largeImage_of_cycleType102
    (h102 : S2203RangeCycleTypeRequired S1982Basis) :
    S2532Target ↔ S1987D5LargeImageFive :=
  (S2532Target_iff_imageTail_of_cycleType102 h102).trans
    (S1987D5LargeImageFive_iff_tail_basis).symm

/-! ## 4. The twelve-cycle exact missing -/

/-- The twelve-cycle input, taken as the exact missing statement of the
twelve-cycle route.  It is literally `S2440TwelveCycleInputRequired`. -/
def S2532ExactMissing : Prop := S2440TwelveCycleInputRequired

/-- The exact missing implies the target. -/
theorem S2532Target_of_exactMissing (h : S2532ExactMissing) : S2532Target :=
  S2470Target_of_twelveCycle h

/-- The root-cycle form of the exact missing: some absolute Galois element acts
on the twelve actual roots of `psi_5` as a twelve-cycle. -/
def S2532RootTwelveCycleRequired : Prop :=
  ∃ σ : S1725AbsoluteGalois,
    (S2480RootPerm σ).cycleType = ({12} : Multiset ℕ)

/-- The twelve-cycle input is exactly the root twelve-cycle statement, by the
S2480 matrix-pair/root cycle-type identification. -/
theorem S2532ExactMissing_iff_rootCycle :
    S2532ExactMissing ↔ S2532RootTwelveCycleRequired := by
  constructor
  · rintro ⟨h, hh, hc⟩
    obtain ⟨σ, rfl⟩ := MonoidHom.mem_range.mp hh
    exact ⟨σ, by rw [← S2480PairMatrix_cycleType σ]; exact hc⟩
  · rintro ⟨σ, hc⟩
    exact ⟨_, MonoidHom.mem_range.mpr ⟨σ, rfl⟩,
      by rw [S2480PairMatrix_cycleType σ]; exact hc⟩

/-! ## 5. The Dedekind--Frobenius transport gap is closed

S2470 produces a twelve-cycle on the roots of an integral model of `psi_5` in
the actual 5-division field.  The root set of such a model is the root set of
`psi_5` itself (the model is a nonzero scalar multiple of `psi_5` over
`F'`).  S2510 lifts the splitting-field automorphism to the absolute Galois
group, S2520 transfers the root cycle type to the roots in the algebraic
closure, and S2501/S2480 identify the closure root permutation with the matrix
action on the twelve pairs.  This proves the former missing transport
`S2470RootToRangeTransport` unconditionally. -/

/-- The root set of an integral model of a nonzero multiple of `psi_5` over
`F'` is the root set of `psi_5`, because the scalar is nonzero. -/
theorem S2532rootSet_eq
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
        C c * S2057Psi5F) :
    (f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
        S2057FiveDivisionField =
      S2057Psi5F.rootSet S2057FiveDivisionField := by
  obtain ⟨c, hc, hc_eq⟩ := hpsi
  rw [hc_eq]
  ext x
  simp only [Polynomial.mem_rootSet']
  constructor
  · rintro ⟨hne, hx⟩
    refine ⟨?_, ?_⟩
    · intro h0
      apply hne
      rw [Polynomial.map_mul, Polynomial.map_C, h0, mul_zero]
    · rw [Polynomial.aeval_mul, Polynomial.aeval_C] at hx
      rcases mul_eq_zero.mp hx with h | h
      · exact absurd ((algebraMap S1720Field S2057FiveDivisionField).injective (by simpa using h)) hc
      · exact h
  · rintro ⟨hne, hx⟩
    refine ⟨?_, ?_⟩
    · rw [Polynomial.map_mul, Polynomial.map_C]
      refine mul_ne_zero (Polynomial.C_ne_zero.mpr ?_) hne
      intro h0
      exact hc ((algebraMap S1720Field S2057FiveDivisionField).injective (by simpa using h0))
    · rw [Polynomial.aeval_mul, Polynomial.aeval_C, hx, mul_zero]

/-- The root set of such an integral model is identified with the twelve roots
of `psi_5` in the actual 5-division field. -/
noncomputable def S2532RootEquiv
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
        C c * S2057Psi5F) :
    (f.map (algebraMap (RingOfIntegers S1720Field) S1720Field)).rootSet
        S2057FiveDivisionField ≃ S2132DivisionRoots :=
  Equiv.subtypeEquivRight (fun x => by
    rw [S2532rootSet_eq f hpsi])

/-- The Dedekind--Frobenius root cycle type of an integral model is the cycle
type of the permutation of the twelve `psi_5` roots induced by the same
automorphism. -/
theorem S2532rootCycleType_eq
    (f : (RingOfIntegers S1720Field)[X])
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
        C c * S2057Psi5F)
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (σ : Gal(S2057FiveDivisionField/S1720Field)) :
    rootCycleType S1720Field S2057FiveDivisionField f hsplit σ =
      (show Equiv.Perm S2132DivisionRoots from S2132DivisionRootEquiv σ).cycleType := by
  classical
  unfold rootCycleType
  let e := S2532RootEquiv f hpsi
  let g : Equiv.Perm S2132DivisionRoots := S2132DivisionRootEquiv σ
  have hperm : e.permCongr
      (rootPerm S1720Field S2057FiveDivisionField f hsplit σ) = g := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [Equiv.permCongr_apply]
    rfl
  have hcy := S2132cycleType_permCongr e
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ)
  rw [hperm] at hcy
  rw [show Classical.decEq ((map (algebraMap (RingOfIntegers S1720Field) S1720Field) f).rootSet S2057FiveDivisionField) = (fun a b => Subtype.instDecidableEq a b) from Subsingleton.elim _ _]
  rw [← S2132cycleType_permCongr e
    (rootPerm S1720Field S2057FiveDivisionField f hsplit σ), hperm]

/-- **The former S2470 transport gap is a theorem.**  A twelve-cycle of a
splitting-field automorphism on the roots of an integral model of a nonzero
multiple of `psi_5` produces a twelve-cycle in the actual mod-5 matrix range.
This is the composition S2470 (Dedekind--Frobenius), S2510 (absolute lift),
S2520 (splitting-field/closure root transport), and S2480/S2501
(root/matrix-pair identification). -/
theorem S2532RootToRangeTransport : S2470RootToRangeTransport := by
  intro f hmonic hsplit σ hpsi h12
  obtain ⟨τ, hτ⟩ := S2510_exists_lift σ
  refine ⟨S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis τ,
    MonoidHom.mem_range.mpr ⟨τ, rfl⟩, ?_⟩
  rw [S2501PairMatrix_cycleType τ]
  rw [← S2520cycleType_eq σ τ hτ]
  rw [← S2532rootCycleType_eq f hpsi hsplit σ]
  exact h12

/-- The concrete residue datum gives a twelve-cycle in the actual range. -/
theorem S2532ExactMissing_of_residueData (D : S2470ActualResidueData) :
    S2532ExactMissing := by
  obtain ⟨σ, hσ⟩ := D.rootTwelveCycle
  exact S2532RootToRangeTransport D.f D.f_monic D.f_splits σ D.f_psi5 hσ

/-- The concrete residue datum implies the actual target. -/
theorem S2532Target_of_residueData (D : S2470ActualResidueData) :
    S2532Target :=
  S2532Target_of_exactMissing (S2532ExactMissing_of_residueData D)

/-- The same conclusion directly through S2470's residue-data theorem.  The
transport argument is supplied by `S2532RootToRangeTransport`, so no transport
hypothesis remains. -/
theorem S2532Target_of_residueData_via_S2470 (D : S2470ActualResidueData) :
    S2532Target :=
  S2470Target_of_residueData_and_transport D S2532RootToRangeTransport

/-- The exact remaining arithmetic input of the residue route, as a plain Prop:
a prime and a monic integral model of a nonzero multiple of `psi_5` with
separable irreducible degree-twelve reduction.  It is definitionally
`S2470ResidueCertificateRequired`. -/
def S2532ResidueCertificateRequired : Prop := Nonempty S2470ActualResidueData

/-- The residue certificate is the S2470 residue certificate. -/
theorem S2532ResidueCertificateRequired_iff_S2470 :
    S2532ResidueCertificateRequired ↔ S2470ResidueCertificateRequired :=
  Iff.rfl

/-- The residue certificate implies the twelve-cycle exact missing. -/
theorem S2532ExactMissing_of_residueCertificate
    (h : S2532ResidueCertificateRequired) : S2532ExactMissing :=
  h.elim S2532ExactMissing_of_residueData

/-- The residue certificate implies the actual target. -/
theorem S2532Target_of_residueCertificate
    (h : S2532ResidueCertificateRequired) : S2532Target :=
  h.elim S2532Target_of_residueData

/-- The same through S2470's certificate theorem, with the transport discharged:
`S2470ResidueCertificateRequired` alone now implies the target. -/
theorem S2532Target_of_residueCertificate_via_S2470
    (h : S2470ResidueCertificateRequired) : S2532Target :=
  S2470Target_of_certificate_and_transport h S2532RootToRangeTransport

/-! ## 6. Axiom footprint -/

#print axioms S2532Target_iff_S2470
#print axioms S2532Target_iff_S2375
#print axioms S2532Target_iff_S2440
#print axioms S2532Target_iff_S2481
#print axioms S2532Target_of_imageTail
#print axioms S2532Target_of_twelveCycle
#print axioms S2532Target_of_largeImage
#print axioms S2532Target_of_rangeTop
#print axioms S2532Target_iff_imageTail_of_cycleType102
#print axioms S2532Target_iff_largeImage_of_cycleType102
#print axioms S2532Target_of_exactMissing
#print axioms S2532ExactMissing_iff_rootCycle
#print axioms S2532rootSet_eq
#print axioms S2532RootEquiv
#print axioms S2532rootCycleType_eq

/-- **Non-monic form of the root-to-range transport.**  The monicity hypothesis
is not used by the transport: only the nonzero-multiple model condition, the
root cycle type and splitting are relevant. -/
theorem S2532RootToRangeTransportNonmonic
    (f : (RingOfIntegers S1720Field)[X])
    (hsplit : (f.map
      (algebraMap (RingOfIntegers S1720Field) S2057FiveDivisionField)).Splits)
    (sigma : Gal(S2057FiveDivisionField/S1720Field))
    (hpsi : ∃ c : S1720Field, c ≠ 0 ∧
      f.map (algebraMap (RingOfIntegers S1720Field) S1720Field) =
        C c * S2057Psi5F)
    (h12 : rootCycleType S1720Field S2057FiveDivisionField f hsplit sigma =
      ({12} : Multiset ℕ)) :
    S2440TwelveCycleInputRequired := by
  obtain ⟨tau, htau⟩ := S2510_exists_lift sigma
  refine ⟨S1720Curve.galoisLTorsionMatrixRepresentation S1987Five S1982Basis tau,
    MonoidHom.mem_range.mpr ⟨tau, rfl⟩, ?_⟩
  rw [S2501PairMatrix_cycleType tau]
  rw [← S2520cycleType_eq sigma tau htau]
  rw [← S2532rootCycleType_eq f hpsi hsplit sigma]
  exact h12
#print axioms S2532RootToRangeTransportNonmonic

#print axioms S2532RootToRangeTransport
#print axioms S2532ExactMissing_of_residueData
#print axioms S2532Target_of_residueData
#print axioms S2532Target_of_residueData_via_S2470
#print axioms S2532ResidueCertificateRequired
#print axioms S2532ExactMissing_of_residueCertificate
#print axioms S2532Target_of_residueCertificate
#print axioms S2532Target_of_residueCertificate_via_S2470

end LeanFormal.IUT.XiFPaper.S2532PairTransitiveActual

end
