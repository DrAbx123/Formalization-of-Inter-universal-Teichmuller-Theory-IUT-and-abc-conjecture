import tmp.sheaf.xif.paper.S2441C9PaperCarrierActual
import tmp.sheaf.xif.paper.S694ThetaAverageNormalizationActual
import tmp.sheaf.xif.paper.ProcessionNormalizationWeightsActual

/-!
# S2451: actual Proposition 3.9(i) procession average for the concrete
S1895 q-pilot scalar

## Source statement

IUT III, Proposition 3.9, (i), p.116 (corpus lines III:6888--6893), defines
the procession-normalization of log-volumes on a procession of capsules as

> the average, over the various capsules under consideration.

IUT III, Remark 3.9.3, pp.119--120 (corpus lines III:7127--7150), identifies
the capsules of the procession with the index sets S±_{j+1}, j = 1,...,l*;
the project records the corresponding l* paper labels and the uniform paper
weight 1/l* in S694ThetaAverageNormalizationActual.  The project's S1940
states explicitly that these l* labels are the l* capsules of the paper
procession and that the diagonal capsule average of a constant readout is that
constant.

For the q-pilot side, IUT III, Definition 3.8, (i), p.112, and Corollary
3.12, pp.173--174, give the q-pilot object and its procession-normalized
log-volume -|log q|.  The concrete S1895/S1527 scalar is

  paperQPilotLogVolume D = -sourceBadQAbsLog (paperInput D).initial
    = -((S1487Cand.order : Real) * Real.log 5),

constructed in S1968 and re-used in S1979/S2441 (S2441 proves the concrete
sourceQPilotSignedLog = -(order_C3 * log 5) normalization).

## What this file constructs (actual)

1. A generic finite weighted average capsuleAverage, with the exact
   constant-average equality capsuleAverage_const under normalized weights.
2. The actual paper capsule index S2451PaperCapsuleLabel D, namely the l*
   classes of F_l^x (PaperThetaLabel D.l = Fin (lStar D.l.value)), with
   the actual paper weight 1/l* and its total-one theorem.
3. The diagonal q-pilot capsule family over the paper capsule index, constant
   at the concrete scalar paperQPilotLogVolume D, and the definition

     paperProcessionQPilotLogVolume D

   as its Proposition 3.9(i) paper capsule average.  The diagonal
   constant-average equality

     paperProcessionQPilotLogVolume D = paperQPilotLogVolume D

   is proved, together with the explicit 1/l* sum and the evaluations
   -(order_C3 * log 5), sourceQPilotSignedLog, and -deg (paperQPilotDivisor).
4. The full F_l^x label-indexed version

     paperProcessionQPilotLogVolumeFLabel D

   using the actual label group (ZMod l.value)^x of
   ProcessionNormalizationWeightsActual and the uniform weight 1/(l-1).
   Its diagonal constant-average equality is proved as well, and the two
   conventions are proved equal (paperProcessionQPilotLogVolume_eq_FLabel).
   This covers both the F_l^x label average of Theorem B/Corollary 3.12
   (as recorded in ProcessionNormalizationWeightsActual.md) and the
   paper's l* capsule average of Proposition 3.9(i) (as recorded in S694
   and S1940).

## Exact missing: the actual capsule-level q-pilot family

What is **not** constructed in the tree is the actual source-faithful
capsule-level q-pilot data: a family of q-pilot divisors/log-volumes indexed
by the paper capsules, together with the identification that the paper's
procession-normalized q-pilot log-volume is the weighted average of that
family.  The l* capsule index and the paper weights are actual (S694), and
the global q-pilot divisor/log-volume paperQPilotDivisor D /
paperQPilotLogVolume D is actual (S1968); the missing piece is the
*per-capsule image* of that global object and its average.

This file averages the concrete S1968/S2441 scalar paperQPilotLogVolume D.
It does not assert the further paper normalizations isolated in S2441's
S2441QPilotPaperNormalizationRequired (the 1/(2l) root factor, the 1/[F:Q]
normalized degree, and the local residue weights); those remain separate
exact missing data.  The only subject here is the Proposition 3.9(i)
procession average of the concrete scalar, in the diagonal case.

S2451ProcessionAverageRequired D records exactly those fields.  No
inhabitant is constructed or asserted: in particular, the diagonal
l*-capsule family of section 3 is a diagonal model whose per-capsule
q-pilot divisor is definitionally the same global divisor at every capsule,
not a construction of the paper's capsule-level q-pilot data.
S2451ProcessionAverageRequiredProp D is the corresponding
Nonempty proposition, also without a proof.

No forbidden proof placeholder, custom assumption, degenerate placeholder
type, empty type, arbitrary inhabitant, or assumption-only Nonempty gate is
used.  This file was
written under the serial build hold and was **not** compiled in this
session; the build/axiom probes at the end are to be run only after the
serial gate is released.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

open LeanFormal.IUT

local instance s2451GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s2451FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

namespace LeanFormal.IUT.XiFPaper.S2451ProcessionAverageActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.IUTIV.Estimates
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1895OIdentificationsActual
open LeanFormal.IUT.XiFPaper.S1927GlobalFrobenioidLogShellActual
open LeanFormal.IUT.XiFPaper.S1960QPilotAnchorActual
open LeanFormal.IUT.XiFPaper.S1968QVDeterminedQPilotActual
open LeanFormal.IUT.XiFPaper.S2441C9PaperCarrierActual
open LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual
open LeanFormal.IUT.XiFPaper.ProcessionNormalizationWeightsActual
open scoped BigOperators

universe u

/-! ## 0. The finite weighted capsule average -/

/-- The Proposition 3.9(i) weighted average of a finite capsule family.  The
weights are the actual normalized capsule weights; the values are the
capsule-normalized log-volumes. -/
noncomputable def capsuleAverage {ι : Type u} [Fintype ι]
    (weight : ι → Real) (value : ι → Real) : Real :=
  ∑ i, weight i * value i

/-- **Constant-average equality**: if the weights are normalized to total one,
the weighted average of a constant capsule family is that constant.  This is
the arithmetic form of the diagonal q-pilot image case of Proposition
3.9(i). -/
theorem capsuleAverage_const {ι : Type u} [Fintype ι]
    (weight : ι → Real) (c : Real)
    (hweight : (∑ i, weight i) = 1) :
    capsuleAverage weight (fun _ => c) = c := by
  unfold capsuleAverage
  rw [← Finset.sum_mul, hweight, one_mul]

/-! ## 1. The actual F_l^x label group and its uniform weight -/

/-- The actual procession label group F_l^x of an S1895 paper input,
namely (ZMod l.value)^x, of cardinality l - 1. -/
abbrev S2451Label (D : S1895PaperInput) : Type :=
  ProcessionLabel D.l

/-- The actual label cardinality is l - 1, not l and not l*. -/
theorem S2451Label_card (D : S1895PaperInput) :
    Fintype.card (S2451Label D) = D.l.value - 1 :=
  processionLabel_card D.l

/-- The actual uniform F_l^x weights total one. -/
theorem S2451Label_weight_total (D : S1895PaperInput) :
    (∑ _j : S2451Label D, processionLabelWeight D.l) = 1 :=
  processionLabelWeight_total D.l

/-- **Diagonal constant-average equality for the actual F_l^x labels**: a
label function constant on F_l^x has procession average equal to its
constant value.  This is the direct F_l^x specialization of the generic
constant capsule average. -/
theorem processionAverage_const (l : PrimeGeFive) (c : Real) :
    processionAverage l (fun _ : ProcessionLabel l => c) = c := by
  unfold processionAverage
  rw [← Finset.sum_mul, processionLabelWeight_total, one_mul]

/-! ## 2. The concrete S1895 q-pilot scalar -/

/-- The concrete S1895 q-pilot scalar is the actual source signed q-pilot
log-volume -sum_b |log q_b|. -/
theorem s2451_qPilotLogVolume_eq_source (D : S1895PaperInput) :
    paperQPilotLogVolume D =
      sourceQPilotSignedLog (paperInput D).initial :=
  paperQPilotLogVolume_eq_signedLog D

/-- The concrete S1895 q-pilot scalar is -(order_C3 * log 5). -/
theorem s2451_qPilotLogVolume_eq_orderC3 (D : S1895PaperInput) :
    paperQPilotLogVolume D = -((S1487Cand.order : ℝ) * Real.log 5) :=
  paperQPilotLogVolume_eq_orderC3 D

/-- The concrete S1895 q-pilot scalar is strictly negative. -/
theorem s2451_qPilotLogVolume_neg (D : S1895PaperInput) :
    paperQPilotLogVolume D < 0 :=
  paperQPilotLogVolume_neg D

/-! ## 3. The actual paper l* capsule index and weight

The paper's l* labels are the l* capsules of the procession (S694,
S1940; IUT III, Remark 3.9.3).  They are realized as
PaperThetaLabel l = Fin (lStar l.value). -/

/-- The actual paper capsule index: the l* classes of F_l^x, realized as
Fin (l*). -/
abbrev S2451PaperCapsuleLabel (D : S1895PaperInput) : Type :=
  LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual.PaperThetaLabel D.l

/-- The number of paper capsules is l* = (l - 1) / 2. -/
theorem S2451PaperCapsuleLabel_card (D : S1895PaperInput) :
    Fintype.card (S2451PaperCapsuleLabel D) = (D.l.value - 1) / 2 := by
  simpa [S2451PaperCapsuleLabel,
    LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual.PaperThetaLabel, lStar]
    using (Fintype.card_fin (lStar D.l.value))

/-- The actual paper capsule weight is 1/l*, and it totals one. -/
theorem S2451PaperCapsuleWeight_total (D : S1895PaperInput) :
    (∑ _i : S2451PaperCapsuleLabel D, paperThetaLabelWeight D.l) = 1 := by
  simpa [S2451PaperCapsuleLabel] using
    (LeanFormal.IUT.XiFPaper.S694ThetaAverageNormalizationActual.paperThetaLabelWeight_sum
      (l := D.l))

/-- The actual paper capsule weight is nonnegative. -/
theorem S2451PaperCapsuleWeight_nonneg (D : S1895PaperInput) :
    0 ≤ paperThetaLabelWeight D.l := by
  unfold paperThetaLabelWeight
  exact inv_nonneg.mpr (Nat.cast_nonneg _)

/-- The paper capsule average: the uniform 1/l* weighted average over the
actual l* paper capsule labels. -/
noncomputable def paperCapsuleAverage (D : S1895PaperInput)
    (value : S2451PaperCapsuleLabel D → Real) : Real :=
  capsuleAverage (fun _ : S2451PaperCapsuleLabel D => paperThetaLabelWeight D.l)
    value

/-- The paper capsule average of a constant family is that constant. -/
theorem paperCapsuleAverage_const (D : S1895PaperInput) (c : Real) :
    paperCapsuleAverage D (fun _ => c) = c := by
  unfold paperCapsuleAverage
  exact capsuleAverage_const
    (fun _ : S2451PaperCapsuleLabel D => paperThetaLabelWeight D.l)
    c (S2451PaperCapsuleWeight_total D)

/-! ## 4. The diagonal q-pilot procession and its Proposition 3.9(i) average -/

/-- The diagonal q-pilot capsule family over the actual paper capsule index:
the global q-pilot log-volume is the same in every capsule.  This is the
diagonal q-pilot image case of Proposition 3.9(i), not a construction of the
paper's non-diagonal capsule-level q-pilot data (recorded as missing in
section 7). -/
noncomputable def diagonalQPilotProcession (D : S1895PaperInput) :
    S2451PaperCapsuleLabel D → Real :=
  fun _ => paperQPilotLogVolume D

@[simp] theorem diagonalQPilotProcession_apply (D : S1895PaperInput)
    (i : S2451PaperCapsuleLabel D) :
    diagonalQPilotProcession D i = paperQPilotLogVolume D := rfl

/-- **The actual Proposition 3.9(i) procession average of the diagonal
concrete S1895 q-pilot scalar**: the paper's l*-capsule uniform average of
the constant global q-pilot log-volume. -/
noncomputable def paperProcessionQPilotLogVolume (D : S1895PaperInput) : Real :=
  paperCapsuleAverage D (diagonalQPilotProcession D)

/-- **The diagonal constant-average equality**: the Proposition 3.9(i)
procession average of the diagonal concrete S1895 q-pilot scalar is the
scalar itself. -/
theorem paperProcessionQPilotLogVolume_eq_diagonal (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D = paperQPilotLogVolume D := by
  unfold paperProcessionQPilotLogVolume diagonalQPilotProcession
  exact paperCapsuleAverage_const D (paperQPilotLogVolume D)

/-- The paper procession-normalized q-pilot log-volume is the S1968 q-pilot
log-volume. -/
theorem paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume
    (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D = paperQPilotLogVolume D :=
  paperProcessionQPilotLogVolume_eq_diagonal D

/-- The paper capsule average as the explicit uniform 1/l* sum. -/
theorem paperProcessionQPilotLogVolume_eq_sum (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D =
      paperThetaLabelWeight D.l *
        (∑ _i : S2451PaperCapsuleLabel D, paperQPilotLogVolume D) := by
  unfold paperProcessionQPilotLogVolume paperCapsuleAverage capsuleAverage
    diagonalQPilotProcession
  rw [Finset.mul_sum]

/-! ## 5. The full F_l^x label-indexed version -/

/-- The F_l^x label-indexed version of the diagonal q-pilot procession
average, using the actual full label group (ZMod l.value)^x and the uniform
weight 1/(l-1) of ProcessionNormalizationWeightsActual. -/
noncomputable def paperProcessionQPilotLogVolumeFLabel
    (D : S1895PaperInput) : Real :=
  processionAverage D.l (fun _ : ProcessionLabel D.l => paperQPilotLogVolume D)

/-- The F_l^x diagonal constant-average equality. -/
theorem paperProcessionQPilotLogVolumeFLabel_eq_diagonal
    (D : S1895PaperInput) :
    paperProcessionQPilotLogVolumeFLabel D = paperQPilotLogVolume D := by
  unfold paperProcessionQPilotLogVolumeFLabel
  exact processionAverage_const (l := D.l) (paperQPilotLogVolume D)

/-- The F_l^x version equals the S1968 q-pilot log-volume. -/
theorem paperProcessionQPilotLogVolumeFLabel_eq_paperQPilotLogVolume
    (D : S1895PaperInput) :
    paperProcessionQPilotLogVolumeFLabel D = paperQPilotLogVolume D :=
  paperProcessionQPilotLogVolumeFLabel_eq_diagonal D

/-- The F_l^x average as the explicit (1/(l-1)) * sum formula. -/
theorem paperProcessionQPilotLogVolumeFLabel_eq_sum_div
    (D : S1895PaperInput) :
    paperProcessionQPilotLogVolumeFLabel D =
      (∑ _j : ProcessionLabel D.l, paperQPilotLogVolume D) /
        (D.l.value - 1 : Real) := by
  unfold paperProcessionQPilotLogVolumeFLabel
  exact processionAverage_formula D.l (fun _ => paperQPilotLogVolume D)

/-- **The l* paper capsule average and the full F_l^x label average agree
on the diagonal q-pilot scalar.**  Both are different normalizations of the
same constant scalar, hence both equal it; this records the two source
conventions explicitly. -/
theorem paperProcessionQPilotLogVolume_eq_FLabel (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D = paperProcessionQPilotLogVolumeFLabel D := by
  rw [paperProcessionQPilotLogVolume_eq_diagonal,
    paperProcessionQPilotLogVolumeFLabel_eq_diagonal]

/-! ## 6. Evaluations of the paper procession q-pilot log-volume -/

/-- The procession-normalized q-pilot log-volume is -(order_C3 * log 5). -/
theorem paperProcessionQPilotLogVolume_eq_orderC3 (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D = -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume,
    paperQPilotLogVolume_eq_orderC3]

/-- The same evaluation from the S2441 concrete normalization
sourceQPilotSignedLog = -(order_C3 * log 5). -/
theorem paperProcessionQPilotLogVolume_eq_s2441 (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D = -((S1487Cand.order : ℝ) * Real.log 5) := by
  rw [paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume,
    s2451_qPilotLogVolume_eq_source]
  exact s2441_concrete_normalization D

/-- The procession-normalized q-pilot log-volume is the actual source signed
q-pilot log-volume. -/
theorem paperProcessionQPilotLogVolume_eq_source (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D =
      sourceQPilotSignedLog (paperInput D).initial := by
  rw [paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume,
    paperQPilotLogVolume_eq_signedLog]

/-- The procession-normalized q-pilot log-volume is the negative degree of the
actual q-pilot divisor. -/
theorem paperProcessionQPilotLogVolume_eq_neg_deg (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D =
      - IUTIVArithmeticDivisor.deg (F := PaperFmod D) (paperQPilotDivisor D) := by
  rw [paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume,
    paperQPilotLogVolume_eq_neg_deg]

/-- The procession-normalized q-pilot log-volume is strictly negative. -/
theorem paperProcessionQPilotLogVolume_neg (D : S1895PaperInput) :
    paperProcessionQPilotLogVolume D < 0 := by
  rw [paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume]
  exact paperQPilotLogVolume_neg D

/-! ## 7. Exact missing: the actual capsule-level q-pilot family

The paper capsule index S2451PaperCapsuleLabel D and the paper weight
1/l* are actual (section 3), and the global q-pilot divisor/log-volume is
actual (S1968).  What is missing is the source-faithful *per-capsule* q-pilot
family: the q-pilot divisor imaged in each capsule, its log-volume, and the
identification of the paper's procession-normalized q-pilot log-volume with
the weighted average of that family.  The structure below records exactly
these fields.  No inhabitant is constructed or asserted. -/

/-- **Exact missing paper-level capsule family/weights for the concrete S1895
q-pilot scalar.**

The l* capsule index and the uniform paper weight 1/l* are the actual
ones from S694/S1940.  The fields below are the missing per-capsule q-pilot
data and the missing identification of the paper average with the concrete
scalar:

* the q-pilot arithmetic divisor imaged in each capsule;
* the q-pilot log-volume carried by each capsule, as the negative degree of
  its divisor;
* the actual paper capsule weights (normalized to total one);
* the weighted Proposition 3.9(i) average and its identification with the
  actual global scalar paperQPilotLogVolume D.

The per-capsule divisors are not forced to be the global divisor: the
non-diagonal capsule-level q-pilot image is exactly the missing data.  The
diagonal model of section 4 is the special case in which every per-capsule
divisor is the global one.

The diagonal l*-capsule model of section 4 supplies the arithmetic
constant-average equality but not an inhabitant of this structure: it does
not construct the source-faithful per-capsule q-pilot divisor family, and its
per-capsule divisor is simply the same global divisor by definition.  No
inhabitant is asserted here.

This structure is an interface record, not a proof that no inhabitant
exists: its fields are the exact source data and identifications that the
paper construction must supply.  The point is that the tree does not
construct them, so no source-faithful inhabitant is available. -/
structure S2451ProcessionAverageRequired (D : S1895PaperInput) where
  /-- the q-pilot arithmetic divisor imaged in each paper capsule -/
  qPilotDivisor :
    S2451PaperCapsuleLabel D → IUTIVArithmeticDivisor (PaperFmod D)
  /-- the q-pilot log-volume carried by each paper capsule -/
  capsuleLogVolume : S2451PaperCapsuleLabel D → Real
  /-- it is the negative degree of the capsule's q-pilot divisor -/
  capsuleLogVolume_eq : ∀ i,
    capsuleLogVolume i =
      - IUTIVArithmeticDivisor.deg (F := PaperFmod D) (qPilotDivisor i)
  /-- the actual paper capsule weight 1/l* -/
  capsuleWeight : S2451PaperCapsuleLabel D → Real
  /-- the weights are the actual paper weights -/
  capsuleWeight_eq : ∀ i, capsuleWeight i = paperThetaLabelWeight D.l
  /-- the actual paper weights are nonnegative -/
  capsuleWeight_nonneg : ∀ i, 0 ≤ capsuleWeight i
  /-- the actual paper weights total one -/
  capsuleWeight_total : (∑ i, capsuleWeight i) = 1
  /-- the Proposition 3.9(i) procession average of the capsule family -/
  processionAverage : Real
  /-- the average is the weighted capsule sum -/
  processionAverage_eq :
    processionAverage = capsuleAverage capsuleWeight capsuleLogVolume
  /-- **the missing identification**: the paper's procession-normalized
      q-pilot log-volume is this capsule average -/
  processionAverage_eq_paper :
    processionAverage = paperQPilotLogVolume D

/-- The exact missing paper-level capsule family/weights, as a proposition.
No inhabitant is proved. -/
def S2451ProcessionAverageRequiredProp (D : S1895PaperInput) : Prop :=
  Nonempty (S2451ProcessionAverageRequired D)

/-! ## 8. Build/axiom probes

These are to be run only after the serial build gate is released; this file
was written without compilation. -/

#print axioms capsuleAverage_const
#print axioms processionAverage_const
#print axioms paperCapsuleAverage_const
#print axioms paperProcessionQPilotLogVolume
#print axioms paperProcessionQPilotLogVolume_eq_diagonal
#print axioms paperProcessionQPilotLogVolume_eq_paperQPilotLogVolume
#print axioms paperProcessionQPilotLogVolume_eq_sum
#print axioms paperProcessionQPilotLogVolumeFLabel
#print axioms paperProcessionQPilotLogVolumeFLabel_eq_diagonal
#print axioms paperProcessionQPilotLogVolume_eq_FLabel
#print axioms paperProcessionQPilotLogVolume_eq_orderC3
#print axioms paperProcessionQPilotLogVolume_eq_s2441
#print axioms paperProcessionQPilotLogVolume_eq_source
#print axioms paperProcessionQPilotLogVolume_eq_neg_deg
#print axioms paperProcessionQPilotLogVolume_neg

#check S2451ProcessionAverageRequired
#check S2451ProcessionAverageRequiredProp

end LeanFormal.IUT.XiFPaper.S2451ProcessionAverageActual

end
