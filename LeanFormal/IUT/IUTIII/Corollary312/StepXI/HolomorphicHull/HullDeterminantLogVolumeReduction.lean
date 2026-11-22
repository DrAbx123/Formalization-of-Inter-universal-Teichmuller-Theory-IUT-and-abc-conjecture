import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.Volume
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.SourceHullCompactnessReduction
import LeanFormal.IUT.IUTIII.Corollary312.StepXI.HolomorphicHull.IQCarrierConcreteModel
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Algebra.Order.Star.Real

/-!
# Reduction pass for `IUT-III.holomorphic-hull-determinant-log-volume`
(task hull-determinant-log-volume-20261016)

Frozen target: the `Obligation` `hullDeterminantLogVolume` of
`HolomorphicHull/Volume.lean:179` ("Finite positive-packet determinant, tensor,
rescaling, and hull-average identities are proved; the paper's holomorphic hull
and source-facing log-volume construction remain pending"), whose source is
IUT III, Corollary 3.12 proof, Steps (xi-d)--(xi-g).

## Original-text references (corpus transcription `papers/motizuki_corpus/text/`)

* IUT III, Corollary 3.12 (Log-volume Estimates for Theta-Pilot Objects),
  statement: `Inter-universal Teichmuller Theory III.txt:10325-10360`
  (paper pp. 173-174): `-|log(Theta)|` is the procession-normalized
  mono-analytic log-volume (average over `j in F_l^star`) of the holomorphic
  hull of the union of the possible images of a Theta-pilot object;
  `-|log(q)| in R`; `|log(q)| > 0`; conclusion `-|log(Theta)| in R` and
  `-|log(Theta)| >= -|log(q)|`, equivalently `C_Theta >= -1` for any
  `C_Theta in R` with `-|log(Theta)| <= C_Theta * |log(q)|`.
* IUT III, Remark 3.9.5, (i): `:7654-7681` (paper pp. 126-127): the
  holomorphic hull of a region is the smallest subset of the form `lambda * O`
  containing it, each component of `lambda` nonzero; non-relatively-compact
  regions are sent to `IQ((-))`.
* IUT III, Remark 3.9.5, (ii): `:7681-7723`: `P` (direct product regions),
  `H` (hulls), `phi : P -> H` with (P1) `phi(H) = H`, (P2) `P in phi(P)`,
  (P3) monotonicity, and the intersection formula `phi(P) = Inter_{H >= P} H`.
* IUT III, Remark 3.9.5, (iii): `:7723-7750`: log-volumes `mu_log` and
  `mu_log(phi(P)) >= mu_log(H) >= mu_log(P)` for the hull approximants.
* IUT III, Remark 3.9.5, (vii): `:7875-8300` (paper pp. 131-134):
  (Ob1) tensor packets of log-shells; (Ob2) regions to arithmetic vector
  bundles via the hull; (Ob3) `det (x) M (-)`; (Ob3-1-1) positive tensor powers
  of determinants of the direct summands, consistent with the weighted-sum
  log-volume (weights = products of `N_v`); (Ob3-1-2) tensoring with the
  inverse determinant of the structure sheaf; (Ob3-2) the positive integer
  `M`; (Ob3-3) the arithmetic degree of the `det (x) M` output is (with
  suitable normalization factors) the log-volume of the original arithmetic
  vector bundle; (Ob4) `M`-th tensor powers of the q-pilot object.
* IUT III, Step (xi-d): `:10823-10864` (paper pp. 182-183): the determinant
  (suitable positive tensor power) of the localizations of arithmetic vector
  bundles of rank > 1, and the suitably normalized log-volume applied to the
  regions `1,U` and the q-pilot region; `-|log(Theta)|` is the (negative)
  log-volume of `1,U`; `-|log(q)|` is the log-volume of the q-pilot region;
  the tensor packets of log-shells constitute `1,U`. Step (xi-e):
  `:10864-10888`. Step (xi-f): `:10888-10899`: `-|log(q)|` lies in
  `R_{<= -|log(Theta)|}`, hence `-|log(q)| <= -|log(Theta)|`, hence
  `C_Theta >= -1`. Step (xi-g): `:10899-10907`.
* IUT III, Proposition 3.9, (i), (iii), (iv): `:6838-7010`; Remark 3.1.1,
  (iii), (iv) (direct product regions; weighted log-volume sums).

## What this file proves and what it only cards

The four finite identity families of the frozen target are frozen as
`HullDeterminantLogVolumeFrozenSpec` and instantiated by the existing theorems
of `Volume.lean`; they are the diagonal-matrix specializations of the standard
real linear-algebra determinant laws, which are proved here in log form
(`matrixLogDet_mul_posDef`, `matrixLogDet_smul_posDef`,
`matrixLogDet_kronecker_posDef`, `matrixLogDet_pow_posDef`; the last is the
algebraic mirror of the `det (x) M` bookkeeping of (Ob3-2)/(Ob3-3)).

The paper's source-side content is NOT proved here; it is frozen as named
cards using the paper's objects, together with everything provable from the
card fields: the hull adjunction `HolomorphicHullAdjunction` (theorems (P1),
(P3), and the intersection formula), the `det (x) M` bookkeeping
`DetTensorPowerLogVolumeBookkeeping`, and the final comparison
`Cor312ComparisonData`, whose numeric conclusion `cor312CThetaLowerBound` is
proved outright with the hypothesis `|log(q)| > 0` of Corollary 3.12 explicit.

## Honest boundaries (must not be overstated)

* The calibration instances (`d5CarrierModelHullAdjunction`, and the scalar
  log-degree model of `DetTensorPowerLogVolumeBookkeeping`) are consistency
  witnesses on the real line / scalar log-degrees in the shape of the d5
  real-line carrier model (`IQCarrierConcreteModel.lean`, hull = explicit
  bounded `Set.Iic 0` shell). They are NOT the paper's carrier
  `IQ(S+-_{j+1}; n, D^vdash_{vQ})`, provide no theta-pilot carrier, and do not
  discharge Card-HULLREAL.
* O1: `sourceHullVolume_eq_top_of_degreeFaithful`
  (`SourceImageHullVolume.lean:428`) shows that under pointwise degree
  faithfulness the value-realized hull volume is `top`; any lemma requiring
  that faithfulness premise together with a finiteness premise has an empty
  premise space (`top < top` is unsatisfiable). No such lemma is used or
  strengthened here.
* The repo's `IQHullLogVolumeInterface` keeps log-volumes in `ENNReal`
  (positive magnitudes) while the paper writes signed values `-|log(Theta)|`;
  the two conventions are kept separate and the translation is recorded in the
  cards.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedDecidableInType false

namespace LeanFormal.IUT

open scoped BigOperators
open scoped Kronecker

noncomputable section

universe u v
/-! ## 1. Frozen specification of the Volume.lean:179 interface

The fields below restate, at their exact quantifier shape, the four finite
identity families of the frozen interface layer.  They are the diagonal-matrix
(positive-packet) reductions of: the determinant bookkeeping of Step (xi-d) /
(Ob3-3) for `det_eq_prod` and `log_eq_log_det`; the tensor packets of
log-shells of (Ob1) / (xi-d) for `det_tensor` and `log_tensor`; the
`lambda * O` hull form of Remark 3.9.5, (i), for `det_rescale` and
`log_rescale`; and the procession-normalized average of Corollary 3.12 with
the hull sandwich `mu_log(phi(P)) >= mu_log(P)` of Remark 3.9.5, (iii), for
`hull_average`.  The paper objects themselves (the IQ carrier, the actual
`det (x) M` operation, the log-volume normalization) are not represented by
this structure; they are the cards of Sections 3 and 4. -/
structure HullDeterminantLogVolumeFrozenSpec : Prop where
  det_eq_prod : forall {label : Type*} [Fintype label] (packet : PositivePacket label),
    packetDet packet = ∏ i, packet.scale i
  log_eq_log_det : forall {label : Type*} [Fintype label] (packet : PositivePacket label),
    packetLogVolume packet = Real.log (packetDet packet)
  det_tensor : forall {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (p : PositivePacket alpha) (q : PositivePacket beta),
    packetDet (tensorPacket p q) =
      packetDet p ^ Fintype.card beta * packetDet q ^ Fintype.card alpha
  log_tensor : forall {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    (p : PositivePacket alpha) (q : PositivePacket beta),
    packetLogVolume (tensorPacket p q) =
      (Fintype.card beta : Real) * packetLogVolume p +
        (Fintype.card alpha : Real) * packetLogVolume q
  det_rescale : forall {label : Type*} [Fintype label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label),
    packetDet (rescalePacket c hc packet) = c ^ Fintype.card label * packetDet packet
  log_rescale : forall {label : Type*} [Fintype label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label),
    packetLogVolume (rescalePacket c hc packet) =
      (Fintype.card label : Real) * Real.log c + packetLogVolume packet
  hull_average : forall {label : Type*} [Fintype label]
    (hull : FiniteHull label) (data : WeightedValues label)
    (hvalue : forall i, data.value i = hull.volume i)
    (hw : forall i, 0 <= data.weight i),
    data.average <= hull.hullVolume

/-- The frozen specification is realized by the already-compiled theorems of
`Volume.lean`; this records exactly which statements are proved at the
finite-packet interface layer (no new mathematics). -/
theorem hullDeterminantLogVolumeFrozenSpec_holds :
    HullDeterminantLogVolumeFrozenSpec where
  det_eq_prod := fun packet => packetDet_eq_prod packet
  log_eq_log_det := fun packet => packetLogVolume_eq_log_det packet
  det_tensor := fun p q => packetDet_tensor p q
  log_tensor := fun p q => packetLogVolume_tensor p q
  det_rescale := fun c hc packet => packetDet_rescale c hc packet
  log_rescale := fun c hc packet => packetLogVolume_rescale c hc packet
  hull_average := fun hull data hvalue hw => FiniteHull.average_le hull data hvalue hw

/-! ## 2. General finite linear algebra (approach (a))

The frozen packet identities are specializations at diagonal matrices.  Below,
the standard real determinant laws are proved in logarithmic form for positive
definite matrices: multiplicativity, scalar rescaling, the Kronecker
(tensor-packet) law, and the positive tensor power law (the `det (x) M`
degree scaling of (Ob3-2)/(Ob3-3) in its algebraic mirror). -/

/-- The log-determinant `log (det A)` of a real square matrix: the quantity
whose finite-packet shadow is `packetLogVolume` (Step (xi-d), (Ob3-3)). -/
noncomputable def matrixLogDet {n : Type*} [Fintype n] [DecidableEq n]
    (A : Matrix n n Real) : Real :=
  Real.log A.det

/-- Log-determinant is additive on positive definite factors
(`Matrix.det_mul`). -/
theorem matrixLogDet_mul_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet (A * B) = matrixLogDet A + matrixLogDet B := by
  unfold matrixLogDet
  rw [Matrix.det_mul, Real.log_mul (ne_of_gt hA.det_pos) (ne_of_gt hB.det_pos)]

/-- Log-determinant rescaling law for positive scalars: the `lambda * O` hull
form of Remark 3.9.5, (i), at the determinant level. -/
theorem matrixLogDet_smul_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (c : Real) (hc : 0 < c) (hA : A.PosDef) :
    matrixLogDet (c • A) =
      (Fintype.card n : Real) * Real.log c + matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_smul,
    Real.log_mul (pow_ne_zero _ (ne_of_gt hc)) (ne_of_gt hA.det_pos),
    Real.log_pow]
/-- Log-determinant of the Kronecker product of positive definite matrices:
the tensor-packet law of (Ob1) / Step (xi-d) at the determinant level. -/
theorem matrixLogDet_kronecker_posDef {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n]
    {A : Matrix m m Real} {B : Matrix n n Real} (hA : A.PosDef) (hB : B.PosDef) :
    matrixLogDet (A ⊗ₖ B) =
      (Fintype.card n : Real) * matrixLogDet A +
        (Fintype.card m : Real) * matrixLogDet B := by
  unfold matrixLogDet
  rw [Matrix.det_kronecker,
    Real.log_mul (pow_ne_zero _ (ne_of_gt hA.det_pos))
      (pow_ne_zero _ (ne_of_gt hB.det_pos))]
  simp only [Real.log_pow]

/-- The positive tensor power law: forming the `M`-th tensor power scales the
log-determinant by `M` (the algebraic mirror of the `det (x) M` bookkeeping,
(Ob3-2)/(Ob3-3); the source-side arithmetic-degree identification remains the
card of Section 4). -/
theorem matrixLogDet_pow_posDef {n : Type*} [Fintype n] [DecidableEq n]
    {A : Matrix n n Real} (hA : A.PosDef) (M : Nat) :
    matrixLogDet (A ^ M) = (M : Real) * matrixLogDet A := by
  unfold matrixLogDet
  rw [Matrix.det_pow, Real.log_pow]

/-- The diagonal matrix of a positive packet. -/
noncomputable def packetDiagonalMatrix {label : Type*} [Fintype label]
    [DecidableEq label]
    (packet : PositivePacket label) : Matrix label label Real :=
  Matrix.diagonal packet.scale

/-- `packetDet` is the determinant of the packet's diagonal matrix. -/
theorem packetDet_eq_packetDiagonalMatrix_det {label : Type*} [Fintype label]
    [DecidableEq label] (packet : PositivePacket label) :
    packetDet packet = (packetDiagonalMatrix packet).det := by
  rw [packetDet_eq_prod, packetDiagonalMatrix, Matrix.det_diagonal]

/-- The packet's diagonal matrix is positive definite
(`Matrix.posDef_diagonal_iff`). -/
theorem packetDiagonalMatrix_posDef {label : Type*} [Fintype label] [DecidableEq label]
    (packet : PositivePacket label) :
    (packetDiagonalMatrix packet).PosDef := by
  rw [packetDiagonalMatrix]
  exact Matrix.posDef_diagonal_iff.mpr packet.positive

/-- The packet determinant is positive: the positive-definite determinant
theorem `Matrix.PosDef.det_pos` at the packet's diagonal matrix. -/
theorem packetDet_pos {label : Type*} [Fintype label] [DecidableEq label]
    (packet : PositivePacket label) :
    0 < packetDet packet := by
  rw [packetDet_eq_packetDiagonalMatrix_det packet]
  exact (packetDiagonalMatrix_posDef packet).det_pos

/-- The packet log-volume is the log-determinant of the packet's diagonal
matrix (synthesis of `packetDet_eq_prod` and `packetLogVolume_eq_log_det`). -/
theorem packetLogVolume_eq_matrixLogDet {label : Type*} [Fintype label] [DecidableEq label]
    (packet : PositivePacket label) :
    packetLogVolume packet = matrixLogDet (packetDiagonalMatrix packet) := by
  rw [matrixLogDet, packetLogVolume_eq_log_det, packetDet_eq_packetDiagonalMatrix_det]

/-- The tensor packet's diagonal matrix is the Kronecker product of the factor
diagonal matrices (`Matrix.diagonal_kronecker_diagonal`). -/
theorem packetDiagonalMatrix_tensor {alpha beta : Type*} [Fintype alpha] [Fintype beta]
    [DecidableEq alpha] [DecidableEq beta]
    (p : PositivePacket alpha) (q : PositivePacket beta) :
    packetDiagonalMatrix (tensorPacket p q) =
      (packetDiagonalMatrix p) ⊗ₖ (packetDiagonalMatrix q) := by
  unfold packetDiagonalMatrix
  rw [Matrix.diagonal_kronecker_diagonal, tensorPacket]

/-- The tensor identity `packetDet_tensor` re-derived from the general
`Matrix.det_kronecker` law: the frozen tensor family is the diagonal Kronecker
specialization. -/
theorem packetDet_tensor_via_det_kronecker {alpha beta : Type*}
    [Fintype alpha] [Fintype beta] [DecidableEq alpha] [DecidableEq beta]
    (p : PositivePacket alpha) (q : PositivePacket beta) :
    packetDet (tensorPacket p q) =
      packetDet p ^ Fintype.card beta * packetDet q ^ Fintype.card alpha := by
  rw [packetDet_eq_packetDiagonalMatrix_det (tensorPacket p q),
    packetDiagonalMatrix_tensor p q, Matrix.det_kronecker,
    <- packetDet_eq_packetDiagonalMatrix_det p,
    <- packetDet_eq_packetDiagonalMatrix_det q]
/-- The rescaled packet's diagonal matrix is the scalar multiple of the matrix
(the `c • A` mirror of the `lambda * O` rescaling). -/
theorem packetDiagonalMatrix_rescale {label : Type*} [Fintype label] [DecidableEq label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetDiagonalMatrix (rescalePacket c hc packet) =
      c • packetDiagonalMatrix packet := by
  unfold packetDiagonalMatrix
  have hscale : (rescalePacket c hc packet).scale = c • packet.scale := by
    funext i
    simp [rescalePacket, smul_eq_mul]
  rw [hscale, Matrix.diagonal_smul]

/-- The rescaling identity `packetDet_rescale` re-derived from the general
`Matrix.det_smul` law. -/
theorem packetDet_rescale_via_det_smul {label : Type*} [Fintype label] [DecidableEq label]
    (c : Real) (hc : 0 < c) (packet : PositivePacket label) :
    packetDet (rescalePacket c hc packet) =
      c ^ Fintype.card label * packetDet packet := by
  rw [packetDet_eq_packetDiagonalMatrix_det (rescalePacket c hc packet),
    packetDiagonalMatrix_rescale c hc packet, Matrix.det_smul,
    <- packetDet_eq_packetDiagonalMatrix_det packet]

/-- The packet-level positive tensor power law: the `M`-th power of the
packet's diagonal matrix has log-determinant `M * packetLogVolume` (the
algebraic mirror of the `det (x) M` log-volume bookkeeping,
(Ob3-2)/(Ob3-3)). -/
theorem packetLogVolume_tensorPower {label : Type*} [Fintype label] [DecidableEq label]
    (packet : PositivePacket label) (M : Nat) :
    matrixLogDet (packetDiagonalMatrix packet ^ M) =
      (M : Real) * packetLogVolume packet := by
  rw [matrixLogDet, Matrix.det_pow, Real.log_pow,
    <- packetDet_eq_packetDiagonalMatrix_det packet, <- packetLogVolume_eq_log_det]

/-- Arithmetic degree of a finitely indexed realified degree profile: the sum
of the local degrees (the `normalized log-volume = arithmetic degree` side of
(Ob3-3), finite index model). -/
def profileArithmeticDegree {Place : Type*} [Fintype Place] (profile : Place -> Real) :
    Real :=
  ∑ place, profile place

/-- A degree profile scales by a positive tensor power `M`: the arithmetic
degree of the `M`-th tensor power is `M` times the degree ((Ob3-2), (Ob4) at
the degree level). -/
theorem profileArithmeticDegree_nsmul {Place : Type*} [Fintype Place]
    (M : Nat) (profile : Place -> Real) :
    profileArithmeticDegree (M • profile) =
      (M : Real) * profileArithmeticDegree profile := by
  unfold profileArithmeticDegree
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro place _
  change M • profile place = (M : Real) * profile place
  exact nsmul_eq_mul M (profile place)

/-- The adjusted `det (x) M`: tensor the determinant degree profile with the
inverse determinant of the structure sheaf ((Ob3-1-2)), then raise to the
`M`-th tensor power ((Ob3-2)); the arithmetic degree is `M` times the
difference of the degrees (the (Ob3-3) bookkeeping in its algebraic mirror). -/
theorem profileArithmeticDegree_adjustedDetTensorPower {Place : Type*} [Fintype Place]
    (M : Nat) (arithmeticBundle structureSheaf : Place -> Real) :
    profileArithmeticDegree (M • (arithmeticBundle - structureSheaf)) =
      (M : Real) * (profileArithmeticDegree arithmeticBundle -
        profileArithmeticDegree structureSheaf) := by
  have hsub : profileArithmeticDegree (arithmeticBundle - structureSheaf) =
      profileArithmeticDegree arithmeticBundle -
        profileArithmeticDegree structureSheaf := by
    unfold profileArithmeticDegree
    simp only [Pi.sub_apply]
    rw [Finset.sum_sub_distrib]
  rw [profileArithmeticDegree_nsmul M (arithmeticBundle - structureSheaf), hsub]
/-! ## 3. The hull adjunction card (Remark 3.9.5, (i), (ii))

The card freezes the paper's definition: `hull` is the smallest element of `H`
(the `lambda * O` regions, indexed by the scaling components `lambda`) that
contains the direct product region `P`.  Theorems (P1), (P3), and the
intersection display of Remark 3.9.5, (ii), are proved from the card fields. -/

/-- The paper's `P -> H` adjunction of Remark 3.9.5, (i), (ii): `isHullRegion`
is membership in `H` (the `lambda * O` regions of (i), with the nonzero
component condition carried by the scaling index), `hull` is `phi`, and the
last two fields are the definition of the holomorphic hull as the *smallest*
subset of the form `lambda * O` containing the region. -/
structure HolomorphicHullAdjunction (X : Type u) (ScalingIndex : Type v) where
  /-- `P` of Remark 3.9.5, (ii): the direct product regions (Remark 3.1.1, (iii)). -/
  isDirectProductRegion : Set X -> Prop
  /-- The regions `lambda * O`: the `lambda`-multiples of the unit region. -/
  principalRegion : ScalingIndex -> Set X
  /-- The paper's `phi`. -/
  hull : Set X -> Set X
  /-- `H` of Remark 3.9.5, (ii): the hull regions, i.e. the `lambda * O`. -/
  isHullRegion : Set X -> Prop
  /-- `H` is exactly the class of `lambda * O` regions. -/
  isHullRegion_iff_principal :
    forall H, isHullRegion H <-> exists lambda : ScalingIndex, H = principalRegion lambda
  /-- `H` is contained in `P` (Remark 3.9.5, (ii)). -/
  isHullRegion_subset_directProduct :
    forall {H : Set X}, isHullRegion H -> isDirectProductRegion H
  /-- (P2) of Remark 3.9.5, (ii): `P` is contained in `phi(P)` (up to the
  relatively-compact hypothesis of (i), which the card leaves to the supplier). -/
  hull_contains : forall {P : Set X}, isDirectProductRegion P -> P <= hull P
  /-- `phi(P)` is again a hull region. -/
  hull_isHullRegion : forall {P : Set X}, isDirectProductRegion P -> isHullRegion (hull P)
  /-- **Smallest**: Remark 3.9.5, (i): `phi(P)` is the smallest `lambda * O`
  containing `P`. -/
  hull_least : forall {P H : Set X}, isDirectProductRegion P -> isHullRegion H ->
    P <= H -> hull P <= H

namespace HolomorphicHullAdjunction

variable {X : Type u} {ScalingIndex : Type v}

/-- (P1) of Remark 3.9.5, (ii): `phi(H) = H` for every hull region `H`. -/
theorem hull_idem (adj : HolomorphicHullAdjunction X ScalingIndex)
    {H : Set X} (hH : adj.isHullRegion H) : adj.hull H = H := by
  refine subset_antisymm ?_ ?_
  · exact adj.hull_least (adj.isHullRegion_subset_directProduct hH) hH subset_rfl
  · exact adj.hull_contains (adj.isHullRegion_subset_directProduct hH)

/-- (P3) of Remark 3.9.5, (ii): `phi` is monotone on direct product regions. -/
theorem hull_mono (adj : HolomorphicHullAdjunction X ScalingIndex)
    {P1 P2 : Set X} (h1 : adj.isDirectProductRegion P1)
    (h2 : adj.isDirectProductRegion P2) (hsub : P1 <= P2) :
    adj.hull P1 <= adj.hull P2 :=
  adj.hull_least h1 (adj.hull_isHullRegion h2)
    (subset_trans hsub (adj.hull_contains h2))

/-- The intersection display of Remark 3.9.5, (ii):
`phi(P) = Inter_{H hull region, H >= P} H`. -/
theorem hull_eq_sInter (adj : HolomorphicHullAdjunction X ScalingIndex)
    {P : Set X} (hP : adj.isDirectProductRegion P) :
    adj.hull P = ⋂₀ {H : Set X | adj.isHullRegion H ∧ P <= H} := by
  refine subset_antisymm ?_ ?_
  · intro x hx
    rw [Set.mem_sInter]
    intro H hH
    exact adj.hull_least hP hH.1 hH.2 hx
  · intro x hx
    rw [Set.mem_sInter] at hx
    exact hx (adj.hull P) ⟨adj.hull_isHullRegion hP, adj.hull_contains hP⟩

end HolomorphicHullAdjunction
/-- The d5 real-line carrier model (`IQCarrierConcreteModel.lean`) as a hull
adjunction: the hull region is the explicit bounded log-shell `Set.Iic 0`
(`iqCarrierModelHull`), the single scaling is the model's neutral scaling.
This is a calibration instance in the shape of the d5 hull face; it is not the
paper's carrier. -/
noncomputable def d5CarrierModelHullAdjunction :
    HolomorphicHullAdjunction Real Unit where
  isDirectProductRegion P := P <= iqCarrierModelHull
  principalRegion _ := iqCarrierModelHull
  hull _ := iqCarrierModelHull
  isHullRegion H := H = iqCarrierModelHull
  isHullRegion_iff_principal := fun H =>
    ⟨fun h => ⟨(), h⟩, fun ⟨_, h⟩ => h⟩
  isHullRegion_subset_directProduct := fun {H} hH => le_of_eq hH
  hull_contains := fun {P} hP => hP
  hull_isHullRegion := fun {P} _ => rfl
  hull_least := fun {P H} _ hH _ => le_of_eq hH.symm

/-- The calibration hull coincides with the d5 interface hull field
(`iqCarrierModelInterface.hull`). -/
theorem d5CarrierModelHullAdjunction_hull_eq_interfaceHull :
    d5CarrierModelHullAdjunction.hull (Set.Iic (0 : Real)) =
      iqCarrierModelInterface.hull := rfl

/-- The d5 interface hull field is a hull region of the calibration
adjunction. -/
theorem d5CarrierModelHullAdjunction_isHullRegion_interfaceHull :
    d5CarrierModelHullAdjunction.isHullRegion iqCarrierModelInterface.hull := rfl

/-- (P1) fires at the d5 calibration: the calibration hull is `phi`-fixed. -/
theorem d5CarrierModelHullAdjunction_hull_idem :
    d5CarrierModelHullAdjunction.hull iqCarrierModelInterface.hull =
      iqCarrierModelInterface.hull :=
  HolomorphicHullAdjunction.hull_idem d5CarrierModelHullAdjunction
    d5CarrierModelHullAdjunction_isHullRegion_interfaceHull

/-- The calibration level shows the hull adjunction card is satisfiable (its
premise space is nonempty): a consistency witness only. -/
theorem holomorphicHullAdjunction_nonempty_calibration :
    Nonempty (HolomorphicHullAdjunction Real Unit) :=
  ⟨d5CarrierModelHullAdjunction⟩

/-! ## 4. The `det (x) M` and final-comparison cards -/

/-- The `det (x) M` log-volume bookkeeping of (Ob3-2)/(Ob3-3) as named data:
a normalized log-volume on regions together with the `det (x) M` operation
whose normalized log-volume is `M` times that of the original arithmetic
vector bundle (with the suitable normalization factors of (Ob3-3); this
identification at the paper's carrier is NOT proved here). -/
structure DetTensorPowerLogVolumeBookkeeping (Region : Type u) where
  /-- The normalized log-volume of regions / realified arithmetic bundles. -/
  logVolume : Region -> ENNReal
  /-- The positive integer `M` of the operation `det (x) M` (Ob3-2). -/
  tensorPowerExponent : Nat
  tensorPowerExponent_pos : 0 < tensorPowerExponent
  /-- The `det (x) M` operation on the region/bundle side (with the structure
  sheaf adjustment of (Ob3-1-2) already applied). -/
  detTensorPower : Region -> Region
  /-- (Ob3-3): the normalized log-volume of the `det (x) M` output is `M`
  times the normalized log-volume of the original arithmetic vector bundle. -/
  logVolume_detTensorPower : forall S, logVolume (detTensorPower S) =
    (tensorPowerExponent : ENNReal) * logVolume S

/-- Scalar log-degree calibration of the `det (x) M` bookkeeping: `M`-fold
scaling of the log-degree scales the `ofReal (max . 0)` log-volume by `M`
(consistency witness, not the source carrier). -/
noncomputable def detTensorPowerBookkeeping_scalarLogDegree
    (M : Nat) (hM : 0 < M) :
    DetTensorPowerLogVolumeBookkeeping Real where
  logVolume x := ENNReal.ofReal (max x 0)
  tensorPowerExponent := M
  tensorPowerExponent_pos := hM
  detTensorPower x := (M : Real) * x
  logVolume_detTensorPower := by
    intro x
    calc ENNReal.ofReal (max ((M : Real) * x) 0)
        = ENNReal.ofReal ((M : Real) * max x 0) := by
          rw [mul_max_of_nonneg x 0 (Nat.cast_nonneg M), mul_zero]
      _ = ENNReal.ofReal (M : Real) * ENNReal.ofReal (max x 0) :=
          ENNReal.ofReal_mul (Nat.cast_nonneg M)
      _ = (M : ENNReal) * ENNReal.ofReal (max x 0) := by
          rw [ENNReal.ofReal_natCast]
/-- The paper's `R_{<= -|log(Theta)|}`: the ray of Corollary 3.12 /
Step (xi-f). -/
def hullLogVolumeRay (thetaHullLogVolume : Real) : Set Real :=
  Set.Iic thetaHullLogVolume

/-- Membership in the ray is the inequality of Step (xi-f). -/
theorem mem_hullLogVolumeRay_iff {thetaHullLogVolume lambdaValue : Real} :
    lambdaValue ∈ hullLogVolumeRay thetaHullLogVolume <->
      lambdaValue <= thetaHullLogVolume :=
  Iff.rfl

/-- The (xi-e)/(xi-f) comparison data: the hull log-volume `-|log(Theta)|`
(the procession-normalized mono-analytic log-volume of the holomorphic hull),
the q-pilot log-volume `-|log(q)|`, the inclusion of Step (xi-f)
(`-|log(q)|` lies in the ray), and the identification of the q-pilot
log-volume with `-|log(q)|` for a q-parameter with `|log(q)| > 0` as in the
statement of Corollary 3.12.  The card records the conclusion data of the
source argument; the source construction producing it is not proved here. -/
structure Cor312ComparisonData where
  /-- `-|log(Theta)|`: the procession-normalized hull log-volume. -/
  thetaHullLogVolume : Real
  /-- `-|log(q)|`: the q-pilot object log-volume of the input data. -/
  qPilotLogVolume : Real
  /-- Step (xi-f): `-|log(q)|` lies in `R_{<= -|log(Theta)|}`. -/
  qPilot_mem_ray : qPilotLogVolume ∈ hullLogVolumeRay thetaHullLogVolume
  /-- The q-parameter `q` of the elliptic curve. -/
  qParameter : Real
  qParameter_pos : 0 < qParameter
  /-- `|log(q)| > 0` of the statement of Corollary 3.12. -/
  qParameter_log_ne_zero : Real.log qParameter ≠ 0
  /-- The pilot-object log-volume is `-|log(q)|`. -/
  qPilotLogVolume_eq : qPilotLogVolume = -|Real.log qParameter|

/-- **The final arithmetic step of Corollary 3.12** (Step (xi-f)): from
`-|log(q)| <= -|log(Theta)|` and `-|log(Theta)| <= C_Theta * |log(q)|` with
`|log(q)| > 0`, conclude `C_Theta >= -1`.  Fully proved real arithmetic; the
source input is exactly the two comparison hypotheses. -/
theorem cor312CThetaLowerBound {thetaLogVolume : Real} {qParameter : Real}
    (hq : Real.log qParameter ≠ 0)
    (hincl : -|Real.log qParameter| <= thetaLogVolume)
    {cTheta : Real} (hc : thetaLogVolume <= cTheta * |Real.log qParameter|) :
    -1 <= cTheta := by
  have hqpos : 0 < |Real.log qParameter| := abs_pos.mpr hq
  have hdiv : thetaLogVolume / |Real.log qParameter| <= cTheta :=
    (div_le_iff₀ hqpos).mpr hc
  have hlower : (-1 : Real) <= thetaLogVolume / |Real.log qParameter| := by
    rw [le_div_iff₀ hqpos, neg_one_mul]
    exact hincl
  linarith

/-- The card-level Corollary 3.12 conclusion: `C_Theta >= -1`. -/
theorem Cor312ComparisonData.final_bound (data : Cor312ComparisonData)
    {cTheta : Real}
    (hc : data.thetaHullLogVolume <= cTheta * |Real.log data.qParameter|) :
    -1 <= cTheta :=
  cor312CThetaLowerBound data.qParameter_log_ne_zero
    (by rw [<- data.qPilotLogVolume_eq]; exact data.qPilot_mem_ray) hc

/-- The comparison card is satisfiable (premise space nonempty): an exact
numeric consistency instance at `q = exp 2`, `-|log(Theta)| = -1`,
`C_Theta = -1/2`. -/
theorem cor312CThetaLowerBound_expTwo_satisfiable :
    -1 <= (-1 / 2 : Real) :=
  cor312CThetaLowerBound (thetaLogVolume := -1) (qParameter := Real.exp 2)
    (cTheta := -1 / 2)
    (by rw [Real.log_exp]; norm_num)
    (by rw [Real.log_exp]; norm_num)
    (by rw [Real.log_exp]; norm_num)

/-- A concrete `Cor312ComparisonData` instance (consistency witness). -/
theorem cor312ComparisonData_nonempty : Nonempty Cor312ComparisonData :=
  ⟨{ thetaHullLogVolume := -1
     qPilotLogVolume := -2
     qPilot_mem_ray := by
       change (-2 : Real) <= -1
       norm_num
     qParameter := Real.exp 2
     qParameter_pos := Real.exp_pos 2
     qParameter_log_ne_zero := by rw [Real.log_exp]; norm_num
     qPilotLogVolume_eq := by rw [Real.log_exp]; norm_num }⟩
/-! ## 5. Counterexamples: which hypotheses are essential (approach (c))

The frozen log identities are genuinely conditional: with a zero scale the
log-determinant identity fails, and the log rescaling law needs a nonzero
scalar.  These witnesses show the `PositivePacket` positivity field and the
`hc : 0 < c` hypothesis are not padding. -/

/-- Without a nonzero-entry hypothesis the log-determinant identity fails: at
the scales `(0, 2)` the sum of logs is `log 2` while `log (det) = log 0 = 0`. -/
theorem packetLogSum_ne_log_det_of_zero_scale :
    exists f : Fin 2 -> Real,
      (∑ i, Real.log (f i)) ≠ Real.log ((Matrix.diagonal f).det) := by
  refine ⟨fun i : Fin 2 => if i = 0 then (0 : Real) else 2, ?_⟩
  have h10 : ¬ ((1 : Fin 2) = 0) := by decide
  have hsum : (∑ i : Fin 2, Real.log (if i = 0 then (0 : Real) else 2)) =
      Real.log 2 := by
    rw [Fin.sum_univ_two]
    simp [Real.log_zero, h10]
  have hdet : Real.log ((Matrix.diagonal
      (fun i : Fin 2 => if i = 0 then (0 : Real) else 2)).det) = 0 := by
    rw [Matrix.det_diagonal, Fin.prod_univ_two]
    simp [Real.log_zero, h10]
  rw [hsum, hdet]
  exact (Real.log_pos (by norm_num : (1 : Real) < 2)).ne'

/-- The `1 x 1` matrix `[2]` of the rescaling counterexample. -/
def rescalingCounterexampleMatrix : Matrix (Fin 1) (Fin 1) Real :=
  fun _ _ => 2

/-- The log rescaling law needs a nonzero scalar: at `c = 0` and the `1 x 1`
matrix `[2]` the two sides differ. -/
theorem matrixLogDet_smul_ne_zero_scalar_counterexample :
    exists (c : Real) (A : Matrix (Fin 1) (Fin 1) Real),
      matrixLogDet (c • A) ≠
        (Fintype.card (Fin 1) : Real) * Real.log c + matrixLogDet A := by
  refine ⟨0, rescalingCounterexampleMatrix, ?_⟩
  have hleft : matrixLogDet ((0 : Real) • rescalingCounterexampleMatrix) = 0 := by
    rw [matrixLogDet]
    have hdet : ((0 : Real) • rescalingCounterexampleMatrix).det = 0 := by
      rw [Matrix.det_fin_one]
      simp [rescalingCounterexampleMatrix]
    rw [hdet, Real.log_zero]
  have hright : (Fintype.card (Fin 1) : Real) * Real.log (0 : Real) +
      matrixLogDet rescalingCounterexampleMatrix = Real.log 2 := by
    rw [matrixLogDet, Matrix.det_fin_one]
    simp [rescalingCounterexampleMatrix, Real.log_zero]
  rw [hleft, hright]
  exact (Real.log_pos (by norm_num : (1 : Real) < 2)).ne

end

end LeanFormal.IUT

namespace LeanFormal.IUT.Audit

/-- Audit record for the reduction pass of the frozen target
`IUT-III.holomorphic-hull-determinant-log-volume` (Volume.lean:179). -/
def hullDeterminantLogVolumeReduction : Obligation :=
  { id := "IUT-III.holomorphic-hull-determinant-log-volume-reduction"
    source :=
      "IUT III, Corollary 3.12 proof, Steps (xi-d)-(xi-g) " ++
        "(corpus text lines 10823-10907); Remark 3.9.5, (i), (ii), (iii), " ++
        "(vii), (Ob1)-(Ob4); Proposition 3.9, (i), (iii), (iv)"
    status := VerificationStatus.interface
    note :=
      "Reduction pass (2026-10-16). Proved: the four frozen finite-packet " ++
        "identity families are the diagonal specializations of the standard " ++
        "real determinant laws (matrixLogDet_mul_posDef, " ++
        "matrixLogDet_smul_posDef, matrixLogDet_kronecker_posDef, " ++
        "matrixLogDet_pow_posDef; packetDet_tensor_via_det_kronecker and " ++
        "packetDet_rescale_via_det_smul re-derive the Volume.lean identities; " ++
        "packetDet_pos via Matrix.PosDef.det_pos; packetLogVolume_tensorPower " ++
        "and profileArithmeticDegree_adjustedDetTensorPower are the algebraic " ++
        "mirrors of the det (x) M bookkeeping of (Ob3-2)/(Ob3-3)). Proved from " ++
        "the hull-adjunction card: (P1) hull_idem, (P3) hull_mono, and the " ++
        "intersection display hull_eq_sInter of Remark 3.9.5, (ii). Proved " ++
        "outright: the final arithmetic step of Corollary 3.12 / Step (xi-f), " ++
        "cor312CThetaLowerBound, with |log(q)| > 0 explicit. NOT proved (cards): " ++
        "the paper's carrier IQ(S+-; n, D^vdash) realization (Card-HULLREAL); the " ++
        "source-side identification (Ob3-3) that the arithmetic degree of the " ++
        "det (x) M output equals the normalized log-volume of the original " ++
        "arithmetic vector bundle; the production of the (xi-e)/(xi-f) comparison " ++
        "data by the multiradial algorithm. Calibration instances " ++
        "(d5CarrierModelHullAdjunction; detTensorPowerBookkeeping_scalarLogDegree) " ++
        "are consistency witnesses on the real line / scalar log-degrees, not the " ++
        "paper's carrier and not a theta-pilot carrier. O1 caveat: no lemma " ++
        "requiring both degree faithfulness and hull finiteness is used " ++
        "(that premise space is empty by sourceHullVolume_eq_top_of_degreeFaithful)."
    dependsOn :=
      [ "IUT-III.holomorphic-hull-determinant-log-volume" ] }

end LeanFormal.IUT.Audit
