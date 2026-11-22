import tmp.sheaf.xif.paper.S1931SourceHaarSignedAverageActual
import tmp.sheaf.xif.paper.S1487OQPilotScalarEqualityActual

/-!
# S1941: the actual C3 / S1487Cand q against the actual C6 canonical hull

## What is computed

The paper-route actual C3 at the concrete Gaussian five place is the S1391
L-carrier `S1487FaithfulC3` (equivalently `S1527C3` / `S1920PaperC3`).  Its
completion q is `S1487Cand` (`s1941ActualC3_q`) and its theta packet is the
source-Haar packet `sourceHaarActualThetaPacket`, whose parameter is *one*:

    (S1487FaithfulC3 l).thetaPacket.q = 1       (s1941ActualC3_theta_q).

Consequently the S1931 exact-first-missing equation

    Real.log C3.thetaPacket.q
      = - (arithmeticTupleHullUnitLogVolume places tuple * card) / W

for this actual C3 is *not* an equation about `S1487Cand.q`; it is exactly

    arithmeticTupleHullUnitLogVolume places tuple = 0

where `places`/`tuple` are the actual C6 tensor data of `S1487FaithfulC3`
(`s1941ActualQEquation_iff_firstMissing`).  Equivalently, the actual C6
canonical hull and the canonical unit reference must have equal Haar mass
(`s1941FirstMissing_iff_hull_mass_eq`); because the hull log-volume is
nonnegative, this is also the upper bound `H <= 0`
(`s1941FirstMissing_iff_hullVolume_le_zero`).

## Status

`S1941FirstMissing` is the exact arithmetic first missing; it is a named
proposition, not an axiom, and it is not proved here.  The old-schema
`SignedUnitFactorThetaComparison` is *not* instantiable at the actual C3: the
actual C3 is the S1391 L-carrier, while the old schema additionally requires
roots of the completion q unit (`NatRootSystem qUnit`) which do not exist in
the completion (`SourcePilotRegion` records the exact first-field gap).  We
therefore prove the exact L-carrier form `SignedUnitFactorThetaComparisonL`
and its equivalence to `S1941FirstMissing`, and we prove the old-schema
source-Haar target is equivalent to the same equation whenever an old C3 with
the same theta packet is supplied.

No sorry, admit, axiom, True, PUnit, or arbitrary inhabitant is used.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S1941ActualQEquationActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.OriginalInput
open LeanFormal.IUT.N8Closure.SourcePilotRegion
open LeanFormal.IUT.N8C6ActualIQ
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper
open LeanFormal.IUT.XiFPaper.HaarSignedAverageProof
open LeanFormal.IUT.XiFPaper.ProcessionThetaPacketAverageActual
open LeanFormal.IUT.XiFPaper.S1391C3LSourcePilotActual
open LeanFormal.IUT.XiFPaper.S1487OQPilotScalarEqualityActual
open LeanFormal.IUT.XiFPaper.S1931SourceHaarSignedAverageActual
open MeasureTheory
open scoped BigOperators

universe ua uv upi umon ui

variable {l : PrimeGeFive}
variable {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
variable {V : Type uv} {I : OriginalInput.{ua, uv, upi, umon, ui} l V}

local instance s1941GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance s1941FivePrime : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

/-! ## 1. The theta-packet logarithm for an arbitrary packet -/

/-- The actual theta packet log-volume is the Gaussian weight sum times the
logarithm of the packet parameter.  This is the packet-level form of the
S1931 computation, no C3 record is used. -/
theorem s1941ThetaPacket_logVolume_eq (tp : FiniteThetaPacket l) :
    tp.logVolume = sourceThetaWeightSum l * Real.log tp.q := by
  have h : tp.logVolume =
      ∑ j : SignedLabel l.value,
        ((gaussExponent j.1).toNat : ℝ) * Real.log tp.q := by
    unfold FiniteThetaPacket.logVolume
    exact Finset.sum_congr rfl (fun j _ => FiniteThetaPacket.log_scale tp j)
  rw [h, ← Finset.sum_mul]
  rfl

/-- The signed theta average of a packet is `- (log q * W) / card`. -/
theorem s1941ThetaSignedAverage_eq_neg (tp : FiniteThetaPacket l) :
    - (tp.logVolume / (c3ThetaCard (l := l) : ℝ)) =
      - (Real.log tp.q * sourceThetaWeightSum l) /
        (c3ThetaCard (l := l) : ℝ) := by
  rw [s1941ThetaPacket_logVolume_eq]
  ring

/-- For a packet with `q = 1`, the signed theta average is zero. -/
theorem s1941ThetaSignedAverage_eq_zero_of_q_eq_one
    (tp : FiniteThetaPacket l) (hq : tp.q = 1) :
    - (tp.logVolume / (c3ThetaCard (l := l) : ℝ)) = 0 := by
  rw [s1941ThetaPacket_logVolume_eq, hq, Real.log_one, mul_zero, zero_div, neg_zero]

/-! ## 2. The S1931 equation for an arbitrary packet -/

/-- The S1931 exact-first-missing equation, stated for an arbitrary theta
packet and an arbitrary C6 tuple.  For a C3 it is the equation produced by
`s1931FirstMissing_logq`. -/
def S1941PacketEquation
    (tp : FiniteThetaPacket l)
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i) : Prop :=
  Real.log tp.q =
    - (arithmeticTupleHullUnitLogVolume places tuple *
        (c3ThetaCard (l := l) : ℝ)) / sourceThetaWeightSum l

/-- If the packet has `q = 1`, the S1931 equation is exactly the vanishing of
the actual C6 hull unit log-volume. -/
theorem s1941PacketEquation_iff_hullVolume_eq_zero
    {l : PrimeGeFive} {K : Type ua} [Field K] [NumberField K] {p : Nat}
    [Fact p.Prime] {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    (tp : FiniteThetaPacket l) (hq : tp.q = 1) :
    S1941PacketEquation (l := l) tp places tuple ↔
      arithmeticTupleHullUnitLogVolume places tuple = 0 := by
  have hcard : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  unfold S1941PacketEquation
  rw [hq, Real.log_one]
  constructor
  · intro h
    have h' : - (arithmeticTupleHullUnitLogVolume places tuple *
        (c3ThetaCard (l := l) : ℝ)) / sourceThetaWeightSum l = 0 := h.symm
    rw [div_eq_zero_iff] at h'
    rcases h' with h' | h'
    · have hmul : arithmeticTupleHullUnitLogVolume places tuple *
          (c3ThetaCard (l := l) : ℝ) = 0 := by linarith
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hcard)
    · exact absurd h' (ne_of_gt hW)
  · intro h
    rw [h]
    simp

/-! ## 3. The actual C3 and its C6 data -/

/-- The actual paper-route C3: the S1391 L-carrier at the concrete Gaussian
five place over the S1487 faithful input. -/
abbrev S1941ActualC3 (l : PrimeGeFive) :
    SourcePilotRegionDataL (I := S1487FaithfulInput (l := l)) :=
  S1487FaithfulC3 (l := l)

/-- The actual C3 carries the S1487 completion q candidate. -/
theorem s1941ActualC3_q (l : PrimeGeFive) :
    (S1941ActualC3 l).q = S1487Cand := by
  exact S1487FaithfulC3_q (l := l)

/-- **The actual theta packet of the actual C3 has parameter one.**  It is the
source-Haar packet `sourceHaarActualThetaPacket`, not the completion q
candidate `S1487Cand`. -/
theorem s1941ActualC3_theta_q (l : PrimeGeFive) :
    (S1941ActualC3 l).thetaPacket.q = 1 := rfl

/-- The actual C6 tensor places of the actual C3. -/
abbrev S1941ActualPlaces (l : PrimeGeFive) :=
  (S1941ActualC3 l).tensorPlaces

/-- The actual C6 tensor tuple of the actual C3. -/
abbrev S1941ActualTuple (l : PrimeGeFive) :=
  (S1941ActualC3 l).tensorTuple

/-- The actual C6 canonical hull unit log-volume of the actual C3. -/
noncomputable def S1941ActualHullVolume (l : PrimeGeFive) : ℝ :=
  arithmeticTupleHullUnitLogVolume (S1941ActualPlaces l) (S1941ActualTuple l)

/-- **The exact arithmetic first missing.**  The actual C6 canonical hull and
the canonical unit reference have the same unit-relative log-volume. -/
def S1941FirstMissing (l : PrimeGeFive) : Prop :=
  S1941ActualHullVolume l = 0

/-- The actual S1931 equation at the actual C3. -/
def S1941ActualQEquation (l : PrimeGeFive) : Prop :=
  S1941PacketEquation (l := l) (S1941ActualC3 l).thetaPacket
    (S1941ActualPlaces l) (S1941ActualTuple l)

/-- **The actual equation is exactly the vanishing of the actual C6 hull
unit log-volume.**  The completion parameter `S1487Cand` is not involved: the
actual theta packet has `q = 1`. -/
theorem s1941ActualQEquation_iff_firstMissing (l : PrimeGeFive) :
    S1941ActualQEquation l ↔ S1941FirstMissing l := by
  unfold S1941ActualQEquation S1941FirstMissing S1941ActualHullVolume
  exact s1941PacketEquation_iff_hullVolume_eq_zero
    (S1941ActualPlaces l) (S1941ActualTuple l)
    (S1941ActualC3 l).thetaPacket (s1941ActualC3_theta_q l)

/-- The actual signed theta average of the actual C3 is zero. -/
theorem s1941Actual_signedAverage_zero (l : PrimeGeFive) :
    - ((S1941ActualC3 l).thetaPacket.logVolume /
        (c3ThetaCard (l := l) : ℝ)) = 0 :=
  s1941ThetaSignedAverage_eq_zero_of_q_eq_one _ (s1941ActualC3_theta_q l)


/-- The actual left-hand side of the S1931 equation. -/
noncomputable def S1941ActualLHS (l : PrimeGeFive) : ℝ :=
  Real.log (S1941ActualC3 l).thetaPacket.q

/-- The actual right-hand side of the S1931 equation. -/
noncomputable def S1941ActualRHS (l : PrimeGeFive) : ℝ :=
  - (S1941ActualHullVolume l * (c3ThetaCard (l := l) : ℝ)) /
    sourceThetaWeightSum l

/-- The actual equation is the equality of the two displayed sides. -/
theorem s1941ActualQEquation_iff_LHS_eq_RHS (l : PrimeGeFive) :
    S1941ActualQEquation l ↔ S1941ActualLHS l = S1941ActualRHS l :=
  Iff.rfl

/-- **The actual left-hand side is zero**: the actual theta packet has q = 1. -/
theorem s1941ActualLHS_eq_zero (l : PrimeGeFive) :
    S1941ActualLHS l = 0 := by
  rw [S1941ActualLHS, s1941ActualC3_theta_q l, Real.log_one]

/-- The actual right-hand side vanishes exactly when the actual C6 hull
unit log-volume vanishes. -/
theorem s1941ActualRHS_eq_zero_iff (l : PrimeGeFive) :
    S1941ActualRHS l = 0 ↔ S1941ActualHullVolume l = 0 := by
  have hcard : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  unfold S1941ActualRHS
  constructor
  · intro h
    have h' : - (S1941ActualHullVolume l * (c3ThetaCard (l := l) : ℝ)) /
        sourceThetaWeightSum l = 0 := h
    rw [div_eq_zero_iff] at h'
    rcases h' with h' | h'
    · have hmul : S1941ActualHullVolume l * (c3ThetaCard (l := l) : ℝ) = 0 := by
        linarith
      exact (mul_eq_zero.mp hmul).resolve_right (ne_of_gt hcard)
    · exact absurd h' (ne_of_gt hW)
  · intro h
    rw [h]
    simp

/-- The actual right-hand side is nonpositive. -/
theorem s1941ActualRHS_nonpos (l : PrimeGeFive) :
    S1941ActualRHS l ≤ 0 := by
  have hcard : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  have hH : 0 ≤ S1941ActualHullVolume l :=
    arithmeticTupleHullUnitLogVolume_nonneg (S1941ActualPlaces l) (S1941ActualTuple l)
  unfold S1941ActualRHS
  have hmul : 0 ≤ S1941ActualHullVolume l * (c3ThetaCard (l := l) : ℝ) :=
    mul_nonneg hH (le_of_lt hcard)
  rw [neg_div]
  exact neg_nonpos.mpr (div_nonneg hmul (le_of_lt hW))

/-- The actual right-hand side is strictly negative if the hull unit
log-volume is positive. -/
theorem s1941ActualRHS_neg_of_hullVolume_pos (l : PrimeGeFive)
    (h : 0 < S1941ActualHullVolume l) : S1941ActualRHS l < 0 := by
  have hcard : (0 : ℝ) < (c3ThetaCard (l := l) : ℝ) := by
    exact_mod_cast c3ThetaCard_pos (l := l)
  have hW : (0 : ℝ) < sourceThetaWeightSum l := sourceThetaWeightSum_pos l
  have hmul : 0 < S1941ActualHullVolume l * (c3ThetaCard (l := l) : ℝ) :=
    mul_pos h hcard
  unfold S1941ActualRHS
  rw [neg_div]
  exact neg_neg_of_pos (div_pos hmul hW)

/-! ## 4. The C6 hull/unit-reference form of the first missing -/

/-- The exact first missing is the equality of the actual C6 canonical-hull
and canonical-unit-reference Haar masses, for any additive Haar measure. -/
theorem s1941FirstMissing_iff_hull_mass_eq (l : PrimeGeFive)
    [MeasurableSpace (ArithmeticTensorTupleBlock
      (S1941ActualPlaces l) (S1941ActualTuple l))]
    [BorelSpace (ArithmeticTensorTupleBlock
      (S1941ActualPlaces l) (S1941ActualTuple l))]
    (mu : Measure (ArithmeticTensorTupleBlock
      (S1941ActualPlaces l) (S1941ActualTuple l)))
    [Measure.IsAddHaarMeasure mu] :
    S1941FirstMissing l ↔
      mu (arithmeticTupleCanonicalHull (S1941ActualPlaces l) (S1941ActualTuple l)) =
        mu (arithmeticTupleCanonicalUnitReference (S1941ActualPlaces l)
          (S1941ActualTuple l)) := by
  unfold S1941FirstMissing S1941ActualHullVolume
  exact hullUnitLogVolume_eq_zero_iff_measure_eq
    (places := S1941ActualPlaces l) (tuple := S1941ActualTuple l) mu

/-- Because the actual hull unit log-volume is nonnegative, the first missing
is equivalently the upper bound `H <= 0`. -/
theorem s1941FirstMissing_iff_hullVolume_le_zero (l : PrimeGeFive) :
    S1941FirstMissing l ↔ S1941ActualHullVolume l <= 0 := by
  unfold S1941FirstMissing
  constructor
  · intro h; rw [h]
  · intro h
    exact le_antisymm h
      (arithmeticTupleHullUnitLogVolume_nonneg
        (S1941ActualPlaces l) (S1941ActualTuple l))

/-- If the actual hull unit log-volume is positive, the actual equation is
false. -/
theorem s1941ActualQEquation_false_of_hullVolume_pos (l : PrimeGeFive)
    (h : 0 < S1941ActualHullVolume l) :
    ¬ S1941ActualQEquation l := by
  intro hq
  have hzero : S1941FirstMissing l :=
    (s1941ActualQEquation_iff_firstMissing l).mp hq
  exact (ne_of_gt h) hzero

/-! ## 5. The L-carrier signed-unit-factor target -/

/-- The exact L-carrier form of the S1904/S1931 signed unit-factor identity.
This is the identity that is actually typed on the paper-route actual C3; it
uses the same signed packet average and the same C6 canonical regions. -/
def SignedUnitFactorThetaComparisonL
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu]
    (tp : FiniteThetaPacket l) : Prop :=
  arithmeticTupleHullUnitLogVolume places tuple +
      Real.log ((paperArithmeticHaar places tuple mu)
        (arithmeticTupleCanonicalUnitReference places tuple)).toReal =
    - (tp.logVolume / (c3ThetaCard (l := l) : ℝ))

/-- **The actual L-carrier target is exactly the arithmetic first missing.** -/
theorem s1941Actual_signedUnitFactorL_iff_firstMissing (l : PrimeGeFive)
    [MeasurableSpace (ArithmeticTensorTupleBlock
      (S1941ActualPlaces l) (S1941ActualTuple l))]
    [BorelSpace (ArithmeticTensorTupleBlock
      (S1941ActualPlaces l) (S1941ActualTuple l))]
    (mu : Measure (ArithmeticTensorTupleBlock
      (S1941ActualPlaces l) (S1941ActualTuple l)))
    [Measure.IsAddHaarMeasure mu] :
    SignedUnitFactorThetaComparisonL (l := l)
      (S1941ActualPlaces l) (S1941ActualTuple l) mu
      (S1941ActualC3 l).thetaPacket ↔
      S1941FirstMissing l := by
  have hzero := s1941Actual_signedAverage_zero l
  have hunit : Real.log ((paperArithmeticHaar (S1941ActualPlaces l)
      (S1941ActualTuple l) mu)
        (arithmeticTupleCanonicalUnitReference (S1941ActualPlaces l)
          (S1941ActualTuple l))).toReal = 0 := by
    rw [paperArithmeticHaar_unitReference (S1941ActualPlaces l)
      (S1941ActualTuple l) mu]
    simp
  unfold SignedUnitFactorThetaComparisonL S1941FirstMissing S1941ActualHullVolume
  rw [hzero, hunit]
  constructor
  · intro h
    linarith
  · intro h
    rw [h]
    ring

/-! ## 6. The old-schema target whenever an old C3 is supplied -/

/-- For any old-schema C3 whose theta packet is the source-Haar packet `q = 1`,
the S1931 source-Haar target is equivalent to the vanishing of the C6 hull
unit log-volume.  This is the exact bridge to `SignedUnitFactorThetaComparison`
for old C3 records carrying the actual theta packet. -/
theorem s1941OldTarget_iff_hullVolume_eq_zero
    {l : PrimeGeFive} {V : Type uv}
    {I : OriginalInput.{ua, uv, upi, umon, ui} l V}
    {K : Type ua} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
    {iota : Type uv} [Fintype iota] {W : iota -> Type ui}
    (places : (i : iota) -> W i -> FinitePlaceAtPrime K p)
    (tuple : (i : iota) -> W i)
    [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
    [BorelSpace (ArithmeticTensorTupleBlock places tuple)]
    (mu : Measure (ArithmeticTensorTupleBlock places tuple))
    [Measure.IsAddHaarMeasure mu]
    (C3 : SourcePilotRegionData (l := l) (V := V) I)
    (hq : C3.thetaPacket.q = 1) :
    SignedUnitFactorThetaComparison (l := l) (V := V) (I := I)
        (places := places) (tuple := tuple)
        (paperArithmeticHaar places tuple mu) C3 ↔
      arithmeticTupleHullUnitLogVolume places tuple = 0 := by
  rw [← s1931_firstMissing_iff_comparison (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (mu := mu) C3]
  rw [s1931FirstMissing_logq (l := l) (V := V) (I := I)
    (places := places) (tuple := tuple) (C3 := C3)]
  exact s1941PacketEquation_iff_hullVolume_eq_zero places tuple
    C3.thetaPacket hq

/-! ## 7. Axiom probes -/

#print axioms s1941ThetaPacket_logVolume_eq
#print axioms s1941PacketEquation_iff_hullVolume_eq_zero
#print axioms s1941ActualC3_theta_q
#print axioms s1941ActualQEquation_iff_firstMissing
#print axioms s1941ActualLHS_eq_zero
#print axioms s1941ActualRHS_eq_zero_iff
#print axioms s1941ActualRHS_nonpos
#print axioms s1941FirstMissing_iff_hull_mass_eq
#print axioms s1941FirstMissing_iff_hullVolume_le_zero
#print axioms s1941ActualQEquation_false_of_hullVolume_pos
#print axioms s1941Actual_signedUnitFactorL_iff_firstMissing
#print axioms s1941OldTarget_iff_hullVolume_eq_zero

end LeanFormal.IUT.XiFPaper.S1941ActualQEquationActual