# FINITE-DIM-LEMMAS — volume chain on finite blocks (A1127)

Status: lemma design; no compile.

## 1. Two finite blocks, not definitionally equal

C3 block:
  C3LogShellTensorBlockL = ArithmeticTensorTupleBlock C3L.tensorPlaces C3L.tensorTuple
  (Mzk1C3LogShellTensorLActual:44).

qVFam block:
  qVFamTensorBlock T b = ArithmeticTensorTupleBlock (qVFamTensorPlaces T b) qVFamTensorTuple
  (QVFamTensorCoefficientActual:72).

Both are finite-dimensional Q_p-vector spaces, but the places/tuples are different
source data. There is no theorem
  C3L.tensorPlaces = qVFamTensorPlaces T b and C3L.tensorTuple = qVFamTensorTuple,
so there is no definitional identification of the blocks. In particular,
actualC3LogShellTensorHaarL cannot be used directly as a measure on qVFamTensorBlock
without an explicit linear/topological equivalence.

## 2. Actual Haar on qVFamTensorBlock (finite, green inputs)

Green:
- s996QVFamLinearization (S996:42-45):
    e : qVFamTensorBlock T b ~= Fin d -> Qp,
    d = Module.finrank Qp (qVFamTensorBlock T b).
- finiteLogShellHaarData (S976:36-48):
    on FiniteLogShellCarrier p d = Fin d -> Qp,
    measure = Measure.addHaar, unitRegion = closedBall 0 1,
    unit_pos, unit_lt_top.

Transport to qVFamTensorBlock:

noncomputable def qVFamActualHaar :
    Measure (qVFamTensorBlock T b) :=
  (Measure.addHaar : Measure (Fin d -> Qp)).map (s996QVFamLinearization T b).symm

instance : Measure.IsAddHaarMeasure (qVFamActualHaar T b) := by
  unfold qVFamActualHaar
  infer_instance

noncomputable def qVFamActualUnitRegion : Set (qVFamTensorBlock T b) :=
  (s996QVFamLinearization T b).symm '' Metric.closedBall (0 : Fin d -> Qp) 1

Then positive/finite follow by transport from S976 (closedBall positive/finite)
or by compactness of the closed ball and the linear homeomorphism. The transport
lemmas are not yet packaged as one theorem; the pieces are green but the
combined statement is a small GAP.

## 3. C3 actual Haar/unit/hull (green)

On the C3 block, actualC3LogShellTensorHaarL = Measure.addHaar
(Mzk1C3LogShellTensorLActual:100), and:
- actualC3LogShellTensorRegionL_compact (C3L:87);
- actualC3LogShellTensorHaarL_lt_top (C3L:110);
- tensorIntegerRegionL and tensorIntegerRegionL_subset_actual
  (Mzk1TensorRegionNormalizationActual, A1124).

Thus on the C3 block:
  unitRegionC3 := tensorIntegerRegionL,
  hullRegionC3 := actualC3LogShellTensorRegionL,
  unitRegionC3 subset hullRegionC3                          PROVED (A1124),
  mu hullRegionC3 < top                                    PROVED (C3L:110).

But this is the C3 carrier, not qVFamTensorBlock.

## 4. Can we transfer the C3 chain to qVFamTensorBlock?

Need a structure (all fields explicit GAP):

structure C3QVFamBlockIdentification where
  e : C3LogShellTensorBlockL (I := I) C3L ~= qVFamTensorBlock T b
  e_isLinear : IsLinearMap Qp e
  measure_compat : forall S, mu_C3 S = mu_qVFam (e '' S)
  region_compat : e '' actualC3LogShellTensorRegionL = qVFamHullRegion
  unit_compat : e '' tensorIntegerRegionL = qVFamUnitRegion

None of these is present. Without them, C3 actualC3LogShellTensorHaarL and
qVFamActualHaar are unrelated normalizations, related only up to a scalar.

## 5. qPilot/theta comparison on the finite carrier (green chain)

Already available on the finite coordinate carrier:

- s1004E : qVFamTensorBlock T b ~= Fin d -> Qp (S1004:47-51).
- s1004QPilotImage := s1004E '' qPilotPaperRegion (S1004:52-55).
- s1004Hull := s1004E '' paperRootThetaImageNZ (S1004:56-59).
- s1004Containment : s1004QPilotImage subset s1004Hull
  (S1004:60-61, from qPilotPaperRegion_subset_thetaImageNZ).
- s1004H := finiteLogShellHaarData p d (S1004:62-64).
- s1004PerB :
    measure qPilotImage positive
    and measure hull finite
    => Real.log (measure qPilotImage).toReal <=
       Real.log (measure hull).toReal
  (S1004:79-85).

This is a real qPilot/theta containment and a conditional measure comparison on
the finite carrier. But it is not the C3 actualRegion chain: qPilotImage/hull
are images of paperRootThetaImageNZ/qPilotPaperRegion, not
tensorIntegerRegionL/actualC3LogShellTensorRegionL, and the normalization is
finiteLogShellHaarData (unit closed ball), not actualC3 raw addHaar.

## 6. Lean draft for the desired finite comparison

On qVFamTensorBlock, using s996QVFamLinearization e and qVFamActualHaar:

def qVFamQPilotImage : Set (qVFamTensorBlock T b) :=
  e.symm '' s1004QPilotImage

def qVFamThetaHullImage : Set (qVFamTensorBlock T b) :=
  e.symm '' s1004Hull

theorem qVFamQPilot_subset_theta :
    qVFamQPilotImage subset qVFamThetaHullImage :=
  Set.image_mono s1004Containment

def qVFamNormalizedLog (S : Set (qVFamTensorBlock T b)) : Real :=
  Real.log (qVFamActualHaar S).toReal -
    Real.log (qVFamActualHaar qVFamActualUnitRegion).toReal

theorem qVFam_measure_mono
    (h : qVFamQPilotImage subset qVFamThetaHullImage)
    (hpos : 0 < qVFamActualHaar qVFamQPilotImage)
    (hfin : qVFamActualHaar qVFamThetaHullImage < top) :
    qVFamNormalizedLog qVFamQPilotImage <= qVFamNormalizedLog qVFamThetaHullImage :=
  -- Real.log_le_log + measure_mono, same pattern as S962:42-59
  by
    sorry

This is a draft; the proof is the same as tensorNormalizedLogVolume_mono.

## 7. Verdict

- Finite qVFam block: actual Haar from s996QVFamLinearization + Measure.addHaar;
  unitRegion from closedBall; positivity/finiteness green pieces, packaging is a
  small GAP.
- C3 block: actual Haar/region and tensorIntegerRegionL subset actualRegion are
  green (A1124), but this is a different carrier.
- Cross-carrier identification C3LogShellTensorBlockL ~ qVFamTensorBlock is the
  exact GAP; without it the C3 measure chain cannot be used on qVFam.
- qPilot/theta containment and conditional measure comparison already exist on
  the finite carrier via S1004; they are not the actualC3 chain.
- No fake identification; all cross-carrier transfers are explicit GAP fields.
