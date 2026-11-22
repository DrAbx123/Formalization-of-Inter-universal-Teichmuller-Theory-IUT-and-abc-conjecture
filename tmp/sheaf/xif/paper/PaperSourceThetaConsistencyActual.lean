import tmp.sheaf.xif.paper.PaperSourceGeometryActual
import tmp.sheaf.xif.paper.QVFamThetaImageActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual

/-! # Source q / thetaPacket consistency with CompletionValuedSourceGeometry

The new source geometry has qUnit and thetaPacket fields.  This file constructs
the geometry from the actual qVFamily q (at one bad place b) instead of taking
thetaPacket as an independent input:

* qUnit is the actual qVFamily q as a unit of the normalized completion;
* thetaPacket is FiniteThetaPacket.ofQ (||qUnit||) (norm positive), so the
  geometry field thetaPacket.q = ||qUnit v|| is proved by rfl;
* theta special values are the actual powers ||qUnit||^(j^2).

The source qVFamily q is a classical q.  If the paper theta value needs a
2l-th root, the root is not in the normalized completion; the exact root gap is
recorded as a Prop, not fabricated.

No independent thetaPacket parameter is used for the constructed geometry.
No sorry/axiom. -/

noncomputable section
open scoped BigOperators
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.PaperSourceGeometryActual
open LeanFormal.IUT.XiFPaper.QVFamThetaImageActual
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

/-- The actual normalized completion place of b. -/
abbrev sourceThetaPlace : FinitePlaceAtPrime T.arithmetic.F (qVFamTensorP T b) :=
  qVFamTensorPlaces T b () (qVFamTensorTuple ())

/-- Actual qVFamily q as a unit of the normalized completion. -/
noncomputable def sourceQVFamilyUnit :
    CompletionValueCarrier (sourceThetaPlace T b) :=
  Units.mk0 ((qVFamily T b).q : CommonPrimeCompletion (sourceThetaPlace T b))
    (by
      intro h
      have hzero : (qVFamily T b).q = 0 := by
        exact h
      exact (qVFamily T b).q_ne_zero hzero)

/-- The actual normalized norm of the source q unit. -/
noncomputable def sourceThetaQ : Real :=
  ‖(sourceQVFamilyUnit T b : CommonPrimeCompletion (sourceThetaPlace T b))‖

/-- The actual positive norm of the source q unit. -/
theorem sourceThetaQ_pos : 0 < sourceThetaQ T b :=
  norm_pos_iff.mpr (Units.ne_zero (sourceQVFamilyUnit T b))

/-- Actual theta packet determined by the source q unit norm, not supplied. -/
noncomputable def sourceThetaPacketFromQ : FiniteThetaPacket l :=
  FiniteThetaPacket.ofQ (sourceThetaQ T b) (sourceThetaQ_pos T b)

/-- The constructed theta packet's q is exactly the norm of the actual qUnit. -/
theorem sourceThetaPacketFromQ_q :
    (sourceThetaPacketFromQ (l := l) T b).q = sourceThetaQ T b := rfl

/-- Actual theta special values: scale j = q^(j^2). -/
theorem sourceThetaPacketFromQ_scale
    (j : SignedLabel l.value) :
    (sourceThetaPacketFromQ (l := l) T b).scale j =
      (sourceThetaQ T b) ^ (gaussExponent j.1).toNat := rfl

/-- The actual consistency bridge: CompletionValuedSourceGeometry built from
the source q, with thetaPacket derived from its norm. -/
noncomputable def paperSourceGeometryFromQ :
    CompletionValuedSourceGeometry (l := l) (K := T.arithmetic.F)
      (p := qVFamTensorP T b) PUnit where
  place := fun _ => sourceThetaPlace T b
  qUnit := fun _ => sourceQVFamilyUnit T b
  thetaPacket := sourceThetaPacketFromQ (l := l) T b
  thetaPacket_q_eq := fun _ => rfl

/-- Exact root gap: the paper theta value may need a 2l-th root of the
classical source q, but no root is constructed in the normalized completion. -/
structure PaperThetaRootGap where
  classicalQ : Real
  classicalQ_eq : classicalQ = sourceThetaQ T b
  rootOrder : Nat
  rootOrder_eq : rootOrder = 2 * l.value
  rootInNormalizedCompletion : Prop
  rootInNormalizedCompletion_eq : rootInNormalizedCompletion =
    (∃ r : CommonPrimeCompletion (sourceThetaPlace T b),
      r ^ (2 * l.value) = (sourceQVFamilyUnit T b :
        CommonPrimeCompletion (sourceThetaPlace T b)))
  rootInAlgebraicClosure : Prop
  rootInAlgebraicClosure_eq : rootInAlgebraicClosure =
    (∃ r : AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)),
      r ^ (2 * l.value) =
        algebraMap (CommonPrimeCompletion (sourceThetaPlace T b))
          (AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)))
          (sourceQVFamilyUnit T b : CommonPrimeCompletion (sourceThetaPlace T b)))

/-- The exact root-gap record, without asserting the missing completion root. -/
noncomputable def paperThetaRootGap : PaperThetaRootGap T b where
  classicalQ := sourceThetaQ T b
  classicalQ_eq := rfl
  rootOrder := 2 * l.value
  rootOrder_eq := rfl
  rootInNormalizedCompletion :=
    (∃ r : CommonPrimeCompletion (sourceThetaPlace T b),
      r ^ (2 * l.value) = (sourceQVFamilyUnit T b :
        CommonPrimeCompletion (sourceThetaPlace T b)))
  rootInNormalizedCompletion_eq := rfl
  rootInAlgebraicClosure :=
    (∃ r : AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)),
      r ^ (2 * l.value) =
        algebraMap (CommonPrimeCompletion (sourceThetaPlace T b))
          (AlgebraicClosure (CommonPrimeCompletion (sourceThetaPlace T b)))
          (sourceQVFamilyUnit T b : CommonPrimeCompletion (sourceThetaPlace T b)))
  rootInAlgebraicClosure_eq := rfl

end LeanFormal.IUT.XiFPaper.PaperSourceThetaConsistencyActual

end
