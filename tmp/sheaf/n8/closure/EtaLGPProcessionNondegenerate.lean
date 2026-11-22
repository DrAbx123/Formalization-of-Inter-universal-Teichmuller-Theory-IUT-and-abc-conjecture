import tmp.sheaf.n8.closure.EtaSourceLGPProcessionFromCards
import LeanFormal.IUT.IUTIII.Theorem311.SourceK1K2ActualTuplePacket

set_option maxHeartbeats 1200000
set_option relaxedAutoImplicit false

/-!
# LGP procession nondegeneracy audit

The conditional `lgpProcessionFromFour` is the production constructor with
Label = Z, Choice = Nat, base = 0; it is a degenerate identity procession.
This file proves the degeneracy projections, then constructs the actual
nondegenerate-in-ind3 `actualTupleProcession` from the same actual
`SourceDefinition31Data`.  Its horizontal ind1/ind2 are still identity and its
Hodge theater is the canonical identity system; the full paper LGP needs a
`SourceTheorem311Completion` (source Input + q/scale), which is not constructed
by the four source cards.  No degenerate identity is passed off as paper LGP.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceHodgeTheaterBridge
open LeanFormal.IUT.N8Closure.NativeInput
open LeanFormal.IUT.N8Closure.NativeContractFieldsActualAttempt
open LeanFormal.IUT.N8Closure.NativeBadFintypeSourceAttempt
open LeanFormal.IUT.N8Closure.NativeBadFiniteTargetCorrection
open LeanFormal.IUT.N8Closure.NativeReductionRestActual
open LeanFormal.IUT.N8Closure.NativeQParameterActual
open LeanFormal.IUT.N8Closure.NativeSplitMultiplicativeAttempt
open LeanFormal.IUT.N8Closure.NativeTorsionClauseActual
open LeanFormal.IUT.N8Closure.EtaBadFiniteSourceActual
open LeanFormal.IUT.N8Closure.EtaNativeDefinition31ObjectsAssembly
open LeanFormal.IUT.N8Closure.EtaSourceWithBadFiniteCondition
open LeanFormal.IUT.N8Closure.EtaReductionRestAssemblyActual
open LeanFormal.IUT.N8Closure.EtaSplitCardSourceQualification
open LeanFormal.IUT.N8Closure.EtaSourceDefinition31NativeAttempt
open LeanFormal.IUT.N8Closure.EtaTorsionSourceQualification
open LeanFormal.IUT.N8Closure.EtaRemainingDonorsAssembly
open LeanFormal.IUT.N8Closure.EtaSourceLGPProcessionFromCards
open LeanFormal.IUT.K1K2Realization.HullPresentationActualTuplePacket

namespace LeanFormal.IUT.N8Closure.EtaLGPProcessionNondegenerate

universe u

variable {l : PrimeGeFive} (X : N8NativeInput l)

/-- Degeneracy projection: the conditional procession ind1 is identity. -/
theorem lgpProcessionFromFour_ind1_identity
    (I : SourceWithFourQualifications (X := X)) (g : ℤ) (c : ℕ) :
    (lgpProcessionFromFour (X := X) I).ind1 g c = c :=
  rfl

/-- Degeneracy projection: ind2 is identity. -/
theorem lgpProcessionFromFour_ind2_identity
    (I : SourceWithFourQualifications (X := X)) (g : ℤ) (c : ℕ) :
    (lgpProcessionFromFour (X := X) I).ind2 g c = c :=
  rfl

/-- Degeneracy projection: ind3 is identity. -/
theorem lgpProcessionFromFour_ind3_identity
    (I : SourceWithFourQualifications (X := X)) (n : ℕ) (c : ℕ) :
    (lgpProcessionFromFour (X := X) I).ind3 n c = c :=
  rfl

/-- Degeneracy projection: level is constantly zero. -/
theorem lgpProcessionFromFour_level_zero
    (I : SourceWithFourQualifications (X := X)) (c : ℕ) :
    (lgpProcessionFromFour (X := X) I).level c = 0 :=
  rfl

/-- Actual nondegenerate-in-ind3 procession from the same source data, using
the production actual tuple procession constructor. -/
noncomputable def tupleProcessionFromFour
    (I : SourceWithFourQualifications (X := X)) :
    SourceLGPProcession l (ULift.{0} ℤ) ℕ :=
  actualTupleProcession (l := l) (S := sourceDataFromFour (X := X) I)

/-- The tuple procession ind3 is the actual lower-scale map c - n, not
identity. -/
theorem tupleProcessionFromFour_ind3
    (I : SourceWithFourQualifications (X := X)) (n : ℕ) (c : ℕ) :
    (tupleProcessionFromFour (X := X) I).ind3 n c = c - n :=
  rfl

theorem tupleProcessionFromFour_ind3_nondegenerate
    (I : SourceWithFourQualifications (X := X)) (c : ℕ) :
    (tupleProcessionFromFour (X := X) I).ind3 1 (c + 1) = c :=
  rfl

/-- The tuple procession horizontal ind1 is still identity. -/
theorem tupleProcessionFromFour_ind1_identity
    (I : SourceWithFourQualifications (X := X)) (g : ULift.{0} ℤ) (c : ℕ) :
    (tupleProcessionFromFour (X := X) I).ind1 g c = c :=
  rfl

/-- Exact no-go target: a full SourceTheorem311Completion (source Input plus
q/scale data) is not constructed from the four cards. -/
def MissingNondegenerateLGPConstructor : Prop :=
  ¬ Nonempty (SourceTheorem311Completion.{0, 0, 0} l ℤ ℕ)

end LeanFormal.IUT.N8Closure.EtaLGPProcessionNondegenerate

end