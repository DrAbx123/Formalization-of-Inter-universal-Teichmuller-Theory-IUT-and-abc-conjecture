import tmp.sheaf.xif.paper.LGPPhiInputConstructionActual
import tmp.sheaf.xif.paper.GlobalFrobenioidPresentationActual
import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceModelBackend

-- LGP Phi/Input: actual q-side DivisorialMonoidOn/Input filled; exact LGP gap
--
-- The actual DivisorialMonoidOn `globalEffectiveDivisorMonoidActual` and the
-- actual SourceModelFrobenioid.Input `numberFieldSourceModelInput` are filled
-- as the q-side backend objects. The algebraic-closure root normalization and
-- scalar theta action are actual proofs from LGPPhiInputConstructionActual.
--
-- These are NOT asserted to be the LGP-monoid DivisorialMonoidOn/Input of
-- C^⊩_LGP/C^⊩_lgp: that source-specific identification is an exact object-level
-- gap. No value-layer substitution.
-- WRITE-ONLY; no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPPhiInputFilledActual

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.LGPFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputConstructionActual

universe u

variable {K : Type u} [Field K] [NumberField K]

-- Actual q-side DivisorialMonoidOn on the same one-object backend base.
noncomputable def lgpPhiCandidate :
    Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM :=
  globalEffectiveDivisorMonoidActual (K := K)

-- Actual SourceModelFrobenioid.Input for that DivisorialMonoidOn.
noncomputable def lgpInputCandidate :
    Iut.SourceModelFrobenioid.Input (lgpPhiCandidate (K := K)) :=
  numberFieldSourceModelInput (F := K)

-- The filled actual data: Phi, Input, and the actual algebraic-closure root
-- normalization and scalar theta action from the previous file.
structure LGPPhiInputFilled
    (T : SourceNativeInitialThetaData.{0} l) where
  Phi : Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM
  data : Iut.SourceModelFrobenioid.Input Phi
  rootNormalization : LGPRootNormalization (l := l) T

noncomputable def lgpPhiInputFilled
    (T : SourceNativeInitialThetaData.{0} l) :
    LGPPhiInputFilled (l := l) (K := K) T where
  Phi := lgpPhiCandidate (K := K)
  data := lgpInputCandidate (K := K)
  rootNormalization := lgpRootNormalization_holds (l := l) T

-- Exact object-level gap: the actual q-side Phi/Input and the algebraic-closure
-- root normalization/scalar action do not identify these data with the LGP
-- global realified monoid or its tensor-packet action. The identification is
-- recorded as an exact gap, not asserted.
structure LGPPhiInputLGPIdentificationGap where
  qSidePhi : Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM
  qSideData : Iut.SourceModelFrobenioid.Input qSidePhi
  is_LGP : Prop
  tensorAction : Prop
  rootCrossDomain : Prop

def LGPPhiInputLGPIdentificationGapObstruction : Prop :=
  Nonempty (LGPPhiInputLGPIdentificationGap.{u})

#check lgpPhiCandidate
#check lgpInputCandidate
#check LGPPhiInputFilled
#check lgpPhiInputFilled
#check LGPPhiInputLGPIdentificationGap
#check LGPPhiInputLGPIdentificationGapObstruction

end LeanFormal.IUT.XiFPaper.LGPPhiInputFilledActual

end