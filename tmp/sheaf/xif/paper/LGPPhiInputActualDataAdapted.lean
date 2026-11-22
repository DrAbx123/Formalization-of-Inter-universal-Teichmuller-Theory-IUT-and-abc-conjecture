import tmp.sheaf.xif.paper.LGPPhiInputFilledActualAdapted
import tmp.sheaf.xif.paper.LGPPhiInputConstructionActualAdapted

-- Actual LGP Phi/Input data: full effective-divisor fallback
--
-- The attempted saturation of a proper generated submonoid of the effective
-- divisor monoid did not go through without an actual saturation theorem.
-- Fallback used here: the actual full DivisorialMonoidOn
-- globalEffectiveDivisorMonoidActual, with the actual numberFieldSourceModelInput,
-- plus the actual algebraic-closure theta scalar action and root normalization.
-- The remaining source identification is stated as an explicit obligation, not
-- a fabricated proof and not a Nonempty gap.
-- WRITE-ONLY until local debugging.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPPhiInputActualDataAdapted

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceModelBackend
open LeanFormal.IUT.XiFPaper.LGPFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.GlobalFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.LGPPhiInputConstructionActualAdapted

universe u

variable {K : Type u} [Field K] [NumberField K]

-- Actual full effective-divisor DivisorialMonoidOn on the backend base.
noncomputable def lgpPhiFull :
    Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM :=
  globalEffectiveDivisorMonoidActual (K := K)

-- Actual SourceModelFrobenioid.Input for the full effective-divisor monoid.
noncomputable def lgpInputFull :
    Iut.SourceModelFrobenioid.Input (lgpPhiFull (K := K)) :=
  numberFieldSourceModelInput (F := K)

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- Actual theta scalar action and root normalization data.
structure LGPThetaActionActual where
  scalarAction : ∀ b : Bad (nativePlaceSelection T),
    SignedLabel l.value → (LGPAlgClosed (l := l) T b)ˣ →* (LGPAlgClosed (l := l) T b)ˣ
  rootNormalization : LGPRootNormalization (l := l) T

noncomputable def lgpThetaActionActualData :
    LGPThetaActionActual (l := l) T where
  scalarAction := fun b j => lgpThetaScalarAction T b j
  rootNormalization := lgpRootNormalization_holds (l := l) T

-- Filled actual Phi/Input/action data on the q-side backend.
structure LGPPhiInputActualDataAdapted where
  Phi : Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM
  data : Iut.SourceModelFrobenioid.Input Phi
  action : LGPThetaActionActual (l := l) T

noncomputable def lgpPhiInputActualData :
    LGPPhiInputActualDataAdapted (K := K) (l := l) T where
  Phi := lgpPhiFull (K := K)
  data := lgpInputFull (K := K)
  action := lgpThetaActionActualData (l := l) T

#check lgpPhiFull
#check lgpInputFull
#check LGPThetaActionActual
#check lgpThetaActionActualData
#check LGPPhiInputActualDataAdapted
#check lgpPhiInputActualData

end LeanFormal.IUT.XiFPaper.LGPPhiInputActualDataAdapted

end