import tmp.sheaf.xif.paper.LGPFrobenioidPresentationActual
import tmp.sheaf.xif.paper.TwoLthRootQVActual
import LeanFormal.IUT.IUTIII.Theorem311.SourceLGPMonoidLayer

-- LGP Phi/Input: actual qVFamily/2l-root data and exact object-level gap
--
-- The only actual input available for the LGP theta values is the qVFamily
-- (QPilotZeroLocusDivisorActual) together with a compatible 2l-th root system
-- in the completion (TwoLthRootQVActual). The root system is conditional:
-- the completion is not algebraically closed, so the actual 2l-th root is
-- recorded as an exact gap unless a NatRootSystem is supplied.
--
-- The LGP DivisorialMonoidOn/Input itself (the LGP-monoid divisor data and
-- theta-value action on the global realified Frobenioid) is not constructed
-- from the number-field backend; it is recorded as an exact object-level gap.
-- No value-layer theta values are used.
-- WRITE-ONLY; no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPPhiInputActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LGPFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- The actual qVFamily is the only q family used for the LGP theta input.
noncomputable abbrev lgpQV (b : Bad (nativePlaceSelection T)) :=
  qVFamily T b

theorem lgpQV_q_eq (b : Bad (nativePlaceSelection T)) :
    (lgpQV T b).q = (qVFamily T b).q := rfl

-- A compatible 2l-th root system gives an actual 2l-th root unit in the
-- completion, determined up to μ_{2l}.
noncomputable def lgpTwoLthRoot
    (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVUnit T b)) :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  twoLthRoot T b R

theorem lgpTwoLthRoot_pow
    (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVUnit T b)) :
    lgpTwoLthRoot T b R ^ twoLExponent l = qVUnit T b :=
  twoLthRoot_pow T b R

-- Actual LGP theta value at a nonzero theta label, as a completion unit
-- (root)^(j^2). No real-valued or value-layer substitution is made.
noncomputable def lgpThetaValue
    (b : Bad (nativePlaceSelection T))
    (R : NatRootSystem (qVUnit T b))
    (j : SignedLabel l.value) :
    (Completion ((nativeBadLift T).lift b))ˣ :=
  lgpTwoLthRoot T b R ^ (gaussExponent j.1).toNat

-- The theta generator index interface is actual (Fin l*). The LGP monoid
-- itself must carry its own actual carrier; the standard finite interface is
-- not the source LGP-monoid divisor data.
abbrev lgpThetaGeneratorIndex : Type :=
  Fin (lStar l.value)

-- Exact root-system gap: a compatible NatRootSystem for every actual qV unit.
def LGPThetaRootSystemGap : Prop :=
  Nonempty (∀ b : Bad (nativePlaceSelection T), NatRootSystem (qVUnit T b))

-- Exact object-level gap for the LGP presentation data: the actual
-- DivisorialMonoidOn and Input carrying the LGP-monoid divisor/theta action
-- are not constructed. This is the same object as
-- LGPFrobenioidPresentationData; it is recorded here with the theta
-- normalization field attached.
structure LGPPhiInputGap where
  Phi : Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM
  data : Iut.SourceModelFrobenioid.Input Phi
  thetaAction : Prop
  twoLNormalization : Prop
  is_LGP : Prop

def LGPPhiInputObstruction : Prop :=
  Nonempty (LGPPhiInputGap.{u})

-- Conditional actual LGPFrobenioidPresentationData from explicit Phi/Input
-- and the exact LGP/normalization proofs.
noncomputable def lgpPresentationDataOfPhiInput
    (D : LGPPhiInputGap.{u})
    (hTheta : D.thetaAction) (hRoot : D.twoLNormalization)
    (hLGP : D.is_LGP) :
    LGPFrobenioidPresentationData.{u} where
  Phi := D.Phi
  data := D.data
  is_LGP := D.is_LGP

-- Conditional presentation from the explicit LGP Phi/Input object.
noncomputable def lgpFrobenioidPresentationOfPhiInput
    (D : LGPPhiInputGap.{u})
    (hTheta : D.thetaAction) (hRoot : D.twoLNormalization)
    (hLGP : D.is_LGP) : Iut.FrobenioidPresentation :=
  lgpFrobenioidPresentationOfData
    (lgpPresentationDataOfPhiInput D hTheta hRoot hLGP)

#check lgpQV
#check lgpTwoLthRoot
#check lgpTwoLthRoot_pow
#check lgpThetaValue
#check LGPThetaRootSystemGap
#check LGPPhiInputGap
#check LGPPhiInputObstruction
#check lgpPresentationDataOfPhiInput
#check lgpFrobenioidPresentationOfPhiInput

end LeanFormal.IUT.XiFPaper.LGPPhiInputActual

end