import tmp.sheaf.xif.paper.LGPPhiInputActual
import tmp.sheaf.n8.closure.C3Roots

-- LGP theta root data from the actual algebraic closure Kummer tower
--
-- The completion is not algebraically closed, so TwoLthRootQVActual cannot
-- produce a completion root system unconditionally. The algebraic closure
-- DOES carry an actual NatRootSystem (C3Roots.algClosedRootSystem), hence an
-- actual 2l-th root of unitToAlgClosed(qVUnit). This file constructs that
-- actual algebraic-closure root and theta values.
--
-- It does NOT fabricate a map from the algebraic-closure root into the
-- completion or into the LGP DivisorialMonoidOn/Input. That cross-domain and
-- Kummer-action data is recorded as an exact object-level gap.
-- WRITE-ONLY; no local lake/lean.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.LGPPhiInputActual
open LeanFormal.IUT.XiFPaper.LGPFrobenioidPresentationActual
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.TwoLthRootQVActual
open LeanFormal.IUT.N8Closure.C3Roots

universe u

variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

-- The actual algebraic closure of the completion carrying qVFamily.
abbrev LGPAlgClosed (b : Bad (nativePlaceSelection T)) : Type :=
  AlgebraicClosure (Completion ((nativeBadLift T).lift b))

-- The actual algebraic-closure root system over the qV unit.
noncomputable def lgpAlgClosedRootSystem
    (b : Bad (nativePlaceSelection T)) :
    NatRootSystem (unitToAlgClosed (qVUnit T b)) :=
  algClosedRootSystem (qVUnit T b)

-- The actual 2l-th root in the algebraic closure.
noncomputable def lgpTwoLthRootAlgClosed
    (b : Bad (nativePlaceSelection T)) :
    (LGPAlgClosed (l := l) T b)ˣ :=
  (lgpAlgClosedRootSystem T b).root (twoLExponent l)

theorem lgpTwoLthRootAlgClosed_pow
    (b : Bad (nativePlaceSelection T)) :
    lgpTwoLthRootAlgClosed T b ^ twoLExponent l =
      unitToAlgClosed (qVUnit T b) := by
  unfold lgpTwoLthRootAlgClosed lgpAlgClosedRootSystem
  exact NatRootSystem.pow_self (algClosedRootSystem (qVUnit T b))
    (twoLExponent l) (by
      unfold twoLExponent
      exact Nat.mul_ne_zero (by norm_num) l.prime.ne_zero)

-- Actual algebraic-closure theta values (root)^(j^2).
noncomputable def lgpThetaValueAlgClosed
    (b : Bad (nativePlaceSelection T))
    (j : SignedLabel l.value) :
    (LGPAlgClosed (l := l) T b)ˣ :=
  lgpTwoLthRootAlgClosed T b ^ (gaussExponent j.1).toNat

-- Actual qV divisor exponent data: the qVFamily order at each bad place.
noncomputable def lgpQVDivisorExponent
    (b : Bad (nativePlaceSelection T)) : Nat :=
  (qVFamily T b).order

theorem lgpQVDivisorExponent_pos
    (b : Bad (nativePlaceSelection T)) :
    0 < lgpQVDivisorExponent T b :=
  (qVFamily T b).order_pos

-- Exact cross-domain gap: the algebraic-closure root/theta values are actual,
-- but there is no constructed map from this algebraic closure into the
-- completion (where the LGP DivisorialMonoidOn/Input and Kummer action live).
structure LGPRootCrossDomainGap where
  algClosedCarrier : Type
  completionRoot : Prop
  rootTransport : Prop
  kummerCompatibility : Prop

def LGPRootCrossDomainObstruction : Prop :=
  Nonempty (LGPRootCrossDomainGap)

-- Exact object-level gap: the LGP DivisorialMonoidOn/Input built from the
-- actual qV divisor data and the algebraic-closure theta action is still not
-- supplied. This is not a value-layer object.
structure LGPPhiInputFromQVData where
  Phi : Iut.DivisorialMonoidOn (LGPBaseCategory.{u}) LGPIsFSM
  data : Iut.SourceModelFrobenioid.Input Phi
  qVExponent : Bad (nativePlaceSelection T) → Nat
  qVExponent_eq : qVExponent = lgpQVDivisorExponent T
  thetaValueAction : Prop
  rootNormalization : Prop
  is_LGP : Prop

def LGPPhiInputFromQVDataObstruction {l : PrimeGeFive}
    (T : SourceNativeInitialThetaData.{0} l) : Prop :=
  Nonempty (LGPPhiInputFromQVData.{u} T)

#check lgpAlgClosedRootSystem
#check lgpTwoLthRootAlgClosed
#check lgpTwoLthRootAlgClosed_pow
#check lgpThetaValueAlgClosed
#check lgpQVDivisorExponent
#check LGPRootCrossDomainGap
#check LGPRootCrossDomainObstruction
#check LGPPhiInputFromQVData
#check LGPPhiInputFromQVDataObstruction

end LeanFormal.IUT.XiFPaper.LGPPhiInputFromAlgebraicClosureActual

end