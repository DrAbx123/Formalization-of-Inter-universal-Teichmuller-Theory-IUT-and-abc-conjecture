import tmp.sheaf.xif.paper.S530EtThQSqrtRecipeSpecActual
import tmp.sheaf.xif.paper.S531EtThThetaUnitRecipeActual
import tmp.sheaf.xif.paper.S546QHalfCandidateActual
import tmp.sheaf.xif.paper.S517EtThSpecialTwoTorsionGapActual
import tmp.sheaf.xif.paper.S485TateTwoTorsionQSqrtActual

-- S611: actual special 2-torsion point and actual qHalf from S546;
-- evalSection/normalization/constant-multiple rigidity explicit or exact.

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S611SpecialTwoTorsionEvaluationActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QPilotZeroLocusDivisorActual
open LeanFormal.IUT.XiFPaper.S485TateTwoTorsionQSqrtActual
open LeanFormal.IUT.XiFPaper.S494TateTwoTorsionConverseGapActual
open LeanFormal.IUT.XiFPaper.S546QHalfCandidateActual
open LeanFormal.IUT.XiFPaper.S530EtThQSqrtRecipeSpecActual
open LeanFormal.IUT.XiFPaper.S531EtThThetaUnitRecipeActual
open LeanFormal.IUT.XiFPaper.S517EtThSpecialTwoTorsionGapActual

universe u
variable {l : PrimeGeFive}
variable (T : SourceNativeInitialThetaData.{0} l)
variable (b : Bad (nativePlaceSelection T))

-- Actual qHalf from S546 in the same ACF as S485.
noncomputable def qHalfRootS546 : (ACF T b)ˣ :=
  S546QHalfCandidateActual.qHalfRoot (l := l)
    (K := T.arithmetic.F) (place := (nativeBadLift T).lift b) (qVFamily T b)

theorem qHalfRootS546_pow :
    qHalfRootS546 (l := l) T b ^ (2 * l.value) = qUnit T b := by
  simpa [qHalfRootS546, qUnit] using
    (S546QHalfCandidateActual.qHalfRoot_pow (l := l)
      (K := T.arithmetic.F) (place := (nativeBadLift T).lift b) (qVFamily T b))

noncomputable def qHalfUnitS546 : (ACF T b)ˣ :=
  qHalfRootS546 (l := l) T b ^ l.value

theorem qHalfUnitS546_sq :
    qHalfUnitS546 (l := l) T b ^ 2 = qUnit T b := by
  rw [qHalfUnitS546, ← pow_mul,
    show l.value * 2 = 2 * l.value by ring, qHalfRootS546_pow]

-- Actual special 2-torsion point: the q-sqrt point from S485.
noncomputable def specialQSqrtPoint : ConversePoint T b :=
  qSqrtTwoTorsionPoint (l := l) T b

theorem specialQSqrtPoint_two_torsion :
    specialQSqrtPoint (l := l) T b + specialQSqrtPoint (l := l) T b = 0 :=
  qSqrtTwoTorsionPoint_double (l := l) T b

-- Conditional evaluation/normalization data; evalSection is explicit.
structure QHalfSpecialEvaluationData where
  specialPoint : ConversePoint T b
  specialPoint_two_torsion : specialPoint + specialPoint = 0
  specialPoint_component_condition : Prop
  evalSection : ConversePoint T b → ACF T b
  evalSection_special : Prop
  qHalfRoot : (ACF T b)ˣ
  qHalfRoot_pow : qHalfRoot ^ (2 * l.value) = qUnit T b
  qHalfUnit : (ACF T b)ˣ
  qHalfUnit_eq : qHalfUnit = qHalfRoot ^ l.value
  qHalfUnit_sq : qHalfUnit ^ 2 = qUnit T b
  normalization : Prop
  constant_multiple_rigidity : Prop

noncomputable def qHalfSpecialEvaluationData
    (specialPoint_component_condition : Prop)
    (evalSection : ConversePoint T b → ACF T b)
    (evalSection_special normalization constant_multiple_rigidity : Prop) :
    QHalfSpecialEvaluationData (l := l) T b where
  specialPoint := specialQSqrtPoint (l := l) T b
  specialPoint_two_torsion := specialQSqrtPoint_two_torsion (l := l) T b
  specialPoint_component_condition := specialPoint_component_condition
  evalSection := evalSection
  evalSection_special := evalSection_special
  qHalfRoot := qHalfRootS546 (l := l) T b
  qHalfRoot_pow := qHalfRootS546_pow (l := l) T b
  qHalfUnit := qHalfUnitS546 (l := l) T b
  qHalfUnit_eq := rfl
  qHalfUnit_sq := qHalfUnitS546_sq (l := l) T b
  normalization := normalization
  constant_multiple_rigidity := constant_multiple_rigidity

#check qHalfRootS546_pow
#check qHalfUnitS546_sq
#check specialQSqrtPoint_two_torsion
#check qHalfSpecialEvaluationData

end LeanFormal.IUT.XiFPaper.S611SpecialTwoTorsionEvaluationActual

end