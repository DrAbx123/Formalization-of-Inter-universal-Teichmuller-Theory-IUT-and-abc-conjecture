/- R3a (6/n): K-side bad-place Tate data (real parts proved; q/Kummer-root are explicit
  scoped source-data fields, NOT invented).

  RECON (Lead + sophie, 2026-11-18):
  * source structures `SourceNativeInitialThetaData` (SourceDefinition31Quantifiers.lean:1681)
    and `SourceInitialThetaTuple` have NO q field and NO Kummer-root field;
  * the actual q carrier is `QPilotZeroLocusDivisorActual.qVFamily` (Fmod side, line 55),
    not a Kw element; `IUTII/Frobenioid/LocalIntegralUnitKummer` has abstract
    IntegralKummerRootRealization but no connection to qVFamily and no concrete 2l-th root;
  * K-side real donors: ksP/ksPlace/ksD/ksLogP/normDegreeWeight/ksP_eq_qVFamTensorP
    (Mzk1ULKSideLettersActual), CommonPrimeCompletion, and the tree's
    `adicCompletion_uniformizer` (FinitePlaceCompletionLocalInputs.lean:117) gives a real
    uniformizer of the tower's K_w.
  ⇒ `π` is REAL (`ksUniformizer`), place/p/Kv/d/logp/weight are REAL; `q` and the
  2l-th Kummer root are explicit fields of `ThetaKummerRootData` (paper J1, IV L1359-1364:
  |log q| = (1/(2l)) log q, r = q^{1/(2l)}; L1365-1376 CΘ uses the same scale),
  documented source-data prerequisites, not invented elements. No sorry/axiom. -/
import tmp.sheaf.xif.paper.Mzk1URThetaKSideActual
import tmp.sheaf.xif.paper.Mzk1URThetaKLowerCoreActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCompletionLocalInputs
import Mathlib.Tactic

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaBadTateActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKSideActual
open LeanFormal.IUT.XiFPaper.Mzk1URThetaKLowerCoreActual

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- scoped Kummer 根数据（paper J1：q 与它的 2l 次根；结构参数 d 在实例化时取 2*l.value）。 -/
structure ThetaKummerRootData (Kv : Type*) [Field Kv] (d : ℕ) where
  q : Kv
  root : Kv
  hroot : root ^ d = q

/-- 坏位 Tate 数据（实际塔）。 -/
structure ThetaBadTateData (b : Bad (nativePlaceSelection T)) where
  p : ℕ
  hprime : Nat.Prime p
  place : NumberField.FinitePlace T.arithmetic.K
  Kv : Type
  [fieldKv : Field Kv]
  /-- 真实 uniformizer（ksUniformizer）。 -/
  π : Kv
  /-- scoped Kummer 根数据：q 及 2l 次根（d := 2 * l.value）。 -/
  kummer : ThetaKummerRootData Kv (2 * l.value)
  d : ℝ
  logp : ℝ
  weight : ℝ

attribute [instance] ThetaBadTateData.fieldKv

/-- ksUniformizer：塔的 K_w 的 uniformizer，直接取 `FinitePlaceStepVAssembly.arithmeticTupleLocalUniformizer`
    （K 侧 tensor block 的局部因子整数环的 irreducible 生成元，即 kurt 的 K-side uniformizer）。 -/
noncomputable def ksUniformizer (b : Bad (nativePlaceSelection T)) :
    CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ())) :=
  ((arithmeticTupleLocalUniformizer (places := ksPlaces T b)
    (tuple := ksTuple) (i := ())).val :
    CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ())))

theorem ksUniformizer_ne_zero (b : Bad (nativePlaceSelection T)) :
    ksUniformizer T b ≠ 0 := by
  intro h
  have hirr := arithmeticTupleLocalUniformizer_irreducible
    (places := ksPlaces T b) (tuple := ksTuple) ()
  refine hirr.ne_zero (Subtype.ext ?_)
  simpa [ksUniformizer] using h

/-- 从塔的 K 侧 donor 组装坏位 Tate 数据；π 取真实的 ksUniformizer，kummer 为显式 source-data。 -/
noncomputable def thetaBadTateData (b : Bad (nativePlaceSelection T))
    (kummer : ThetaKummerRootData (CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))) (2 * l.value)) :
    ThetaBadTateData T b where
  p := ksP T b
  hprime := (completionRationalPrime_fact (nativeBadToKPlace T b)).out
  place := nativeBadToKPlace T b
  Kv := CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))
  fieldKv := inferInstance
  π := ksUniformizer T b
  kummer := kummer
  d := ksD T b
  logp := ksLogP T b
  weight := normDegreeWeight T b

theorem thetaBadTateData_Kv (b : Bad (nativePlaceSelection T))
    (kummer : ThetaKummerRootData (CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))) (2 * l.value)) :
    (thetaBadTateData T b kummer).Kv = CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ())) := rfl

theorem thetaBadTateData_pi (b : Bad (nativePlaceSelection T))
    (kummer : ThetaKummerRootData (CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))) (2 * l.value)) :
    (thetaBadTateData T b kummer).π = ksUniformizer T b := rfl

theorem thetaBadTateData_p_eq_qVFamTensorP (b : Bad (nativePlaceSelection T))
    (kummer : ThetaKummerRootData (CommonPrimeCompletion ((ksPlaces T b) () (ksTuple ()))) (2 * l.value)) :
    (thetaBadTateData T b kummer).p = qVFamTensorP T b :=
  ksP_eq_qVFamTensorP T b

#print axioms ksUniformizer_ne_zero
#print axioms thetaBadTateData_Kv
#print axioms thetaBadTateData_pi
#print axioms thetaBadTateData_p_eq_qVFamTensorP

end LeanFormal.IUT.XiFPaper.Mzk1G1F2ThetaBadTateActual