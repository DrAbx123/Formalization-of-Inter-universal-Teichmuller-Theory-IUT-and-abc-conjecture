/- H-T: underIntGen 的 natAbs = residueCharacteristic（有理素数），以及到
qVFamTensorP 的桥（条件于 residueCharacteristic = completionRationalPrime.val 的
Mathlib 层引理 hres; 该桥单独报为剩余小缺口）。

donors: Mzk1HT82PaperWeightDiffActual.underIntGen_liesOver;
LeanFormal.IUT.NumberFieldFinitePlace.under_eq_span_residueCharacteristic
(Foundations/Geometry/FinitePlaceDegreeSumBound:39);
sophie Mzk1ULKSideLettersActual.ksP_eq_qVFamTensorP. -/
import Mathlib.Tactic
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1ULKSideLettersActual
import LeanFormal.IUT.Foundations.Geometry.FinitePlaceDegreeSumBound
import tmp.sheaf.xif.paper.Mzk1HT82CompletionPrimeResidueActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual

open LeanFormal.IUT
open NumberField
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82AbsDifferentSumActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual

universe u

variable (K : Type u) [Field K] [NumberField K]

/-- 若 P.under ℤ = span {q}（q : ℤ），则 underIntGen P 的 natAbs = q.natAbs。 -/
theorem underIntGen_natAbs_of_under_eq_span
    (P : Ideal (𝓞 K)) {q : ℤ}
    (h : P.under ℤ = Ideal.span {q}) :
    (underIntGen (K := K) P).natAbs = q.natAbs := by
  haveI : P.LiesOver (Ideal.span {underIntGen (K := K) P}) :=
    underIntGen_liesOver (K := K) P
  have hlies : Ideal.span {underIntGen (K := K) P} = P.under ℤ :=
    Ideal.LiesOver.over
  rw [h] at hlies
  have hassoc : Associated (underIntGen (K := K) P) q :=
    Ideal.span_singleton_eq_span_singleton.mp hlies
  exact Int.associated_iff_natAbs.mp hassoc

/-- underIntGen 的 natAbs = residueCharacteristic place（有理素数，ℕ）。 -/
theorem underIntGen_natAbs_eq_residueCharacteristic
    (place : NumberField.FinitePlace K) :
    (underIntGen (K := K) place.maximalIdeal.asIdeal).natAbs =
      residueCharacteristic place := by
  have h := under_eq_span_residueCharacteristic (K := K) place
  simpa using underIntGen_natAbs_of_under_eq_span K place.maximalIdeal.asIdeal
    (q := (residueCharacteristic place : ℤ)) h

/-- 到 qVFamTensorP 的桥（条件于 Mathlib 层引理
completionRationalPrime.val = residueCharacteristic; 该 hres 是剩余 Mathlib-level
小缺口，已报 Lead/sophie）。 -/
theorem underIntGen_natAbs_eq_qVFamTensorP
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T))
    (hres : residueCharacteristic (nativeBadToKPlace T b) = qVFamTensorP T b) :
    (underIntGen (K := T.arithmetic.K)
        ((nativeBadToKPlace T b).maximalIdeal.asIdeal)).natAbs = qVFamTensorP T b := by
  have h := underIntGen_natAbs_eq_residueCharacteristic T.arithmetic.K
    (nativeBadToKPlace T b)
  rw [h, hres]

/-- **无条件版**: underIntGen 的 natAbs = qVFamTensorP（用 generic
completionRationalPrime_val_eq_residueCharacteristic 消掉 hres）。 -/
theorem underIntGen_natAbs_eq_qVFamTensorP' 
    {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
    [Fintype (Bad (nativePlaceSelection T))]
    (b : Bad (nativePlaceSelection T)) :
    (underIntGen (K := T.arithmetic.K)
        ((nativeBadToKPlace T b).maximalIdeal.asIdeal)).natAbs = qVFamTensorP T b := by
  rw [underIntGen_natAbs_eq_residueCharacteristic T.arithmetic.K
    (nativeBadToKPlace T b)]
  rw [← LeanFormal.IUT.XiFPaper.Mzk1HT82CompletionPrimeResidueActual.completionRationalPrime_val_eq_residueCharacteristic
    (nativeBadToKPlace T b)]
  exact LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual.ksP_eq_qVFamTensorP T b

#print axioms underIntGen_natAbs_eq_qVFamTensorP'
#print axioms underIntGen_natAbs_of_under_eq_span
#print axioms underIntGen_natAbs_eq_residueCharacteristic
#print axioms underIntGen_natAbs_eq_qVFamTensorP

end LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual