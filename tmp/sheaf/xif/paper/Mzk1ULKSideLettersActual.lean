/- U-C (P): K-side letters for hstepVIII (paper IUT IV L1626-1650: k_i := K_{v_i},
R_i := O_{K_{v_i}}; route 5.2 L370: actual base completions = base places with
K-valued completions).  Outer weight = normDegreeWeight (f_P/[K:Q], Def 1.9 /
L1236-1251).  The Step(v) inner lambda/Sum-lambda average is `paperWeight`
(auxiliary; different slot).

ksP b := rational prime of the bad K-place (nativeBadToKPlace T b); this is
proved equal to qVFamTensorP T b in the next batch via the comap transfer along
Q -> Fmod -> K (completionRationalPrime_eq_of_comap_eq at
FinitePlaceCommonPrimeCompletion:70 plus nativeBadToKPlace_comap); letters here
are stated with ksP so that the packaging is definitional (rfl).
-/
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.Mzk1ULPaperLettersActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceFractionalAbsorption
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.LocalFields.IntegralTraceDualTensorInclusion
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.LocalFieldLogarithm

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- the rational prime of the bad K-place nativeBadToKPlace T b (equals
qVFamTensorP T b; the equality is the next-batch comap transfer lemma). -/
noncomputable def ksP (b : Bad (nativePlaceSelection T)) : ℕ :=
  (completionRationalPrime (nativeBadToKPlace T b)).val

/-- the K-side place, packaged at its own rational prime (second field is rfl). -/
noncomputable def ksPlace (b : Bad (nativePlaceSelection T)) :
    FinitePlaceAtPrime T.arithmetic.K ((completionRationalPrime (nativeBadToKPlace T b)).val) :=
  ⟨nativeBadToKPlace T b, rfl⟩

/-- K-side absolute local different order delta_b (K_w / Q_p), paper's d_i. -/
noncomputable def ksD (b : Bad (nativePlaceSelection T)) : ℝ := by
  letI : Fact (Nat.Prime ((completionRationalPrime (nativeBadToKPlace T b)).val)) :=
    completionRationalPrime_fact (nativeBadToKPlace T b)
  exact LeanFormal.IUT.LocalFieldLogarithm.localNormOrder ((completionRationalPrime (nativeBadToKPlace T b)).val)
      ((LeanFormal.IUT.IntegralTraceDualTensorInclusion.localDifferentGenerator
        (p := (completionRationalPrime (nativeBadToKPlace T b)).val) (L := CommonPrimeCompletion (ksPlace T b))) :
        CommonPrimeCompletion (ksPlace T b))
    * Real.log ((completionRationalPrime (nativeBadToKPlace T b)).val)

/-- the K-side log p letter. -/
noncomputable def ksLogP (b : Bad (nativePlaceSelection T)) : ℝ :=
  Real.log (ksP T b)

/-- the paper normalized degree weight f_P/[K:Q] at the bad K-place,
reusing david's paperDifferentWeight (Mzk1HT82PaperWeightDiffActual). -/
noncomputable def normDegreeWeight (b : Bad (nativePlaceSelection T)) : ℝ :=
  LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual.paperDifferentWeight
    T.arithmetic.K (nativeBadToKPlace T b).maximalIdeal.asIdeal


/-- **PROVED bridge**: the rational prime of the bad K-place equals the qVFam
rational prime (both places lie over the same bad moduli place b.1; the
contraction maps compose along Q -> Fmod -> K resp. Q -> Fmod -> F). -/
theorem ksP_eq_qVFamTensorP (b : Bad (nativePlaceSelection T)) :
    ksP T b = qVFamTensorP T b := by
  unfold ksP qVFamTensorP
  have hK : NumberFieldFinitePlace.comap (k := ℚ) (nativeBadToKPlace T b)
      = NumberFieldFinitePlace.comap (k := ℚ) (nativeBadToFPlace T b) := by
    rw [← NumberFieldFinitePlace.comap_comap (k := ℚ)
      (K := T.arithmetic.Fmod) (L := T.arithmetic.K) (nativeBadToKPlace T b)]
    rw [nativeBadToKPlace_comap]
    rw [← NumberFieldFinitePlace.comap_comap (k := ℚ)
      (K := T.arithmetic.Fmod) (L := T.arithmetic.F) (nativeBadToFPlace T b)]
    rw [nativeBadToFPlace_comap]
  change (completionRationalPrime (nativeBadToKPlace T b)).val
      = (completionRationalPrime (nativeBadToFPlace T b)).val
  unfold completionRationalPrime
  rw [hK]

end LeanFormal.IUT.XiFPaper.Mzk1ULKSideLettersActual
end