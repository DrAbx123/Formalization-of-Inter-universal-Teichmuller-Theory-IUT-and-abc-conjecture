/- R1 F-side hprime: natAbs(underIntGen x) = qVFamTensorP T b for x in the F-fiber over b.1.
   Proof: x.under Fmod = b.1.maxIdeal = qVFamTensorPlace.maxIdeal.under Fmod
   (LiesOver.over + nativeBadLift.lift_comap/comap_maximalIdeal);
   then under ℤ equal via Ideal.under_under; generator congr;
   then underIntGen_natAbs_eq_residueCharacteristic + completionRationalPrime bridge. -/
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import tmp.sheaf.xif.paper.Mzk1HT82CompletionPrimeResidueActual
import tmp.sheaf.xif.paper.QVFamTensorCoefficientActual
import tmp.sheaf.xif.paper.VbadPlaceIndexingActual
import Mathlib.RingTheory.RamificationInertia.Basic
import Mathlib.RingTheory.Ideal.Over
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR1FiberPrimeFActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82CompletionPrimeResidueActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- qVFamTensorPlace 的 maximal ideal 在 Fmod 上的 under 等于 b.1.maximalIdeal。 -/
theorem qVFamTensorPlace_under (b : Bad (nativePlaceSelection T)) :
    (qVFamTensorPlace T b).maximalIdeal.asIdeal.under (𝓞 (T.arithmetic.Fmod)) =
      b.1.maximalIdeal.asIdeal := by
  rw [Ideal.under_def]
  rw [← NumberFieldFinitePlace.comap_maximalIdeal (k := T.arithmetic.Fmod)
    (qVFamTensorPlace T b)]
  rw [show NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod) (qVFamTensorPlace T b) = b.1
    from (nativeBadLift T).lift_comap b]

/-- F-side hprime: underIntGen natAbs = qVFamTensorP on the b-fiber. -/
theorem fiber_prime_consistency_F (b : Bad (nativePlaceSelection T))
    {x : Ideal (𝓞 (T.arithmetic.F))}
    (hx : x ∈ IsDedekindDomain.primesOverFinset (b.1.maximalIdeal.asIdeal)
      (𝓞 (T.arithmetic.F))) :
    (underIntGen (K := T.arithmetic.F) x).natAbs = qVFamTensorP T b := by
  have hb0 : b.1.maximalIdeal.asIdeal ≠ ⊥ := b.1.maximalIdeal.ne_bot
  have hmem := (IsDedekindDomain.mem_primesOverFinset_iff
    (B := 𝓞 (T.arithmetic.F)) hb0).mp hx
  have hx_over : x.under (𝓞 (T.arithmetic.Fmod)) = b.1.maximalIdeal.asIdeal := (hmem.2.over).symm
  have h_under : x.under (𝓞 (T.arithmetic.Fmod)) =
      (qVFamTensorPlace T b).maximalIdeal.asIdeal.under (𝓞 (T.arithmetic.Fmod)) := by
    rw [hx_over, qVFamTensorPlace_under]
  have h1 := Ideal.under_under (A := ℤ) (B := 𝓞 (T.arithmetic.Fmod))
    (C := 𝓞 (T.arithmetic.F)) x
  have h2 := Ideal.under_under (A := ℤ) (B := 𝓞 (T.arithmetic.Fmod))
    (C := 𝓞 (T.arithmetic.F)) ((qVFamTensorPlace T b).maximalIdeal.asIdeal)
  have hZ : x.under ℤ = ((qVFamTensorPlace T b).maximalIdeal.asIdeal).under ℤ := by
    rw [← h1, ← h2, h_under]
  have hspan : x.under ℤ =
      Ideal.span {(residueCharacteristic (qVFamTensorPlace T b) : ℤ)} := by
    rw [hZ, under_eq_span_residueCharacteristic (K := T.arithmetic.F) (qVFamTensorPlace T b)]
  have hnat := underIntGen_natAbs_of_under_eq_span (T.arithmetic.F) x
    (q := (residueCharacteristic (qVFamTensorPlace T b) : ℤ)) hspan
  rw [hnat]
  rw [Int.natAbs_natCast]
  unfold qVFamTensorP
  exact (completionRationalPrime_val_eq_residueCharacteristic (qVFamTensorPlace T b)).symm

#print axioms qVFamTensorPlace_under
#print axioms fiber_prime_consistency_F

end LeanFormal.IUT.XiFPaper.Mzk1ULR1FiberPrimeFActual