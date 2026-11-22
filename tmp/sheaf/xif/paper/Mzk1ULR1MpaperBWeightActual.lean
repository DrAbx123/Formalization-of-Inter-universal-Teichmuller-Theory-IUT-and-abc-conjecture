/- R1 per-b weight identity: MpaperB_b = - qPilotMass (cPFullFiber_b), unconditionally.
   cPFullFiber_b := (1/[F:Q]) * Sum_{P|b} f_P * orderAtFPlace P   (full-fiber paper c_P);
   MpaperB_b = (1/(2l)) * (1/[F:Q]) * Sum f_P order_P log p (OrdFiberTower def);
   qPilotMass cP = -(cP/(2l)) * log p  (Mzk1ULR1QPilotMassBasicActual.qPilotMass_eq);
   => MpaperB_b = - qPilotMass cPFullFiber_b.  No fake equality; direct unfolding/ring,
   using the F-side fiber-prime consistency natAbs(underIntGen P) = qVFamTensorP b for every
   P | b (proved below from P.under Fmod = b.1 and under_eq_span_residueCharacteristic; this
   is the unconditional hprime, cf. Mzk1ULR1FiberPrimeFActual.fiber_prime_consistency_F).
   NOTE (route R0.2): cPFullFiber_b = (1/[F:Q])Σ f_P orderAtFPlace = ([Fmod_b:Q_p]/[Fmod:Q])*cP_b;
   the hper slot in Mzk1URThetaHullInclusionActual.neg_Mpaper_v2_eq_sum_qPilotMass uses cPFullFiber (NOT local qVFam cP). -/
import tmp.sheaf.xif.paper.Mzk1ULOrdFiberTowerActual
import tmp.sheaf.xif.paper.Mzk1ULR1QPilotMassBasicActual
import tmp.sheaf.xif.paper.Mzk1ULQPilotMagnitudeV2Actual
import tmp.sheaf.xif.paper.Mzk1HT82PaperWeightDiffActual
import tmp.sheaf.xif.paper.Mzk1HT82UnderIntGenQVActual
import Mathlib.Tactic

noncomputable section
set_option linter.unusedSectionVars false
open scoped BigOperators
namespace LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.N8Closure
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.XiFPaper.QVFamTensorCoefficientActual
open LeanFormal.IUT.XiFPaper.VbadPlaceIndexingActual
open LeanFormal.IUT.XiFPaper.Mzk1ULQPilotMagnitudeV2Actual
open LeanFormal.IUT.XiFPaper.Mzk1HT82PaperWeightDiffActual
open LeanFormal.IUT.XiFPaper.Mzk1ULOrdFiberTowerActual
open LeanFormal.IUT.XiFPaper.Mzk1ULR1QPilotMassBasicActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82UnderIntGenQVActual
open LeanFormal.IUT.XiFPaper.Mzk1HT82CompletionPrimeResidueActual
open NumberField

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
variable [Fintype (Bad (nativePlaceSelection T))]

/-- full-fiber paper c_P at b: (1/[F:Q]) Sum_{P|b} f_P orderAtFPlace P. -/
noncomputable def cPFullFiber (b : Bad (nativePlaceSelection T)) : Real :=
  (1 / (Module.finrank ℚ (T.arithmetic.F) : Real)) *
    ∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real))

/-- R1: MpaperB_b = - qPilotMass (cPFullFiber_b). -/
theorem MpaperB_eq_neg_qPilotMass (b : Bad (nativePlaceSelection T)) :
    MpaperB (l := l) T b =
      - qPilotMass (l := l) T b (cPFullFiber (l := l) T b) := by
  -- F-side fiber-prime consistency: every P | b has natAbs(underIntGen P) = qVFamTensorP b.
  have hprime : ∀ x ∈ (IsDedekindDomain.primesOverFinset
      (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      (underIntGen (K := T.arithmetic.F) x.1).natAbs = qVFamTensorP T b := by
    intro x _
    have hb0 : b.1.maximalIdeal.asIdeal ≠ ⊥ := b.1.maximalIdeal.ne_bot
    have hmem := (IsDedekindDomain.mem_primesOverFinset_iff
      (B := 𝓞 (T.arithmetic.F)) hb0).mp x.2
    have hx_over : x.1.under (𝓞 (T.arithmetic.Fmod)) = b.1.maximalIdeal.asIdeal :=
      (hmem.2.over).symm
    have hplace : (qVFamTensorPlace T b).maximalIdeal.asIdeal.under (𝓞 (T.arithmetic.Fmod)) =
        b.1.maximalIdeal.asIdeal := by
      rw [Ideal.under_def]
      rw [← NumberFieldFinitePlace.comap_maximalIdeal (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b)]
      rw [show NumberFieldFinitePlace.comap (k := T.arithmetic.Fmod)
        (qVFamTensorPlace T b) = b.1 from (nativeBadLift T).lift_comap b]
    have h1 := Ideal.under_under (A := ℤ) (B := 𝓞 (T.arithmetic.Fmod))
      (C := 𝓞 (T.arithmetic.F)) x.1
    have h2 := Ideal.under_under (A := ℤ) (B := 𝓞 (T.arithmetic.Fmod))
      (C := 𝓞 (T.arithmetic.F)) ((qVFamTensorPlace T b).maximalIdeal.asIdeal)
    have hZ : x.1.under ℤ = ((qVFamTensorPlace T b).maximalIdeal.asIdeal).under ℤ := by
      rw [← h1, ← h2, hx_over, hplace]
    have hspan : x.1.under ℤ =
        Ideal.span {(residueCharacteristic (qVFamTensorPlace T b) : ℤ)} := by
      rw [hZ, under_eq_span_residueCharacteristic (K := T.arithmetic.F) (qVFamTensorPlace T b)]
    have h := underIntGen_natAbs_of_under_eq_span (K := T.arithmetic.F) x.1
      (q := (residueCharacteristic (qVFamTensorPlace T b) : ℤ)) hspan
    have h' : (underIntGen (K := T.arithmetic.F) x.1).natAbs =
        residueCharacteristic (qVFamTensorPlace T b) := by
      simpa using h
    calc (underIntGen (K := T.arithmetic.F) x.1).natAbs
        = residueCharacteristic (qVFamTensorPlace T b) := h'
      _ = (completionRationalPrime (qVFamTensorPlace T b)).val :=
          (completionRationalPrime_val_eq_residueCharacteristic
            (qVFamTensorPlace T b)).symm
      _ = qVFamTensorP T b := rfl
  have hlog : ∀ x ∈ (IsDedekindDomain.primesOverFinset
      (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
      Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : Real) =
        Real.log (qVFamTensorP T b : Real) := by
    intro x hx
    rw [hprime x hx]
  have hsum : (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real) *
          Real.log ((underIntGen (K := T.arithmetic.F) x.1).natAbs : Real)))
      = (∑ x ∈ (IsDedekindDomain.primesOverFinset
        (b.1.maximalIdeal.asIdeal) (𝓞 (T.arithmetic.F))).attach,
        ((x.1.inertiaDeg ℤ : Real) * (orderAtFPlace T b x.1 x.2 : Real))) *
        Real.log (qVFamTensorP T b : Real) := by
    rw [Finset.sum_congr rfl (fun x hx => by rw [hlog x hx])]
    rw [Finset.sum_mul]
  unfold MpaperB cPFullFiber
  rw [qPilotMass_eq, hsum]
  ring

#print axioms MpaperB_eq_neg_qPilotMass

end LeanFormal.IUT.XiFPaper.Mzk1ULR1MpaperBWeightActual
