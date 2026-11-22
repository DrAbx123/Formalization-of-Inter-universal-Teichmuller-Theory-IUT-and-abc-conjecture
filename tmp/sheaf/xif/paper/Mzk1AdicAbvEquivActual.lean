/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import Iut.Cor312.ThetaData.GalCompletion
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Tactic

/-! # adicAbv transport along an isomorphism of number fields

`adicAbv` at the transported height-one prime is the original `adicAbv` under the
ring isomorphism: `adicAbv K' (equivOfRingEquiv e v) (e x) = adicAbv K v x`.

Proof route: `valuation_of_comap` gives the valuation equality, and the
absolute norm is preserved by the prime bijection, so `toNNReal` agrees.
No fake. -/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open scoped NNReal
open NumberField IsDedekindDomain IsDedekindDomain.HeightOneSpectrum

namespace LeanFormal.IUT.XiFPaper.Mzk1AdicAbvEquivActual

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [NumberField K']

/-- Absolute norms agree under the prime bijection. -/
theorem absNorm_equivOfRingEquiv (e : K ≃+* K')
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) :
    Ideal.absNorm (HeightOneSpectrum.equivOfRingEquiv
        (NumberField.RingOfIntegers.mapRingEquiv e) v).asIdeal =
      Ideal.absNorm v.asIdeal := by
  set f := NumberField.RingOfIntegers.mapRingEquiv e
  rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
  have hIJ : v.asIdeal =
      (HeightOneSpectrum.equivOfRingEquiv f v).asIdeal.map
        (f.symm : NumberField.RingOfIntegers K' →+* NumberField.RingOfIntegers K) := by
    rw [show (HeightOneSpectrum.equivOfRingEquiv f v).asIdeal =
      v.asIdeal.comap (f.symm : NumberField.RingOfIntegers K' →+* NumberField.RingOfIntegers K)
      from rfl]
    exact (v.asIdeal).map_comap_of_surjective
      (f.symm : NumberField.RingOfIntegers K' →+* NumberField.RingOfIntegers K)
      (RingEquiv.surjective f.symm) |>.symm
  exact Nat.card_congr (Ideal.quotientEquiv _ _ f.symm hIJ).toEquiv

/-- The transported adic absolute value. -/
theorem adicAbv_equivOfRingEquiv (e : K ≃+* K')
    (v : HeightOneSpectrum (NumberField.RingOfIntegers K)) (x : K) :
    NumberField.HeightOneSpectrum.adicAbv K'
        (HeightOneSpectrum.equivOfRingEquiv (NumberField.RingOfIntegers.mapRingEquiv e) v) (e x) =
      NumberField.HeightOneSpectrum.adicAbv K v x := by
  set f := NumberField.RingOfIntegers.mapRingEquiv e
  have hf : Function.Bijective f := f.bijective
  have hcomp : ((f.symm : NumberField.RingOfIntegers K' →+* NumberField.RingOfIntegers K).comp
      (f : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K')) =
      RingHom.id (NumberField.RingOfIntegers K) := by
    ext r
    simp [RingEquiv.symm_apply_apply]
  have hw : v.asIdeal =
      (HeightOneSpectrum.equivOfRingEquiv f v).asIdeal.comap
        (f : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K') := by
    rw [show (HeightOneSpectrum.equivOfRingEquiv f v).asIdeal =
      v.asIdeal.comap (f.symm : NumberField.RingOfIntegers K' →+* NumberField.RingOfIntegers K)
      from rfl]
    rw [Ideal.comap_comap (f := (f : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K'))
      (g := (f.symm : NumberField.RingOfIntegers K' →+* NumberField.RingOfIntegers K)), hcomp,
      Ideal.comap_id]
  have hval := Iut.valuation_of_comap (K := K) (L := K')
      (f := (f : NumberField.RingOfIntegers K →+* NumberField.RingOfIntegers K'))
      (R := NumberField.RingOfIntegers K) (S := NumberField.RingOfIntegers K') hf hw
    (e : K →+* K') (fun r => by
      simp only [← NumberField.RingOfIntegers.coe_eq_algebraMap]
      change e (r : K) = ((f r : NumberField.RingOfIntegers K') : K')
      rw [NumberField.RingOfIntegers.mapRingEquiv_apply]) x
  simp only [NumberField.HeightOneSpectrum.adicAbv_def]
  rw [hval]
  simp only [RingEquiv.coe_toRingHom]
  have hz1 := HeightOneSpectrum.absNorm_ne_zero (HeightOneSpectrum.equivOfRingEquiv f v)
  have hz2 := HeightOneSpectrum.absNorm_ne_zero v
  have habs_nn : ((Ideal.absNorm
      (HeightOneSpectrum.equivOfRingEquiv f v).asIdeal : ℕ) : NNReal) =
      ((Ideal.absNorm v.asIdeal : ℕ) : NNReal) := by
    exact_mod_cast absNorm_equivOfRingEquiv e v
  by_cases hm : (HeightOneSpectrum.equivOfRingEquiv f v).valuation K' (e x) = 0
  · rw [WithZeroMulInt.toNNReal_pos_apply hz1 hm,
      WithZeroMulInt.toNNReal_pos_apply hz2 hm]
  · rw [WithZeroMulInt.toNNReal_neg_apply hz1 hm,
      WithZeroMulInt.toNNReal_neg_apply hz2 hm, habs_nn]

end LeanFormal.IUT.XiFPaper.Mzk1AdicAbvEquivActual

end