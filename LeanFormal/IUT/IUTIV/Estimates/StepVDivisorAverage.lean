import LeanFormal.IUT.IUTIV.Estimates.ArithmeticDivisorDegree

/-!
# IUT IV Theorem 1.10, Step (iii)/(v): fiber degrees as weighted averages

Step (v) of IUT IV Theorem 1.10 (`IV.txt` L1715–L1741) uses the weights
`λ_v = [(F)_v : Q_{vQ}]` and identifies the weighted averages of the local orders
`d_v·log p` (resp. `ord(q_v)·log p`) with the normalized degrees
`log d^K_{vQ} = deg_{V(F)_{vQ}}(d_ADiv)` (resp. `log q_{vQ}`) of Step (iii).

On the arithmetic-divisor layer of `ArithmeticDivisorDegree.lean` this is the
following computation.  Let `E` be a finite set of finite places lying over the
rational prime `p`, and let `D` be an arithmetic divisor whose coefficient at
`v ∈ E` is `e_v · c_v` (`e_v` the ramification index over `ℤ`; `c_v` an order in
the normalization `ord(p) = 1`).  Since `log q_v = f_v · log p` and
`[F_v : Q_p] = e_v f_v`,

`deg_F(D_E) / ∑_{v∈E} [F_v : Q_p] = (∑_{v∈E} c_v · log p · [F_v : Q_p]) / ∑_{v∈E} [F_v : Q_p]`,

i.e. the unnormalized fiber degree is exactly the `λ`-weighted average of
`c_v · log p` used in `StepVProcessionAverage` (`D` and `Q` there).
-/

namespace LeanFormal.IUT.IUTIV.StepVDivisorAverage

open LeanFormal.IUT.IUTIV.Estimates IsDedekindDomain NumberField

noncomputable section

variable {F : Type*} [Field F] [NumberField F]

/-- `log q_v = f_v · log p` for a finite place `v` over the rational prime `p`. -/
theorem weight_finite_eq_inertiaDeg_mul_log (p : ℕ)
    (v : HeightOneSpectrum (𝓞 F)) [v.asIdeal.LiesOver (Ideal.span {(p : ℤ)})] :
    IUTIVPlace.weight F (.finite v) = (v.asIdeal.inertiaDeg ℤ : ℝ) * Real.log p := by
  rw [IUTIVPlace.weight_finite, ← Ideal.absNorm_pow_inertiaDeg (p := Ideal.span {(p : ℤ)})]
  have hspan : (Ideal.span {(p : ℤ)}).absNorm = p := by
    rw [Ideal.absNorm_span_singleton]
    simp
  rw [hspan, Nat.cast_pow, Real.log_pow]

/-- **Fiber degree = weighted average (IV Thm 1.10 Step (iii)/(v)).**  If `D` has
coefficient `e_v · c_v` at every `v ∈ E` and every `v ∈ E` lies over `p`, then the
unnormalized fiber degree of `D` over `E` is the `[F_v : Q_p]`-weighted average of
`c_v · log p`. -/
theorem eDegreeUnnormalized_eq_weightedAverage (p : ℕ)
    (E : Finset (HeightOneSpectrum (𝓞 F)))
    (hE : ∀ v ∈ E, v.asIdeal.LiesOver (Ideal.span {(p : ℤ)}))
    (c : HeightOneSpectrum (𝓞 F) → ℝ) (D : IUTIVArithmeticDivisor F)
    (hD : ∀ v ∈ E, D (.finite v) = (v.asIdeal.ramificationIdx ℤ : ℝ) * c v) :
    IUTIVArithmeticDivisor.eDegreeUnnormalized F (E.image IUTIVPlace.finite) D =
      (∑ v ∈ E, c v * Real.log p * (IUTIVPlace.localDegree F (.finite v) : ℝ)) /
        ∑ v ∈ E, (IUTIVPlace.localDegree F (.finite v) : ℝ) := by
  have hinj : Set.InjOn (IUTIVPlace.finite (F := F)) E := by
    intro a _ b _ h
    injection h
  unfold IUTIVArithmeticDivisor.eDegreeUnnormalized
  rw [IUTIVArithmeticDivisor.deg_part, Finset.sum_image hinj, Finset.sum_image hinj]
  congr 1
  refine Finset.sum_congr rfl fun v hv => ?_
  haveI := hE v hv
  rw [hD v hv, weight_finite_eq_inertiaDeg_mul_log p v]
  simp only [IUTIVPlace.localDegree, Nat.cast_mul]
  ring

end

end LeanFormal.IUT.IUTIV.StepVDivisorAverage
