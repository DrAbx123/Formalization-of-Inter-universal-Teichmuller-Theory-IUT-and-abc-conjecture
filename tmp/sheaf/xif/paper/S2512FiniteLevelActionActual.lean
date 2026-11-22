import tmp.sheaf.xif.paper.S2511ContinuousTwoCocycleActual

noncomputable section
universe u
open LeanFormal.IUT
open LeanFormal.IUT.LocalIntegralMonoid
open LeanFormal.IUT.XiFPaper.S2481CoeffLimitActual
open LeanFormal.IUT.XiFPaper.S2000CohomologicalPsiCnsActual

namespace LeanFormal.IUT.XiFPaper.S2512FiniteLevelActionActual

variable (p : Nat) [Fact (Nat.Prime p)]
variable (n : ℕ+)

/-- The Galois action on finite roots of unity, restricted from the unit action. -/
noncomputable def S2512RootMulAut (g : Gv p) : MulAut (S2481Roots p n) where
  toFun ζ :=
    ⟨(LocalMLFModelTMPair.monoAnalytic p).unitAction p g (ζ : (Otri p)ˣ), by
      rw [mem_rootsOfUnity]
      have hζ := (mem_rootsOfUnity n (ζ : (Otri p)ˣ)).mp ζ.2
      simpa using congrArg ((LocalMLFModelTMPair.monoAnalytic p).unitAction p g) hζ⟩
  invFun ζ :=
    ⟨(LocalMLFModelTMPair.monoAnalytic p).unitAction p g⁻¹ (ζ : (Otri p)ˣ), by
      rw [mem_rootsOfUnity]
      have hζ := (mem_rootsOfUnity n (ζ : (Otri p)ˣ)).mp ζ.2
      simpa using congrArg ((LocalMLFModelTMPair.monoAnalytic p).unitAction p g⁻¹) hζ⟩
  left_inv ζ := by
    apply Subtype.ext
    change ((LocalMLFModelTMPair.monoAnalytic p).unitAction p g⁻¹)
        (((LocalMLFModelTMPair.monoAnalytic p).unitAction p g) (ζ : (Otri p)ˣ))
      = (ζ : (Otri p)ˣ)
    rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one, MulAut.one_apply]
  right_inv ζ := by
    apply Subtype.ext
    change ((LocalMLFModelTMPair.monoAnalytic p).unitAction p g)
        (((LocalMLFModelTMPair.monoAnalytic p).unitAction p g⁻¹) (ζ : (Otri p)ˣ))
      = (ζ : (Otri p)ˣ)
    rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply]
  map_mul' ζ η := by
    ext
    simp

/-- The actual finite-level continuous action. -/
noncomputable def S2512FiniteLevelAction :
    Iut.ContinuousGroupAction (Gv p) (S2481Roots p n) where
  automorphism :=
    { toFun := S2512RootMulAut p n
      map_one' := by
        apply MulEquiv.ext
        intro ζ
        ext
        simp [S2512RootMulAut]
      map_mul' g h := by
        apply MulEquiv.ext
        intro ζ
        ext
        simp [S2512RootMulAut, MulAut.mul_apply] }
  continuous_action := by
    have hact : Continuous (fun q : Gv p × (Otri p)ˣ =>
        (LocalMLFModelTMPair.monoAnalytic p).unitAction p q.1 q.2) :=
      ((LocalMLFModelTMPair.monoAnalytic p).discreteIntegralUnitAction p).continuous_action
    have hf : Continuous (fun q : Gv p × S2481Roots p n =>
        (q.1, (q.2 : (Otri p)ˣ))) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hcomp := hact.comp hf
    apply Continuous.subtype_mk
    · change Continuous (fun q : Gv p × S2481Roots p n =>
        ((LocalMLFModelTMPair.monoAnalytic p).unitAction p q.1) (q.2 : (Otri p)ˣ))
      exact hcomp


end LeanFormal.IUT.XiFPaper.S2512FiniteLevelActionActual
end