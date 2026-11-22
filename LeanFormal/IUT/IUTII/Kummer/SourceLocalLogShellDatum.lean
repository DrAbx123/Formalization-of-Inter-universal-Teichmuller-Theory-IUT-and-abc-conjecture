import LeanFormal.IUT.IUTII.Kummer.SourceLogShellCarrier
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceCommonPrimeCompletion
import LeanFormal.IUT.Foundations.LocalFields.LogarithmLocalInverse

/-!
# The actual local log-shell datum at a finite place

This file constructs the per-place bridge recorded in the N4--N7 gap card.
For an actual finite place `place` of a number field and the common prime `p`,
let `L := CommonPrimeCompletion place`.  The actual integral units
`(Integers L)^x` and the constructed `unitLogHom` give a `SourceLogShellDatum`
whose `logShell` is exactly the actual `integralLogShell` of `L`.

This is only the per-place log-shell bridge.  It does not construct the
source theta-pilot image, a multi-place tensor comparison, or the missing
source-to-arithmetic map, and it does not close N4--N7.
-/

namespace LeanFormal.IUT

open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm

noncomputable section

universe u

variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]

/-- The source factor `p*` agrees with the actual local log-shell scale. -/
theorem sourceLogShellStar_eq_logShellScale {p : Nat} (hp : p.Prime) :
    sourceLogShellStar p = logShellScale p := by
  rcases hp.eq_two_or_odd with htwo | hodd
  · subst p
    norm_num [sourceLogShellStar, logShellScale]
  · unfold sourceLogShellStar logShellScale
    rw [if_pos hodd]
    have hpne : p ≠ 2 := by
      rintro rfl
      norm_num at hodd
    rw [if_neg hpne]

/-- The actual local log-shell datum at a finite place.  The local field is
the genuine common-prime completion; the units and logarithm are the actual
integral units and `unitLogHom`. -/
def sourceLocalLogShellDatum (place : FinitePlaceAtPrime K p) :
    SourceLogShellDatum where
  p := p
  hp := Fact.out
  K := CommonPrimeCompletion place
  fieldK := inferInstance
  charZeroK := inferInstance
  Units := (Integers (CommonPrimeCompletion place))ˣ
  groupUnits := inferInstance
  invariants := ⊤
  logMap := unitLogHom (K := CommonPrimeCompletion place) (p := p)

/-- The additive projection of the actual unit logarithm. -/
@[simp] theorem unitLogHom_toAdd_apply
    (place : FinitePlaceAtPrime K p)
    (u : (Integers (CommonPrimeCompletion place))ˣ) :
    Multiplicative.toAdd
        (unitLogHom (K := CommonPrimeCompletion place) (p := p) u) =
      unitLog (K := CommonPrimeCompletion place) u := rfl

/-- The `p*` factor of the local datum is the actual log-shell scale. -/
@[simp] theorem sourceLocalLogShellDatum_pStar
    (place : FinitePlaceAtPrime K p) :
    (sourceLocalLogShellDatum (p := p) place).pStar = logShellScale p := by
  simp [SourceLogShellDatum.pStar, sourceLocalLogShellDatum,
    sourceLogShellStar_eq_logShellScale (Fact.out : p.Prime)]

/-- The pre-log-shell of the actual local datum is the range of the actual
integral unit logarithm, in additive coordinates. -/
theorem sourceLocalLogShellDatum_preLogShell
    (place : FinitePlaceAtPrime K p) :
    (sourceLocalLogShellDatum (p := p) place).preLogShell =
      Set.range (fun u : (Integers (CommonPrimeCompletion place))ˣ =>
        unitLog (K := CommonPrimeCompletion place) u) := by
  ext a
  constructor
  · rintro ⟨u, -, h⟩
    change Multiplicative.toAdd
      (unitLogHom (K := CommonPrimeCompletion place) (p := p) u) = a at h
    exact ⟨u, by simpa only [unitLogHom_toAdd_apply] using h⟩
  · rintro ⟨u, h⟩
    refine ⟨u, trivial, ?_⟩
    change Multiplicative.toAdd
      (unitLogHom (K := CommonPrimeCompletion place) (p := p) u) = a
    simpa only [unitLogHom_toAdd_apply] using h

/-- The same pre-log-shell as the additive image of the range of `unitLogHom`. -/
theorem sourceLocalLogShellDatum_preLogShell_eq_range_unitLogHom
    (place : FinitePlaceAtPrime K p) :
    (sourceLocalLogShellDatum (p := p) place).preLogShell =
      Multiplicative.toAdd '' Set.range
        (unitLogHom (K := CommonPrimeCompletion place) (p := p)) := by
  rw [sourceLocalLogShellDatum_preLogShell]
  ext a
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨unitLogHom (K := CommonPrimeCompletion place) (p := p) u,
      ⟨u, rfl⟩, rfl⟩
  · rintro ⟨m, ⟨u, rfl⟩, h⟩
    exact ⟨u, by simpa [unitLogHom] using h⟩

/-- The actual local log-shell datum has exactly the actual integral
log-shell of the common-prime completion. -/
theorem sourceLocalLogShellDatum_logShell_eq_integralLogShell
    (place : FinitePlaceAtPrime K p) :
    (sourceLocalLogShellDatum (p := p) place).logShell =
      (integralLogShell (K := CommonPrimeCompletion place) (p := p) :
        Set (CommonPrimeCompletion place)) := by
  rw [SourceLogShellDatum.logShell_eq_invScaledPreLogShell]
  unfold SourceLogShellDatum.invScaledPreLogShell
  rw [sourceLocalLogShellDatum_pStar, sourceLocalLogShellDatum_preLogShell]
  ext b
  constructor
  · rintro ⟨x, hx, hb⟩
    rcases hx with ⟨u, rfl⟩
    change ∃ v : (Integers (CommonPrimeCompletion place))ˣ,
      (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        unitLog (K := CommonPrimeCompletion place) v = b
    exact ⟨u, hb⟩
  · intro hb
    change ∃ v : (Integers (CommonPrimeCompletion place))ˣ,
      (logShellScale p : CommonPrimeCompletion place)⁻¹ *
        unitLog (K := CommonPrimeCompletion place) v = b at hb
    rcases hb with ⟨u, rfl⟩
    exact ⟨unitLog (K := CommonPrimeCompletion place) u,
      ⟨u, rfl⟩, rfl⟩

/-- The actual zero log-coordinate lies in the local log-shell. -/
theorem sourceLocalLogShellDatum_zero_mem_logShell
    (place : FinitePlaceAtPrime K p) :
    (0 : CommonPrimeCompletion place) ∈
      (sourceLocalLogShellDatum (p := p) place).logShell := by
  rw [sourceLocalLogShellDatum_logShell_eq_integralLogShell]
  exact (integralLogShell (K := CommonPrimeCompletion place) (p := p)).zero_mem

/-- The logarithm of the identity actual integral unit lies in the local
log-shell. -/
theorem sourceLocalLogShellDatum_unitLog_one_mem_logShell
    (place : FinitePlaceAtPrime K p) :
    unitLog (K := CommonPrimeCompletion place)
        (1 : (Integers (CommonPrimeCompletion place))ˣ) ∈
      (sourceLocalLogShellDatum (p := p) place).logShell := by
  rw [unitLog_one (K := CommonPrimeCompletion place) (p := p)]
  exact sourceLocalLogShellDatum_zero_mem_logShell (p := p) place

/-! ## Axiom probe -/

#print axioms sourceLogShellStar_eq_logShellScale
#print axioms sourceLocalLogShellDatum
#print axioms unitLogHom_toAdd_apply
#print axioms sourceLocalLogShellDatum_pStar
#print axioms sourceLocalLogShellDatum_preLogShell
#print axioms sourceLocalLogShellDatum_preLogShell_eq_range_unitLogHom
#print axioms sourceLocalLogShellDatum_logShell_eq_integralLogShell
#print axioms sourceLocalLogShellDatum_zero_mem_logShell
#print axioms sourceLocalLogShellDatum_unitLog_one_mem_logShell

end

end LeanFormal.IUT
