/- PROBE (henry): StepV possible-image set for the power family `Phi_m = mulLeft (ϖ^m)`
with `varpi = 1`: the possible images are exactly `⋃_m ϖ^m · O_hol`.
Direct `lake env lean` (watchdog OFF per Lead). Uses
`isUnit_arithmeticTupleTprod` + `Units.mulLeftLinearEquiv` (Mathlib)
`LinearEquiv.Basic:903`, `arithmeticTupleCanonicalUnitReference`, `arithmeticTupleTprod_one`.
No fake; the L_w hull identification is the next brick. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import Mathlib.Tactic

set_option maxHeartbeats 3000000
set_option synthInstance.maxHeartbeats 3000000

noncomputable section
namespace LeanFormal.IUT.XiFPaper.ProbeLwImagesActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p} {tuple : (i : ι) → V i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

omit [Fintype ι] in
/-- The updated pure-tensor family has no zero component when `ϖ ≠ 0`. -/
theorem update_one_pow_ne_zero (istar : ι) {varpi : CommonPrimeCompletion (places istar (tuple istar))}
    (hvarpi : varpi ≠ 0) (m : ℤ) (i : ι) :
    Function.update (1 : (i : ι) → CommonPrimeCompletion (places i (tuple i))) istar (varpi ^ m) i ≠ 0 := by
  by_cases hi : i = istar
  · subst hi
    simpa using zpow_ne_zero m hvarpi
  · simp [Function.update_apply, hi]

/-- **Set identity**: with `Phi = Set.range (m ↦ mulLeft (ϖ^m))` and `varpi = 1`, the StepV
possible images are exactly `⋃_m ϖ^m · O_hol`. -/
theorem stepVPossibleImages_range_mulLeft
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar))) (hvarpi : varpi ≠ 0) :
    LeanFormal.IUT.NumberFieldFinitePlace.arithmeticTupleStepVPossibleImages (p := p)
        places tuple istar 1
        (Set.range (fun m : ℤ =>
          (isUnit_arithmeticTupleTprod places tuple
            (Function.update (1 : (i : ι) → CommonPrimeCompletion (places i (tuple i))) istar
              (varpi ^ m)) (update_one_pow_ne_zero istar hvarpi m)).unit.mulLeftLinearEquiv
            ℚ_[p] (ArithmeticTensorTupleBlock places tuple))) =
      ⋃ m : ℤ,
        (fun x => arithmeticTupleTprod places tuple (Function.update 1 istar (varpi ^ m)) * x) ''
          arithmeticTupleCanonicalUnitReference places tuple := by
  ext s
  constructor
  · rintro ⟨φ, ⟨m, rfl⟩, x, hx, rfl⟩
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    refine ⟨x, hx, ?_⟩
    rw [Units.mulLeftLinearEquiv_apply, IsUnit.unit_spec]
    simp only [arithmeticTupleTprod_one, one_mul]
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨m, x, hx, rfl⟩
    refine ⟨_, ⟨m, rfl⟩, x, hx, ?_⟩
    rw [Units.mulLeftLinearEquiv_apply]
    simp only [arithmeticTupleTprod_one, one_mul]

#print axioms stepVPossibleImages_range_mulLeft
end LeanFormal.IUT.XiFPaper.ProbeLwImagesActual