/- R2 carrier bridge, brick 1 (set-level, no number theory): with `Phi` the range of the
scalar multiplications `mulLeft (tprod(update 1 istar (varpi^m)))`, the StepV possible-image
set is exactly `⋃_m (varpi^m · O_hol)`.  This is the F-block analogue of the L_w local root
ball construction; the `L_w`/`rootNormHull` hull identification is the next brick.
REUSE: `Mzk1BoxReadoutLocalActual.packetHull`/`PacketHullData`,
`FinitePlaceStepVAssembly.arithmeticTupleStepVPossibleImages`/`arithmeticTupleCanonicalUnitReference`,
`LinearMap.mulLeft` (`LinearMap.mulLeft_apply`).
No fake; no equality of packetHull with rootNormHull claimed here. -/
import tmp.sheaf.xif.paper.Mzk1BoxReadoutLocalActual
import tmp.sheaf.xif.paper.RootHullContainmentInequalityActual
import tmp.sheaf.xif.paper.RootNormalizedContainmentActual
import Mathlib.Tactic

set_option maxHeartbeats 2000000

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2PacketCarrierActual
open LeanFormal.IUT.NumberFieldFinitePlace

universe u v w
variable {K : Type u} [Field K] [NumberField K] {p : Nat} [Fact p.Prime]
variable {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
variable {places : (i : ι) → V i → FinitePlaceAtPrime K p} {tuple : (i : ι) → V i}
variable [MeasurableSpace (ArithmeticTensorTupleBlock places tuple)]
variable [BorelSpace (ArithmeticTensorTupleBlock places tuple)]

/-- **StepV possible images for the power family**: with `Phi := Set.range (m ↦ mulLeft ϖ^m)`
the possible-image set is the union of the `ϖ^m`-scalings of `O_hol`. -/
theorem stepVPossibleImages_range_mulLeft
    (istar : ι) (varpi : CommonPrimeCompletion (places istar (tuple istar))) :
    ArithmeticTensorTupleBlock.arithmeticTupleStepVPossibleImages (p := p) places tuple istar varpi
        (Set.range (fun m : ℤ =>
          LinearMap.mulLeft ℚ_[p]
            (arithmeticTupleTprod places tuple (Function.update 1 istar (varpi ^ m))))) =
      ⋃ m : ℤ,
        (fun x => arithmeticTupleTprod places tuple (Function.update 1 istar (varpi ^ m)) * x) ''
          arithmeticTupleCanonicalUnitReference places tuple := by
  ext s
  constructor
  · rintro ⟨φ, ⟨m, rfl⟩, x, hx, rfl⟩
    refine Set.mem_iUnion.mpr ⟨m, ?_⟩
    refine ⟨x, hx, ?_⟩
    rw [LinearMap.mulLeft_apply, mul_one]
  · intro hs
    rcases Set.mem_iUnion.mp hs with ⟨m, x, hx, rfl⟩
    exact ⟨_, ⟨m, rfl⟩, x, hx, by rw [LinearMap.mulLeft_apply, mul_one]⟩

#print axioms stepVPossibleImages_range_mulLeft
end LeanFormal.IUT.XiFPaper.Mzk1G1R1IR2PacketCarrierActual
