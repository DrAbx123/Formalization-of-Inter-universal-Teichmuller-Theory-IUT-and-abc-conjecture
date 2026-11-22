import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceThetaPilotScaledRegion
import LeanFormal.IUT.IUTII.Kummer.SourceThetaPilotIQContainment

/-!
# ShehddQPilotRungAssemblyActual — q-pilot/Theta-pilot rung assembly

Real assembly for LADDER rung qpilot from compiled components:
* finite-place Theta-pilot generator membership in the single-coordinate fractional
  lattice, nonnegative pilot exponent, and the scaled-region containment;
* Kummer-side Theta-pilot IQ containment (possible image and product-map image inside
  the IQ packets).
No sorry/axiom, no True placeholder.
-/

noncomputable section

namespace LeanFormal.IUT.XiFPaper.ShehddQPilotRungAssemblyActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.Theorem311Source.SourceLGPMonoidLayer

universe u v w uK uM

/-- **PROVED assembly:** the finite-place Theta-pilot generator lies in the
single-coordinate fractional lattice, and a positive pilot weight with positive local
order gives nonnegative pilot exponent. -/
theorem thetaPilot_generator_lattice_chain {K : Type u} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (iSelected : ι) (q : CommonPrimeCompletion (places iSelected (tuple iSelected)))
    (weight : ℕ) {mu lambda : ℝ} (hweight : 0 < weight) (hlambda : 0 < lambda)
    (hq : ‖q ^ weight‖ ≤ (p : ℝ) ^ (-mu)) :
    arithmeticTupleThetaPilotGenerator places tuple iSelected q weight ∈
        arithmeticTupleSingleFractionalLattice places tuple iSelected mu ∧
      0 ≤ (weight : ℝ) * lambda :=
  ⟨arithmeticTupleThetaPilotGenerator_mem_singleFractionalLattice places tuple
      iSelected q weight hq,
    arithmeticTupleThetaPilotExponent_nonneg hweight hlambda⟩

/-- **PROVED assembly:** the scaled Theta-pilot region is contained in the
single-coordinate fractional lattice times any normalization submodule containing the
integral closure. -/
theorem thetaPilot_region_containment_chain {K : Type u} [Field K] [NumberField K]
    {p : ℕ} [Fact p.Prime] {ι : Type v} [Fintype ι] [DecidableEq ι] {V : ι → Type w}
    (places : (i : ι) → V i → FinitePlaceAtPrime K p) (tuple : (i : ι) → V i)
    (iSelected : ι) (q : CommonPrimeCompletion (places iSelected (tuple iSelected)))
    (weight : ℕ) {mu : ℝ} (hq : ‖q ^ weight‖ ≤ (p : ℝ) ^ (-mu))
    (N : Submodule ℤ_[p] (ArithmeticTensorTupleBlock places tuple))
    (hO : (integralClosure ℤ_[p] (ArithmeticTensorTupleBlock places tuple)).toSubmodule
      ≤ N) (hNN : N * N ≤ N) :
    arithmeticTupleThetaPilotRegion places tuple iSelected q weight ≤
      arithmeticTupleSingleFractionalLattice places tuple iSelected mu * N :=
  arithmeticTupleThetaPilotRegion_le_singleCoordinateFractional places tuple
    iSelected q weight hq N hO hNN

/-- **PROVED assembly (Kummer side):** a Theta-pilot generator in the IQ packet forces
both the one-place possible image and its product-map image into the IQ packets. -/
theorem thetaPilot_IQ_containment_chain {l : PrimeGeFive} {G : LGPMonoid.{uM} l}
    {D : SourceLogShellDatum.{uK}} {j : Nat}
    {P : LGPMonoidAction G Rat (sourceLogShellOnePlaceFamily D j)}
    (T : ThetaPilotObject P ())
    (hgen : T.generator ∈ sourceThetaPilotIQPacket D j) :
    T.possibleImage ⊆ sourceThetaPilotIQPacket D j ∧
      sourceThetaPilotProductMap D j '' T.possibleImage ⊆
        (sourceThetaPilotTensorIQPacket D j : Set D.K) :=
  ⟨possibleImage_subset_sourceThetaPilotIQPacket T hgen,
    sourceThetaPilotProductMap_image_subset_tensorIQPacket T hgen⟩

end LeanFormal.IUT.XiFPaper.ShehddQPilotRungAssemblyActual
end
