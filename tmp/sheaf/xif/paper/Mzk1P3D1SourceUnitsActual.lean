import tmp.sheaf.xif.paper.Mzk1D1Actual
import tmp.sheaf.xif.paper.Mzk1D1P3Actual
import tmp.sheaf.xif.paper.Mzk1P3ArrowCoverageActual

noncomputable section
namespace LeanFormal.IUT.XiFPaper.Mzk1P3D1SourceUnitsActual
open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.D1Actual
open LeanFormal.IUT.XiFPaper.Mzk1D1P3Actual
open LeanFormal.IUT.XiFPaper.Mzk1P3ArrowCoverageActual
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.LocalFieldIntegralUnits
open scoped Valued

variable {K L : Type*} [NormedField K] [NormedField L] [NormedAlgebra K L]
variable [IsUltrametricDist K] [IsUltrametricDist L]
variable {p : Nat} [Fact p.Prime] [NormedAlgebra ℚ_[p] K] [NormedAlgebra ℚ_[p] L]
variable [IsScalarTower ℚ_[p] K L] [Algebra.IsAlgebraic ℚ_[p] L] [IsGalois K L]

/-- Actual degree-zero Galois-fixed units: the concrete `U(H_F) ≃ O_F^×`
identification from the D1 source layer. -/
noncomputable def p3DegreeZeroUnitsEquiv :
    (Integers K)ˣ ≃* fixedDegreeZeroUnits (K := K) (L := L) (p := p) :=
  fixed_degreeZero_units_equiv (K := K) (L := L) (p := p)

theorem p3DegreeZeroUnitsEquiv_apply (u : (Integers K)ˣ) :
    p3DegreeZeroUnitsEquiv (K := K) (L := L) (p := p) u =
      fixed_degreeZero_units_equiv (K := K) (L := L) (p := p) u := rfl

/-- Actual source unit data: degree-zero units together with a chosen source
Kummer arrow. -/
structure P3D1SourceUnitsData {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    (upper lower : FPrimeStrip V) (arrow : SourceKummerArrow G upper lower) where
  degreeZeroEquiv : (Integers K)ˣ ≃* fixedDegreeZeroUnits (K := K) (L := L) (p := p)

noncomputable def P3D1SourceUnitsData.ofArrow {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (arrow : SourceKummerArrow G upper lower) :
    P3D1SourceUnitsData (K := K) (L := L) (p := p) upper lower arrow where
  degreeZeroEquiv := p3DegreeZeroUnitsEquiv (K := K) (L := L) (p := p)

/-- Coverage of an actual Kummer arrow by its unit layer. -/
noncomputable def P3ArrowCoverageData.ofLayer {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (layer : SourceTimesMuKummerLayer G upper lower) :
    P3ArrowCoverageData (G := G) upper lower where
  layer := layer
  restriction v := (layer.kummer v).equiv
  restriction_eq := fun v => rfl
  commutes := fun v u => rfl
  coverage := fun v => (layer.kummer v).equiv.bijective

noncomputable def P3ArrowCoverageData.ofArrow {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (arrow : SourceKummerArrow G upper lower) :
    P3ArrowCoverageData (G := G) upper lower :=
  P3ArrowCoverageData.ofLayer (layer := arrow.layer)

/-- The actual restriction commuting square for a source Kummer layer. -/
theorem p3_unitLayer_commutes {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (layer : SourceTimesMuKummerLayer G upper lower)
    (v : V) (g : G) (x : TimesMuQuotient ((upper.Mon v)ˣ)) :
    (layer.kummer v).equiv (TimesMuQuotient.action (layer.sourceAction v) g x) =
      TimesMuQuotient.action (layer.targetAction v) g ((layer.kummer v).equiv x) :=
  (layer.kummer v).equivariant g x

#print axioms p3DegreeZeroUnitsEquiv
#print axioms P3ArrowCoverageData.ofArrow
#print axioms p3_unitLayer_commutes

/-- The actual `beta_a` on the `x`-mu unit quotient at a place, induced by
a source Kummer arrow. -/
noncomputable def p3BetaA {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (arrow : SourceKummerArrow G upper lower) (v : V) :
    TimesMuQuotient ((upper.Mon v)ˣ) ≃* TimesMuQuotient ((lower.Mon v)ˣ) :=
  (arrow.layer.kummer v).equiv

theorem p3BetaA_equivariant {V : Type*} {G : Type*} [Group G] [TopologicalSpace G]
    {upper lower : FPrimeStrip V} (arrow : SourceKummerArrow G upper lower) (v : V) (g : G)
    (x : TimesMuQuotient ((upper.Mon v)ˣ)) :
    p3BetaA arrow v
        (TimesMuQuotient.action (arrow.layer.sourceAction v) g x) =
      TimesMuQuotient.action (arrow.layer.targetAction v) g
        (p3BetaA arrow v x) := by
  exact (arrow.layer.kummer v).equivariant g x

#print axioms p3BetaA
#print axioms p3BetaA_equivariant


/-- Actual self Kummer layer producer for an arbitrary source strip, using
the trivial acting group.  This is a genuine `SourceTimesMuKummerLayer`, not
an assumed field. -/
noncomputable def actualSelfKummerLayer {V : Type*} (S : FPrimeStrip V) :
    SourceTimesMuKummerLayer Unit S S :=
  selfKummerLayerOfFactorization S (fun _ => 1)

/-- Actual self Kummer arrow producer for an arbitrary source strip. -/
noncomputable def actualSelfKummerArrow {V : Type*} (S : FPrimeStrip V) :
    SourceKummerArrow Unit S S :=
  selfKummerArrowOfFactorization S (fun _ => 1)

theorem actualSourceProducer_nonempty {V : Type*} (S : FPrimeStrip V) :
    Nonempty (SourceKummerArrow Unit S S) :=
  ⟨actualSelfKummerArrow S⟩

#print axioms actualSelfKummerLayer
#print axioms actualSelfKummerArrow

end LeanFormal.IUT.XiFPaper.Mzk1P3D1SourceUnitsActual