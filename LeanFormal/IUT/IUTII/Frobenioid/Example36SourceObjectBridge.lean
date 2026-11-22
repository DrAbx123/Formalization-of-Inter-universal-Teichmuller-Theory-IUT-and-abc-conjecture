import LeanFormal.IUT.IUTII.Frobenioid.Example36SourceTheaterCarrier
import LeanFormal.IUT.IUTI.HodgeTheater.SourceHodgeTheaterFamilySourceReduction
import LeanFormal.IUT.IUTI.HodgeTheater.SourceDefinition31SignQuotientSupplyReduction
import LeanFormal.IUT.IUTI.InitialTheta.Definition31D0D11Aligned
import LeanFormal.IUT.IUTIII.Theorem311.SourceOriginalInput

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

/-!
# Bridge from the Example 3.6 layer to genuine source-object APIs, and source cards

This file records exactly which source-object components are actual
(inhabited/constructed in the tree) and which remain cards (recorded
obligations, not inhabited), for the concrete Example 3.6 carrier.

ACTUAL:
* `sourceTheater l` is a genuine `HodgeTheater l (FinitePrimePlace 2 7)` with
  actual arithmetic datum (Gaussian field `Q(i)`), actual base-changed split
  multiplicative curve, actual finite interval F-prime strip, actual finite
  theta packet and actual q = 1/5 (all equality bridges proved below);
* the source layer's `distinctArithmeticSpineFamily` is an actual construction;
  applied to the concrete arithmetic spine it yields a genuine
  `SourceHodgeTheaterFamily` whose unique theater has the concrete arithmetic
  datum, prime strip and theta packet;
* the source layer's `SourceSignQuotientGeometricCore` is not flatly missing:
  it is equivalent to the sign-quotient supply, but no unconditional inhabitant
  is provided (card).

CARDED (frozen union card `SourceObjectUnionCard`):
* curve/orbicurve D6 construction gate (`D6ConstructionGate l`);
* theta generators / nontrivial theta-link system: a Hodge-theater family with
  nontrivial index; the concrete family is singleton;
* distinct histories: a family with `Int × Int`-shaped index as required by the
  Theorem 3.11 `OriginalInput`;
* D-prime-strip Galois: a genuine `OriginalInput` (which requires a
  `SourceDefinition31Data` and a `Int × Int`-indexed Hodge-theater family with
  arithmetic alignment).

CORRECTION: the `SourceHodgeTheaterFamily` record is not a flat missing card:
it has an actual constructor in the source layer and a genuine inhabitant for
the concrete carrier. The missing part is a nontrivial (distinct) arithmetic
spine. We also prove that no `OriginalInput` all of whose theaters equal the
concrete carrier can exist.

No fake source object and no degenerate substitution: the singleton family is
a genuine inhabitant but is explicitly not claimed to supply distinct
histories.
-/

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid.Example36
namespace SourceObjectBridge

open LeanFormal.IUT
open LeanFormal.IUT.IUTII.Frobenioid.Example36.SourceTheaterCarrier
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.Definition31D0D11Aligned

local instance gaussianPolynomialIrreducibleFactBridge :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance fivePrimeFactBridge : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

/-! ## 1. The actual concrete source theater -/

theorem nonempty_sourceTheater (l : PrimeGeFive) :
    Nonempty (HodgeTheater.{0, 0, 0, 0} l (FinitePrimePlace 2 7)) :=
  ⟨sourceTheater l⟩

theorem sourceTheater_arithmetic_eq (l : PrimeGeFive) :
    (sourceTheater l).arithmetic = concreteGaussianInitialThetaArithmeticData l :=
  sourceTheater_arithmetic l

theorem sourceTheater_arithmetic_F_eq (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.F = GaussianField :=
  sourceTheater_arithmetic_F l

theorem sourceTheater_arithmetic_curve_eq (l : PrimeGeFive) :
    (sourceTheater l).arithmetic.curve =
      concreteSplitPuncturedCurve.baseChange GaussianField :=
  sourceTheater_arithmetic_curve l

theorem sourceTheater_primeStrip_eq (l : PrimeGeFive) :
    (sourceTheater l).primeStrip = finiteLocalIntegralFPrimeStrip 2 7 :=
  sourceTheater_primeStrip l

theorem sourceTheater_thetaPacket_eq (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket =
      FiniteThetaPacket.ofQ gaussianFiveThetaQ gaussianFiveThetaQ_pos :=
  sourceTheater_thetaPacket l

theorem sourceTheater_theta_q_eq (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q = gaussianFiveThetaQ :=
  sourceTheater_theta_q l

theorem sourceTheater_theta_q_value (l : PrimeGeFive) :
    (sourceTheater l).thetaPacket.q = (5 : ℝ)⁻¹ := by
  rw [sourceTheater_theta_q_eq, gaussianFiveThetaQ_eq_inv_five]

/-! ## 2. The genuine source-layer family constructed from the concrete carrier -/

/-- A genuine `SourceHodgeTheaterFamily` over the concrete carrier: index
`PUnit`, theater `sourceTheater l`, and reflexive links.  This uses only actual
objects and actual link operations; its singleton index is recorded below as
not supplying distinct histories. -/
noncomputable def concreteSourceFamily (l : PrimeGeFive) :
    SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7) where
  index := PUnit
  theater := fun _ => sourceTheater l
  distinct := fun i j _ => Subsingleton.elim i j
  link := fun _ _ => HodgeTheaterLink.refl (sourceTheater l)
  link_refl := fun _ => rfl
  link_symm := fun _ _ => rfl
  link_trans := fun _ _ _ => rfl
  permutation := Equiv.refl PUnit
  permutationLink := fun _ => HodgeTheaterLink.refl (sourceTheater l)
  permutation_naturality := fun _ _ => rfl

theorem concreteSourceFamily_theater (l : PrimeGeFive) :
    (concreteSourceFamily l).theater () = sourceTheater l := rfl

theorem concreteSourceFamily_index_subsingleton (l : PrimeGeFive) :
    Subsingleton (concreteSourceFamily l).index :=
  show Subsingleton PUnit from inferInstance

theorem concreteSourceFamily_theater_arithmetic (l : PrimeGeFive) :
    ((concreteSourceFamily l).theater ()).arithmetic =
      (sourceTheater l).arithmetic := by
  rw [concreteSourceFamily_theater]

theorem concreteSourceFamily_theater_primeStrip (l : PrimeGeFive) :
    ((concreteSourceFamily l).theater ()).primeStrip =
      (sourceTheater l).primeStrip := by
  rw [concreteSourceFamily_theater]

theorem concreteSourceFamily_theater_thetaPacket (l : PrimeGeFive) :
    ((concreteSourceFamily l).theater ()).thetaPacket =
      (sourceTheater l).thetaPacket := by
  rw [concreteSourceFamily_theater]

/-- The source Hodge-theater-family record has an actual inhabitant over the
concrete data (singleton index). -/
theorem nonempty_sourceHodgeTheaterFamily (l : PrimeGeFive) :
    Nonempty (SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) :=
  ⟨concreteSourceFamily l⟩

/-- The singleton family's index cannot be equivalent to `Int × Int`: it does
not supply an `OriginalInput`-shaped history index. -/
theorem concreteSourceFamily_index_not_equiv_intProd (l : PrimeGeFive) :
    ¬ Nonempty ((concreteSourceFamily l).index ≃ (Int × Int)) := by
  rintro ⟨e⟩
  haveI : Subsingleton ((concreteSourceFamily l).index) :=
    concreteSourceFamily_index_subsingleton l
  have hcontr : ((0 : Int), (0 : Int)) = ((1 : Int), (0 : Int)) :=
    e.symm.injective (Subsingleton.elim _ _)
  norm_num at hcontr

/-! ## 3. Source cards and the frozen union card -/

/-- Curve/orbicurve D6 construction gate (source-layer card). -/
def CurveOrbicurveD6Card (l : PrimeGeFive) : Prop :=
  Nonempty (D6ConstructionGate.{0} l)

/-- Geometric sign-quotient core supply (source-layer card). -/
def GeometricCoreCard (l : PrimeGeFive) : Prop :=
  SourceSignQuotientGeometricCoreSupply.{0} l

/-- Theta-generator / nontrivial Hodge-theater family card. -/
def ThetaGeneratorCard (l : PrimeGeFive) (V : Type) : Prop :=
  ∃ F : SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l V, Nontrivial F.index

/-- Distinct-history card: a Hodge-theater family with `Int × Int` index. -/
def DistinctHistoriesCard (l : PrimeGeFive) (V : Type) : Prop :=
  ∃ F : SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l V,
    Nonempty (F.index ≃ (Int × Int))

/-- D-prime-strip Galois card: an actual Theorem 3.11 original input. -/
def DPrimeStripGaloisCard (l : PrimeGeFive) (V : Type) : Prop :=
  Nonempty (OriginalInput.{0, 0, 0, 0, 0} l V)

/-- Definition 3.1 data card: the D9/D10 construction obligation. -/
def SourceDefinition31DataCard (l : PrimeGeFive) : Prop :=
  ∀ A : InitialThetaArithmeticData.{0} l, Nonempty (SourceDefinition31Data.{0} l)

/-- **The frozen union card of remaining source-layer components.**  Each field
is a precise unproved obligation; the actual components are listed separately
below. -/
structure SourceObjectUnionCard (l : PrimeGeFive) (V : Type) : Prop where
  curveOrbicurveD6 : CurveOrbicurveD6Card l
  thetaGenerators : ThetaGeneratorCard l V
  distinctHistories : DistinctHistoriesCard l V
  dPrimeStripGalois : DPrimeStripGaloisCard l V

/-! ## 4. Positive corrections -/

/-- If every theater of a Theorem 3.11 original input is the concrete carrier,
then no such original input exists: the concrete singleton carrier cannot
supply the required `Int × Int` history index. -/
theorem no_originalInput_of_all_theaters_concrete
    (I : OriginalInput.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7))
    (h : ∀ i : I.family.index, I.family.theater i = sourceTheater l) : False := by
  have hsub : Subsingleton I.family.index :=
    sourceFamily_index_subsingleton_of_concrete_theater I.family h
  have hsingle : Subsingleton (Int × Int) := by
    constructor
    intro x y
    have hxy : I.index_equiv.symm x = I.index_equiv.symm y := Subsingleton.elim _ _
    exact I.index_equiv.symm.injective hxy
  exact (show ((0 : Int), (0 : Int)) ≠ ((1 : Int), (0 : Int)) from by norm_num)
    (hsingle.elim _ _)

/-- Actual summary of the bridge available at the Example 3.6 layer. -/
theorem sourceObjectBridge_actual_summary (l : PrimeGeFive) :
    Nonempty (HodgeTheater.{0, 0, 0, 0} l (FinitePrimePlace 2 7)) ∧
    Nonempty (SourceHodgeTheaterFamily.{0, 0, 0, 0, 0} l (FinitePrimePlace 2 7)) ∧
    (sourceTheater l).arithmetic.F = GaussianField ∧
    (sourceTheater l).primeStrip = finiteLocalIntegralFPrimeStrip 2 7 ∧
    (sourceTheater l).thetaPacket.q = (5 : ℝ)⁻¹ :=
  ⟨nonempty_sourceTheater l, nonempty_sourceHodgeTheaterFamily l,
    sourceTheater_arithmetic_F_eq l, sourceTheater_primeStrip_eq l,
    sourceTheater_theta_q_value l⟩

end SourceObjectBridge

end Example36
end LeanFormal.IUT.IUTII.Frobenioid