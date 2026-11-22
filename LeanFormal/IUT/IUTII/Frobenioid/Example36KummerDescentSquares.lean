import LeanFormal.IUT.IUTII.Frobenioid.Example36LogKummerMap
import LeanFormal.IUT.IUTII.Frobenioid.Example36ValueMapTransportCorrection
import LeanFormal.IUT.IUTII.Frobenioid.Example36QuadraticRamificationProof

/-!
# Layer2: actual K1/K2 Kummer descent squares with cross-field transport

Actual ingredients: cross-field scaled source value kernel and its target identity
(Example36ValueMapTransportCorrection), e-th power degree law, genuine unit map
unitsMapOfRingHom T.fieldMap, actual log-Kummer data and Frobenius commutation
(Example36LogKummerMap), scaled logarithm commutation, and the concrete quadratic
instance with proved ramification index two (Example36QuadraticRamificationProof).

The K1 square is the actual value-map identity for the e-scaled source kernel.
The K2 square is the actual log-Kummer/Frobenius commutation plus the actual
scaled-logarithm commutation.  The frozen card records only the missing source
K1/K2 operator identification; it is not inhabited and no theorem consumes it.
-/

set_option linter.unusedVariables false

noncomputable section

namespace LeanFormal.IUT.IUTII.Frobenioid
namespace Example36

open IsDedekindDomain NumberField
open scoped NumberField
open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellLattice
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogShellFrobeniusAction
open LeanFormal.IUT.IUTII.Frobenioid.Example36.LogKummerMap
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

local instance kummerDescentGaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

local instance kummerDescentFivePrime : Fact (Nat.Prime 5) :=
  ⟨Nat.prime_five⟩

universe u

variable {F : Type u} [Field F] [NumberField F]
variable {F' : Type u} [Field F'] [NumberField F']

/-! ## 1. The K1/K2 Kummer descent square data -/

structure KummerDescentSquareData
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) where
  e : ℕ
  sourceValueKernel : LeanFormal.IUT.FrobenioidValueKernel Fˣ
  targetValueKernel : LeanFormal.IUT.FrobenioidValueKernel F'ˣ
  scaledSourceValueKernel : LeanFormal.IUT.FrobenioidValueKernel Fˣ
  unitTransport : Fˣ →* F'ˣ
  e_eq : e = T.ramificationIndex w
  source_eq : sourceValueKernel = finiteValueKernel D (T.finitePlaceRestriction w)
  target_eq : targetValueKernel = finiteValueKernel D' w
  scaled_eq : scaledSourceValueKernel = transportedScaledSourceValueKernel T w
  unitTransport_eq : unitTransport = unitsMapOfRingHom T.fieldMap
  K1_square : ∀ f : Fˣ,
    scaledSourceValueKernel.realification f =
      targetValueKernel.realification (unitTransport f)
  K1_degree_pow : ∀ f : Fˣ,
    scaledSourceValueKernel.degree f = sourceValueKernel.degree f ^ e
  sourceLogKummer : LogKummerData
  targetLogKummer : LogKummerData
  K2_square : ∀ h : targetLogKummer.H,
    targetLogKummer.logKummer (targetLogKummer.frobenius h) =
      targetLogKummer.pScaling (targetLogKummer.logKummer h)
  K2_scaled_log_square : ∀ u : principalUnits (K := concreteLogShellField),
    scaledPrincipalUnitLog (principalUnitFrobenius u) =
      integralLogShellPScaling (scaledPrincipalUnitLog u)

/-- The actual descent square: every field instantiated from transported data
and its proved laws. -/
noncomputable def kummerDescentSquareData
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    KummerDescentSquareData T w where
  e := T.ramificationIndex w
  sourceValueKernel := finiteValueKernel D (T.finitePlaceRestriction w)
  targetValueKernel := finiteValueKernel D' w
  scaledSourceValueKernel := transportedScaledSourceValueKernel T w
  unitTransport := unitsMapOfRingHom T.fieldMap
  e_eq := rfl
  source_eq := rfl
  target_eq := rfl
  scaled_eq := rfl
  unitTransport_eq := rfl
  K1_square := fun f =>
    transportedScaledSourceValueKernel_realification_eq_target T w f
  K1_degree_pow := fun f =>
    transportedScaledSourceValueKernel_degree_eq_pow T w f
  sourceLogKummer := logKummerData
  targetLogKummer := logKummerData
  K2_square := fun h => logKummerData.commutes h
  K2_scaled_log_square := fun u => scaledPrincipalUnitLog_frobenius u

theorem kummerDescentSquareData_e_pos
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) :
    0 < (kummerDescentSquareData T w).e :=
  T.ramificationIndex_pos w

theorem kummerDescentSquareData_K1_square
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) (f : Fˣ) :
    (kummerDescentSquareData T w).scaledSourceValueKernel.realification f =
      (kummerDescentSquareData T w).targetValueKernel.realification
        ((kummerDescentSquareData T w).unitTransport f) :=
  (kummerDescentSquareData T w).K1_square f

theorem kummerDescentSquareData_K2_square
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F'))
    (h : (kummerDescentSquareData T w).targetLogKummer.H) :
    (kummerDescentSquareData T w).targetLogKummer.logKummer
        ((kummerDescentSquareData T w).targetLogKummer.frobenius h) =
      (kummerDescentSquareData T w).targetLogKummer.pScaling
        ((kummerDescentSquareData T w).targetLogKummer.logKummer h) :=
  (kummerDescentSquareData T w).K2_square h

/-! ## 2. The concrete e = 2 descent square -/

noncomputable def quadraticKummerDescentSquare :
    KummerDescentSquareData
      (D := numberFieldGlobalPlaceData (F := ℚ))
      (D' := numberFieldGlobalPlaceData (F := squareRootField ℚ (2 : ℚ)))
      quadraticSquareRootTwoTransport sqrtTwoUpperPlace :=
  kummerDescentSquareData quadraticSquareRootTwoTransport sqrtTwoUpperPlace

theorem quadraticKummerDescentSquare_e_eq_two :
    quadraticKummerDescentSquare.e = 2 := by
  change quadraticSquareRootTwoTransport.ramificationIndex sqrtTwoUpperPlace = 2
  exact quadraticSquareRootTwoTransport_ramificationIndex_eq_two sqrtTwoUpperPlace

theorem quadraticKummerDescentSquare_e_ne_one :
    quadraticKummerDescentSquare.e ≠ 1 := by
  rw [quadraticKummerDescentSquare_e_eq_two]
  norm_num

/-! ## 3. Frozen source K1/K2 identification card -/

structure KummerDescentSourceIdentificationCard
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    (T : PlaceLocalizationTransport D D') (w : HeightOneSpectrum (𝓞 F')) where
  sourceK1Map : Fˣ → ℝ
  sourceK2Map :
    principalUnits (K := concreteLogShellField) → principalUnitLogShell
  sourceK1Map_eq : sourceK1Map = fun f =>
    (transportedScaledSourceValueKernel T w).realification f
  sourceK2Map_eq : sourceK2Map = logKummer

theorem KummerDescentSourceIdentificationCard.sourceK1Map_spec
    {D : GlobalPlaceData F} {D' : GlobalPlaceData F'}
    {T : PlaceLocalizationTransport D D'} {w : HeightOneSpectrum (𝓞 F')}
    (C : KummerDescentSourceIdentificationCard T w) (f : Fˣ) :
    C.sourceK1Map f = (transportedScaledSourceValueKernel T w).realification f := by
  rw [C.sourceK1Map_eq]

end Example36
end LeanFormal.IUT.IUTII.Frobenioid