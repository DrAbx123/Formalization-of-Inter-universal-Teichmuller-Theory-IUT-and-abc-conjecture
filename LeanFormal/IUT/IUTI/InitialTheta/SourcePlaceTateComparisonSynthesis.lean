import LeanFormal.IUT.IUTI.InitialTheta.SourcePlaceQParameterUniformization
import LeanFormal.IUT.Foundations.Geometry.TatePointQuotientBoundary
import LeanFormal.IUT.Foundations.Geometry.TateUniformizationContract
import Mathlib.Tactic

/-!
# D4 synthesis: the Tate-identification card is the one-way uniformization contract

Source: IUT I, Definition 3.1(b) with (c)(e) (corpus citations and the card
`BadPlaceTateUniformizationCards` are in
`SourcePlaceQParameterUniformization.lean`, the previous increment).

The previous increment froze the bad-place Tate-identification card and
registered its missing instance as the pending content of
`Foundations.Geometry.elliptic-tate-uniformization`.  This file performs the
minimal constructive synthesis available from the repository's own one-way
contract `CurveIndexedTateUniformization`:

* the reverse bridge `TateCurveComparison.ofUniformization` reconstructs the
  comparison from the one-way contract; the two round-trip laws and
  injectivity of `toUniformization` show that comparison data and contract
  data are equivalent structures;
* the contract family `BadPlaceUniformizationContract` over the bad moduli
  set instantiates the D4 card through the bridge, and Clause (b) is
  assembled from the contract family alone.

Consequently the smallest missing input is exactly the one-way contract
family over the bad places, i.e. the pending content of
`Foundations.Geometry.elliptic-tate-uniformization` (LocalQParameter.lean
line 145).  No Tate uniformization theorem is claimed.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace LeanFormal.IUT

noncomputable section

universe u

/-! ## Reverse bridge: comparison data from the one-way contract -/

namespace TateCurveComparison

variable {F : Type u} [Field F] [NumberField F]
variable {X : PuncturedEllipticCurve F}
variable {place : NumberField.FinitePlace F}
variable {parameter : NumberFieldFinitePlace.FinitePlaceQCandidate place}

/-- The one-way contract's data is exactly comparison data: packing the
point uniformization and its Galois equivariance yields the Tate curve
comparison. -/
def ofUniformization
    (realization : CurveIndexedTateUniformization X place parameter) :
    TateCurveComparison X place parameter where
  canonicalIsElliptic := realization.canonicalIsElliptic
  coordinateChange := realization.coordinateChange
  realizesCurve := realization.realizesCurve
  points :=
    { pointEquiv := realization.pointUniformization
      galois_naturality := realization.pointUniformization_galoisEquivariant }

theorem ofUniformization_toUniformization
    (realization : CurveIndexedTateUniformization X place parameter) :
    (ofUniformization realization).toUniformization = realization := by
  cases realization
  rfl

theorem toUniformization_ofUniformization
    (comparison : TateCurveComparison X place parameter) :
    ofUniformization comparison.toUniformization = comparison := by
  cases comparison
  rfl

theorem toUniformization_injective :
    Function.Injective
      (toUniformization (X := X) (place := place) (parameter := parameter)) := by
  intro comparison₁ comparison₂ h
  rw [← toUniformization_ofUniformization comparison₁, h,
    toUniformization_ofUniformization comparison₂]

end TateCurveComparison

namespace InitialThetaSource

namespace PlaceTateComparisonConstruction

variable {l : PrimeGeFive}
variable {A : InitialThetaArithmeticData.{u} l}

/-- The one-way uniformization contract family over the bad moduli set: for
every finite place of `F` over `V_mod_bad`, a q-parameter candidate, the
curve-indexed Tate uniformization contract at that place, and prime-to-l
coprimality of the parameter order.  Supplying an instance of this family is
exactly the pending content of the elliptic Tate obligation; no instance is
constructed from the arithmetic data here. -/
structure BadPlaceUniformizationContract (P : SourcePlaceSelection A) where
  parameter : ∀ (w : NumberField.FinitePlace A.F),
    NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad →
      NumberFieldFinitePlace.FinitePlaceQCandidate w
  realization : ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      CurveIndexedTateUniformization A.curve w (parameter w hw)
  order_coprime : ∀ (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad),
      Nat.Coprime (parameter w hw).order l.value

namespace BadPlaceUniformizationContract

variable {P : SourcePlaceSelection A}

/-- The contract family instantiates the D4 Tate-identification card via the
reverse bridge. -/
def toTateUniformizationCards (K : BadPlaceUniformizationContract P) :
    PlaceQParameterUniformization.BadPlaceTateUniformizationCards P where
  parameter := K.parameter
  comparison := fun w hw =>
    TateCurveComparison.ofUniformization (K.realization w hw)
  order_coprime := K.order_coprime

@[simp] theorem toTateUniformizationCards_parameter
    (K : BadPlaceUniformizationContract P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    (K.toTateUniformizationCards).parameter w hw = K.parameter w hw :=
  rfl

theorem toTateUniformizationCards_uniformization
    (K : BadPlaceUniformizationContract P)
    (w : NumberField.FinitePlace A.F)
    (hw : NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ P.V_mod_bad) :
    ((K.toTateUniformizationCards).comparison w hw).toUniformization =
      K.realization w hw :=
  TateCurveComparison.ofUniformization_toUniformization (K.realization w hw)

end BadPlaceUniformizationContract

variable {S : SourceSignQuotientData A}
variable {CA : SourceClauseA A S}

/-- Clause (b) assembly directly from the one-way contract family: the
uniformization card is instantiated by the bridge, and the Clause (b)
constructor of the previous increment consumes it. -/
theorem sourceClauseB_of_uniformizationContract
    (P : SourcePlaceSelection A)
    (hV_mod_bad : S.V_mod_bad = P.V_mod_bad)
    (multiplicative : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      A.curve.HasMultiplicativeReductionAt w)
    (K : BadPlaceUniformizationContract P)
    (residueCoprime : ∀ w : NumberField.FinitePlace A.F,
      NumberFieldFinitePlace.comap (k := A.Fmod) w ∈ S.V_mod_bad →
      Nat.Coprime l.value
        (NumberFieldFinitePlace.residueCharacteristic
          (NumberFieldFinitePlace.comap (k := A.Fmod) w))) :
    SourceClauseB A S CA :=
  PlaceQParameterUniformization.sourceClauseB_of_tateUniformizationCards
    P hV_mod_bad multiplicative K.toTateUniformizationCards residueCoprime

end PlaceTateComparisonConstruction

end InitialThetaSource

namespace Audit

/-- The synthesis increment: the D4 card is equivalent to the one-way
contract family over the bad places, so the missing input is exactly the
pending elliptic Tate content. -/
def tateUniformizationCardSynthesis : Obligation :=
  { id := "IUT-I.definition-3.1-D4-tate-uniformization-card-synthesis"
    source := "IUT I, Definition 3.1(b)(c)(e): reverse synthesis of the D4 Tate comparison card"
    status := VerificationStatus.conditional
    note :=
      "Proved: the one-way curve-indexed uniformization contract reconstructs " ++
        "the Tate curve comparison (pointEquiv is pointUniformization and " ++
        "Galois naturality is the contract's equivariance), with both " ++
        "round-trip laws and injectivity of toUniformization; the bad-place " ++
        "contract family instantiates BadPlaceTateUniformizationCards, and " ++
        "Clause (b) is assembled from the contract family alone. The " ++
        "smallest missing input is therefore exactly the contract family " ++
        "over the bad places (Foundations.Geometry.elliptic-tate-uniformization, " ++
        "pending); no Tate theorem is claimed."
    dependsOn :=
      [ "IUT-I.definition-3.1-D4-tate-uniformization-identification",
        "IUT-I.definition-3.1-D4-clause-assembly",
        "Foundations.Geometry.elliptic-tate-uniformization",
        "Foundations.Geometry.curve-indexed-tate-uniformization",
        "Foundations.Geometry.tate-point-quotient-boundary" ] }

end Audit

end

end LeanFormal.IUT
