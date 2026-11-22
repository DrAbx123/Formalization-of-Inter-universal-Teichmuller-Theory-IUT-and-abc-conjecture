import tmp.sheaf.xif.paper.S1266SourceInd3Actual
import tmp.sheaf.xif.paper.S1313IntegralLogShellContractActual
import Mathlib.Data.Fin.Rev

/-!
# S1327: the integral Ind3 log-shell carrier and stage

## Why this file exists

S1266SourceInd3Actual constructs the actual (Ind3) times-mu stage data of IUT III,
Theorem 3.11, (ii), for an arbitrary original input I, and names the exact first
missing source datum: the analytic log-shell carrier Ind3LogShellCarrier, whose
first field shell is the first field of
SourceProcessionCapsule.LogShellFamily.

S1297Ind3LogShellActual filled that first field with S1270's
actualLogShellFamily, whose shell at an actual place is the rational span
(sourceLocalLogShellDatum ...).IQSpan.  That object is a Q-vector space:
every nonzero rational -- in particular p^{-1} -- acts on it, so the integral
Z/Z_p structure of IUT III, Definition 1.1, (i), is lost.  S1301 audited this
defect for the earlier capsule contracts.

S1313IntegralLogShellContractActual replaces those substitutes by the actual
integral log-shell.  It builds two genuine SourceProcessionCapsuleContract
values:

* actualIntegralCapsuleContract, over the coefficient ring Z, whose logShell
  field is integralLogShellFamily I j; at every capsule label, rational
  valuation and actual finite place the shell is the integral log-shell

    I_v = (p*_v)^{-1} * log_v(O^×_{K_v})  as an additive subgroup of K_v;

* actualPadicLatticeCapsuleContract, over the coefficient ring Z_[l], whose
  logShell field is padicLatticeLogShellFamily I j; the shell is the genuine
  Z_[l]-lattice integralLogShellLattice, free of finite rank.

## What is constructed here

* IntegralPlaceTotal is the total actual place type (vQ, v) of S1313.
* integralInd3LogShellCarrier is a genuine Ind3LogShellCarrier over Z and that
  actual place type.  Its shell field is, definitionally, the carrier of
  S1313's actual integral log-shell actualIntegralLogShell I vQ v, i.e. exactly
  the first field Shell of the contract's logShell.  No PUnit, no IQSpan, no
  Q-span and no arbitrary module is used.
* integralInd3LogShellCarrier_shell_eq_contract records the exact first field at
  the contract: the carrier's shell is literally
  ((actualIntegralCapsuleContract I).logShell j).Shell i vQ v.
* integralInd3LogShellFamily is the induced LogShellFamily; it is
  definitionally equal to integralLogShellFamily and hence to the contract's
  logShell field.  toLogShellFamilyOfCarrier is the universe-correct version of
  S1266's Ind3LogShellCarrier.toLogShellFamily, and
  toLogShellFamilyOfCarrier_eq_s1266 proves that on Type 0 places it is literally
  S1266's constructor.
* padicInd3LogShellCarrier / padicInd3LogShellFamily do the same for the
  Z_[l]-lattice contract actualPadicLatticeCapsuleContract; the shell is the
  Z_[l]-lattice integralLogShellLattice.
* IntegralInd3StageDatum / PadicInd3StageDatum attach S1266's actual times-mu
  stage data sourceInd3StageData and the actual stage poly-isomorphism
  ind3StagePolyIso to the integral carriers.  The bundle does not assert a
  compatibility between the times-mu stage and the log-shell module: S1266
  records that these are different levels (at the times-mu level the stage
  comparison is an isomorphism, ind3StageComparison_image_univ), so the
  one-sided (Ind3) comparison must come from the log-shell/Kummer side.
* IntegralInd3StageDatumAtV is the conditional source-place (V) version:
  filling the first field on V requires the exact place comparison
  IntegralInd3PlaceComparison (V -> (vQ, v)).  No inhabitant of that comparison
  is constructed or asserted, and no arbitrary constant place map is used.
  Given a comparison, ind3LogShellCarrierRequired_of_integralPlaceMap closes
  S1266's Ind3LogShellCarrierRequired at V.

## Integrality is proved, not asserted

For every capsule label and actual place:

* one_mem_integralShell: the shell contains 1, so it is nonzero;
* integralShell_nontrivial: it has at least two elements (0 and 1);
* integralShell_eq_range: it is the actual compact image
  (p*_v)^{-1} log_v(O^×_{K_v}) of the local units;
* integralShell_set_eq_sourceLocalLogShellDatum: it is the log-shell of the
  actual source local datum;
* integralShell_span_padic_eq_top and exists_padicSpan_not_mem_integralShell:
  its Q_p-span is the whole local field, but the shell itself is a proper
  subset;
* integralShell_not_smul_inv_closed and integralShell_not_rat_smul_closed: the
  shell is not closed under division by p, nor under all rational scalars.
  Hence it is not a Q_p- or Q-vector space, and in particular cannot be the
  IQSpan used by S1270;
* for the Z_[l] contract: padicShell_free, padicShell_finite, padicShell_finrank
  (rank = local degree), padicShell_ne_univ and padicShell_not_smul_inv_closed.

No sorry, no new axiom, no PUnit/one-point model, no IQSpan/Q-span.
-/

noncomputable section

open scoped TensorProduct

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

namespace LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual

open LeanFormal.IUT
open LeanFormal.IUT.Theorem311Source
open LeanFormal.IUT.Theorem311Source.SourceProcessionCapsule
open LeanFormal.IUT.XiFPaper.S1266SourceInd3Actual
open LeanFormal.IUT.XiFPaper.S1313IntegralLogShellContractActual
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.LocalFieldIntegralUnits

universe ua uv upi umon ui

variable {l : PrimeGeFive} {V : Type uv}
variable (I : OriginalInput.{ua, uv, upi, umon, ui} l V)

/-- The rational valuation of a place is prime, so the local field is a
Q_p-adic field.  This is the same local instance used by S1313. -/
local instance integralValuationFact (vQ : ActualIntegralValuation) :
    Fact (Nat.Prime vQ.1) := ⟨vQ.2⟩

/-- The arithmetic prime l is prime. -/
local instance integralPrimeGeFiveFact (l : PrimeGeFive) :
    Fact (Nat.Prime l.value) := l.factPrime

/-! ## 1. The integral carrier over the actual places -/

/-- The total actual place type (vQ, v) of S1313: a rational valuation together
with an actual finite place over it. -/
abbrev IntegralPlaceTotal : Type (max 0 ua) :=
  (vQ : ActualIntegralValuation) × actualIntegralPlace I vQ

/-- The carrier of the actual integral log-shell at an actual place.  This is
the first field Shell of S1313's integralLogShellFamily, i.e. the integral
log-shell I_v = (p*_v)^{-1} log_v(O^×_{K_v}) as a Z-module. -/
abbrev integralShell (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) : Type ua :=
  ↥(actualIntegralLogShell I vQ v)

/-- The shell is literally the carrier of S1313's actualIntegralLogShell. -/
theorem integralShell_eq_subtype (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    integralShell I vQ v = ↥(actualIntegralLogShell I vQ v) := rfl

/-- The actual integral Ind3 log-shell carrier over the total actual place
type, with coefficient ring Z.  Its first field is S1313's actual integral
log-shell, not a Q-span and not PUnit. -/
noncomputable def integralInd3LogShellCarrier (j : Nat) :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := IntegralPlaceTotal I) (R := ℤ) j where
  shell i x := integralShell I x.1 x.2
  addCommMonoid i x := inferInstance
  module i x := inferInstance

/-- The first field of the integral carrier is the actual integral log-shell. -/
theorem integralInd3LogShellCarrier_shell (j : Nat) (i : Capsule j)
    (x : IntegralPlaceTotal I) :
    (integralInd3LogShellCarrier I j).shell i x =
      integralShell I x.1 x.2 := rfl

/-- The first field is the actual integral log-shell as a subtype. -/
theorem integralInd3LogShellCarrier_shell_eq_subtype (j : Nat) (i : Capsule j)
    (x : IntegralPlaceTotal I) :
    (integralInd3LogShellCarrier I j).shell i x =
      ↥(actualIntegralLogShell I x.1 x.2) := rfl

/-- The first field of the carrier is literally the first field Shell of
S1313's actual integral capsule contract at every capsule level. -/
theorem integralInd3LogShellCarrier_shell_eq_contract
    (j : Fin (capsuleLevels l)) (i : Capsule j.val)
    (x : IntegralPlaceTotal I) :
    (integralInd3LogShellCarrier I j.val).shell i x =
      ((actualIntegralCapsuleContract I).logShell j).Shell i x.1 x.2 := rfl

/-- The first field is literally the first field of S1313's integral log-shell
family, which is the logShell family of the integral capsule contract. -/
theorem integralInd3LogShellCarrier_shell_eq_integralLogShellFamily
    (j : Nat) (i : Capsule j) (x : IntegralPlaceTotal I) :
    (integralInd3LogShellCarrier I j).shell i x =
      (integralLogShellFamily I j).Shell i x.1 x.2 := rfl

/-- The carrier is an actual inhabitant of S1266's open carrier requirement at
the actual place type. -/
theorem integralInd3LogShellCarrierRequired_actual (j : Nat) :
    Ind3LogShellCarrierRequired.{max 0 ua, 0, ua}
      (V := IntegralPlaceTotal I) (R := ℤ) j :=
  ⟨integralInd3LogShellCarrier I j⟩

/-- The fiberwise carrier at one rational valuation. -/
noncomputable def integralInd3LogShellCarrierAt
    (vQ : ActualIntegralValuation) (j : Nat) :
    Ind3LogShellCarrier.{ua, 0, ua} (V := actualIntegralPlace I vQ) (R := ℤ) j where
  shell i v := integralShell I vQ v
  addCommMonoid i v := inferInstance
  module i v := inferInstance

/-- The fiberwise first field is the actual integral log-shell. -/
theorem integralInd3LogShellCarrierAt_shell (vQ : ActualIntegralValuation)
    (j : Nat) (i : Capsule j) (v : actualIntegralPlace I vQ) :
    (integralInd3LogShellCarrierAt I vQ j).shell i v =
      integralShell I vQ v := rfl

/-- The total carrier restricts to the fiber carrier. -/
theorem integralInd3LogShellCarrier_restrict (j : Nat) (i : Capsule j)
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (integralInd3LogShellCarrier I j).shell i ⟨vQ, v⟩ =
      (integralInd3LogShellCarrierAt I vQ j).shell i v := rfl

/-- The fiberwise carrier is an actual inhabitant of S1266's open requirement
at that valuation. -/
theorem integralInd3LogShellCarrierAtRequired_actual
    (vQ : ActualIntegralValuation) (j : Nat) :
    Ind3LogShellCarrierRequired.{ua, 0, ua}
      (V := actualIntegralPlace I vQ) (R := ℤ) j :=
  ⟨integralInd3LogShellCarrierAt I vQ j⟩

/-! ## 2. Exactness of the first field: the induced log-shell family

S1266's Ind3LogShellCarrier.toLogShellFamily fixes the valuation type and the
place types in Type 0.  The actual finite-place fibers live in Type ua, so the
universe-correct version below is the one that applies.  On Type 0 places it is
literally S1266's constructor. -/

/-- Universe-correct form of S1266's Ind3LogShellCarrier.toLogShellFamily. -/
noncomputable def toLogShellFamilyOfCarrier.{uW, uVQ, uPlace, uR, uShell}
    {W : Type uW} {R : Type uR} [CommSemiring R] {j : Nat}
    (L : Ind3LogShellCarrier.{uW, uR, uShell} (V := W) (R := R) j)
    {VQ : Type uVQ} (Place : VQ → Type uPlace) (p : ∀ vQ, Place vQ → W) :
    LogShellFamily.{uR, uVQ, uPlace, uShell} R Place j where
  Shell i vQ v := L.shell i (p vQ v)
  addCommMonoid i vQ v := L.addCommMonoid i (p vQ v)
  module i vQ v := L.module i (p vQ v)

/-- The first field of the induced family is the carrier's first field. -/
theorem toLogShellFamilyOfCarrier_shell.{uW, uVQ, uPlace, uR, uShell}
    {W : Type uW} {R : Type uR} [CommSemiring R] {j : Nat}
    (L : Ind3LogShellCarrier.{uW, uR, uShell} (V := W) (R := R) j)
    {VQ : Type uVQ} (Place : VQ → Type uPlace) (p : ∀ vQ, Place vQ → W)
    (i : Capsule j) (vQ : VQ) (v : Place vQ) :
    (toLogShellFamilyOfCarrier L Place p).Shell i vQ v = L.shell i (p vQ v) :=
  rfl

/-- In the Type 0 case the universe-correct constructor is literally S1266's
Ind3LogShellCarrier.toLogShellFamily: nothing is renamed or re-typed. -/
theorem toLogShellFamilyOfCarrier_eq_s1266
    {W : Type} {R : Type} [CommSemiring R] {j : Nat}
    (L : Ind3LogShellCarrier.{0, 0, ua} (V := W) (R := R) j)
    (VQ : Type) (Place : VQ → Type) (p : ∀ vQ, Place vQ → W) :
    toLogShellFamilyOfCarrier L Place p = L.toLogShellFamily R j VQ Place p :=
  rfl

/-- The actual integral log-shell family induced by the integral carrier. -/
noncomputable def integralInd3LogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℤ (actualIntegralPlace I) j :=
  toLogShellFamilyOfCarrier (integralInd3LogShellCarrier I j)
    (actualIntegralPlace I) (fun vQ v => ⟨vQ, v⟩)

/-- The induced family's first field is the actual integral log-shell. -/
theorem integralInd3LogShellFamily_shell (j : Nat) (i : Capsule j)
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (integralInd3LogShellFamily I j).Shell i vQ v =
      integralShell I vQ v := rfl

/-- The induced family's first field is literally the carrier of S1313's
actualIntegralLogShell. -/
theorem integralInd3LogShellFamily_Shell (j : Nat) (i : Capsule j)
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (integralInd3LogShellFamily I j).Shell i vQ v =
      ↥(actualIntegralLogShell I vQ v) := rfl

/-- The induced family is definitionally S1313's integralLogShellFamily. -/
theorem integralInd3LogShellFamily_eq_integralLogShellFamily (j : Nat) :
    integralInd3LogShellFamily I j = integralLogShellFamily I j := rfl

/-- Hence the induced family is exactly the contract's logShell field. -/
theorem integralInd3LogShellFamily_eq_contract_logShell
    (j : Fin (capsuleLevels l)) :
    integralInd3LogShellFamily I j.val =
      (actualIntegralCapsuleContract I).logShell j :=
  rfl

/-- The literal first-field form at the contract's capsule level. -/
theorem integralInd3LogShellFamily_Shell_eq_contract_shell
    (j : Fin (capsuleLevels l)) (i : Capsule j.val)
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (integralInd3LogShellFamily I j.val).Shell i vQ v =
      ((actualIntegralCapsuleContract I).logShell j).Shell i vQ v :=
  rfl

/-! ## 3. The shell is a genuine integral log-shell

These are the local-field facts that a Q-span or a field surrogate does not
have.  All of them are the corresponding S1313 statements at the actual place,
restated for the carrier's first field. -/

/-- The integral shell contains 1: the integer ring lies inside it, so it is a
nonzero lattice. -/
theorem one_mem_integralShell (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (1 : CommonPrimeCompletion v) ∈ actualIntegralLogShell I vQ v :=
  one_mem_integralLogShell (K := CommonPrimeCompletion v) (p := vQ.1)

/-- The integral shell contains 0. -/
theorem zero_mem_integralShell (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (0 : CommonPrimeCompletion v) ∈ actualIntegralLogShell I vQ v :=
  (actualIntegralLogShell I vQ v).zero_mem

/-- Each shell has at least two elements: it is not the one-point PUnit model. -/
theorem integralShell_nontrivial (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Nontrivial (integralShell I vQ v) := by
  refine ⟨⟨1, one_mem_integralShell I vQ v⟩,
    ⟨0, zero_mem_integralShell I vQ v⟩, ?_⟩
  intro h
  have h1 : (1 : CommonPrimeCompletion v) = 0 := congrArg Subtype.val h
  exact one_ne_zero h1

/-- The carrier's own first field is nontrivial. -/
theorem integralInd3LogShellCarrier_shell_nontrivial
    (j : Nat) (i : Capsule j) (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Nontrivial ((integralInd3LogShellCarrier I j).shell i ⟨vQ, v⟩) :=
  integralShell_nontrivial I vQ v

/-- The fiberwise carrier's first field is nontrivial. -/
theorem integralInd3LogShellCarrierAt_shell_nontrivial
    (vQ : ActualIntegralValuation) (j : Nat) (i : Capsule j)
    (v : actualIntegralPlace I vQ) :
    Nontrivial ((integralInd3LogShellCarrierAt I vQ j).shell i v) :=
  integralShell_nontrivial I vQ v

/-- The integral shell is the actual compact image (p*_v)^{-1} log_v(O^×) of
the local units, not an abstract span. -/
theorem integralShell_eq_range (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      Set.range (fun u : (Integers (CommonPrimeCompletion v))ˣ =>
        (logShellScale vQ.1 : CommonPrimeCompletion v)⁻¹ *
          unitLog (K := CommonPrimeCompletion v) u) :=
  actualIntegralLogShell_eq_range I vQ v

/-- The integral shell is the log-shell of the actual source local datum. -/
theorem integralShell_set_eq_sourceLocalLogShellDatum
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      (actualIntegralLocalDatum I vQ v).logShell :=
  actualIntegralLogShell_eq_sourceLocalLogShellDatum I vQ v

/-- The Z-module carrier is the carrier of the actual Z_p-lattice. -/
theorem integralShell_set_eq_latticeCarrier
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) =
      (actualIntegralLogShellLattice I vQ v : Set (CommonPrimeCompletion v)) :=
  actualIntegralLogShell_eq_latticeCarrier I vQ v

/-- The shell is closed under the actual additive structure. -/
theorem integralShell_add_mem (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) {x y : CommonPrimeCompletion v}
    (hx : x ∈ actualIntegralLogShell I vQ v)
    (hy : y ∈ actualIntegralLogShell I vQ v) :
    x + y ∈ actualIntegralLogShell I vQ v :=
  actualIntegralLogShell_add_mem I vQ v hx hy

/-- The Z-module structure of the shell: integer multiples stay in it. -/
theorem integralShell_int_smul_mem (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) (n : ℤ) {x : CommonPrimeCompletion v}
    (hx : x ∈ actualIntegralLogShell I vQ v) :
    n • x ∈ actualIntegralLogShell I vQ v :=
  actualIntegralLogShell_int_smul_mem I vQ v n hx

/-- The shell is closed under the actual Z_[p]-scalars, so it is an integral
lattice and not merely an additive subgroup. -/
theorem integralShell_padicInt_mul_mem (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) (z : ℤ_[vQ.1])
    {x : CommonPrimeCompletion v}
    (hx : x ∈ actualIntegralLogShell I vQ v) :
    algebraMap ℚ_[vQ.1] (CommonPrimeCompletion v) (z : ℚ_[vQ.1]) * x ∈
      actualIntegralLogShell I vQ v :=
  actualIntegralLogShell_padicInt_mul_mem I vQ v z hx

/-- The shell is not the whole local field: no field surrogate. -/
theorem integralShell_ne_univ (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) ≠ Set.univ :=
  actualIntegralLogShell_ne_univ I vQ v

/-- The shell is not closed under division by the local prime: it is a lattice,
not a Q_p-vector space. -/
theorem integralShell_not_smul_inv_closed (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    ¬ (∀ x ∈ actualIntegralLogShell I vQ v,
        (vQ.1 : ℚ_[vQ.1])⁻¹ • x ∈ actualIntegralLogShell I vQ v) :=
  actualIntegralLogShell_not_smul_inv_closed I vQ v

/-- The shell is not closed under all rational scalars: it is not a
Q-vector space.  This is the precise sense in which the carrier is not the
IQSpan used by S1270. -/
theorem integralShell_not_rat_smul_closed (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    ¬ (∀ (q : ℚ) (x : CommonPrimeCompletion v),
        x ∈ actualIntegralLogShell I vQ v → q • x ∈ actualIntegralLogShell I vQ v) := by
  intro h
  apply integralShell_not_smul_inv_closed I vQ v
  intro x hx
  have hq : algebraMap ℚ ℚ_[vQ.1] ((vQ.1 : ℚ))⁻¹ • x ∈
      actualIntegralLogShell I vQ v := by
    rw [IsScalarTower.algebraMap_smul]
    exact h ((vQ.1 : ℚ))⁻¹ x hx
  have hinv : (((vQ.1 : ℕ) : ℚ_[vQ.1]))⁻¹ =
      algebraMap ℚ ℚ_[vQ.1] ((vQ.1 : ℚ))⁻¹ := by
    rw [map_inv₀, map_natCast]
  rw [← hinv] at hq
  exact hq

/-- The Q_p-span of the shell is the whole local field. -/
theorem integralShell_span_padic_eq_top (vQ : ActualIntegralValuation)
    (v : actualIntegralPlace I vQ) :
    Submodule.span ℚ_[vQ.1]
      (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) = ⊤ :=
  actualIntegralLogShell_span_padic_eq_top I vQ v

/-- The shell is properly smaller than its own Q_p-span. -/
theorem exists_padicSpan_not_mem_integralShell
    (vQ : ActualIntegralValuation) (v : actualIntegralPlace I vQ) :
    ∃ x : CommonPrimeCompletion v,
      x ∈ Submodule.span ℚ_[vQ.1]
        (actualIntegralLogShell I vQ v : Set (CommonPrimeCompletion v)) ∧
        x ∉ actualIntegralLogShell I vQ v :=
  exists_padicSpan_not_mem_actualIntegralLogShell I vQ v

/-! ## 4. The Z_[l]-lattice carrier from actualPadicLatticeCapsuleContract -/

/-- The total actual place type at the fixed arithmetic prime l: a rational
place above l together with an actual finite place of the source field above
l. -/
abbrev PadicPlaceTotal : Type (max 0 ua) :=
  RationalPlaceAt l × PadicLatticePlace I

/-- The carrier of the actual Z_[l]-lattice integralLogShellLattice. -/
abbrev padicShell (v : PadicLatticePlace I) : Type ua :=
  ↥(padicIntegralLogShellLattice I v)

/-- The shell is literally the carrier of S1313's padicIntegralLogShellLattice. -/
theorem padicShell_eq_subtype (v : PadicLatticePlace I) :
    padicShell I v = ↥(padicIntegralLogShellLattice I v) := rfl

/-- The actual integral Ind3 log-shell carrier over the Z_[l]-lattice, with
coefficient ring Z_[l].  Its first field is S1313's Z_[l]-lattice, not a Q-span
and not PUnit. -/
noncomputable def padicInd3LogShellCarrier (j : Nat) :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := PadicPlaceTotal I)
      (R := ℤ_[l.value]) j where
  shell i x := padicShell I x.2
  addCommMonoid i x := inferInstance
  module i x := inferInstance

/-- The first field of the Z_[l]-carrier is the actual Z_[l]-lattice. -/
theorem padicInd3LogShellCarrier_shell (j : Nat) (i : Capsule j)
    (x : PadicPlaceTotal I) :
    (padicInd3LogShellCarrier I j).shell i x = padicShell I x.2 := rfl

/-- The first field of the Z_[l]-carrier is literally the first field Shell of
S1313's actualPadicLatticeCapsuleContract. -/
theorem padicInd3LogShellCarrier_shell_eq_contract
    (j : Fin (capsuleLevels l)) (i : Capsule j.val)
    (x : PadicPlaceTotal I) :
    (padicInd3LogShellCarrier I j.val).shell i x =
      ((actualPadicLatticeCapsuleContract I).logShell j).Shell i x.1 x.2 := rfl

/-- The first field is literally the first field of S1313's Z_[l]-lattice
log-shell family, which is the logShell family of the Z_[l] contract. -/
theorem padicInd3LogShellCarrier_shell_eq_padicLatticeLogShellFamily
    (j : Nat) (i : Capsule j) (x : PadicPlaceTotal I) :
    (padicInd3LogShellCarrier I j).shell i x =
      (padicLatticeLogShellFamily I j).Shell i x.1 x.2 := rfl

/-- The Z_[l]-carrier is an actual inhabitant of S1266's open carrier
requirement at the l-adic place type. -/
theorem padicInd3LogShellCarrierRequired_actual (j : Nat) :
    Ind3LogShellCarrierRequired.{max 0 ua, 0, ua}
      (V := PadicPlaceTotal I) (R := ℤ_[l.value]) j :=
  ⟨padicInd3LogShellCarrier I j⟩

/-- The actual Z_[l]-lattice log-shell family induced by the carrier. -/
noncomputable def padicInd3LogShellFamily (j : Nat) :
    LogShellFamily.{0, 0, ua, ua} ℤ_[l.value]
      (fun _ : RationalPlaceAt l => PadicLatticePlace I) j :=
  toLogShellFamilyOfCarrier (padicInd3LogShellCarrier I j)
    (fun _ : RationalPlaceAt l => PadicLatticePlace I) (fun vQ v => ⟨vQ, v⟩)

/-- The induced Z_[l] family's first field is the lattice. -/
theorem padicInd3LogShellFamily_shell (j : Nat) (i : Capsule j)
    (vQ : RationalPlaceAt l) (v : PadicLatticePlace I) :
    (padicInd3LogShellFamily I j).Shell i vQ v = padicShell I v := rfl

/-- The induced Z_[l] family is definitionally S1313's
padicLatticeLogShellFamily. -/
theorem padicInd3LogShellFamily_eq_padicLatticeLogShellFamily (j : Nat) :
    padicInd3LogShellFamily I j = padicLatticeLogShellFamily I j := rfl

/-- Hence the induced Z_[l] family is exactly the contract's logShell field. -/
theorem padicInd3LogShellFamily_eq_contract_logShell
    (j : Fin (capsuleLevels l)) :
    padicInd3LogShellFamily I j.val =
      (actualPadicLatticeCapsuleContract I).logShell j := rfl

/-- The Z_[l]-lattice contains 1. -/
theorem one_mem_padicShell (v : PadicLatticePlace I) :
    (1 : CommonPrimeCompletion v) ∈ padicIntegralLogShellLattice I v :=
  one_mem_integralLogShell (K := CommonPrimeCompletion v) (p := l.value)

/-- Each Z_[l]-lattice shell has at least two elements. -/
theorem padicShell_nontrivial (v : PadicLatticePlace I) :
    Nontrivial (padicShell I v) := by
  refine ⟨⟨1, one_mem_padicShell I v⟩,
    ⟨0, (padicIntegralLogShellLattice I v).zero_mem⟩, ?_⟩
  intro h
  have h1 : (1 : CommonPrimeCompletion v) = 0 := congrArg Subtype.val h
  exact one_ne_zero h1

/-- The Z_[l]-lattice is free. -/
theorem padicShell_free (v : PadicLatticePlace I) :
    Module.Free ℤ_[l.value] (padicShell I v) :=
  padicIntegralLogShellLattice_free I v

/-- The Z_[l]-lattice is a finite module. -/
theorem padicShell_finite (v : PadicLatticePlace I) :
    Module.Finite ℤ_[l.value] (padicShell I v) :=
  padicIntegralLogShellLattice_finite I v

/-- The rank of the Z_[l]-lattice is the local degree. -/
theorem padicShell_finrank (v : PadicLatticePlace I) :
    Module.finrank ℤ_[l.value] (padicShell I v) =
      Module.finrank ℚ_[l.value] (CommonPrimeCompletion v) :=
  padicIntegralLogShellLattice_finrank I v

/-- The Z_[l]-lattice is not the whole local field. -/
theorem padicShell_ne_univ (v : PadicLatticePlace I) :
    (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) ≠ Set.univ :=
  padicIntegralLogShellLattice_ne_univ I v

/-- The Z_[l]-lattice is not closed under division by l: it is a lattice, not a
Q_l-vector space. -/
theorem padicShell_not_smul_inv_closed (v : PadicLatticePlace I) :
    ¬ (∀ x ∈ padicIntegralLogShellLattice I v,
        (l.value : ℚ_[l.value])⁻¹ • x ∈ padicIntegralLogShellLattice I v) :=
  padicIntegralLogShellLattice_not_smul_inv_closed I v

/-- The Q_l-span of the Z_[l]-lattice is the whole local field. -/
theorem padicShell_span_padic_eq_top (v : PadicLatticePlace I) :
    Submodule.span ℚ_[l.value]
      (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) = ⊤ :=
  padicIntegralLogShellLattice_span_padic_eq_top I v

/-- The Z_[l]-lattice is properly smaller than its own Q_l-span. -/
theorem exists_padicSpan_not_mem_padicShell (v : PadicLatticePlace I) :
    ∃ x : CommonPrimeCompletion v,
      x ∈ Submodule.span ℚ_[l.value]
        (padicIntegralLogShellLattice I v : Set (CommonPrimeCompletion v)) ∧
        x ∉ padicIntegralLogShellLattice I v :=
  exists_padicSpan_not_mem_padicIntegralLogShellLattice I v

/-! ## 5. The Ind3 stage attached to the integral carriers

S1266's stage data and stage poly-isomorphism are indexed by the source place
type V; the carriers are indexed by the actual places.  The bundles below
record both pieces with exact projections and do not assert a compatibility
between them.  The stage's own compatibility (the action law) is S1266's actual
sourceInd3StageData. -/

/-- The integral Ind3 datum at the actual places: the integral log-shell carrier
over Z, S1266's actual times-mu stage data, and the actual stage
poly-isomorphism to the core stage 0. -/
structure IntegralInd3StageDatum (n : Int) (j : Nat) where
  /-- The actual integral log-shell carrier over the actual places. -/
  logShell :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := IntegralPlaceTotal I) (R := ℤ) j
  /-- The actual times-mu stage data at every source place. -/
  stageData : ∀ v : V, SourceInd3StageData I n v
  /-- The actual full poly-isomorphism from stage m to the core stage 0. -/
  stagePolyIso : ∀ m : Int,
    SourceFTimesMuPrimeStripEquivalence (ind3TimesMuStrip I n m)
      (ind3TimesMuStrip I n 0)

/-- The actual integral Ind3 stage datum, assembled from S1313's integral
carrier and S1266's actual stage data and stage poly-isomorphism. -/
noncomputable def integralInd3StageDatum (n : Int) (j : Nat) :
    IntegralInd3StageDatum I n j where
  logShell := integralInd3LogShellCarrier I j
  stageData v := sourceInd3StageData I n v
  stagePolyIso m := ind3StagePolyIso I n m

@[simp] theorem integralInd3StageDatum_logShell (n : Int) (j : Nat) :
    (integralInd3StageDatum I n j).logShell =
      integralInd3LogShellCarrier I j := rfl

@[simp] theorem integralInd3StageDatum_logShell_shell
    (n : Int) (j : Nat) (i : Capsule j) (x : IntegralPlaceTotal I) :
    (integralInd3StageDatum I n j).logShell.shell i x =
      integralShell I x.1 x.2 := rfl

@[simp] theorem integralInd3StageDatum_stageData (n : Int) (j : Nat) (v : V) :
    (integralInd3StageDatum I n j).stageData v =
      sourceInd3StageData I n v := rfl

@[simp] theorem integralInd3StageDatum_stagePolyIso (n : Int) (j : Nat) (m : Int) :
    (integralInd3StageDatum I n j).stagePolyIso m =
      ind3StagePolyIso I n m := rfl

/-- The attached stage comparison is S1266's actual stage comparison. -/
@[simp] theorem integralInd3StageDatum_stageCompare
    (n : Int) (j : Nat) (v : V) (m : Int) :
    ((integralInd3StageDatum I n j).stageData v).compare m =
      ind3StageComparison I n m v := rfl

/-- The attached stage action is S1266's actual times-mu action. -/
@[simp] theorem integralInd3StageDatum_stageAction
    (n : Int) (j : Nat) (v : V) (m : Int) :
    ((integralInd3StageDatum I n j).stageData v).action m =
      ind3StageAction I n m v := rfl

/-- The Z_[l]-lattice Ind3 datum at the l-adic places. -/
structure PadicInd3StageDatum (n : Int) (j : Nat) where
  /-- The actual Z_[l]-lattice carrier. -/
  logShell :
    Ind3LogShellCarrier.{max 0 ua, 0, ua} (V := PadicPlaceTotal I)
      (R := ℤ_[l.value]) j
  /-- The actual times-mu stage data at every source place. -/
  stageData : ∀ v : V, SourceInd3StageData I n v
  /-- The actual full poly-isomorphism from stage m to the core stage 0. -/
  stagePolyIso : ∀ m : Int,
    SourceFTimesMuPrimeStripEquivalence (ind3TimesMuStrip I n m)
      (ind3TimesMuStrip I n 0)

/-- The actual Z_[l]-lattice Ind3 stage datum. -/
noncomputable def padicInd3StageDatum (n : Int) (j : Nat) :
    PadicInd3StageDatum I n j where
  logShell := padicInd3LogShellCarrier I j
  stageData v := sourceInd3StageData I n v
  stagePolyIso m := ind3StagePolyIso I n m

@[simp] theorem padicInd3StageDatum_logShell (n : Int) (j : Nat) :
    (padicInd3StageDatum I n j).logShell =
      padicInd3LogShellCarrier I j := rfl

@[simp] theorem padicInd3StageDatum_stageData (n : Int) (j : Nat) (v : V) :
    (padicInd3StageDatum I n j).stageData v =
      sourceInd3StageData I n v := rfl

@[simp] theorem padicInd3StageDatum_stagePolyIso (n : Int) (j : Nat) (m : Int) :
    (padicInd3StageDatum I n j).stagePolyIso m =
      ind3StagePolyIso I n m := rfl

/-! ## 6. Exact first field at the ambient source place type V

S1266's carrier is indexed by the source place type V of OriginalInput.  V is
an arbitrary type and is not identified with the actual finite places in the
source data.  Hence filling the first field on V requires the exact place
comparison below.  No inhabitant is constructed or asserted, and no arbitrary
constant place map is used. -/

/-- The place comparison from the source place type to the actual places of
S1313.  This is the exact first field needed to make the carrier live on the
same place index as S1266's Ind3 stage and poly-isomorphism. -/
abbrev IntegralInd3PlaceComparison : Type (max uv (max 0 ua)) :=
  V → IntegralPlaceTotal I

/-- The exact first field, as a proposition.  No inhabitant is constructed or
asserted in this file. -/
def IntegralInd3PlaceComparisonRequired : Prop :=
  Nonempty (IntegralInd3PlaceComparison I)

/-- Conditional V-indexed integral carrier: fill the first field with S1313's
actual integral log-shell family along a place comparison. -/
noncomputable def integralInd3LogShellCarrierOfMap (j : Nat)
    (p : IntegralInd3PlaceComparison I) :
    Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℤ) j where
  shell i v := integralShell I (p v).1 (p v).2
  addCommMonoid i v := inferInstance
  module i v := inferInstance

/-- The conditional carrier's first field is the actual integral log-shell
composed with the place comparison. -/
theorem integralInd3LogShellCarrierOfMap_shell (j : Nat)
    (p : IntegralInd3PlaceComparison I) (i : Capsule j) (v : V) :
    (integralInd3LogShellCarrierOfMap I j p).shell i v =
      integralShell I (p v).1 (p v).2 := rfl

/-- Conditional closure of S1266's open carrier requirement at the source place
type V, from the exact place comparison. -/
theorem ind3LogShellCarrierRequired_of_integralPlaceMap (j : Nat)
    (p : IntegralInd3PlaceComparison I) :
    Ind3LogShellCarrierRequired.{uv, 0, ua} (V := V) (R := ℤ) j :=
  ⟨integralInd3LogShellCarrierOfMap I j p⟩

/-- Conditional V-indexed integral Ind3 stage datum: all three pieces live on
V, with the log-shell carrier filled from S1313 along the exact place
comparison p. -/
structure IntegralInd3StageDatumAtV (p : IntegralInd3PlaceComparison I)
    (n : Int) (j : Nat) where
  /-- The V-indexed integral log-shell carrier. -/
  logShell : Ind3LogShellCarrier.{uv, 0, ua} (V := V) (R := ℤ) j
  /-- Exactness of the first field: it is the carrier built from p. -/
  logShell_eq : logShell = integralInd3LogShellCarrierOfMap I j p
  /-- The actual times-mu stage data at every source place. -/
  stageData : ∀ v : V, SourceInd3StageData I n v
  /-- The actual full poly-isomorphism from stage m to the core stage 0. -/
  stagePolyIso : ∀ m : Int,
    SourceFTimesMuPrimeStripEquivalence (ind3TimesMuStrip I n m)
      (ind3TimesMuStrip I n 0)

/-- The conditional V-indexed integral Ind3 stage datum. -/
noncomputable def integralInd3StageDatumAtV
    (p : IntegralInd3PlaceComparison I) (n : Int) (j : Nat) :
    IntegralInd3StageDatumAtV I p n j where
  logShell := integralInd3LogShellCarrierOfMap I j p
  logShell_eq := rfl
  stageData v := sourceInd3StageData I n v
  stagePolyIso m := ind3StagePolyIso I n m

@[simp] theorem integralInd3StageDatumAtV_logShell
    (p : IntegralInd3PlaceComparison I) (n : Int) (j : Nat) :
    (integralInd3StageDatumAtV I p n j).logShell =
      integralInd3LogShellCarrierOfMap I j p := rfl

/-- The conditional datum's first field is exactly the actual integral
log-shell along p. -/
@[simp] theorem integralInd3StageDatumAtV_logShell_shell
    (p : IntegralInd3PlaceComparison I) (n : Int) (j : Nat)
    (i : Capsule j) (v : V) :
    (integralInd3StageDatumAtV I p n j).logShell.shell i v =
      integralShell I (p v).1 (p v).2 := rfl

@[simp] theorem integralInd3StageDatumAtV_stageData
    (p : IntegralInd3PlaceComparison I) (n : Int) (j : Nat) (v : V) :
    (integralInd3StageDatumAtV I p n j).stageData v =
      sourceInd3StageData I n v := rfl

@[simp] theorem integralInd3StageDatumAtV_stagePolyIso
    (p : IntegralInd3PlaceComparison I) (n : Int) (j : Nat) (m : Int) :
    (integralInd3StageDatumAtV I p n j).stagePolyIso m =
      ind3StagePolyIso I n m := rfl

/-! ## 7. Poly-isomorphism, tensor packet and nondegeneracy -/

/-- The actual poly-isomorphism of the integral family: reverse the capsule
labels and act by the identity on the integral shells. -/
noncomputable def integralInd3PolyIso (j : Nat) :
    PolyIsoAction (integralInd3LogShellFamily I j) :=
  integralLogShellPolyIso I j

/-- The label permutation of the integral action is the reversal. -/
theorem integralInd3PolyIso_labelPerm (j : Nat) :
    (integralInd3PolyIso I j).labelPerm = Fin.revPerm := rfl

/-- The integral poly-isomorphism is not the identity action. -/
theorem integralInd3PolyIso_ne_refl :
    integralInd3PolyIso I 1 ≠
      PolyIsoAction.refl (integralInd3LogShellFamily I 1) := by
  change integralLogShellPolyIso I 1 ≠
    PolyIsoAction.refl (integralLogShellFamily I 1)
  exact actualIntegralLogShellPolyIso_ne_refl I

/-- The tensor packet of the integral family is exactly the contract's tensor
packet. -/
theorem integralInd3LogShellFamily_tensorPacket
    (j : Fin (capsuleLevels l)) (vQ : ActualIntegralValuation) :
    TensorPacket (integralInd3LogShellFamily I j.val) vQ =
      SourceProcessionCapsuleContract.tensorPacket ℤ
        (actualIntegralCapsuleContract I) j vQ := rfl

/-- The tensor packet of the Z_[l] family is exactly the Z_[l] contract's
tensor packet. -/
theorem padicInd3LogShellFamily_tensorPacket
    (j : Fin (capsuleLevels l)) (vQ : RationalPlaceAt l) :
    TensorPacket (padicInd3LogShellFamily I j.val) vQ =
      SourceProcessionCapsuleContract.tensorPacket ℤ_[l.value]
        (actualPadicLatticeCapsuleContract I) j vQ := rfl

/-- The rational valuation type is not a one-point index. -/
theorem integralValuation_nontrivial : Nontrivial ActualIntegralValuation :=
  actualIntegralValuation_nontrivial

/-- The total actual place type is nonempty: the actual finite-place fiber over
the rational prime 5 is nonempty. -/
theorem integralPlaceTotal_five_nonempty : Nonempty (IntegralPlaceTotal I) := by
  obtain ⟨v⟩ := actualIntegralPlace_five_nonempty I
  exact ⟨⟨⟨5, by norm_num⟩, v⟩⟩

/-! ## 8. Axiom probes -/

#print axioms integralInd3LogShellCarrier
#print axioms integralInd3LogShellCarrier_shell_eq_contract
#print axioms integralInd3LogShellCarrier_shell_eq_integralLogShellFamily
#print axioms integralInd3LogShellCarrierRequired_actual
#print axioms integralInd3LogShellFamily_eq_contract_logShell
#print axioms toLogShellFamilyOfCarrier_eq_s1266
#print axioms one_mem_integralShell
#print axioms integralShell_nontrivial
#print axioms integralShell_eq_range
#print axioms integralShell_set_eq_sourceLocalLogShellDatum
#print axioms integralShell_not_smul_inv_closed
#print axioms integralShell_not_rat_smul_closed
#print axioms integralShell_span_padic_eq_top
#print axioms exists_padicSpan_not_mem_integralShell
#print axioms padicInd3LogShellCarrier
#print axioms padicInd3LogShellCarrier_shell_eq_padicLatticeLogShellFamily
#print axioms padicInd3LogShellFamily_eq_contract_logShell
#print axioms padicShell_nontrivial
#print axioms padicShell_free
#print axioms padicShell_finite
#print axioms padicShell_finrank
#print axioms padicShell_not_smul_inv_closed
#print axioms integralInd3StageDatum
#print axioms integralInd3PolyIso_ne_refl
#print axioms integralInd3LogShellFamily_tensorPacket
#print axioms padicInd3LogShellFamily_tensorPacket
#print axioms integralInd3LogShellCarrierOfMap
#print axioms ind3LogShellCarrierRequired_of_integralPlaceMap
#print axioms integralPlaceTotal_five_nonempty

end LeanFormal.IUT.XiFPaper.S1327Ind3IntegralLogShellActual

namespace LeanFormal.IUT.Audit

/-- Status record for the S1327 integral Ind3 log-shell carrier and stage. -/
def s1327Ind3IntegralLogShellActual : Obligation :=
  { id := "IUT-III.Ind3.integral-log-shell-carrier-actual"
    source :=
      "IUT III, Theorem 3.11, (ii), (Ind3); Proposition 3.5, (ii), (a), (b); " ++
        "IUT III, Definition 1.1, (i); IUT II, Definition 4.9, (i)"
    status := VerificationStatus.sourceProjection
    note :=
      "Fills S1266's Ind3LogShellCarrier first field with S1313's actual " ++
        "integral log-shell: the Z-module carrier actualIntegralLogShell at " ++
        "every capsule label, rational valuation and actual finite place " ++
        "(shell = ((actualIntegralCapsuleContract I).logShell j).Shell i vQ v, " ++
        "rfl), and the Z_[l]-lattice carrier padicIntegralLogShellLattice at " ++
        "the arithmetic prime l (shell = " ++
        "((actualPadicLatticeCapsuleContract I).logShell j).Shell i vQ v, rfl). " ++
        "No IQSpan, Q-span, PUnit or arbitrary module. The shells are proved " ++
        "to contain 1, nontrivial, equal to the actual range of the unit " ++
        "logarithm, not the whole local field, not closed under p^{-1} or " ++
        "rational scalars (hence not a Q_p/Q-vector space), and the " ++
        "Z_[l]-lattice is free of finite rank. S1266's actual times-mu stage " ++
        "data and stage poly-isomorphism are attached. At the ambient source " ++
        "place type V the first field is conditional on the exact place " ++
        "comparison IntegralInd3PlaceComparison (V -> (vQ, v)); no inhabitant " ++
        "of that comparison is asserted and no constant place map is used."
    dependsOn :=
      [ "IUT-III.Ind3.times-mu-stage-actual"
      , "IUT-III.integral-log-shell-contract-actual"
      , "IUT-III.integral-log-shell-lattice" ] }

end LeanFormal.IUT.Audit
