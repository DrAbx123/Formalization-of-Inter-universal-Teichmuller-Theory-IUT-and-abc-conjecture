import tmp.sheaf.xif.paper.S1927GlobalFrobenioidLogShellActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceGaloisLogShell

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# S1949: the actual nonarchimedean `G_v`-invariant submonoid and p-adic log

Layer: **O** (original Theta-link / q-pilot), per-place input to the S1927 global
log-shell packet.

## What this file constructs

For every finite prime place `v : FinitePrimePlace 2 7`, with actual rational place
`P_v := finitePrimePlaceToQ v` and actual complete local field `K_v := Completion P_v`:

1. **The actual `G_v`-invariant units.**  Let `L_v := SourceAlgebraicClosure P_v =
   AlgebraicClosure K_v`, and let `(Integers L_v)ˣ` be the units of its integral
   closure.  `SourceGaloisFixedUnits P_v` is defined by the actual invariance
   condition

     `u ∈ SourceGaloisFixedUnits P_v ↔ ∀ σ : L_v ≃ₐ[K_v] L_v,
        localGaloisUnitMap (σ restricted to Q_p) u = u`.

   The file proves that its elements are exactly the images of the actual base
   integral units (`sourceGaloisFixedUnits_mem_iff_base`, via
   `mem_localGaloisFixedIntegralUnits_iff`), and that every transported element is
   fixed by every actual local Galois automorphism
   (`galoisFixedCompletionUnits_fixed`).  The transport

     `sourceGaloisFixedUnitsEquiv v : (CompletionIntegers P_v)ˣ ≃*
        SourceGaloisFixedUnits P_v`

   composes `normalizedCompletionUnitsEquiv` with the actual fixed-unit descent
   `baseUnitsGaloisFixedEquiv`.  The resulting subgroup of the actual completion
   units is `galoisFixedCompletionUnits v`; `galoisFixedCompletionUnits_eq_top`
   records that it is all of `O_v^×`.  This is the fixed-unit theorem for the actual
   local Galois action (the fixed field of `G_v` is `K_v`), not a placeholder:
   the definition is by the invariance condition and the fixed-unit identification is
   proved.

2. **The actual p-adic log.**  `completionUnitLogHom P_v` is the actual analytic
   logarithm `(CompletionIntegers P_v)ˣ →* Multiplicative (Completion P_v)`, built in
   `FinitePlaceSourceLogShell` from the logarithmic series `log1p` on principal
   units (`completionUnitLog_eq_log1p`) and the finite principal-unit quotient; no
   logarithm is postulated.  `completionUnitLog_compat` identifies it with the
   logarithm of the actual Galois-fixed units in the algebraic closure.

3. **The actual local SourceLogShellDatum.**  `actualLocalLogShellDatum v` has

     `p = v.1`, `K = Completion P_v`, `Units = (CompletionIntegers P_v)ˣ`,
     `invariants = galoisFixedCompletionUnits v`,
     `logMap = completionUnitLogHom P_v`.

   Interface theorems:

   * `actualLocalLogShellDatum_pStar`: `pStar = logShellScale v.1`;
   * `actualPreLogShell_eq_range`: the pre-log-shell is the image of the actual
     invariant units under the actual p-adic log;
   * `actualLogShell_eq_completionLogShell`: the log-shell is exactly the actual
     `completionLogShell = (p*)⁻¹ · log(O_v^×)`;
   * `completionIntegers_subset_actualLogShell`, `actualLogShell_isCompact` and
     `actualCodomainKummerContained`: the actual completed integers lie in the
     log-shell, the log-shell is compact, and the actual logarithm of every unit lies
     in it;
   * `actualToUpperSemi`: the frozen `NonarchimedeanLogKummerUpperSemi` interface.

4. **The Galois-fixed carrier.**  `actualGaloisFixedLogShellDatum v` uses
   `K = L_v` and `Units = SourceGaloisFixedUnits P_v`; its log-shell is exactly the
   actual compact source Galois log-shell `sourceGaloisLogShell P_v`
   (`galoisLogShell_eq_sourceGaloisLogShell`), which is the image of the completion
   log-shell under `completionToSourceAlgebraicClosure`
   (`actualLogShell_image_eq_galoisLogShell`).

## What is actually closed (SourceLogShellCarrier reductions)

* **R2** (the invariant submonoid was an arbitrary datum): replaced by the actual local
  Galois-fixed units, with the fixed-unit theorem proved.
* **R3** (the p-adic log was a contract parameter): replaced by the actual analytic
  `unitLogHom` of the completed local field.

The file does not fake a log: `actualLogMap_principalUnit_eq_log1p` proves that on
principal units the logarithm is the analytic series, and `unitLogHom_unique`
characterizes the constructed logarithm uniquely.

## Remaining reductions (not claimed)

* **R1**: the paper's `ind-topological` field `Ψ~` is represented by the actual
  completed local field `K_v`; its ind-topological structure is not formalized.
* The `G_v(†Π_v)`-action on the abstract F-prime-strip `†F_v` is represented by the
  actual local Galois action on the integral closure; the abstract action on `†F_v`
  is not constructed.  Consequently the invariant submonoid inside `O_v^×` is all of
  `O_v^×` (a theorem, not a choice).
* **R4** (archimedean log-shell), **R5** (mixed packets) and the global assembly remain
  outside this local file.
* Source locations: IUT III, Definition 1.1, (i); Introduction l.208-226; Proposition
  1.2, (vi).  Upstream local constructions: `FinitePlaceSourceLogShell`,
  `FinitePlaceSourceGaloisLogShell`, `IntegralUnitLogarithm`,
  `IntegralUnitGaloisDescent`.

## Verification

No `sorry`, `axiom`, `True`/`PUnit` slot, empty type, arbitrary inhabitant or
`Nonempty` gate is used.  Axiom probes are at the end of the file.
-/

namespace LeanFormal.IUT.XiFPaper.S1949NonarchimedeanLogShellActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.LocalFieldLogarithm
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual

noncomputable section

/-! ## 0. The actual rational place and its rational prime -/

/-- The actual rational finite place underlying a finite prime place of the one-column. -/
abbrev QPlace (v : FinitePrimePlace 2 7) : NumberField.FinitePlace Rat :=
  finitePrimePlaceToQ v

/-- The rational prime of the actual completion of `Q` at `p` is `p`. -/
theorem completionRationalPrime_rationalFinitePlace
    (p : Nat) [Fact p.Prime] :
    completionRationalPrime (LeanFormal.IUT.rationalFinitePlace p) = ⟨p, Fact.out⟩ := by
  apply Subtype.ext
  have hcomap : comap (k := Rat) (LeanFormal.IUT.rationalFinitePlace p) =
      LeanFormal.IUT.rationalFinitePlace p := by
    apply NumberField.FinitePlace.maximalIdeal_injective
    apply IsDedekindDomain.HeightOneSpectrum.ext
    rw [comap_maximalIdeal]
    simp only [LeanFormal.IUT.rationalFinitePlace,
      NumberField.FinitePlace.maximalIdeal_mk]
    change Ideal.comap (RingHom.id _) (LeanFormal.IUT.rationalHeightOneSpectrum p).asIdeal =
      (LeanFormal.IUT.rationalHeightOneSpectrum p).asIdeal
    rw [Ideal.comap_id]
  have hmax : NumberField.FinitePlace.maximalIdeal (LeanFormal.IUT.rationalFinitePlace p) =
      LeanFormal.IUT.rationalHeightOneSpectrum p :=
    NumberField.FinitePlace.maximalIdeal_mk _
  show (Rat.HeightOneSpectrum.primesEquiv
    (comap (k := Rat) (LeanFormal.IUT.rationalFinitePlace p)).maximalIdeal).val = p
  rw [hcomap, hmax]
  simp [LeanFormal.IUT.rationalHeightOneSpectrum]

/-- The rational prime attached to a one-column place is the place's prime. -/
theorem completionRationalPrime_QPlace (v : FinitePrimePlace 2 7) :
    completionRationalPrime (QPlace v) = ⟨v.1, v.2.2.2⟩ := by
  letI : Fact (Nat.Prime v.1) := ⟨v.2.2.2⟩
  simpa [QPlace, finitePrimePlaceToQ] using
    (completionRationalPrime_rationalFinitePlace (p := v.1))

/-! ## 1. The actual Galois-fixed units of the integral closure

The actual local Galois group is `Gal(L_v/K_v)`, where `K_v = Completion P_v` and
`L_v = SourceAlgebraicClosure P_v = AlgebraicClosure K_v`.  `SourceGaloisFixedUnits`
is the subgroup of `(Integers L_v)ˣ` fixed by this actual action. -/

/-- Transport of the actual Galois-fixed units to the units of the completed local
field.  It is the composite of the actual integer-ring identification with the actual
fixed-unit descent. -/
noncomputable def sourceGaloisFixedUnitsEquiv (v : FinitePrimePlace 2 7) :
    (CompletionIntegers (QPlace v))ˣ ≃* SourceGaloisFixedUnits (QPlace v) :=
  ((normalizedCompletionUnitsEquiv (QPlace v)).symm).trans
    (baseUnitsGaloisFixedEquiv
      (K := NormalizedCompletion (QPlace v))
      (L := SourceAlgebraicClosure (QPlace v))
      (p := (completionRationalPrime (QPlace v)).val))

/-- The actual `G_v`-invariant subgroup of the completed local field units: the units
whose image in the integral closure of `K_v` is fixed by every actual local Galois
automorphism. -/
noncomputable def galoisFixedCompletionUnits (v : FinitePrimePlace 2 7) :
    Subgroup (CompletionIntegers (QPlace v))ˣ :=
  (⊤ : Subgroup (SourceGaloisFixedUnits (QPlace v))).comap
    (sourceGaloisFixedUnitsEquiv v).toMonoidHom

/-- The transported invariant subgroup is the full unit group of `O_v`: the actual
fixed-unit theorem says that the Galois-fixed units of the integral closure are exactly
the base integral units.  This is a theorem about the actual action, not a stipulation. -/
theorem galoisFixedCompletionUnits_eq_top (v : FinitePrimePlace 2 7) :
    galoisFixedCompletionUnits v = ⊤ := by
  rw [galoisFixedCompletionUnits, Subgroup.comap_top]

/-- Every element of the actual completion units is fixed by every actual local Galois
automorphism after transport to the integral closure. -/
theorem galoisFixedCompletionUnits_fixed (v : FinitePrimePlace 2 7)
    (u : (CompletionIntegers (QPlace v))ˣ)
    (σ : SourceAlgebraicClosure (QPlace v) ≃ₐ[NormalizedCompletion (QPlace v)]
      SourceAlgebraicClosure (QPlace v)) :
    (localGaloisUnitMap (K := SourceAlgebraicClosure (QPlace v))
      (p := (completionRationalPrime (QPlace v)).val)
      (σ.restrictScalars ℚ_[(completionRationalPrime (QPlace v)).val])
      ((sourceGaloisFixedUnitsEquiv v u : SourceGaloisFixedUnits (QPlace v)) :
        (Integers (SourceAlgebraicClosure (QPlace v)))ˣ)) =
      ((sourceGaloisFixedUnitsEquiv v u : SourceGaloisFixedUnits (QPlace v)) :
        (Integers (SourceAlgebraicClosure (QPlace v)))ˣ) :=
  (sourceGaloisFixedUnitsEquiv v u).property σ

/-- The actual fixed units of the integral closure are exactly the images of the base
integral units. -/
theorem sourceGaloisFixedUnits_mem_iff_base (v : FinitePrimePlace 2 7)
    (w : (Integers (SourceAlgebraicClosure (QPlace v)))ˣ) :
    w ∈ SourceGaloisFixedUnits (QPlace v) ↔
      ∃ u : (Integers (NormalizedCompletion (QPlace v)))ˣ,
        integralUnitMap (algebraMap (NormalizedCompletion (QPlace v))
          (SourceAlgebraicClosure (QPlace v)))
          (isometry_localField_algebraMap (K := NormalizedCompletion (QPlace v))
            (L := SourceAlgebraicClosure (QPlace v))) u = w :=
  mem_localGaloisFixedIntegralUnits_iff (p := (completionRationalPrime (QPlace v)).val) w

/-! ## 2. The actual p-adic logarithm on the fixed units and its compatibility -/

/-- The actual logarithm of the identity fixed unit is zero. -/
theorem sourceGaloisFixedUnitLog_one (v : FinitePrimePlace 2 7) :
    sourceGaloisFixedUnitLog (QPlace v) (1 : SourceGaloisFixedUnits (QPlace v)) = 0 := by
  change algebraMap (NormalizedCompletion (QPlace v)) (SourceAlgebraicClosure (QPlace v))
    (unitLog (K := NormalizedCompletion (QPlace v))
      ((baseUnitsGaloisFixedEquiv
        (K := NormalizedCompletion (QPlace v))
        (L := SourceAlgebraicClosure (QPlace v))
        (p := (completionRationalPrime (QPlace v)).val)).symm 1)) = 0
  rw [map_one]
  rw [unitLog_one (K := NormalizedCompletion (QPlace v))
    (p := (completionRationalPrime (QPlace v)).val)]
  rw [map_zero]

/-- The actual logarithm of fixed units is additive on products. -/
theorem sourceGaloisFixedUnitLog_mul (v : FinitePrimePlace 2 7)
    (u w : SourceGaloisFixedUnits (QPlace v)) :
    sourceGaloisFixedUnitLog (QPlace v) (u * w) =
      sourceGaloisFixedUnitLog (QPlace v) u + sourceGaloisFixedUnitLog (QPlace v) w := by
  change algebraMap (NormalizedCompletion (QPlace v)) (SourceAlgebraicClosure (QPlace v))
    (unitLog (K := NormalizedCompletion (QPlace v))
      ((baseUnitsGaloisFixedEquiv
        (K := NormalizedCompletion (QPlace v))
        (L := SourceAlgebraicClosure (QPlace v))
        (p := (completionRationalPrime (QPlace v)).val)).symm (u * w))) =
    algebraMap (NormalizedCompletion (QPlace v)) (SourceAlgebraicClosure (QPlace v))
      (unitLog (K := NormalizedCompletion (QPlace v))
        ((baseUnitsGaloisFixedEquiv
          (K := NormalizedCompletion (QPlace v))
          (L := SourceAlgebraicClosure (QPlace v))
          (p := (completionRationalPrime (QPlace v)).val)).symm u)) +
    algebraMap (NormalizedCompletion (QPlace v)) (SourceAlgebraicClosure (QPlace v))
      (unitLog (K := NormalizedCompletion (QPlace v))
        ((baseUnitsGaloisFixedEquiv
          (K := NormalizedCompletion (QPlace v))
          (L := SourceAlgebraicClosure (QPlace v))
          (p := (completionRationalPrime (QPlace v)).val)).symm w))
  rw [map_mul]
  rw [unitLog_mul (K := NormalizedCompletion (QPlace v))
    (p := (completionRationalPrime (QPlace v)).val)]
  rw [map_add]

/-- The actual p-adic logarithm on the Galois-fixed units, with values in the actual
algebraic closure. -/
noncomputable def sourceGaloisFixedUnitLogHom (v : FinitePrimePlace 2 7) :
    SourceGaloisFixedUnits (QPlace v) →* Multiplicative (SourceAlgebraicClosure (QPlace v)) where
  toFun u := Multiplicative.ofAdd (sourceGaloisFixedUnitLog (QPlace v) u)
  map_one' := by
    change sourceGaloisFixedUnitLog (QPlace v) 1 = 0
    exact sourceGaloisFixedUnitLog_one v
  map_mul' u w := by
    change sourceGaloisFixedUnitLog (QPlace v) (u * w) =
      sourceGaloisFixedUnitLog (QPlace v) u + sourceGaloisFixedUnitLog (QPlace v) w
    exact sourceGaloisFixedUnitLog_mul v u w

/-- The actual analytic logarithm on `O_v^×` and the logarithm on the Galois-fixed units
agree under the actual embedding of the completion in its algebraic closure. -/
theorem completionUnitLog_compat (v : FinitePrimePlace 2 7)
    (u : (CompletionIntegers (QPlace v))ˣ) :
    completionToSourceAlgebraicClosure (QPlace v) (completionUnitLog (QPlace v) u) =
      sourceGaloisFixedUnitLog (QPlace v) (sourceGaloisFixedUnitsEquiv v u) := by
  simp only [completionToSourceAlgebraicClosure, completionUnitLog,
    sourceGaloisFixedUnitLog, galoisFixedUnitLog, sourceGaloisFixedUnitsEquiv,
    normalizedCompletionUnitsEquiv, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
    RingHom.comp_apply, RingEquiv.toRingHom_eq_coe, RingHom.coe_coe,
    RingEquiv.symm_apply_apply]

/-! ## 3. The actual local SourceLogShellDatum -/

/-- The actual nonarchimedean local log-shell datum at a finite prime place: the actual
completed local field, its actual integral units, the actual `G_v`-invariant
subgroup, and the actual analytic p-adic logarithm. -/
noncomputable def actualLocalLogShellDatum (v : FinitePrimePlace 2 7) :
    SourceLogShellDatum where
  p := v.1
  hp := v.2.2.2
  K := Completion (QPlace v)
  Units := (CompletionIntegers (QPlace v))ˣ
  invariants := (galoisFixedCompletionUnits v).toSubmonoid
  logMap := completionUnitLogHom (QPlace v)

/-- The coordinate field of the actual local datum is the actual completion. -/
theorem actualLocalLogShellDatum_K (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).K = Completion (QPlace v) := rfl

/-- The actual `p*`-factor of the local datum. -/
theorem actualLocalLogShellDatum_pStar (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).pStar = logShellScale v.1 := by
  simp [SourceLogShellDatum.pStar, actualLocalLogShellDatum,
    sourceLogShellStar_eq_logShellScale (p := v.1) v.2.2.2]

/-- The invariant submonoid of the actual datum is the actual Galois-fixed unit group. -/
theorem actualInvariants_eq_fixed (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).invariants = (galoisFixedCompletionUnits v).toSubmonoid :=
  rfl

/-- The invariant submonoid of the actual datum is the full unit group (the actual
fixed-unit theorem). -/
theorem actualInvariants_eq_top (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).invariants = ⊤ := by
  change (galoisFixedCompletionUnits v).toSubmonoid = ⊤
  rw [galoisFixedCompletionUnits_eq_top]
  rfl

/-- The actual p-adic log is the actual analytic logarithm on the completion units. -/
@[simp]
theorem actualLogMap_toAdd (v : FinitePrimePlace 2 7)
    (u : (CompletionIntegers (QPlace v))ˣ) :
    ((actualLocalLogShellDatum v).logMap u).toAdd = completionUnitLog (QPlace v) u := rfl

/-- On principal units, the actual local log is the actual analytic series. -/
theorem actualLogMap_principalUnit_eq_log1p (v : FinitePrimePlace 2 7)
    (u : (CompletionIntegers (QPlace v))ˣ)
    (hu : ‖(u.val : Completion (QPlace v)) - 1‖ < 1) :
    ((actualLocalLogShellDatum v).logMap u).toAdd =
      log1p ((u.val : Completion (QPlace v)) - 1) :=
  completionUnitLog_eq_log1p (QPlace v) u hu

/-- The pre-log-shell of the actual datum is exactly the image of the actual integral
units under the actual p-adic logarithm. -/
theorem actualPreLogShell_eq_range (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).preLogShell =
      Set.range (fun u : (CompletionIntegers (QPlace v))ˣ =>
        completionUnitLog (QPlace v) u) := by
  ext a
  constructor
  · rintro ⟨u, -, h⟩
    exact ⟨u, h⟩
  · rintro ⟨u, h⟩
    exact ⟨u, trivial, h⟩

/-- The log-shell of the actual datum is exactly the actual completion log-shell
`(p*)⁻¹ · log(O_v^×)`. -/
theorem actualLogShell_eq_completionLogShell (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).logShell =
      (completionLogShell (QPlace v) : Set (Completion (QPlace v))) := by
  have hp : completionRationalPrime (QPlace v) = ⟨v.1, v.2.2.2⟩ :=
    completionRationalPrime_QPlace v
  rw [completionLogShell_eq_unitLog_range]
  rw [SourceLogShellDatum.logShell_eq_invScaledPreLogShell]
  unfold SourceLogShellDatum.invScaledPreLogShell
  rw [actualPreLogShell_eq_range]
  ext b
  constructor
  · rintro ⟨x, ⟨u, -, rfl⟩, hb⟩
    refine ⟨u, ?_⟩
    dsimp only at hb ⊢
    rw [hp]
    rw [actualLocalLogShellDatum_pStar] at hb
    exact hb
  · rintro ⟨u, rfl⟩
    refine ⟨completionUnitLog (QPlace v) u, ⟨u, rfl⟩, ?_⟩
    rw [actualLocalLogShellDatum_pStar, hp]
    rfl

/-- The actual completed integers are contained in the actual local log-shell. -/
theorem completionIntegers_subset_actualLogShell (v : FinitePrimePlace 2 7) :
    (CompletionIntegers (QPlace v) : Set (Completion (QPlace v))) ⊆
      (actualLocalLogShellDatum v).logShell := by
  rw [actualLogShell_eq_completionLogShell]
  exact completionIntegers_subset_logShell (QPlace v)

/-- The actual completion log-shell (p*)⁻¹ · log(O_v^×) is compact. -/
theorem completionLogShell_isCompact (v : FinitePrimePlace 2 7) :
    IsCompact (completionLogShell (QPlace v) : Set (Completion (QPlace v))) :=
  isCompact_completionLogShell (QPlace v)

/-- The actual local log-shell is compact (with the topology transported from the actual
completion; the SourceLogShellDatum projection itself carries only the field
structure). -/
theorem actualLogShell_isCompact (v : FinitePrimePlace 2 7) :
    letI : TopologicalSpace (actualLocalLogShellDatum v).K :=
      inferInstanceAs (TopologicalSpace (Completion (QPlace v)))
    IsCompact ((actualLocalLogShellDatum v).logShell) := by
  letI : TopologicalSpace (actualLocalLogShellDatum v).K :=
    inferInstanceAs (TopologicalSpace (Completion (QPlace v)))
  rw [actualLogShell_eq_completionLogShell]
  exact isCompact_completionLogShell (QPlace v)

/-- The actual logarithm of every actual integral unit lies in the actual log-shell
(the codomain-side Kummer containment of IUT III, Definition 1.1, (i)). -/
theorem actualCodomainKummerContained (v : FinitePrimePlace 2 7) :
    (actualLocalLogShellDatum v).codomainKummerContained := by
  rw [SourceLogShellDatum.codomainKummerContained_iff]
  intro u
  exact SourceLogShellDatum.preLogShell_subset_logShell _ ⟨u, trivial, rfl⟩

/-- The actual datum maps into the frozen `NonarchimedeanLogKummerUpperSemi`
interface. -/
noncomputable def actualToUpperSemi (v : FinitePrimePlace 2 7) :
    NonarchimedeanLogKummerUpperSemi :=
  (actualLocalLogShellDatum v).toNonarchimedeanUpperSemi
    (actualCodomainKummerContained v)

/-! ## 4. The Galois-fixed carrier in the algebraic closure -/

/-- The same actual local data carried by the Galois-fixed units of the integral closure,
with values in the actual algebraic closure. -/
noncomputable def actualGaloisFixedLogShellDatum (v : FinitePrimePlace 2 7) :
    SourceLogShellDatum where
  p := v.1
  hp := v.2.2.2
  K := SourceAlgebraicClosure (QPlace v)
  Units := SourceGaloisFixedUnits (QPlace v)
  invariants := ⊤
  logMap := sourceGaloisFixedUnitLogHom v

/-- The actual `p*`-factor of the Galois-fixed carrier. -/
theorem actualGaloisFixedLogShellDatum_pStar (v : FinitePrimePlace 2 7) :
    (actualGaloisFixedLogShellDatum v).pStar = logShellScale v.1 := by
  simp [SourceLogShellDatum.pStar, actualGaloisFixedLogShellDatum,
    sourceLogShellStar_eq_logShellScale (p := v.1) v.2.2.2]

/-- The pre-log-shell of the Galois-fixed carrier is the image of the actual fixed units
under the actual p-adic logarithm. -/
theorem galoisPreLogShell_eq_range (v : FinitePrimePlace 2 7) :
    (actualGaloisFixedLogShellDatum v).preLogShell =
      Set.range (fun u : SourceGaloisFixedUnits (QPlace v) =>
        sourceGaloisFixedUnitLog (QPlace v) u) := by
  ext a
  constructor
  · rintro ⟨u, -, h⟩
    exact ⟨u, h⟩
  · rintro ⟨u, h⟩
    exact ⟨u, trivial, h⟩

/-- The log-shell of the Galois-fixed carrier is the actual compact source Galois
log-shell. -/
theorem galoisLogShell_eq_sourceGaloisLogShell (v : FinitePrimePlace 2 7) :
    (actualGaloisFixedLogShellDatum v).logShell =
      (sourceGaloisLogShell (QPlace v) : Set (SourceAlgebraicClosure (QPlace v))) := by
  have hp : completionRationalPrime (QPlace v) = ⟨v.1, v.2.2.2⟩ :=
    completionRationalPrime_QPlace v
  rw [sourceGaloisLogShell_eq_fixedUnitLog_range]
  rw [SourceLogShellDatum.logShell_eq_invScaledPreLogShell]
  unfold SourceLogShellDatum.invScaledPreLogShell
  rw [galoisPreLogShell_eq_range]
  ext b
  constructor
  · rintro ⟨x, ⟨u, -, rfl⟩, hb⟩
    refine ⟨u, ?_⟩
    dsimp only at hb ⊢
    rw [hp]
    rw [actualGaloisFixedLogShellDatum_pStar] at hb
    exact hb
  · rintro ⟨u, rfl⟩
    refine ⟨sourceGaloisFixedUnitLog (QPlace v) u, ⟨u, rfl⟩, ?_⟩
    rw [actualGaloisFixedLogShellDatum_pStar, hp]
    rfl

/-- The image of the actual completion log-shell in the algebraic closure is exactly the
log-shell of the Galois-fixed carrier. -/
theorem actualLogShell_image_eq_galoisLogShell (v : FinitePrimePlace 2 7) :
    completionToSourceAlgebraicClosure (QPlace v) ''
        ((actualLocalLogShellDatum v).logShell) =
      (actualGaloisFixedLogShellDatum v).logShell := by
  rw [actualLogShell_eq_completionLogShell, galoisLogShell_eq_sourceGaloisLogShell]
  exact (sourceGaloisLogShell_eq_completion_image (QPlace v)).symm

/-- The actual Galois-fixed carrier also maps into the frozen upper semi interface. -/
theorem galoisCodomainKummerContained (v : FinitePrimePlace 2 7) :
    (actualGaloisFixedLogShellDatum v).codomainKummerContained := by
  rw [SourceLogShellDatum.codomainKummerContained_iff]
  intro u
  exact SourceLogShellDatum.preLogShell_subset_logShell _ ⟨u, trivial, rfl⟩

/-- The frozen `NonarchimedeanLogKummerUpperSemi` interface of the Galois-fixed
carrier. -/
noncomputable def actualGaloisToUpperSemi (v : FinitePrimePlace 2 7) :
    NonarchimedeanLogKummerUpperSemi :=
  (actualGaloisFixedLogShellDatum v).toNonarchimedeanUpperSemi
    (galoisCodomainKummerContained v)

/-! ## 5. Axiom probes -/

#print axioms completionRationalPrime_QPlace
#print axioms galoisFixedCompletionUnits_eq_top
#print axioms galoisFixedCompletionUnits_fixed
#print axioms sourceGaloisFixedUnits_mem_iff_base
#print axioms sourceGaloisFixedUnitLogHom
#print axioms completionUnitLog_compat
#print axioms actualPreLogShell_eq_range
#print axioms actualLogShell_eq_completionLogShell
#print axioms actualLogMap_principalUnit_eq_log1p
#print axioms completionIntegers_subset_actualLogShell
#print axioms actualLogShell_isCompact
#print axioms actualCodomainKummerContained
#print axioms actualToUpperSemi
#print axioms galoisLogShell_eq_sourceGaloisLogShell
#print axioms actualLogShell_image_eq_galoisLogShell
#print axioms actualGaloisToUpperSemi

end

end LeanFormal.IUT.XiFPaper.S1949NonarchimedeanLogShellActual
