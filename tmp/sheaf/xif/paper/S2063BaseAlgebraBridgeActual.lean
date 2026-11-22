/-
Copyright (c) 2026 IUT Lean formalization contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: IUT Lean formalization contributors
-/
import tmp.sheaf.xif.paper.S2047GaloisCompletionActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlacePadicScalarStructure

/-!
# S2063: actual Algebra-instance bridge for the S2047 base model

S2047 recorded three missing pieces around the actual one-column base field
`Base (QPlace v) = Completion (QPlace v)`:

* `S2047BaseModelEquivRequired : Base (QPlace v) ≃+* ℚ_[v.1]`;
* `S2047RationalCompletionModelEquiv :
    Completion (comap QPlace v) ≃A[ℚ] PadicScalarField (QPlace v)`;
* a term of `S2047GaloisEquivOfBaseData`.

The obstruction is an **instance** obstruction, not a mathematical one.
Typeclass search has two non-definitionally-equal candidates for the rational
algebra structure on the completion of `ℚ`:

* `IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion` (the structure
  used inside `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` and
  `rationalCompletionPadicEquiv`);
* `DivisionRing.toRatAlgebra` (the generic rational-cast structure, which is
  the one selected for `PadicScalarField` and, in this file's context, for the
  completion as well).

Both structures have the same algebra map (the rational cast).  In fact any two
`Algebra ℚ R` structures on a semiring are *equal* (`Rat.algebra_rat_subsingleton`),
although the equality is not definitional.  This file makes that bridge explicit:

1. `instAlgebraAdicCompletion_comap_eq_toRatAlgebra` states the exact instance
   equality for the S2047 domain.
2. `padicRingEquivAux` extracts the underlying `RingEquiv` of
   `Rat.HeightOneSpectrum.adicCompletion.padicEquiv` after transporting the
   `ContinuousAlgEquiv` across that instance equality.  No local instance is
   installed globally and no `Q_p` model is substituted.
3. `baseRingEquiv` composes this ring equivalence with two honest dependent
   transports: one along `underlyingPrime (QPlace v) = rationalHeightOneSpectrum v.1`,
   and one along `primesEquiv (rationalHeightOneSpectrum v.1) = ⟨v.1, v.prime⟩`.
4. `modelEquiv` inhabits `S2047RationalCompletionModelEquiv` by the same
   instance bridge.
5. `baseRingEquiv_ratCast` proves the `map_smul`/rational-scalar compatibility
   directly (`RingHom.map_rat_algebraMap`), and `baseAlgEquiv` upgrades
   `baseRingEquiv` to a `ℚ`-algebra equivalence via `AlgEquiv.ofRingEquiv`.
6. `galoisEquivOfBaseData` inhabits `S2047GaloisEquivOfBaseData`, using
   `IsAlgClosure.equivOfEquiv` for the ring equivalence of algebraic closures
   and its compatibility lemma for `closure_compat`.

All declarations below are proved; the only axioms used are `propext`,
`Classical.choice` and `Quot.sound`.
-/

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 2000000

namespace LeanFormal.IUT.XiFPaper.S2063BaseAlgebraBridgeActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.OneColumnFinitePrimePlaceActual
open LeanFormal.IUT.XiFPaper.S2047GaloisCompletionActual

variable (v : FinitePrimePlace 2 7)

local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-! ## The rational place and the two index equalities -/

/-- The canonical prime attached to the rational height-one spectrum at `v.1`
is `⟨v.1, v.prime⟩`. -/
theorem primesEquiv_rationalHeightOneSpectrum :
    Rat.HeightOneSpectrum.primesEquiv (LeanFormal.IUT.rationalHeightOneSpectrum v.1)
      = ⟨v.1, v.prime⟩ := by
  simp [LeanFormal.IUT.rationalHeightOneSpectrum]

/-- The underlying height-one prime of `QPlace v` is the rational height-one
spectrum at `v.1`.  This is the exact type-level identification of the S2047
base field with the rational adic completion. -/
theorem underlyingPrime_QPlace :
    NumberFieldFinitePlace.underlyingPrime (QPlace v)
      = LeanFormal.IUT.rationalHeightOneSpectrum v.1 := by
  rw [NumberFieldFinitePlace.underlyingPrime, QPlace, finitePrimePlaceToQ]
  exact NumberField.FinitePlace.maximalIdeal_mk _

/-! ## The exact instance bridge

The two `Algebra ℚ` structures on the completion occurring in S2047 are
propositionally equal.  This is the precise missing instance bridge; it is not
a definitional equality, which is why a direct `AlgEquiv`/`cast` of
`rationalCompletionPadicEquiv` fails. -/

/-- The `instAlgebraAdicCompletion` structure used by
`rationalCompletionPadicEquiv` on `Completion (comap (QPlace v))` equals the
generic rational-cast structure `DivisionRing.toRatAlgebra`.  The equality is
proved from `Rat.algebra_rat_subsingleton`; both structures have the rational
cast as algebra map. -/
theorem instAlgebraAdicCompletion_comap_eq_toRatAlgebra :
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        (NumberFieldFinitePlace.underlyingPrime
          (NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
      = DivisionRing.toRatAlgebra :=
  Subsingleton.elim _ _

/-- The same bridge, stated for the actual rational height-one spectrum.  This
is the form used in the construction of the explicit base ring equivalence. -/
theorem instAlgebraAdicCompletion_rational_eq_toRatAlgebra :
    IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        (LeanFormal.IUT.rationalHeightOneSpectrum v.1)
      = DivisionRing.toRatAlgebra :=
  Subsingleton.elim _ _
/-! ## Dependent transports of completions

We keep these elementary transport lemmas explicit instead of relying on
`RingEquiv.cast` with a noncanonical type family; after substituting the index
equality the two structures are definitionally the same and `RingEquiv.refl`
works. -/

/-- Transport the adic completion along an equality of height-one primes. -/
noncomputable def adicCompletionRingEquivOfEq
    {w₁ w₂ : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)}
    (h : w₁ = w₂) : w₁.adicCompletion ℚ ≃+* w₂.adicCompletion ℚ := by
  cases h
  exact RingEquiv.refl _

/-- Transport `ℚ_[n]` to `ℚ_[m]` along an equality of the underlying natural
numbers.  The `Fact` proofs are proof-irrelevant, so after `cases h` the two
types are definitionally equal. -/
noncomputable def padicRingEquivOfNatEq {n m : ℕ} (h : n = m)
    (hn : Fact (Nat.Prime n)) (hm : Fact (Nat.Prime m)) :
    @Padic n hn ≃+* @Padic m hm := by
  cases h
  exact RingEquiv.refl _

/-! ## The explicit ring equivalence `Base (QPlace v) ≃+* ℚ_[v.1]` -/

/-- The underlying `RingEquiv` of `Rat.HeightOneSpectrum.adicCompletion.padicEquiv`
after transporting the `ContinuousAlgEquiv` across the instance bridge
`instAlgebraAdicCompletion = DivisionRing.toRatAlgebra`.

The codomain is the p-adic field with the canonical proof of primality; the
`Fact` argument is irrelevant definitionally, which is why this is the exact
ring level statement needed for the S2047 base comparison. -/
noncomputable def padicRingEquivAux
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    w.adicCompletion ℚ ≃+*
      @Padic (Rat.HeightOneSpectrum.primesEquiv w).1
        ⟨(Rat.HeightOneSpectrum.primesEquiv w).2⟩ := by
  let e : @ContinuousAlgEquiv ℚ (w.adicCompletion ℚ)
      (@Padic (Rat.HeightOneSpectrum.primesEquiv w).1
        ⟨(Rat.HeightOneSpectrum.primesEquiv w).2⟩)
      _ _ _ _ _ DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra := by
    have h : IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
          (NumberField.RingOfIntegers ℚ) ℚ w = DivisionRing.toRatAlgebra :=
      Subsingleton.elim _ _
    exact h ▸ (Rat.HeightOneSpectrum.adicCompletion.padicEquiv w)
  letI : Algebra ℚ (w.adicCompletion ℚ) := DivisionRing.toRatAlgebra
  exact e.toAlgEquiv.toRingEquiv

/-- **Actual base model equivalence**: an explicit ring equivalence between the
actual one-column base completion and `ℚ_[v.1]`.

It is the composition of

* `underlyingPrime (QPlace v) = rationalHeightOneSpectrum v.1`;
* the underlying ring equivalence of `adicCompletion.padicEquiv` at the
  rational height-one spectrum, with the algebra-instance bridge made explicit;
* `primesEquiv (rationalHeightOneSpectrum v.1) = ⟨v.1, v.prime⟩`.

No instance is faked and no `Q_p` model is substituted. -/
noncomputable def baseRingEquiv :
    Iut.SourceFinitePlaceReconstruction.Base (QPlace v) ≃+* ℚ_[v.1] :=
  (adicCompletionRingEquivOfEq (underlyingPrime_QPlace (v := v))).trans <|
    (padicRingEquivAux (w := LeanFormal.IUT.rationalHeightOneSpectrum v.1)).trans <|
      (padicRingEquivOfNatEq
        (congrArg Subtype.val (primesEquiv_rationalHeightOneSpectrum (v := v)))
        ⟨(Rat.HeightOneSpectrum.primesEquiv
          (LeanFormal.IUT.rationalHeightOneSpectrum v.1)).2⟩
        ⟨v.prime⟩)

/-- `S2047BaseModelEquivRequired` is inhabited. -/
noncomputable def S2063BaseModelEquiv :
    S2047BaseModelEquivRequired (v := v) :=
  baseRingEquiv (v := v)

/-! ## The `ContinuousAlgEquiv` model comparison -/

/-- **Actual rational completion model equivalence**:
`Completion (comap (QPlace v)) ≃A[ℚ] PadicScalarField (QPlace v)`.

The `rationalCompletionPadicEquiv` of `FinitePlacePadicScalarStructure` is a
`ContinuousAlgEquiv` with the `instAlgebraAdicCompletion` structure on the
domain, while the S2047 type uses `DivisionRing.toRatAlgebra`.  We transport it
across the exact instance equality `instAlgebraAdicCompletion_comap_eq_toRatAlgebra`;
the rest of the structure (ring map, continuity, inverse) is unchanged. -/
noncomputable def modelEquiv :
    S2047RationalCompletionModelEquiv (v := v) := by
  let e := LeanFormal.IUT.NumberFieldFinitePlace.rationalCompletionPadicEquiv (QPlace v)
  have h : IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
        (NumberField.RingOfIntegers ℚ) ℚ
        (NumberFieldFinitePlace.underlyingPrime
          (NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
      = DivisionRing.toRatAlgebra :=
    instAlgebraAdicCompletion_comap_eq_toRatAlgebra (v := v)
  change @ContinuousAlgEquiv ℚ
    (NumberFieldFinitePlace.Completion (NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
    (NumberFieldFinitePlace.PadicScalarField (QPlace v))
    _ _ _ _ _ DivisionRing.toRatAlgebra DivisionRing.toRatAlgebra
  exact h ▸ e

/-- `S2047RationalCompletionModelEquiv` is inhabited. -/
noncomputable def S2063RationalCompletionModelEquiv :
    S2047RationalCompletionModelEquiv (v := v) :=
  modelEquiv (v := v)
/-! ## The rational-scalar (`map_smul`) bridge -/

/-- The explicit ring equivalence commutes with rational scalars, even though
the two `Algebra ℚ` structures are not definitionally equal.  This is the
`map_smul`/`commutes'` statement for the S2047 base comparison, proved by
`RingHom.map_rat_algebraMap` (every ring hom between `ℚ`-algebras respects the
rational cast). -/
theorem baseRingEquiv_ratCast (q : ℚ) :
    baseRingEquiv (v := v)
        (algebraMap ℚ (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) q) =
      algebraMap ℚ (ℚ_[v.1]) q :=
  RingHom.map_rat_algebraMap (baseRingEquiv (v := v)).toRingHom q

/-- The base ring equivalence upgraded to a `ℚ`-algebra equivalence using the
explicit `commutes'` proof `baseRingEquiv_ratCast`. -/
noncomputable def baseAlgEquiv :
    Iut.SourceFinitePlaceReconstruction.Base (QPlace v) ≃ₐ[ℚ] ℚ_[v.1] :=
  AlgEquiv.ofRingEquiv (baseRingEquiv_ratCast (v := v))

/-! ## `S2047GaloisEquivOfBaseData` -/

/-- **Actual `S2047GaloisEquivOfBaseData`**: the base ring equivalence, the
induced ring equivalence of algebraic closures (`IsAlgClosure.equivOfEquiv`),
and the compatibility of the closure equivalence with the algebra maps. -/
noncomputable def galoisEquivOfBaseData :
    S2047GaloisEquivOfBaseData (v := v) where
  baseEquiv := baseRingEquiv (v := v)
  closureEquiv := IsAlgClosure.equivOfEquiv
    (AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)))
    (AlgebraicClosure ℚ_[v.1]) (baseRingEquiv (v := v))
  closure_compat := by
    intro x
    exact IsAlgClosure.equivOfEquiv_algebraMap
      (AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)))
      (AlgebraicClosure ℚ_[v.1]) (baseRingEquiv (v := v)) x

/-- `S2047GaloisEquivOfBaseRequired` is inhabited. -/
noncomputable def S2063GaloisEquivOfBaseData :
    S2047GaloisEquivOfBaseRequired (v := v) :=
  galoisEquivOfBaseData (v := v)

/-! ## Checks and axiom audit -/

#check baseRingEquiv
#check modelEquiv
#check baseRingEquiv_ratCast
#check baseAlgEquiv
#check galoisEquivOfBaseData
#check S2063BaseModelEquiv
#check S2063RationalCompletionModelEquiv
#check S2063GaloisEquivOfBaseData

#print axioms primesEquiv_rationalHeightOneSpectrum
#print axioms underlyingPrime_QPlace
#print axioms instAlgebraAdicCompletion_comap_eq_toRatAlgebra
#print axioms instAlgebraAdicCompletion_rational_eq_toRatAlgebra
#print axioms adicCompletionRingEquivOfEq
#print axioms padicRingEquivOfNatEq
#print axioms padicRingEquivAux
#print axioms baseRingEquiv
#print axioms modelEquiv
#print axioms baseRingEquiv_ratCast
#print axioms baseAlgEquiv
#print axioms galoisEquivOfBaseData

end LeanFormal.IUT.XiFPaper.S2063BaseAlgebraBridgeActual

end
