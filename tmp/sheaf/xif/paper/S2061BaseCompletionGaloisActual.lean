import tmp.sheaf.xif.paper.S2047GaloisCompletionActual
import tmp.sheaf.xif.paper.S2046OperationComponentsActual

/-!
# S2061: actual base-completion and local absolute Galois bridge for S2047

S2047 recorded four exact missing objects:

* S2047BaseModelEquivRequired : Base (QPlace v) = Completion (QPlace v)
  is ring-equivalent to Q_[v.1];
* S2047RationalCompletionModelEquiv : the rational completion
  Completion (comap (k := Q) (QPlace v)) is continuously Q-algebra
  equivalent to PadicScalarField (QPlace v);
* S2047GaloisEquivOfBaseData : base ring equivalence, algebraic-closure
  ring equivalence and the compatibility of the two;
* S2047GaloisEquivRequired : LocalAbsoluteGalois v.1 is multiplicatively
  equivalent to Gv v = LocalClosure v = Aut(LocalClosure v / LocalBase v).

The obstruction recorded in S2047 was not a mathematical one: the canonical
Algebra Q (adicCompletion Q v) instance and the DivisionRing.toRatAlgebra
instance used by the abbreviations in S2047GaloisCompletionActual are not
definitionally equal.  We do not install or assume a new global instance.
Instead we use the actual Mathlib comparison

  Padic.adicCompletionEquiv : Q_[p] = (primesEquiv.symm p).adicCompletion Q

and the actual algebraic-closure comparison

  IsAlgClosure.equivOfEquiv : closures of ring-equivalent fields are
  ring-equivalent,

then conjugate the automorphism groups.  The only instance bookkeeping is
the standard fact Algebra.rat_algebra_subsingleton, used to compare the
two rational scalar structures inside the proof of the commutation field;
the resulting objects have exactly the S2047 types.

No sorry, axiom, fake instance, Q_p substitution, empty type, or Nonempty
gate is used.  The constructions are explicit values.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 4000000

namespace LeanFormal.IUT.XiFPaper.S2061BaseCompletionGaloisActual

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S1973PsiCnsActual
open LeanFormal.IUT.XiFPaper.S2047GaloisCompletionActual
open LeanFormal.IUT.XiFPaper.S2046OperationComponentsActual

variable (v : FinitePrimePlace 2 7)

local instance (v : FinitePrimePlace 2 7) : Fact (Nat.Prime v.1) := ⟨v.prime⟩

/-! ## 1. The rational adic-completion scalar instance -/

/-- The canonical Q-algebra structure on the adic completion of Q at a
finite place, written as an explicit term so that it can be supplied to
Mathlib projections whose implicit instance arguments are otherwise
synthesized with a different (but propositionally equal) rational algebra
structure. -/
@[reducible]
noncomputable def S2061AdicScalarAlgebra
    (w : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ)) :
    Algebra ℚ (w.adicCompletion ℚ) :=
  @IsDedekindDomain.HeightOneSpectrum.instAlgebraAdicCompletion
    (NumberField.RingOfIntegers ℚ) _ _ ℚ ℚ _ _ _ _ w (Algebra.id ℚ)

/-- The actual rational completion equivalence
Q_[p] = (primesEquiv.symm p).adicCompletion Q of Mathlib. -/
noncomputable def S2061RationalAdicEquiv :=
  Padic.adicCompletionEquiv (R := NumberField.RingOfIntegers ℚ) ⟨v.1, v.prime⟩

/-- The rational height-one spectrum at v.1. -/
abbrev S2061RationalHeightSpectrum :
    IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers ℚ) :=
  LeanFormal.IUT.rationalHeightOneSpectrum v.1

/-- The actual rational completion equivalence as an AlgEquiv with the
canonical adic-completion scalar structure on the source. -/
noncomputable def S2061RationalAdicAlgEquiv :
    @AlgEquiv ℚ (ℚ_[v.1]) ((S2061RationalHeightSpectrum v).adicCompletion ℚ) _ _ _
      (inferInstance : Algebra ℚ ℚ_[v.1]) (S2061AdicScalarAlgebra (S2061RationalHeightSpectrum v)) :=
  @ContinuousAlgEquiv.toAlgEquiv ℚ (ℚ_[v.1])
    ((S2061RationalHeightSpectrum v).adicCompletion ℚ) _ _ _ _ _
    (inferInstance) (S2061AdicScalarAlgebra (S2061RationalHeightSpectrum v))
    (S2061RationalAdicEquiv v)

/-- The inverse direction, as a ring equivalence between the rational
adic completion and Q_[p]. -/
noncomputable def S2061BaseAuxEquiv :
    (S2061RationalHeightSpectrum v).adicCompletion ℚ ≃+* ℚ_[v.1] :=
  @AlgEquiv.toRingEquiv ℚ ((S2061RationalHeightSpectrum v).adicCompletion ℚ) (ℚ_[v.1]) _ _ _
    (S2061AdicScalarAlgebra (S2061RationalHeightSpectrum v)) (inferInstance)
    (@AlgEquiv.symm ℚ (ℚ_[v.1]) ((S2061RationalHeightSpectrum v).adicCompletion ℚ) _ _ _
      (inferInstance) (S2061AdicScalarAlgebra (S2061RationalHeightSpectrum v))
      (S2061RationalAdicAlgEquiv v))

/-! ## 2. S2047BaseModelEquivRequired -/

/-- The actual base-completion ring equivalence
Base (QPlace v) = Completion (QPlace v) = Q_[v.1].

The place of the adic completion in Base (QPlace v) is
(FinitePlace.mk (rationalHeightOneSpectrum v.1)).maximalIdeal; the
RingEquiv.cast along NumberField.FinitePlace.maximalIdeal_mk removes
this last syntactic difference, without changing the underlying
completion. -/
noncomputable def S2061BaseCompletionRingEquiv :
    Iut.SourceFinitePlaceReconstruction.Base (QPlace v) ≃+* ℚ_[v.1] := by
  let h : (NumberField.FinitePlace.mk (LeanFormal.IUT.rationalHeightOneSpectrum v.1)).maximalIdeal =
      LeanFormal.IUT.rationalHeightOneSpectrum v.1 :=
    NumberField.FinitePlace.maximalIdeal_mk _
  let castRing :
      ((NumberField.FinitePlace.mk (LeanFormal.IUT.rationalHeightOneSpectrum v.1)).maximalIdeal).adicCompletion ℚ ≃+*
        (LeanFormal.IUT.rationalHeightOneSpectrum v.1).adicCompletion ℚ :=
    RingEquiv.cast (R := fun w => w.adicCompletion ℚ) h
  exact castRing.trans (S2061BaseAuxEquiv v)

/-- Exact S2047 target: the base-completion model bridge. -/
noncomputable def S2061S2047BaseModelEquiv :
    S2047BaseModelEquivRequired (v := v) :=
  S2061BaseCompletionRingEquiv v

/-! ## 3. S2047RationalCompletionModelEquiv -/

/-- The rational completion as a continuous Q-algebra equivalence at the
exact place appearing in S2047. -/
noncomputable def S2061RationalCompletionModelEquiv :
    S2047RationalCompletionModelEquiv (v := v) := by
  dsimp only [S2047RationalCompletionModelEquiv]
  refine
    { toFun := fun x =>
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))) x
      invFun := fun y =>
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))).invFun y
      left_inv := fun x =>
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))).left_inv x
      right_inv := fun y =>
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))).right_inv y
      map_mul' := fun x y =>
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))).map_mul x y
      map_add' := fun x y =>
        (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
          (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))).map_add x y
      commutes' := fun r => by
        have hsrc :
            @algebraMap ℚ
              (LeanFormal.IUT.NumberFieldFinitePlace.Completion
                (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))) _ _
              (inferInstance : Algebra ℚ
                (LeanFormal.IUT.NumberFieldFinitePlace.Completion
                  (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))) r =
            @algebraMap ℚ
              (LeanFormal.IUT.NumberFieldFinitePlace.Completion
                (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))) _ _
              (S2061AdicScalarAlgebra
                (LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
                  (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))) r := by
          simp
        rw [hsrc]
        exact
          @AlgEquiv.commutes ℚ
            (LeanFormal.IUT.NumberFieldFinitePlace.Completion
              (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
            (LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField (QPlace v)) _ _ _
            (S2061AdicScalarAlgebra
              (LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
                (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))))
            (inferInstance)
            (@ContinuousAlgEquiv.toAlgEquiv ℚ
              (LeanFormal.IUT.NumberFieldFinitePlace.Completion
                (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
              (LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField (QPlace v)) _ _ _ _ _
              (S2061AdicScalarAlgebra
                (LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
                  (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))))
              (inferInstance)
              (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
                (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
                  (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))))) r
      continuous_toFun :=
        @ContinuousAlgEquiv.continuous_toFun ℚ
          (LeanFormal.IUT.NumberFieldFinitePlace.Completion
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
          (LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField (QPlace v)) _ _ _ _ _
          (S2061AdicScalarAlgebra
            (LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
              (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))))
          (inferInstance)
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
            (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
              (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))))
      continuous_invFun :=
        @ContinuousAlgEquiv.continuous_invFun ℚ
          (LeanFormal.IUT.NumberFieldFinitePlace.Completion
            (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))
          (LeanFormal.IUT.NumberFieldFinitePlace.PadicScalarField (QPlace v)) _ _ _ _ _
          (S2061AdicScalarAlgebra
            (LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
              (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v))))
          (inferInstance)
          (Rat.HeightOneSpectrum.adicCompletion.padicEquiv
            (v := LeanFormal.IUT.NumberFieldFinitePlace.underlyingPrime
              (LeanFormal.IUT.NumberFieldFinitePlace.comap (k := ℚ) (QPlace v)))) }

/-! ## 4. The algebraic closure comparison and S2047GaloisEquivOfBaseData -/

/-- The algebraic closures of the actual base field and of Q_[p] are
ring-equivalent, extending the base-completion ring equivalence. -/
noncomputable def S2061ClosureEquiv :
    AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) ≃+*
      AlgebraicClosure ℚ_[v.1] :=
  IsAlgClosure.equivOfEquiv
    (R := ℚ_[v.1])
    (S := Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
    (L := AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)))
    (M := AlgebraicClosure ℚ_[v.1])
    (S2061BaseCompletionRingEquiv v)

/-- The closure equivalence is compatible with the algebra maps on the
nose. -/
theorem S2061ClosureEquiv_compat
    (x : Iut.SourceFinitePlaceReconstruction.Base (QPlace v)) :
    S2061ClosureEquiv v
        (algebraMap (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
          (AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))) x) =
      algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) (S2061BaseCompletionRingEquiv v x) :=
  IsAlgClosure.equivOfEquiv_algebraMap
    (R := ℚ_[v.1])
    (S := Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
    (L := AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)))
    (M := AlgebraicClosure ℚ_[v.1])
    (S2061BaseCompletionRingEquiv v) x

/-- The inverse closure equivalence is compatible with the inverse base ring
equivalence. -/
theorem S2061ClosureEquiv_symm_compat
    (y : ℚ_[v.1]) :
    (S2061ClosureEquiv v).symm (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) y) =
      algebraMap (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
        (AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)))
        ((S2061BaseCompletionRingEquiv v).symm y) :=
  IsAlgClosure.equivOfEquiv_symm_algebraMap
    (R := ℚ_[v.1])
    (S := Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
    (L := AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v)))
    (M := AlgebraicClosure ℚ_[v.1])
    (S2061BaseCompletionRingEquiv v) y

/-- Exact S2047 data: the base-completion ring equivalence, the closure
ring equivalence, and their compatibility. -/
noncomputable def S2061S2047GaloisEquivOfBaseData :
    S2047GaloisEquivOfBaseData (v := v) where
  baseEquiv := S2061BaseCompletionRingEquiv v
  closureEquiv := S2061ClosureEquiv v
  closure_compat := S2061ClosureEquiv_compat v

/-! ## 5. S2047GaloisEquivRequired -/

/-- Conjugation of the local absolute Galois group through the actual
algebraic-closure equivalence.  The compatibility fields above are exactly
what is needed for the conjugated automorphisms to fix the two base fields. -/
noncomputable def S2061GaloisEquiv : LocalAbsoluteGalois v.1 ≃* Gv v where
  toFun σ :=
    AlgEquiv.ofRingEquiv
      (f := (S2061ClosureEquiv v).trans
        (σ.toRingEquiv.trans (S2061ClosureEquiv v).symm))
      (by
        intro x
        change (S2061ClosureEquiv v).symm
            (σ ((S2061ClosureEquiv v)
              (algebraMap (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
                (AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))) x))) =
          algebraMap (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))
            (AlgebraicClosure (Iut.SourceFinitePlaceReconstruction.Base (QPlace v))) x
        rw [S2061ClosureEquiv_compat]
        rw [σ.commutes]
        rw [S2061ClosureEquiv_symm_compat]
        rw [RingEquiv.symm_apply_apply])
  invFun τ :=
    AlgEquiv.ofRingEquiv
      (f := (S2061ClosureEquiv v).symm.trans
        (τ.toRingEquiv.trans (S2061ClosureEquiv v)))
      (by
        intro y
        change (S2061ClosureEquiv v)
            (τ ((S2061ClosureEquiv v).symm
              (algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) y))) =
          algebraMap ℚ_[v.1] (AlgebraicClosure ℚ_[v.1]) y
        rw [S2061ClosureEquiv_symm_compat]
        rw [τ.commutes]
        rw [S2061ClosureEquiv_compat]
        rw [RingEquiv.apply_symm_apply])
  left_inv σ := by
    ext x
    change (S2061ClosureEquiv v)
        (((S2061ClosureEquiv v).trans
            (σ.toRingEquiv.trans (S2061ClosureEquiv v).symm))
          ((S2061ClosureEquiv v).symm x)) = σ x
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
    rfl
  right_inv τ := by
    ext x
    change (S2061ClosureEquiv v).symm
        (((S2061ClosureEquiv v).symm.trans
            (τ.toRingEquiv.trans (S2061ClosureEquiv v)))
          ((S2061ClosureEquiv v) x)) = τ x
    simp only [RingEquiv.trans_apply, RingEquiv.apply_symm_apply, RingEquiv.symm_apply_apply]
    rfl
  map_mul' σ τ := by
    ext x
    simp only [AlgEquiv.mul_apply, AlgEquiv.ofRingEquiv_apply, RingEquiv.trans_apply,
      RingEquiv.symm_apply_apply, RingEquiv.apply_symm_apply]
    congr 1

/-- Exact S2047 missing: the absolute local Galois equivalence. -/
noncomputable def S2061S2047GaloisEquivRequired :
    S2047GaloisEquivRequired (v := v) :=
  S2061GaloisEquiv v

/-- The same object is the (a)-component missing in S2046. -/
noncomputable def S2061S2046GaloisEquivRequired :
    S2046GaloisEquivRequired (v := v) :=
  S2061GaloisEquiv v

/-! ## 6. Checks and axiom probes -/

#check S2061BaseCompletionRingEquiv
#check S2061RationalCompletionModelEquiv
#check S2061ClosureEquiv
#check S2061S2047GaloisEquivOfBaseData
#check S2061GaloisEquiv
#check S2061S2047BaseModelEquiv
#check S2061S2047GaloisEquivRequired
#check S2061S2046GaloisEquivRequired

#print axioms S2061BaseCompletionRingEquiv
#print axioms S2061RationalCompletionModelEquiv
#print axioms S2061ClosureEquiv
#print axioms S2061ClosureEquiv_compat
#print axioms S2061ClosureEquiv_symm_compat
#print axioms S2061S2047GaloisEquivOfBaseData
#print axioms S2061GaloisEquiv
#print axioms S2061S2047GaloisEquivRequired
#print axioms S2061S2046GaloisEquivRequired

end LeanFormal.IUT.XiFPaper.S2061BaseCompletionGaloisActual

end

