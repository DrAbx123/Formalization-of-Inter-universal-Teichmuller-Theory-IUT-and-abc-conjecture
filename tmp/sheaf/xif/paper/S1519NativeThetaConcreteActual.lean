import tmp.sheaf.xif.paper.S1280SourceDefinition31Actual
import tmp.sheaf.xif.paper.S1503SourceNativeBridgeActual
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
import Mathlib.LinearAlgebra.Dimension.Finite

/-!
# S1519: concrete Gaussian native Theta data and its first failing native field

Task. For the concrete Gaussian root S1280Arithmetic l (the actual Q(i)
arithmetic with the base-changed split multiplicative curve from S1280),
either construct an actual SourceNativeInitialThetaData l whose arithmetic is
that root, or identify the exact first missing native field.

Result. The structure is EMPTY for this root. The first native clause that is
already impossible is clause (c), SourceClauseC; inside it the conflict is
between kernel_field_identification and image_contains_SL2.

Reason. The concrete Gaussian root has Fmod = F = K = GaussianField, so K is
F-algebra equivalent to F. In any SourceClauseC:

* kernel_field_identification identifies A.K with the fixed field L of the
  kernel of the actual l-torsion representation;
* image_contains_SL2 forces that representation's image to contain SL_2;
* at K = F, the first identification makes L one-dimensional over F, hence
  L = F; then the representation kernel is everything, the representation is
  trivial, and its range cannot contain the nontrivial unipotent matrix
  !![1,1;0,1].

This is not a "missing later field": no choice of the earlier tuple, place, or
clause data can repair clause (c). Consequently S1503's exact native donors
(NativeBridgeExact, NativeInputBridgeExact) are empty over this root. No
degenerate point-fiber orbicurve, PUnit/True placeholder, arbitrary
inhabitant, or new axiom is used.

Axiom footprint: the standard three (propext, Classical.choice, Quot.sound)
only; see the #print axioms commands at the end.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false

noncomputable section

namespace LeanFormal.IUT.XiFPaper.S1519NativeThetaConcreteActual

open LeanFormal.IUT
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.XiFPaper.S1280SourceDefinition31Actual
open LeanFormal.IUT.XiFPaper.S1503SourceNativeBridgeActual

local instance s1519GaussianIrreducible :
    Fact (Irreducible (Polynomial.X ^ 2 - Polynomial.C (-1) : Polynomial ℚ)) :=
  ⟨gaussianPolynomial_irreducible⟩

variable {l : PrimeGeFive}

/-! ## 1. The concrete Gaussian root has K = F = Q(i) -/

/-- The S1280 concrete Gaussian arithmetic root, with the notation of S1503. -/
abbrev S1519Arithmetic (l : PrimeGeFive) := S1280Arithmetic l

/-- The actual concrete Gaussian root has the same field at all three tower
levels. This is the precise arithmetic feature which makes clause (c)
inconsistent. -/
theorem S1519_K_eq_F (l : PrimeGeFive) :
    (S1519Arithmetic l).K = (S1519Arithmetic l).F :=
  rfl

/-- Consequently K is an F-algebra equivalent to F. -/
theorem S1519_K_algEquiv_F (l : PrimeGeFive) :
    Nonempty ((S1519Arithmetic l).K ≃ₐ[(S1519Arithmetic l).F]
      (S1519Arithmetic l).F) :=
  ⟨AlgEquiv.refl⟩

/-! ## 2. Clause (c) is impossible whenever K is F -/

/-- The exact first failing native field. For any arithmetic root whose K is
F-algebra equivalent to F (in particular the concrete Gaussian root), no
SourceClauseC exists. The contradiction uses only the two clause-(c) fields
kernel_field_identification and image_contains_SL2; all other tuple and
clause data are arbitrary.

The failure is constructive in the negative direction: every candidate
SourceClauseC yields False. Thus this is not a missing field to be supplied
later, but an inconsistent native clause for this arithmetic root. -/
theorem S1519_no_sourceClauseC_false
    {A : InitialThetaArithmeticData l} {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    (hKA : Nonempty (A.K ≃ₐ[A.F] A.F))
    (D : SourceClauseC A S C B) : False := by
  rcases hKA with ⟨eKA⟩
  let L := A.curve.galoisLTorsionKernelField l D.torsion_basis
  let e : A.F ≃ₐ[A.F] L := eKA.symm.trans D.kernel_field_identification
  have hlin := e.toLinearEquiv.finrank_eq
  have hself : Module.finrank A.F A.F = 1 := by
    refine finrank_eq_one (1 : A.F) ?_ ?_
    · exact one_ne_zero
    · intro w
      exact ⟨w, by simp⟩
  have hfin : Module.finrank A.F L = 1 := by
    rw [← hlin, hself]
  have hbot : L = ⊥ := IntermediateField.finrank_eq_one_iff.mp hfin
  have hker0 : L.fixingSubgroup = ⊤ := by
    rw [hbot]
    exact IntermediateField.fixingSubgroup_bot
  have hker1 : A.curve.galoisLTorsionKernelSubgroup l D.torsion_basis = ⊤ := by
    rw [← A.curve.galoisLTorsionKernelField_fixingSubgroup l D.torsion_basis]
    exact hker0
  have hDker : D.representation.ker = ⊤ := by
    rw [D.representation_eq_canonical]
    exact hker1
  have hDrep : D.representation = 1 := MonoidHom.ker_eq_top_iff.mp hDker
  have hrange : D.representation.range = ⊥ := MonoidHom.range_eq_bot_iff.mpr hDrep
  have hle : Subgroup.map Matrix.SpecialLinearGroup.toGL
      (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) ≤
      (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))) := by
    rw [← hrange]
    exact D.image_contains_SL2
  let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value) :=
    ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
  have hg : Matrix.SpecialLinearGroup.toGL g ∈
      Subgroup.map Matrix.SpecialLinearGroup.toGL
        (⊤ : Subgroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value))) :=
    Subgroup.mem_map_of_mem Matrix.SpecialLinearGroup.toGL (Subgroup.mem_top g)
  have hgbot : Matrix.SpecialLinearGroup.toGL g ∈
      (⊥ : Subgroup (Matrix.GeneralLinearGroup (Fin 2) (ZMod l.value))) := hle hg
  have hgone : Matrix.SpecialLinearGroup.toGL g = 1 := Subgroup.mem_bot.mp hgbot
  have hg1 : g = 1 := Matrix.SpecialLinearGroup.toGL_injective (by simpa using hgone)
  have hentry : g 0 1 =
      (1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod l.value)) 0 1 :=
    congrArg (fun x => x 0 1) hg1
  simp [g] at hentry
  haveI : Fact (Nat.Prime l.value) := l.factPrime
  exact (one_ne_zero : (1 : ZMod l.value) ≠ 0) hentry

/-- The clause-(c) record is empty, not merely unconstructed. -/
theorem S1519_sourceClauseC_empty
    {A : InitialThetaArithmeticData l} {S : SourceSignQuotientData A}
    {C : SourceClauseA A S} {B : SourceClauseB A S C}
    (hKA : Nonempty (A.K ≃ₐ[A.F] A.F)) :
    IsEmpty (SourceClauseC A S C B) :=
  ⟨S1519_no_sourceClauseC_false hKA⟩

/-! ## 3. The concrete Gaussian native data and S1503 donors are empty -/

/-- Exact S1503 native field over the concrete Gaussian arithmetic root. -/
abbrev S1519NativeThetaActual (l : PrimeGeFive) : Type 1 :=
  { T : SourceNativeInitialThetaData.{0} l // T.arithmetic = S1280Arithmetic l }

/-- No actual SourceNativeInitialThetaData over S1280Arithmetic l exists.
This is not an assertion that some later field is missing: it is a proof that
the structure has no inhabitant for this root. -/
theorem S1519_nativeThetaActual_impossible (l : PrimeGeFive) :
    ¬ Nonempty (S1519NativeThetaActual l) := by
  rintro ⟨T, hT⟩
  have hKA : Nonempty (T.arithmetic.K ≃ₐ[T.arithmetic.F] T.arithmetic.F) := by
    rw [hT]
    exact ⟨AlgEquiv.refl⟩
  exact S1519_no_sourceClauseC_false
    (A := T.arithmetic) (S := T.tuple.source)
    (C := T.clauseA) (B := T.clauseB) hKA T.clauseC

/-- S1503's exact native bridge field NativeBridgeExact is empty over the
concrete Gaussian root. -/
theorem S1519_no_nativeBridgeExact (l : PrimeGeFive) :
    ¬ Nonempty (NativeBridgeExact (l := l)) := by
  rintro ⟨T, hT⟩
  exact S1519_nativeThetaActual_impossible l ⟨T, hT⟩

/-- S1503's NativeInputBridgeExact, the native donor field used by S1497 and
the paper O(-D) construction, is empty over the concrete Gaussian root. -/
theorem S1519_no_nativeInputBridgeExact (l : PrimeGeFive) :
    ¬ Nonempty (NativeInputBridgeExact (l := l)) := by
  rintro ⟨X, hX⟩
  exact S1519_nativeThetaActual_impossible l ⟨X.S, hX⟩

/-- **The exact first failing native field at the concrete Gaussian root.**
For every supplied sign quotient and every supplied clauses (a) and (b), the
native clause (c) has no inhabitant.  Thus the obstruction is not a missing
later geometric field: clause (c) is already impossible, independently of
the tuple and place data that precede it. -/
theorem S1519_clauseC_empty_at_gaussian (l : PrimeGeFive)
    {S : SourceSignQuotientData (S1280Arithmetic l)}
    {C : SourceClauseA (S1280Arithmetic l) S}
    {B : SourceClauseB (S1280Arithmetic l) S C} :
    IsEmpty (SourceClauseC (S1280Arithmetic l) S C B) :=
  S1519_sourceClauseC_empty (S1519_K_algEquiv_F l)

/-- The precise first failing native field is clause (c).  This is the
clause-level form of S1519_nativeThetaActual_impossible: the whole native
structure is empty because its clause (c) field is already empty. -/
theorem S1519_first_native_field_is_clauseC (l : PrimeGeFive) :
    (∀ {S : SourceSignQuotientData (S1280Arithmetic l)}
      {C : SourceClauseA (S1280Arithmetic l) S}
      {B : SourceClauseB (S1280Arithmetic l) S C},
      IsEmpty (SourceClauseC (S1280Arithmetic l) S C B)) ∧
    IsEmpty (S1519NativeThetaActual l) :=
  ⟨fun {_S _C _B} => S1519_clauseC_empty_at_gaussian l,
    ⟨fun T => S1519_nativeThetaActual_impossible l ⟨T⟩⟩⟩

/-! ## 4. Axiom footprint -/

#print axioms S1519_K_eq_F
#print axioms S1519_K_algEquiv_F
#print axioms S1519_no_sourceClauseC_false
#print axioms S1519_sourceClauseC_empty
#print axioms S1519_clauseC_empty_at_gaussian
#print axioms S1519_nativeThetaActual_impossible
#print axioms S1519_no_nativeBridgeExact
#print axioms S1519_no_nativeInputBridgeExact
#print axioms S1519_first_native_field_is_clauseC

end LeanFormal.IUT.XiFPaper.S1519NativeThetaConcreteActual
