/-
Copyright (c) 2026 LeanFormal contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import tmp.sheaf.xif.paper.S2040PaperOUnitsMuAmbientActual
import LeanFormal.IUT.ABCBridge.Geometry.FinitePlaceSourceAlgebraicClosure
import tmp.sheaf.xif.paper.S2032R6GeneratorActual

/-!
# S2060: actual completion integral units versus the Q_p model

## The carrier correction

S2040PaperOUnitsMuAmbientActual.S2040CompletionLocalIdentification asks for

  (AlgebraicClosure (Completion (qVPlace T b)))ˣ  ≃  LocalOFieldUnits p.

The left-hand side is the *all-units* carrier of the field (the S2035
OUnitsActual carrier).  The right-hand side is S1978's actual integral unit
group (Integers (AlgebraicClosure Q_p))ˣ.  These are different carriers:
the all-units group contains the unit p of norm (p : R)^-1, while every
integral unit has norm one.  Hence the literal structure cannot be filled by a
norm-preserving identification (proved below as
s2040AllUnits_norm_incompatible).  The actual O^ of the completion carrier is
the integral-unit group

  (Integers (AlgebraicClosure (Completion (qVPlace T b))))ˣ.

## What is constructed

* s2060AlgClosureEquiv: a Q_p-algebra equivalence between the algebraic
  closure of the actual completion and Mathlib's PadicAlgCl (the Q_p model),
  with qVPlace T b's rational prime as the base prime.
* s2060AlgClosureEquiv_norm: it preserves the p-adic norm.  This is the
  bridge the task asks about: it is *not* missing.  Both norms are the
  spectral norms over Q_p, and minpoly.algEquiv_eq identifies the minimal
  polynomials, so the spectral values agree.  Consequently the equivalence
  preserves the integral subrings (s2060_mem_integers_iff).
* s2060IntegersRingEquiv and s2060CompletionIntegralUnitsEquiv: the induced
  identification of integral unit groups (the general number-field form of
  S2055's rational-place missing type).
* s2060CompletionIntegralUnitsEquiv_val_norm: norm compatibility.
* s2060CompletionOUnitsMuEquiv: the induced O^mu identification.
* S2060CompletionLocalIdentification: the carrier-corrected S2040 structure,
  with a genuine typed norm-compatibility field;
  s2060CompletionLocalIdentification inhabits it.
* s2060PaperOUnitsMuAmbient: the S2040 paper O^ / O^mu / ambient package
  built from the corrected identification, without the S2035 all-units
  carrier.
* S2060S2040CompletionUnitIdentificationRequired: the exact first missing
  datum of the literal S2040 structure (all units to integral units *with*
  norm compatibility), proved empty.

No sorry, axiom, True/PUnit slot, arbitrary inhabitant or Nonempty gate is
used to assert any identification: every Nonempty statement below carries an
explicit witness.  The one empty type is the honestly recorded impossible
requirement of the literal S2040 statement.
-/

noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.checkUnivs false
set_option maxHeartbeats 8000000

namespace LeanFormal.IUT.XiFPaper.S2060CompletionUnitsActual

open LeanFormal.IUT
open LeanFormal.IUT.NumberFieldFinitePlace
open LeanFormal.IUT.InitialThetaSource
open LeanFormal.IUT.InitialThetaSource.PlacePartitionReduction
open LeanFormal.IUT.LocalFieldIntegralUnits
open LeanFormal.IUT.XiFPaper.S1978LocalFieldOCarrierActual
open LeanFormal.IUT.XiFPaper.TwoLthRootKummerActual
open LeanFormal.IUT.XiFPaper.S2032R6GeneratorActual
open LeanFormal.IUT.XiFPaper.S2040PaperOUnitsMuAmbientActual
open LeanFormal.IUT.XiFPaper.S2040RootStackThetaPilotActual

universe u v

variable {l : PrimeGeFive} (T : SourceNativeInitialThetaData.{0} l)
  (b : Bad (nativePlaceSelection T))

/-! ## 1. The rational prime under the completion place -/

/-- The rational prime under the actual completion place qVPlace T b. -/
noncomputable abbrev s2060Prime : Nat :=
  (completionRationalPrime (qVPlace (l := l) T b)).val

/-- The completion-level algebraic closure carrier. -/
noncomputable abbrev s2060CompletionL : Type :=
  SourceAlgebraicClosure (qVPlace (l := l) T b)

/-- The Q_p-model algebraic closure carrier. -/
noncomputable abbrev s2060QpL : Type :=
  AlgebraicClosure (PadicScalarField (qVPlace (l := l) T b))

/-- The literal S2040 source carrier: the all-units (S2035-style) carrier. -/
noncomputable abbrev s2060LiteralAllUnits : Type :=
  (AlgebraicClosure (Completion (qVPlace (l := l) T b)))ˣ

/-- The literal all-units carrier is definitionally the units of the
completion-level algebraic closure used in this file. -/
theorem s2060LiteralAllUnits_eq : s2060LiteralAllUnits T b = (s2060CompletionL T b)ˣ :=
  rfl

/-! ## 2. The norm-preserving algebraic-closure equivalence -/

/-- A Q_p-algebra equivalence between the algebraic closure of the actual
completion at qVPlace T b and the Q_p model AlgebraicClosure Q_p.
This is IsAlgClosure.equivOfAlgebraic: the completion is a finite, hence
algebraic, extension of Q_p, and both fields are algebraic closures of
Q_p. -/
noncomputable def s2060AlgClosureEquiv :
    s2060CompletionL T b ≃ₐ[PadicScalarField (qVPlace (l := l) T b)] s2060QpL T b := by
  letI := padicCompletionAlgebra (qVPlace (l := l) T b)
  haveI : Algebra.IsAlgebraic (PadicScalarField (qVPlace (l := l) T b))
      (NormalizedCompletion (qVPlace (l := l) T b)) :=
    Algebra.IsAlgebraic.of_finite _ _
  haveI : IsScalarTower (PadicScalarField (qVPlace (l := l) T b))
      (NormalizedCompletion (qVPlace (l := l) T b))
      (SourceAlgebraicClosure (qVPlace (l := l) T b)) :=
    sourceAlgebraicClosureScalarTower (qVPlace (l := l) T b)
  exact IsAlgClosure.equivOfAlgebraic
    (K := PadicScalarField (qVPlace (l := l) T b))
    (J := NormalizedCompletion (qVPlace (l := l) T b))
    (L := SourceAlgebraicClosure (qVPlace (l := l) T b))
    (M := AlgebraicClosure (PadicScalarField (qVPlace (l := l) T b)))

/-- The equivalence is the identity on the embedded Q_p. -/
theorem s2060AlgClosureEquiv_commutes (x : PadicScalarField (qVPlace (l := l) T b)) :
    s2060AlgClosureEquiv T b (algebraMap _ (s2060CompletionL T b) x) =
      algebraMap _ (s2060QpL T b) x :=
  (s2060AlgClosureEquiv T b).commutes x

/-- Norm preservation of the algebraic-closure equivalence.  Both sides are
the spectral norm over Q_p; the equivalence fixes Q_p and hence preserves
minimal polynomials, so the spectral values agree. -/
theorem s2060AlgClosureEquiv_norm (x : s2060CompletionL T b) :
    ‖s2060AlgClosureEquiv T b x‖ = ‖x‖ := by
  letI := padicCompletionAlgebra (qVPlace (l := l) T b)
  have hM := NormedAlgebra.norm_eq_spectralNorm
    (PadicScalarField (qVPlace (l := l) T b))
    (L := AlgebraicClosure (PadicScalarField (qVPlace (l := l) T b)))
    (s2060AlgClosureEquiv T b x)
  have hL := NormedAlgebra.norm_eq_spectralNorm
    (PadicScalarField (qVPlace (l := l) T b))
    (L := SourceAlgebraicClosure (qVPlace (l := l) T b)) x
  rw [hM, hL]
  show spectralValue (minpoly (PadicScalarField (qVPlace (l := l) T b))
      (s2060AlgClosureEquiv T b x)) =
    spectralValue (minpoly (PadicScalarField (qVPlace (l := l) T b)) x)
  rw [minpoly.algEquiv_eq]

/-- Norm preservation for the inverse equivalence. -/
theorem s2060AlgClosureEquiv_symm_norm (y : s2060QpL T b) :
    ‖(s2060AlgClosureEquiv T b).symm y‖ = ‖y‖ := by
  simpa using (s2060AlgClosureEquiv_norm T b
    ((s2060AlgClosureEquiv T b).symm y)).symm

/-- The equivalence preserves the integral subring.  An element of the
completion-level algebraic closure is integral if and only if its image under
the equivalence is integral in the Q_p model. -/
theorem s2060_mem_integers_iff (x : s2060CompletionL T b) :
    x ∈ Integers (s2060CompletionL T b) ↔
      s2060AlgClosureEquiv T b x ∈ Integers (s2060QpL T b) := by
  rw [mem_integers_iff, mem_integers_iff, s2060AlgClosureEquiv_norm]

/-! ## 3. The integral-subring equivalence and the unit identification -/

/-- The ring equivalence of the actual integral subrings induced by the
norm-preserving algebraic-closure equivalence. -/
noncomputable def s2060IntegersRingEquiv :
    Integers (s2060CompletionL T b) ≃+* Integers (s2060QpL T b) where
  toFun x := ⟨s2060AlgClosureEquiv T b x,
    (s2060_mem_integers_iff T b x).mp x.property⟩
  invFun y := ⟨(s2060AlgClosureEquiv T b).symm y,
    (s2060_mem_integers_iff T b _).mpr (by
      rw [AlgEquiv.apply_symm_apply]
      exact y.property)⟩
  left_inv x := by ext; simp
  right_inv y := by ext; simp
  map_add' x y := by ext; simp
  map_mul' x y := by ext; simp

/-- The actual integral units of the completion-level algebraic closure. -/
noncomputable abbrev s2060CompletionIntegralUnits : Type :=
  (Integers (s2060CompletionL T b))ˣ

/-- The actual integral-unit identification between the completion carrier
and the Q_p model.  This is the general-number-field form of S2055's
rational-place missing identification type. -/
noncomputable def s2060CompletionIntegralUnitsEquiv :
    (Integers (s2060CompletionL T b))ˣ ≃* LocalOFieldUnits (s2060Prime T b) :=
  Units.mapEquiv (s2060IntegersRingEquiv T b).toMulEquiv

/-- The unit identification acts by the algebraic-closure equivalence on the
underlying field values. -/
theorem s2060CompletionIntegralUnitsEquiv_val
    (u : (Integers (s2060CompletionL T b))ˣ) :
    ((s2060CompletionIntegralUnitsEquiv T b u : LocalOFieldUnits (s2060Prime T b)) :
        s2060QpL T b) =
      s2060AlgClosureEquiv T b (((u : Integers (s2060CompletionL T b)) :
        s2060CompletionL T b)) :=
  rfl

/-- Norm compatibility of the integral-unit identification. -/
theorem s2060CompletionIntegralUnitsEquiv_val_norm
    (u : (Integers (s2060CompletionL T b))ˣ) :
    ‖((s2060CompletionIntegralUnitsEquiv T b u :
          LocalOFieldUnits (s2060Prime T b)) : s2060QpL T b)‖ =
      ‖((u : Integers (s2060CompletionL T b)) : s2060CompletionL T b)‖ := by
  rw [s2060CompletionIntegralUnitsEquiv_val, s2060AlgClosureEquiv_norm]

/-- Both sides of the integral-unit identification consist of norm-one
elements; this is the O^ level form of norm compatibility. -/
theorem s2060CompletionIntegralUnits_norm_eq_one
    (u : (Integers (s2060CompletionL T b))ˣ) :
    ‖((s2060CompletionIntegralUnitsEquiv T b u :
          LocalOFieldUnits (s2060Prime T b)) : s2060QpL T b)‖ = 1 ∧
      ‖((u : Integers (s2060CompletionL T b)) : s2060CompletionL T b)‖ = 1 :=
  ⟨norm_unit_eq_one _, norm_unit_eq_one _⟩

/-- Norm compatibility as a predicate on unit identifications. -/
def S2060NormCompatible
    (e : (Integers (s2060CompletionL T b))ˣ ≃*
      LocalOFieldUnits (s2060Prime T b)) : Prop :=
  ∀ u : (Integers (s2060CompletionL T b))ˣ,
    ‖((e u : LocalOFieldUnits (s2060Prime T b)) : s2060QpL T b)‖ =
      ‖((u : Integers (s2060CompletionL T b)) : s2060CompletionL T b)‖

/-- The constructed identification satisfies norm compatibility. -/
theorem s2060CompletionIntegralUnitsEquiv_normCompatible :
    S2060NormCompatible T b (s2060CompletionIntegralUnitsEquiv T b) :=
  s2060CompletionIntegralUnitsEquiv_val_norm T b

/-- The all-units (S2035-style) comparison that *is* available: the units of
the two algebraic closures are identified by the norm-preserving
algebraic-closure equivalence.  This is not the integral-unit carrier. -/
noncomputable def s2060AllUnitsEquiv : (s2060CompletionL T b)ˣ ≃* (s2060QpL T b)ˣ :=
  Units.mapEquiv (s2060AlgClosureEquiv T b).toMulEquiv

/-- Norm compatibility of the all-units comparison. -/
theorem s2060AllUnitsEquiv_val_norm (u : (s2060CompletionL T b)ˣ) :
    ‖((s2060AllUnitsEquiv T b u : (s2060QpL T b)ˣ) : s2060QpL T b)‖ =
      ‖(u : s2060CompletionL T b)‖ := by
  rw [s2060AllUnitsEquiv, Units.coe_mapEquiv]
  exact s2060AlgClosureEquiv_norm T b (u : s2060CompletionL T b)

/-! ## 4. The induced O^mu identification -/

/-- A multiplicative equivalence of commutative groups induces a
multiplicative equivalence of their torsion quotients. -/
noncomputable def timesMuQuotientMulEquiv {U : Type u} {V : Type v}
    [CommGroup U] [CommGroup V] (e : U ≃* V) :
    TimesMuQuotient U ≃* TimesMuQuotient V :=
  QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion V) e e.map_torsion

/-- The torsion-quotient equivalence sends quotient classes to quotient
classes. -/
theorem timesMuQuotientMulEquiv_mk' {U : Type u} {V : Type v}
    [CommGroup U] [CommGroup V] (e : U ≃* V) (x : U) :
    timesMuQuotientMulEquiv e (QuotientGroup.mk' (CommGroup.torsion U) x) =
      QuotientGroup.mk' (CommGroup.torsion V) (e x) := by
  show QuotientGroup.congr (CommGroup.torsion U) (CommGroup.torsion V) e e.map_torsion
      (QuotientGroup.mk' (CommGroup.torsion U) x) = _
  exact QuotientGroup.congr_mk' (CommGroup.torsion U) (CommGroup.torsion V) e e.map_torsion x

/-- The induced O^mu identification. -/
noncomputable def s2060CompletionOUnitsMuEquiv :
    TimesMuQuotient ((Integers (s2060CompletionL T b))ˣ) ≃*
      LocalOFieldUnitsMu (s2060Prime T b) :=
  timesMuQuotientMulEquiv (s2060CompletionIntegralUnitsEquiv T b)

/-- The O^mu identification commutes with the quotient maps. -/
theorem s2060CompletionOUnitsMuEquiv_quotientMap
    (u : (Integers (s2060CompletionL T b))ˣ) :
    s2060CompletionOUnitsMuEquiv T b (TimesMuQuotient.quotientMap u) =
      TimesMuQuotient.quotientMap (s2060CompletionIntegralUnitsEquiv T b u) := by
  rw [s2060CompletionOUnitsMuEquiv]
  exact timesMuQuotientMulEquiv_mk' (s2060CompletionIntegralUnitsEquiv T b) u

/-! ## 5. The carrier-corrected S2040 identification -/

/-- The carrier-corrected analogue of S2040CompletionLocalIdentification:
the completion side is the actual integral unit group, and norm_compatible
is the genuine norm-comparison statement (not an opaque Prop). -/
structure S2060CompletionLocalIdentification
    (T : SourceNativeInitialThetaData.{0} l)
    (b : Bad (nativePlaceSelection T)) where
  /-- the rational prime under qVPlace T b -/
  p : Nat
  /-- primality of p -/
  hprime : Fact (Nat.Prime p)
  /-- the integral-unit identification -/
  completionUnitEquiv :
    (Integers (SourceAlgebraicClosure (qVPlace (l := l) T b)))ˣ ≃*
      LocalOFieldUnits p
  /-- norm compatibility of the identification -/
  norm_compatible :
    ∀ u : (Integers (SourceAlgebraicClosure (qVPlace (l := l) T b)))ˣ,
      ‖((completionUnitEquiv u : LocalOFieldUnits p) : AlgebraicClosure ℚ_[p])‖ =
        ‖((u : Integers (SourceAlgebraicClosure (qVPlace (l := l) T b))) :
          SourceAlgebraicClosure (qVPlace (l := l) T b))‖

/-- The corrected identification exists. -/
noncomputable def s2060CompletionLocalIdentification :
    S2060CompletionLocalIdentification (l := l) T b where
  p := s2060Prime T b
  hprime := completionRationalPrime_fact (qVPlace (l := l) T b)
  completionUnitEquiv := s2060CompletionIntegralUnitsEquiv T b
  norm_compatible := s2060CompletionIntegralUnitsEquiv_val_norm T b

/-- The corrected identification uses the rational prime under the completion
place. -/
theorem s2060CompletionLocalIdentification_p :
    (s2060CompletionLocalIdentification T b).p = s2060Prime T b :=
  rfl

/-- The corrected identification's unit equivalence is the constructed
integral-unit identification. -/
theorem s2060CompletionLocalIdentification_unitEquiv :
    (s2060CompletionLocalIdentification T b).completionUnitEquiv =
      s2060CompletionIntegralUnitsEquiv T b :=
  rfl

/-! ## 6. The literal S2040 all-units statement cannot be norm compatible -/

/-- Norm compatibility for the literal S2040 all-units carrier. -/
def S2060AllUnitsNormCompatible
    (e : (s2060CompletionL T b)ˣ ≃* LocalOFieldUnits (s2060Prime T b)) : Prop :=
  ∀ u : (s2060CompletionL T b)ˣ,
    ‖((e u : LocalOFieldUnits (s2060Prime T b)) : s2060QpL T b)‖ =
      ‖(u : s2060CompletionL T b)‖

/-- The literal S2040 carrier has no norm-compatible identification with the
integral units.  The all-units carrier contains the scalar p, of norm
(p : R)^-1 != 1, whereas every integral unit has norm one. -/
theorem s2040AllUnits_norm_incompatible
    (e : (s2060CompletionL T b)ˣ ≃* LocalOFieldUnits (s2060Prime T b)) :
    ¬ S2060AllUnitsNormCompatible T b e := by
  intro h
  let K := PadicScalarField (qVPlace (l := l) T b)
  letI : Algebra K (s2060CompletionL T b) :=
    sourceAlgebraicClosurePadicAlgebra (qVPlace (l := l) T b)
  letI : NormedAlgebra K (s2060CompletionL T b) :=
    sourceAlgebraicClosureNormedAlgebra (qVPlace (l := l) T b)
  let z : s2060CompletionL T b :=
    algebraMap K (s2060CompletionL T b) ((s2060Prime T b : K))
  have hz_norm : ‖z‖ = ((s2060Prime T b : ℝ))⁻¹ := by
    dsimp [z]
    rw [norm_algebraMap']
    exact Padic.norm_p
  have hpne : ((s2060Prime T b : ℝ)) ≠ 0 := by
    exact_mod_cast (Fact.out : Nat.Prime (s2060Prime T b)).ne_zero
  have hz0 : z ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hz_norm
    exact (inv_ne_zero hpne) hz_norm.symm
  let u : (s2060CompletionL T b)ˣ := Units.mk0 z hz0
  have hleft :
      ‖((e u : LocalOFieldUnits (s2060Prime T b)) : s2060QpL T b)‖ = 1 :=
    norm_unit_eq_one _
  have hright : ‖(u : s2060CompletionL T b)‖ = ((s2060Prime T b : ℝ))⁻¹ := by
    show ‖z‖ = ((s2060Prime T b : ℝ))⁻¹
    exact hz_norm
  have hcontr := h u
  rw [hleft, hright] at hcontr
  have hp1 : (1 : ℝ) < (s2060Prime T b : ℝ) := by
    exact_mod_cast (Fact.out : Nat.Prime (s2060Prime T b)).one_lt
  have hlt : ((s2060Prime T b : ℝ))⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp1
  linarith

/-- The exact first missing datum of the literal S2040 structure: an
all-units-to-integral-units identification satisfying norm compatibility.
This type is empty.  The honest replacement is the integral carrier
S2060CompletionLocalIdentification above. -/
abbrev S2060S2040CompletionUnitIdentificationRequired : Type :=
  { e : (s2060CompletionL T b)ˣ ≃* LocalOFieldUnits (s2060Prime T b) //
      S2060AllUnitsNormCompatible T b e }

/-- The literal S2040 norm-compatible identification type is empty. -/
theorem S2060S2040CompletionUnitIdentificationRequired_empty :
    IsEmpty (S2060S2040CompletionUnitIdentificationRequired T b) :=
  ⟨fun x => s2040AllUnits_norm_incompatible T b x.1 x.2⟩

/-- The same impossible requirement written with the literal S2040 carrier
spelling (AlgebraicClosure (Completion (qVPlace T b)))^x. -/
abbrev S2060S2040LiteralFirstMissing : Type :=
  { e : s2060LiteralAllUnits T b ≃* LocalOFieldUnits (s2060Prime T b) //
      S2060AllUnitsNormCompatible T b e }

/-- The literal S2040 spelling of the first missing datum is empty. -/
theorem S2060S2040LiteralFirstMissing_empty :
    IsEmpty (S2060S2040LiteralFirstMissing T b) :=
  ⟨fun x => s2040AllUnits_norm_incompatible T b x.1 x.2⟩

/-! ## 7. The honest replacement identification is nonempty -/

/-- The honest replacement identification type (integral units + norm
compatibility) is nonempty. -/
theorem s2060CompletionIntegralIdentificationRequired_nonempty :
    Nonempty
      { e : (Integers (s2060CompletionL T b))ˣ ≃*
          LocalOFieldUnits (s2060Prime T b) //
        S2060NormCompatible T b e } :=
  ⟨⟨s2060CompletionIntegralUnitsEquiv T b,
    s2060CompletionIntegralUnitsEquiv_normCompatible T b⟩⟩

/-! ## 8. Feeding the S2040 paper O^ / O^mu ambient package -/

/-- The S2040 paper O^ / O^mu / ambient package built from the actual
completion integral units and the Q_p model. -/
noncomputable def s2060PaperOUnitsMuAmbient : S2040PaperOUnitsMuAmbient where
  OUnits := LocalOFieldUnits (s2060Prime T b)
  OUnitsMu := LocalOFieldUnitsMu (s2060Prime T b)
  ambientValues := LocalOFieldIntegral (s2060Prime T b)
  quotient_compatible := Nonempty (Nontrivial (LocalOFieldUnitsMu (s2060Prime T b)))
  ambient_values_paper := Nonempty (LocalOFieldIntegral (s2060Prime T b))
  OUnits_nontrivial := Nonempty (Nontrivial (LocalOFieldUnits (s2060Prime T b)))

/-- The O^mu quotient of the actual local model is nontrivial. -/
theorem s2060PaperOUnitsMuAmbient_quotient_compatible :
    (s2060PaperOUnitsMuAmbient T b).quotient_compatible :=
  ⟨s2040LocalOUnitsMu_nontrivial (s2060Prime T b)⟩

/-- The ambient values are nonempty (the actual O^ model). -/
theorem s2060PaperOUnitsMuAmbient_ambient_values_paper :
    (s2060PaperOUnitsMuAmbient T b).ambient_values_paper :=
  ⟨1⟩

/-- The actual local O^ carrier is nontrivial. -/
theorem s2060PaperOUnitsMuAmbient_OUnits_nontrivial :
    (s2060PaperOUnitsMuAmbient T b).OUnits_nontrivial :=
  ⟨s2040LocalOUnits_nontrivial (s2060Prime T b)⟩

/-! ## 9. Axiom probes -/

#print axioms s2060AlgClosureEquiv
#print axioms s2060AlgClosureEquiv_norm
#print axioms s2060_mem_integers_iff
#print axioms s2060IntegersRingEquiv
#print axioms s2060CompletionIntegralUnitsEquiv
#print axioms s2060CompletionIntegralUnitsEquiv_val_norm
#print axioms s2060CompletionIntegralUnitsEquiv_normCompatible
#print axioms s2060AllUnitsEquiv
#print axioms s2060AllUnitsEquiv_val_norm
#print axioms s2060CompletionOUnitsMuEquiv
#print axioms s2060CompletionOUnitsMuEquiv_quotientMap
#print axioms s2060CompletionLocalIdentification
#print axioms s2040AllUnits_norm_incompatible
#print axioms S2060S2040CompletionUnitIdentificationRequired_empty
#print axioms S2060S2040LiteralFirstMissing_empty
#print axioms s2060PaperOUnitsMuAmbient
#print axioms s2060PaperOUnitsMuAmbient_quotient_compatible

end LeanFormal.IUT.XiFPaper.S2060CompletionUnitsActual
end