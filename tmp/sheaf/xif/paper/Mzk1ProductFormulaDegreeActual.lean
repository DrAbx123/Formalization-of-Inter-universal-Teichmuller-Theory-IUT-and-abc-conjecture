/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/
import LeanFormal.IUT.IUTII.Frobenioid.Example36ProductFormula
import Mathlib.Tactic

/-! # R29m / task-93: P6 product formula and Arakelov degree interface -/

/-
| field | value |
|---|---|
| Status | PARTIAL/green skeleton: product formula re-export; minimal additive Arakelov degree interface on Example36 explicit divisors; degree-difference and principal-unit vanishing proved |
| Reuse | `Example36ProductFormula.lean:246 productFormula_finsupp`, `:271 weightedFiniteSum_eq_archimedeanLogSum`, `:313 globalPrimeStripWeight`, `:327 globalPrimeStripWeightHom`, `:387 globalPrimeStripWeight_principalDivisorExplicit`, `:399/:408 kernel triviality` |
| GAP | GAP-DEGREE-BRIDGE: this degree lives on Example36 explicit divisors; the identification with our S2717/S2807 theta-hull / q-pilot log-volumes is NOT constructed; GAP-NORM-ARCH: paper (1/(2ℓ)) and arch normalization not included; product formula is Mathlib's for global units (not independent) |
| 纪律 | no sorry/axiom; interface is a definition, its consistency theorems are separate; no new assumptions |
-/

noncomputable section
open scoped BigOperators NumberField
open IsDedekindDomain NumberField

namespace LeanFormal.IUT.XiFPaper.Mzk1ProductFormulaDegreeActual

open LeanFormal.IUT.IUTII.Frobenioid.Example36
open LeanFormal.IUT.IUTII.Frobenioid.Example36.PrimeStripProductFormula

variable {F : Type*} [Field F] [NumberField F]

/-! ## 1. Product formula for global units (re-export) -/

/-- **Product formula, normalized finite + archimedean form.**  For every global unit
`f : Fˣ`, the finite weighted sum plus the archimedean weighted sum vanishes.
Re-export of `Example36ProductFormula.lean:246` (`productFormula_finsupp`). -/
theorem productFormula_globalScalar (f : Fˣ) :
    (principalDivisorFinite f).sum (fun v n =>
        (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
      + ∑ w : NumberField.InfinitePlace F,
          (NumberField.InfinitePlace.mult w : ℝ) * archimedeanPlaceValue w f = 0 :=
  productFormula_finsupp (F := F) f

/-- **Equal-weight form**: finite weighted sum = archimedean log sum.
Re-export of `Example36ProductFormula.lean:271`. -/
theorem weightedFiniteSum_eq_archimedeanLogSum_globalScalar (f : Fˣ) :
    (principalDivisorFinite f).sum (fun v n =>
        (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
      = ∑ w : NumberField.InfinitePlace F,
          (NumberField.InfinitePlace.mult w : ℝ) * Real.log (w (f : F)) :=
  weightedFiniteSum_eq_archimedeanLogSum (F := F) f

/-! ## 2. Minimal Arakelov degree interface on explicit divisors -/

/-- The global prime-strip weight on explicit divisors, as a real-valued function. -/
noncomputable def arakelovDegree (d : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  globalPrimeStripWeight (F := F) d

/-- The same degree as an additive homomorphism (interface consistency). -/
noncomputable def arakelovDegreeHom :
    SourceModelBackend.ExplicitDivisor F →+ ℝ :=
  globalPrimeStripWeightHom (F := F)

/-- The concrete function is the additive homomorphism (definition consistency). -/
theorem arakelovDegree_eq_hom (d : SourceModelBackend.ExplicitDivisor F) :
    arakelovDegree (F := F) d = arakelovDegreeHom (F := F) d := rfl

/-- Additivity of the Arakelov degree interface. -/
theorem arakelovDegree_add (d e : SourceModelBackend.ExplicitDivisor F) :
    arakelovDegree (F := F) (d + e) =
      arakelovDegree (F := F) d + arakelovDegree (F := F) e := by
  unfold arakelovDegree
  exact map_add (globalPrimeStripWeightHom (F := F)) d e

/-- Zero of the Arakelov degree interface. -/
theorem arakelovDegree_zero :
    arakelovDegree (F := F) (0 : SourceModelBackend.ExplicitDivisor F) = 0 := by
  unfold arakelovDegree
  exact map_zero (globalPrimeStripWeightHom (F := F))

/-- **Scalar term vanishes**: the Arakelov degree of the explicit principal divisor of
a global unit is zero (product formula).  Re-export of
`Example36ProductFormula.lean:387`. -/
theorem arakelovDegree_principalUnit (f : Fˣ) :
    arakelovDegree (F := F)
      (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) = 0 := by
  unfold arakelovDegree
  exact globalPrimeStripWeight_principalDivisorExplicit (F := F) f

/-! ## 3. Degree difference formula -/

/-- The degree difference of two explicit divisors. -/
noncomputable def arakelovDegreeDifference
    (d₁ d₂ : SourceModelBackend.ExplicitDivisor F) : ℝ :=
  arakelovDegree (F := F) d₁ - arakelovDegree (F := F) d₂

/-- **Degree difference formula (additive form)**: the difference is the degree of the
difference divisor. -/
theorem arakelovDegreeDifference_eq_add (d₁ d₂ : SourceModelBackend.ExplicitDivisor F) :
    arakelovDegreeDifference (F := F) d₁ d₂ =
      arakelovDegree (F := F) (d₁ - d₂) := by
  unfold arakelovDegreeDifference arakelovDegree
  change globalPrimeStripWeightHom (F := F) d₁ - globalPrimeStripWeightHom (F := F) d₂
      = globalPrimeStripWeightHom (F := F) (d₁ - d₂)
  exact (map_sub (globalPrimeStripWeightHom (F := F)) d₁ d₂).symm

/-- **Degree difference against a principal divisor**: subtracting the principal divisor
of a global unit does not change the degree (product formula / scalar term vanishes). -/
theorem arakelovDegreeDifference_principalUnit
    (d : SourceModelBackend.ExplicitDivisor F) (f : Fˣ) :
    arakelovDegreeDifference (F := F) d
        (SourceModelBackend.principalDivisorExplicit (F := F) (Additive.ofMul f)) =
      arakelovDegree (F := F) d := by
  unfold arakelovDegreeDifference
  rw [arakelovDegree_principalUnit (F := F) f, sub_zero]

/-! ## 4. Local-weight expansion (normalization conventions recorded) -/

/-- The degree expanded in the finite/archimedean local weights (definitional). -/
theorem arakelovDegree_eq_localWeights (d : SourceModelBackend.ExplicitDivisor F) :
    arakelovDegree (F := F) d =
      d.1.sum (fun v n =>
          (n : ℝ) * Real.log ((finitePlaceResidueCardinality (F := F) v : ℝ)))
        + ∑ w : NumberField.InfinitePlace F,
            (NumberField.InfinitePlace.mult w : ℝ) * d.2 w := rfl

def productFormulaRows : List (String × String) :=
  [ ("productFormula_globalScalar", "finite + arch weighted sum = 0 (re-export :246)") ,
    ("weightedFiniteSum_eq_archimedeanLogSum_globalScalar", "equal-weight form (re-export :271)") ,
    ("arakelovDegree / arakelovDegreeHom", "minimal interface; function = hom (rfl)") ,
    ("arakelovDegree_add / _zero", "additivity/zero of interface (PROVED)") ,
    ("arakelovDegree_principalUnit", "scalar term vanishes (re-export :387)") ,
    ("arakelovDegreeDifference_eq_add", "difference = degree of difference divisor (PROVED)") ,
    ("arakelovDegreeDifference_principalUnit", "degree change by principal divisor = 0 (PROVED)") ,
    ("GAP-DEGREE-BRIDGE", "Example36 explicit divisor degree vs S2717/S2807 log-volumes: bridge not constructed") ,
    ("GAP-NORM-ARCH", "paper 1/(2l) and arch normalization not included") ]

theorem productFormulaRows_length : productFormulaRows.length = 9 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1ProductFormulaDegreeActual