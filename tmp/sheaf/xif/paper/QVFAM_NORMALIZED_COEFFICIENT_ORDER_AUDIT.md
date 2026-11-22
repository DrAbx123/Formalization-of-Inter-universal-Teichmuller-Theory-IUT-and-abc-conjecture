# QVFamNormalizedCoefficient vs order(qVFamily): audit memo

Date: 2026-10-30. Task T (research / small experiment only; no target or definition change).

Files read:

* tmp/sheaf/xif/paper/TASK_LEDGER.md, tmp/sheaf/xif/paper/NOTATION_Q_UNDERLINES.md
* tmp/sheaf/xif/paper/QVFamNormalizedGeneratorSupplyActual.lean
* tmp/sheaf/xif/paper/QVFamTensorCoefficientActual.lean
* tmp/sheaf/xif/paper/QVFamPureFractionalScalingDataGapActual.lean,
  tmp/sheaf/xif/paper/QVFamPureFractionalScalingDataActual.lean
* tmp/sheaf/xif/paper/QVFamNormalizedCoefficientActual.lean,
  tmp/sheaf/xif/paper/QVFamNormalizedSupplyCoefficientActual.lean,
  tmp/sheaf/xif/paper/QVFamNormalizedCoefficientBridgeActual.lean,
  tmp/sheaf/xif/paper/QVFamCoefficientBridgeActual.lean,
  tmp/sheaf/xif/paper/QVPilotLatticeCoefficientPositiveActual.lean
* LeanFormal/IUT/Foundations/NumberField/LocalQParameter.lean,
  LeanFormal/IUT/Foundations/NumberField/FinitePlaces.lean
* LeanFormal/IUT/ABCBridge/Geometry/FinitePlaceNormalizedCompletion.lean,
  FinitePlaceNormalizedIntegers.lean, FinitePlaceCommonPrimeCompletion.lean,
  FinitePlacePadicScalarStructure.lean, FinitePlaceCompletionNormTransport.lean
* LeanFormal/IUT/IUTIII/Corollary312/ArithmeticQPilotLogVolume.lean,
  ArithmeticQPilotBaseChange.lean
* LeanFormal/IUT/IUTII/Frobenioid/Example36CompletionIsometry.lean,
  Example36CompletionNormFormula.lean, Example36LocalIdealValuation.lean
* LeanFormal/IUT/Foundations/AlgebraicGeometry/BaseScalarValuationRelation.lean
* Mathlib: Analysis/Normed/Unbundled/SpectralNorm.lean,
  NumberTheory/NumberField/Completion/FinitePlace.lean, Data/Int/WithZero.lean,
  Analysis/SpecialFunctions/Log/Base.lean

New artifacts:

* tmp/sheaf/xif/paper/QVFamNormalizedCoefficientOrderAuditActual.lean (compiles, EXIT=0)
* this memo

---

## 0. Verdict

NO. The supply-based coefficient is not the order in general.

Let

    c_norm := QVFamNormalizedGeneratorSupplyActual.qVFamNormalizedCoefficient T b
            = -logb_p ||qVFamNormalizedGenerator T b||,

with p = qVFamTensorP T b the rational prime under the actual F-place
place := qVFamTensorPlace T b = (nativeBadLift T).lift b.  Then

    c_norm = order(qVFamily T b) / e_v,          (spectral normalization)

where e_v = relativeRamificationIndex (k := Q) place is the ramification index
of the F-place over its rational prime.  Hence

    c_norm = order  <->  e_v = 1.

For contrast, the *canonical* (default valuation) completion norm gives

    c_can := -logb_p ||qVFamily.q||_canonical = order * f_v,

with f_v = relativeResidueDegree (k := Q) place.  So

    c_can = order  <->  f_v = 1,
    c_norm = c_can <-> e_v * f_v = 1 (place of degree 1, p completely split),
    c_norm / c_can = 1 / (e_v f_v) = 1 / [F_v : Q_p].

The order itself is recovered by the residue-norm normalization

    -log ||q||_canonical / log (residueNormBase place) = order,

which is already an unconditional theorem in the tree
(ArithmeticQPilotBaseChange.orderNormalizedMagnitude_eq_order).

CAUTION (naming collision): a second, unrelated definition with the same name
exists at tmp/sheaf/xif/paper/QVFamNormalizedCoefficientActual.lean:48:

    QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient := qVFamTensorCoefficient = order

which is equal to order by rfl.  That is a definition by fiat, not a
computation of any completion norm.  The supply-based definition is a different
number.  Any consumer that says 'qVFamNormalizedCoefficient = order' must use
the QVFamNormalizedCoefficientActual spelling (order-based), not the supply one.

---

## 1. Exact objects

* qVFamNormalizedGenerator T b : CommonPrimeCompletion (qVFamTensorPlaces T b () ())
    := (qVFamily T b).q   (QVFamNormalizedGeneratorSupplyActual.lean:56)
* qVFamNormalizedCoefficient T b : Real
    := -Real.logb (qVFamTensorP T b : Real) ||qVFamNormalizedGenerator T b||
    (QVFamNormalizedGeneratorSupplyActual.lean:66)
* order: LocalQParameter.lean:81, order p = Int.toNat p.exponent,
  exponent p = -Multiplicative.toAdd (WithZero.unzero (Valued.v p.q));
  exponent_pos gives order > 0.
* qVFamTensorP T b := (completionRationalPrime (qVFamTensorPlace T b)).val
  (QVFamTensorCoefficientActual.lean:51).

## 2. Which norm instance is actually used (verified)

Compiled probe with pp.all (#print of the definition from the .olean) shows the
norm application inside qVFamNormalizedCoefficient is

    @Norm.norm (CommonPrimeCompletion ...)
      (@NormedField.toNorm ... (@commonPrimeCompletionNormedField ...))

and commonPrimeCompletionNormedField is

    inferInstanceAs (NormedField (NormalizedCompletion place.val))

which is normalizedCompletionNontriviallyNormedField =
spectralNorm.nontriviallyNormedField (PadicScalarField place) (NormalizedCompletion place).
So the supply coefficient is the spectral (Q_p-normalized) norm.
This is now also a theorem (proved by rfl) in the new file:

    commonPrimeCompletion_norm_eq_spectralNorm :
      ||x|| = spectralNorm (PadicScalarField place) (NormalizedCompletion place) x.

By the same pp.all print, the default-norm coefficients use the other instance:

    @Norm.norm (Completion ...)
      (@NormedField.toNorm ... (@NumberField.HeightOneSpectrum.instNormedFieldValuedAdicCompletion ...))
(i.e. qVFamDefaultNorm in QVFamNormalizedCoefficientBridgeActual and
qVFamPureCoefficient in QVFamPureFractionalScalingDataGapActual).  The two
instances are genuinely different terms, so the 'norm-instance gap' is a real
mathematical distinction, not a notation accident.

## 3. The computation

(a) Canonical norm (unconditional, in tree):
    NumberField.FinitePlace.norm_def:  ||x||_can = toNNReal (absNorm_ne_zero v) (Valued.v x)
      = residueNormBase ^ (-nu(x));
    tree: ArithmeticQPilotBaseChange.qNorm_eq_residueNormBase_zpow,
          localLogMagnitude_eq_exponent_mul_log, localLogMagnitude_eq_order_mul_log,
          qOrder_cast_eq_exponent_cast.
    Therefore c_can = -log ||q||_can / log p = order * log(ResNorm)/log p
    = order * f_v (ResNorm = absNorm(place.maximalIdeal) = p^{f_v}).
    This is formalized unconditionally in the new file as
    qVFamDefaultCoefficient_eq_order_mul.

(b) Spectral norm (standard, but its formula is frozen in the tree):
    Mathlib's spectralNorm is the unique K-algebra norm extending the norm of
    the complete base field (spectralNorm_extends, spectralAlgNorm_mul,
    spectralNorm_unique, NormedAlgebra.norm_eq_spectralNorm).  Hence on
    F_v / Q_p it is the unique extension of the p-adic absolute value, so

      ||q||_sp = p ^ (-nu_p(q)) = p ^ (-order/e_v),   nu = completionValuationExponent,

    and c_norm = -logb_p ||q||_sp = order / e_v.

    The tree states exactly this as the frozen hypothesis
    NormValuationCompatible place e  (see section 5), whose spectral spelling
    is normValuationCompatible_iff_spectralNorm: for all units x,
    spectralNorm x = p ^ (-(nu(x)/e)).  With e = e_v and nu(q) = order > 0 it
    gives ||q||_sp = p^{-order/e_v}.

## 4. What is proved where (status)

UNCONDITIONAL, in the tree:

* qNorm_eq_residueNormBase_zpow, localLogMagnitude_eq_order_mul_log,
  orderNormalizedMagnitude_eq_order (ArithmeticQPilotBaseChange).
* qVFamNormalizedGenerator_norm, qVFamNormalizedCoefficient_pos
  (QVFamNormalizedGeneratorSupplyActual): ||g|| = p^{-c_norm}.
* qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio
  and qVFamNormInstanceGap / qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_iff
  (QVFamNormalizedCoefficientBridgeActual): exact ratio formula between the two
  normalizations.

UNCONDITIONAL, new file QVFamNormalizedCoefficientOrderAuditActual.lean (compiled):

* qVFamNormalizedCoefficient_eq_neg_of_norm : if ||g|| = p^x then c_norm = -x.
* qVFamNormalizedCoefficient_eq_order_iff_norm :
    c_norm = order <-> ||g|| = p ^ (-(order))   (the exact missing norm identity).
* qVFamNormalizedCoefficient_eq_order_of_norm : conditional equality.
* qVFamNormalizedCoefficient_eq_order_div_of_norm :
    if ||g|| = p ^ (-(order/e)) then c_norm = order/e.
* qVFamDefaultCoefficient_eq_order_mul : the canonical coefficient equals
    order * (log (residueNormBase place) / log p), i.e. order * f_v.
* commonPrimeCompletion_norm_eq_spectralNorm : the instance is the spectral norm.

CONDITIONAL / MISSING (the only remaining input):

* NormValuationCompatible place e_w, equivalently the frozen card
  normalizedCompletionNormValuationFormulaCard
  (LeanFormal/IUT/IUTII/Frobenioid/Example36CompletionNormFormula.lean):
  the normalized spectral norm is the canonical norm raised to 1/(e_w f_w),
  i.e. ||x|| = p^{-nu(x)/e_w}.  The tree does NOT prove it; its own card says
  this is the missing step.  Nothing in this task assumes or fakes it.

FALSE TARGETS (do not attempt):

* c_norm = order (equivalently QVFamNormalizedCoefficientGap in the supply file
  or QVFamNormInstanceGap in the bridge file) is false whenever e_v f_v > 1:
  c_norm = order/e_v and c_can = order*f_v.  In particular the supply file's
  'remaining exact object-level gap' is not a missing theorem but a false
  identification for every place of local degree > 1.
* c_norm = c_can is false unless e_v f_v = 1.

Proof route if one wants to close the frozen card (not done here):

1. Show that x |-> ||x||_can ^ (1/d), d = [F_v : Q_p] = e_v f_v, is a
   power-multiplicative Q_p-algebra norm on F_v extending the p-adic norm:
   multiplicativity from log-additivity; nonarchimedean from ultrametricity;
   extension on Q_p from BaseScalarValuationRelation.upperPrimeValuation
   (v(p) = exp(-e)) plus scalarPrime_norm (||p||_p = p^{-1}); d = finrank
   from the tree's RelativeCompletionFinrankReduction
   (Module.finrank Q_p F_v = e*f).
2. Apply Mathlib spectralNorm_unique / spectralNorm_unique_field_norm_ext to
   identify it with spectralNorm.
3. Then NormValuationCompatible holds, and
   qVFamNormalizedCoefficient_eq_order_div_of_norm (new file) gives c_norm = order/e_v.
Alternative: spectralNorm_eq_norm_coeff_zero_rpow (coeff 0 of minpoly =
+/- norm of q) plus norm compatibility; heavier.

## 5. Theorem name index

Mathlib:

* Analysis/Normed/Unbundled/SpectralNorm.lean:
  spectralNorm, spectralNorm_extends, spectralNorm.eq_of_tower,
  spectralNorm_unique, spectralNorm_unique_field_norm_ext,
  spectralAlgNorm, spectralAlgNorm_mul, isPowMul_spectralNorm,
  isNonarchimedean_spectralNorm, spectralNorm_eq_norm_coeff_zero_rpow,
  NormedAlgebra.norm_eq_spectralNorm, spectralNorm.nontriviallyNormedField,
  spectralNorm.normedField, spectralNorm.normedAlgebra, spectralNorm.completeSpace.
* NumberTheory/NumberField/Completion/FinitePlace.lean:
  NumberField.FinitePlace.norm_def, instNormedFieldValuedAdicCompletion,
  instRankOneAdicCompletion, rankOne_hom'_def, adicAbv_def,
  toNNReal_valued_eq_adicAbv.
* Data/Int/WithZero.lean: WithZeroMulInt.toNNReal, toNNReal_neg_apply,
  toNNReal_strictMono.
* Analysis/SpecialFunctions/Log/Base.lean: Real.logb, Real.logb_rpow,
  Real.rpow_logb, Real.logb_eq_iff_rpow_eq, Real.logb_self_eq_one.
* Mathlib Analysis/Normed/Field/Basic.lean: AbsoluteValue.toNormedField.

LeanFormal:

* NumberFieldFinitePlace: Completion, NormalizedCompletion,
  normalizedCompletionRingEquiv, normalizedCompletionNontriviallyNormedField,
  normalizedCompletionHomeomorph, normalizedCompletion_norm_le_one_iff,
  normalizedCompletion_norm_lt_one_iff, CommonPrimeCompletion,
  commonPrimeCompletionNormedField, completionRationalPrime, PadicScalarField,
  relativeRamificationIndex, relativeResidueDegree, relativeCompletionDegree,
  absNorm_eq_pow_relativeResidueDegree, norm_algebraMap_pow.
* ArithmeticQPilotLogVolume: localSignedLog, localLogMagnitude, qNorm_lt_one.
* ArithmeticQPilotBaseChange: residueNormBase, qNorm_eq_residueNormBase_zpow,
  localLogMagnitude_eq_exponent_mul_log, localLogMagnitude_eq_order_mul_log,
  qOrder_cast_eq_exponent_cast, orderNormalizedMagnitude,
  orderNormalizedMagnitude_eq_order, log_residueNormBase_eq_residueDegree_mul,
  residueNormBase_eq_lower_pow.
* Example36CompletionIsometry: normalizedCompletion_norm_eq_spectralNorm,
  padicAlgCl_norm_eq_spectralNorm, minpoly_algHom_eq, spectralNorm_algHom_eq,
  imageLogNorm_value, imageLogNormCompatible_iff_normValuation,
  imageLogNormCompatible_ramification.
* Example36CompletionNormFormula: NormValuationCompatible,
  normValuationCompatible_iff_rpow, normValuationCompatible_iff_spectralNorm,
  normalizedCompletion_spectralNorm_algebraMap, NormalizedCompletionNormValuationFormula,
  normalizedCompletionNormValuationFormulaCard (Audit Obligation).
* Example36LocalIdealValuation: completionValuationExponent,
  completionValuationExponent_eq_neg_log, completionValuationAdd,
  completionValuationAdd_eq_log.
* BaseScalarValuationRelation: upperPrimeValuation, scalarPrime_norm,
  padicUnit_norm_one, baseScalarValuationRelation.
* QVFamNormalizedGeneratorSupplyActual: qVFamNormalizedGenerator,
  qVFamNormalizedCoefficient, qVFamNormalizedGenerator_norm,
  qVFamNormalizedGenerator_norm_lt_one, qVFamNormalizedCoefficient_pos,
  QVFamNormalizedCoefficientGap.
* QVFamNormalizedCoefficientBridgeActual: qVFamNormalizedNorm,
  qVFamDefaultNorm, qVFamNormRatio, QVFamNormInstanceGap,
  qVFamNormalizedCoefficient_mul_log_eq_neg_log_norm,
  qVFamNormalizedCoefficient_mul_log_eq_order_mul_log_residueNormBase_sub_log_ratio,
  qVFamNormalizedCoefficient_mul_log_eq_localLogMagnitude_iff.
* QVFamNormalizedCoefficientOrderAuditActual (new): the theorems listed in
  section 4.

## 6. Consequences for the tree

1. The order-based definition QVFamNormalizedCoefficientActual.qVFamNormalizedCoefficient
   (= order by rfl) and the supply-based definition are different numbers and
   must not be used interchangeably.  Consumers of the paper coefficient
   (qVFamPaperRootCoefficient = order/(2l), qVFamilyLatticeCoefficient =
   order * f * basePLogCoefficient) are built on the order-based /
   canonical-log normalization, not on the spectral one.
2. The spectral coefficient order/e_v is the right coefficient for the
   tensor constructor when the generator is the qVFamily q itself in
   CommonPrimeCompletion, because that constructor demands
   ||generator|| = p^{-c} (arithmeticTuplePureFractionalScalingData_ofGenerator).
   It is NOT the paper q-pilot coefficient.
3. The bridge file's conditional equality is the honest form: the two
   normalizations agree iff QVFamNormInstanceGap, which is false for every
   place of local degree > 1 (given the standard norm formula).
4. Do not try to prove c_norm = order or to discharge
   QVFamNormalizedCoefficientGap; record the exact factor e_v instead.
   If a genuinely unconditional statement is wanted, the available one is
   c_norm * log p = order * log(residueNormBase) - log(ratio) (tree bridge
   theorem) together with the factor identities above.

## 7. Compile / verification status

* QVFamNormalizedCoefficientOrderAuditActual.lean: statement_compiles = yes,
  proof_body_checked = yes (lake env lean, EXIT=0, no warnings, no sorry).
  Axiom check (#print axioms) of all five main results: propext,
  Classical.choice, Quot.sound only.  Not added to LeanFormal.Project
  (audit file), so target_accepted = n/a.
* Instance check: pp.all print of the compiled olean (evidence above) plus
  the rfl theorem commonPrimeCompletion_norm_eq_spectralNorm.
* The mathematical statement c_norm = order/e_v is NOT a Lean theorem of the
  tree; it is conditional on the frozen NormValuationCompatible card.  It is
  mathematically true by the uniqueness of the extension of the p-adic
  absolute value to the completion (Mathlib spectralNorm theory).
* No full Project build was run (out of scope, per task).

## 8. One-line summary for the parent

The supply coefficient is the SPECTRAL -log_p norm, hence order/e_v, not
order; the order-based coefficient named the same way is a different object
(= order by definition).  Spectral = order/e_v, canonical = order*f_v,
order only after residue-norm normalization.  The missing Lean input is
NormValuationCompatible (frozen card normalizedCompletionNormValuationFormulaCard).
