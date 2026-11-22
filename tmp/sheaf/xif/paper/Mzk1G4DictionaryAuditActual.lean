/- Copyright (c) 2026 LeanFormal contributors. All rights reserved. -/

/-!
# A802 G4 dictionary audit: lana `SSIneq` vs our `BadSumWeightBound`

Read-only investigation, no fake proofs. The two predicates are structurally different:

* lana `Iut.Wall.SSIneq D` (Iut/Wall/MultiContainer.lean:88) is a SINGLE inequality
  `(sFactor (nC D) - 1) * D.qPilot.absLogQ ≤ logVol D (hullOf D (vcI D))`, for one
  concrete `InitialThetaData D`, with no epsilon and no quantification over triples;
* our `BadSumWeightBound T eN` (Mzk1Gap2ArithmeticReductionActual.lean:56) is an
  epsilon-constant family over ALL ABC triples,
  `∀ ε > 0, ∃ D, ∀ aN bN cN, IsABCTriple → Σ_b (eN ... b : ℝ) * d_b * log p_b
     ≤ (1+ε) * arithmeticWeight (abcRationalPoint aN cN) + D`,
  where `b : Bad (nativePlaceSelection T)`, `p_b = qVFamTensorP T b` is a natural prime
  and `d_b = finrank ℚ_[p_b] (rootNormedExtension T b)`.

## Obstacles to `SSIneq D ↔ BadSumWeightBound T eN`

O1 (quantifier shape): `SSIneq` is one fixed inequality, `BadSumWeightBound` is a
   uniform `ε`-family over all triples. Any bridge needs an explicit normalization
   theorem converting `(sFactor (nC D) - 1) * absLogQ` into the weighted bad-sum
   coefficient, plus an ε-slack/constant comparison. No such theorem exists in either
   repository.
O2 (data mismatch): there is no Lean construction/equivalence between lana
   `InitialThetaData` (fields: number field, elliptic curve, prime ℓ, q-pilot data,
   container/vol/hull data) and our `SourceNativeInitialThetaData T` (fields:
   nativePlaceSelection, qVFamTensorP, rootNormedExtension, ...). The `q`-pilot of `D`
   is a single real `absLogQ`, while our LHS is a finite sum over the bad set of `T`.
   A dictionary needs: (i) a map between the data structures, (ii) an identification of
   `sFactor (nC D)` with the corrected-region coefficient, (iii) a per-prime expansion of
   `(sFactor - 1) * absLogQ` into `Σ_b eN_b d_b log p_b`.
O3 (`hfull` unsat for fixed T): the chain `BadSumWeightBound → ABC`
   (Mzk1Gap2ArithmeticTightnessActual.lean:57) uses
   `hfull : ∀ aN bN cN, IsABCTriple → aN+bN+cN+1 = ∏_b (qVFamTensorP T b)^(eN ... b)`.
   For FIXED `T` this is UNSATISFIABLE, proved in `Mzk1FinalConditionalVacuityActual`
   (`hfull_unsatisfiable`): take a prime P greater than every qVFamTensorP T b; the
   triple (1,(P-1)/2,(P+1)/2) has N = P, and the fixed-bad-set product cannot equal P.
   Hence `badSumWeightBound_implies_ABC` and the A703 final_conditional_ABC are VACUOUS
   as stated (already marked RETRACTED).

## Satisfiability per constructed T (what a corrected route needs)

For a T CONSTRUCTED from the triple/N one can satisfy `hfull`: choose the bad support
to be the prime factors of N = a+b+c+1 and `eN a b c b = v_p(N)`; then the product is N
by unique factorization. In that case the bad-sum with `d_b = 1` equals `log N`, and
`BadSumWeightBound` becomes `log N ≤ (1+ε) log rad(a*b*c) + D` for N = 2c+1, which is
exactly the ABC inequality up to `log 3` (cf. `logN_le_log_c_add_log3`). So per-N T makes
the chain non-vacuous, but the named input then restates ABC rather than following from
lana's `SSIneq`. A bridge from `SSIneq` would additionally need the per-prime expansion
of O2(iii) and the sFactor normalization.

## Status rows -/

namespace LeanFormal.IUT.XiFPaper.Mzk1G4DictionaryAuditActual

def g4Rows : List (String × String) :=
  [ ("SSIneq", "Iut/Wall/MultiContainer.lean:88; single inequality, fixed D"),
    ("BadSumWeightBound", "Mzk1Gap2ArithmeticReductionActual.lean:56; epsilon family over all triples"),
    ("direct iff", "NOT PROVED / structurally not available: O1-O3"),
    ("hfull fixed T", "UNSATISFIABLE (Mzk1FinalConditionalVacuityActual.hfull_unsatisfiable)"),
    ("hfull per-N T", "satisfiable by bad support = primeFactors N, eN = valuation"),
    ("residual route", "per-N T makes BadSumWeightBound = ABC restatement, not a corollary of SSIneq"),
    ("required bridge 1", "map InitialThetaData <-> SourceNativeInitialThetaData (does not exist)"),
    ("required bridge 2", "normalization theorem sFactor-1 = 2*ell*c_V and per-prime expansion"),
    ("required bridge 3", "per-N construction lemma for T with hfull (not formalized)"),
    ("scope", "audit only; no theorem of ABC; ABC gate NOT passed; no fake declarations") ]

theorem g4Rows_length : g4Rows.length = 10 := rfl

end LeanFormal.IUT.XiFPaper.Mzk1G4DictionaryAuditActual

/-! ### Axiom gates (top level) -/

#print axioms LeanFormal.IUT.XiFPaper.Mzk1G4DictionaryAuditActual.g4Rows_length