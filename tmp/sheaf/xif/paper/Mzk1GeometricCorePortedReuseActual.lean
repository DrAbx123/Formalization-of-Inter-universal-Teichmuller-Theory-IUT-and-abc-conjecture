/-! # Mzk1GeometricCorePortedReuseActual — GeometricCore curve/finite-map layer via ported assets

STEP 0 prior-art (asset check 2026-11-10): ported FLT files exist raw in
tmp/external/ported/flt/Definitions/ (EXIT=0):
* Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean:19 structure FiniteMapData
(finite map to P^1 over base scheme; two-affine-open cover, ranges; :61-92 lemmas);
* Def_AlgebraicGeometry_SmoothProperCurveBase.lean: section base change;
* Def_AlgebraicCurve_RiemannRochRows.lean:19-47 RiemannInequality,
RiemannIndexFormula, WeilDualityAdelic, WeilDuality, WeilOmegaEllAgrees,
FunctionFieldRiemannRoch (Prop defs) + :54 functionFieldRiemannRoch_of_riemann_and_duality
+ :59 weilDuality_of_riemannIndex_of_adelic;
* Def_AlgebraicCurve_SerrePairing.lean (263 lines: residue terms, cup pairing, adelic
Serre duality fragments); Def_AlgebraicCurve_CechSectionsOfDivisor.lean;
Def_AlgebraicCurve_DivisorClassGroup.lean; Def_AlgebraicCurve_AdelicIndex.lean.
Tree status: S3171FLTAssetSupportActual:53 marks SmoothProperCurveFiniteMapData
'PENDING adaptation (raw only)'; S3171Step0RecordActual:37-38: RiemannRochRows/
SerrePairing/SmoothProperCurveFiniteMapData PENDING, NOT counted.  No edits to
ported files; no proof claimed.

PAPER: [Mzk1] Thm 2.5 lines 207-221; GeometricCore (S3136/Mzk1Theorem25Statement
Actual): for X smooth proper connected over Qbar and finite T with |T| >= 2g_X+1,
there is a finite morphism psi : X -> P^1_Q with psi(T) subset {0}, psi unramified
over 0, psi^*O(1) ~ O(sum_{t in T}[t]).

PLAN RECORDED HERE (class B; implementation target): state GeometricCore over the
ported `FiniteMapData` (finite map to P^1) + a rational-point/divisor layer, using
ported RiemannRochRows/SerrePairing/CechSectionsOfDivisor to formulate the
Riemann-Roch/Serre-duality inputs as Prop hypotheses (paper-input), then derive
psi with the required properties.  This file only records the reuse matrix and
the exact residual; it does NOT count as a proof. -/

namespace LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePortedReuseActual

structure Mzk1PortedAssetRow where
  geometricCorePart : String
  portedAsset : String
  status : String

def mzk1GeometricCorePortedAssets : List Mzk1PortedAssetRow :=
  [ ⟨"smooth proper connected curve X / finite map psi : X -> P^1", "Def_AlgebraicGeometry_SmoothProperCurveFiniteMapData.lean:19 structure FiniteMapData (finite map to P^1 over base) + Base file", "RAW ported; PENDING adaptation (S3171FLTAssetSupportActual:53); not counted"⟩,
    ⟨"divisor D = sum_{t in T} [t] and L = O(D)", "Def_AlgebraicCurve_DivisorClassGroup.lean / Def_AlgebraicCurve_CanonicalDivisor.lean", "RAW ported; adapt"⟩,
    ⟨"sections of L: H^0 via Cech", "Def_AlgebraicCurve_CechSectionsOfDivisor.lean", "RAW ported; adapt"⟩,
    ⟨"Riemann-Roch / Serre duality statements", "Def_AlgebraicCurve_RiemannRochRows.lean:19-47 (RiemannInequality, RiemannIndexFormula, WeilDuality, FunctionFieldRiemannRoch) + SerrePairing.lean", "RAW ported as Prop defs; PENDING adaptation; usable as STATEMENT layer for GeometricCore hypotheses"⟩,
    ⟨"basepoint-free linear system + separability of points s0,s1", "NOT in ported assets (requires scheme-level linear systems API)", "MISSING (adaptation target)"⟩,
    ⟨"finite morphism from basepoint-free pencil (psi^*O(1) ~ O(D))", "NOT in ported assets (requires Picard/line bundle morphism API)", "MISSING (adaptation target; this is the heart of GeometricCore)"⟩,
    ⟨"unramifiedness over 0 from reduced D", "NOT in ported assets (local-etale/unramified morphism API)", "MISSING (Mathlib has unramified morphisms of schemes, needs assembly)"⟩ ]

theorem mzk1GeometricCorePortedAssets_length : mzk1GeometricCorePortedAssets.length = 7 := rfl

/-- Ordered adaptation plan (data): which ported file feeds which GeometricCore step. -/
def mzk1GeometricCoreAdaptationPlan : List (String × String) :=
  [ ("step 1", "adapt FiniteMapData/Base: target type for psi : X -> P^1; keep raw ported file untouched, wrap in a local structure"),
    ("step 2", "adapt CechSectionsOfDivisor: express H^0(X, L) and the two sections s0,s1 as data"),
    ("step 3", "state RiemannInequality/RiemannIndexFormula/Serre as Prop hypotheses (paper-input, class B) via RiemannRochRows/SerrePairing"),
    ("step 4", "derive basepoint-free pencil (paper: H^1(X,L(-x))=0 via Serre duality + degree bound) — the genuine deep step"),
    ("step 5", "construct psi with psi^*O(1) ~ L (needs morphism/line bundle API — missing)"),
    ("step 6", "prove unramifiedness over 0 (local-etale API assembly)") ]

theorem mzk1GeometricCoreAdaptationPlan_length : mzk1GeometricCoreAdaptationPlan.length = 6 := rfl

#check mzk1GeometricCorePortedAssets_length
#check mzk1GeometricCoreAdaptationPlan_length

end LeanFormal.IUT.XiFPaper.Mzk1GeometricCorePortedReuseActual