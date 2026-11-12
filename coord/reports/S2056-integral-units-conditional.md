# S2056/S2057: conditional integral-units equivalence and canonical norm bridge

Date: 2026-11-02. Layer O. Canonical carrier: S2055CompletionIntegralUnits.
No S2035 all-units carrier is used for PaperO.

## Actual files

S2056IsometricClosureActual.lean
Source SHA256 edd687328d09f96dd2edf7b65b15ffbcb2908c5875e19c2d12acaa0365b6b7ca
olean SHA256 e97e30a47b1fe3b56efd9fdd44fa69099414359832941064aab88a3e5031958e
EXIT=0.

S2057NormBridgeFromIsometry.lean
Source SHA256 f1dbbbe44916f1624e3019a8361c13ad7c98a6d9d5edc62909ca23a48c1cd910
olean SHA256 a735a1187a4618482bc0f85252ea80f33eb1db50f686e66958837e6051cbf2fb
EXIT=0.

Axioms for S2056IntegralUnitsEquiv, S2056IntegralUnitsIdentification_of_isometry,
S2057NormBridgeOfIsometry, S2057NormBridgeOfIsometry_available:
[propext, Classical.choice, Quot.sound].

## What is constructed

S2056ClosureIsometry place is the exact missing isometric closure equivalence:

  equiv : SourceAlgebraicClosure place ≃+* AlgebraicClosure Q_[p]
  norm_pres : forall x, ||equiv x|| = ||x||.

From it S2056 constructs an actual ring equivalence of the integer rings

  S2056IntegersRingEquiv :
    Integers (SourceAlgebraicClosure place) ≃+*
    Integers (AlgebraicClosure Q_[p])

using norm_pres to prove membership in Integers, hence

  S2056IntegralUnitsEquiv :
    S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place,

and S2056IntegralUnitsIdentification_of_isometry gives
Nonempty (S2055IntegralUnitsIdentificationRequired place).

S2057 then constructs the canonical S2046NormBridge v from
S2056ClosureIsometry (QPlace v): identification := S2056IntegralUnitsEquiv,
muCompatible := QuotientGroup.congr on the torsion subgroups.
It does not introduce a new carrier.

## Exact remaining missing

S2056ClosureIsometry (QPlace v): an actual isometric algebraic-closure
equivalence. The tree has ring equivalences (algClosureEquiv) and
spectralNorm_algHom_eq/completion isometry, but no equivalence that both maps
Integers to Integers and preserves the norm. Once this is constructed, the
integralUnitsEquiv and S2046NormBridge follow without further missing input.

Rebased paper input S1978RebasedPaperInput D remains the next paper-level object.
