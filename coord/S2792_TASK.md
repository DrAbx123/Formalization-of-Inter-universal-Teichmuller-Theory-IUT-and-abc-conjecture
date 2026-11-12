# S2792 region bound task

Finish in D:/lean with Lean 4.32.2 + Mathlib v4.32.2.

## Files
- tmp/sheaf/xif/paper/S2792NormalizedLineBundleBridge.lean
- tmp/sheaf/xif/paper/S2796SupportAbsNormLeRadSqActual.lean (ACTUAL)
- tmp/sheaf/xif/paper/S2752FinalHweightvolActual.lean (S2752J; S2752_hweightvol ACTUAL)
- tmp/sheaf/xif/paper/S2735QPilotLineBundleActual.lean (qPilotIdeal, qPilotFractional_absNorm, S2735Arithmetic; K := GaussianField by definition)
- tmp/sheaf/xif/paper/S2751ExtendedAbsNormActual.lean (S2751_extended_absNorm)

## Goals
1. define S2792D := (1/2)*Real.log((5*5*2161*2161 : Nat) : Real)
2. theorem S2792_regionVolume_le_weight_add_D (a b c) (habc : IsABCTriple a b c) :
     S2792RegionVolume a b c <= arithmeticWeight (abcRationalPoint a c) + S2792D
3. theorem S2792RegionWeightGap_actual (eps) (heps : 0 <= eps) : S2792RegionWeightGap eps
4. report EXIT, src SHA, olean SHA, axioms; no sorry/extra axioms.

## Route
- S2792RegionVolume = (1/2)*S2780RegionVolume.
- S2780RegionVolume = log absNorm(qPilotLineBundleExtended (S2752J ...)).
- qPilotLineBundleExtended J = ((qPilotIdeal * J : Ideal (SourceOK ...)) : FractionalIdeal ...).
- S2751_extended_absNorm: absNorm extended = absNorm qPilotIdeal * absNorm J.
- qPilotFractional_absNorm: absNorm qPilotIdeal = 5*5*2161*2161.
- S2796: Ideal.absNorm (supportIdeal K=GaussianField) <= (natRadical (a*b*c))^2; K defeq GaussianField; use coeIdeal_absNorm.
- log_mul positivity; Real.log_le_log; unfold arithmeticWeight / natRadical log relation.
- (1/2)(log A + log B) <= (1/2)(log A + 2*weight) = weight + D.

## Compile
lake env lean -j1 -R 'D:/lean' -o .lake/build/lib/lean/tmp/sheaf/xif/paper/<File>.olean tmp/sheaf/xif/paper/<File>.lean
