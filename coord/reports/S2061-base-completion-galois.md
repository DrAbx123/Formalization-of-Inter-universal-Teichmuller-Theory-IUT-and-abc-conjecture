# S2061: base completion model and local absolute Galois bridge

Layer: O (IUT II Cor 4.10(ii); S2046 component (a)).
Source object: Base(QPlace v) = Completion(QPlace v), the rational completion
Completion(comap QPlace v), LocalAbsoluteGalois v.1 and Gv v.
Direction: explicit completion ring/Alg equivalence, algebraic-closure
comparison, and conjugation of automorphism groups.

## Built

- S2061BaseCompletionRingEquiv : Base(QPlace v) ≃+* Q_[v.1],
  an inhabitant of S2047BaseModelEquivRequired.
- S2061RationalCompletionModelEquiv :
  Completion(comap QPlace v) ≃A[Q] PadicScalarField (QPlace v),
  an inhabitant of S2047RationalCompletionModelEquiv.
- S2061ClosureEquiv :
  AlgebraicClosure (Base(QPlace v)) ≃+* AlgebraicClosure Q_[v.1],
  with S2061ClosureEquiv_compat and S2061ClosureEquiv_symm_compat
  (both from IsAlgClosure.equivOfEquiv).
- S2061S2047GaloisEquivOfBaseData : S2047GaloisEquivOfBaseData.
- S2061GaloisEquiv : LocalAbsoluteGalois v.1 ≃* Gv v, an inhabitant of
  both S2047GaloisEquivRequired and S2046GaloisEquivRequired (the latter
  through S2061S2046GaloisEquivRequired).

The exact typed aliases are S2061S2047BaseModelEquiv,
S2061S2047GaloisEquivOfBaseData, S2061S2047GaloisEquivRequired and
S2061S2046GaloisEquivRequired.

## Method

No global or local fake instance is installed.  The rational
adic-completion algebra structure is written as the explicit term
S2061AdicScalarAlgebra.  The non-definitional equality of the two rational
algebra structures is only used inside proofs through
Algebra.rat_algebra_subsingleton (and simp for the algebraMap), not as an
instance.  The input equivalence is Mathlib's actual
Padic.adicCompletionEquiv / Rat.HeightOneSpectrum.adicCompletion.padicEquiv;
the remaining place transport is RingEquiv.cast along
NumberField.FinitePlace.maximalIdeal_mk.  The algebraic closures are
identified by IsAlgClosure.equivOfEquiv; the Galois groups are conjugated by
that closure equivalence, and the compatibility lemmas are exactly the
linearity proofs.  No Q_p substitution or fake inhabitant is used.

## Verification

Lean: tmp/sheaf/xif/paper/S2061BaseCompletionGaloisActual.lean
EXIT=0; SHA256
412CE88A68EAA291266E9DDB91AE476166D40EB9D2F4815CC7687062748EB9F5
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2061BaseCompletionGaloisActual.olean
olean SHA256
1D0856D94825BA80649F005FE7B9516A48CA3471ADEAF7218B3D5972875A70C4
olean size: 276800 bytes.
axioms (all key declarations):
propext, Classical.choice, Quot.sound (no sorryAx).

Independent consumer tmp/sheaf/xif/paper/_S2061Consumer.lean checks the exact
S2047/S2046 types and the same axiom sets; EXIT=0.

Independent confirmations also exist in S2063BaseAlgebraBridgeActual
(base/rational/closure data) and S2064GaloisEquivActual (group level).  S2061
provides a single-file construction of all four S2047 targets.

Components (b)/(c) of S2046 (local-to-PsiCns and local-to-Gau) remain the
S2045/S2046 missing objects; this package closes only component (a).
