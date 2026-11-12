# S2055: actual completion QPlace integral-units carrier

Date: 2026-11-02. Layer O. No reduced/Q_p-model substitution.

## Built actual

File: tmp/sheaf/xif/paper/S2055CompletionIntegralUnitsActual.lean
Source SHA256 c541028886ce2c249f4d1bb71844a05c6795e7e07eae52f1bb7ded992efc611c
olean SHA256 b5e84bb5608116b62e30e21281c9b4213d89783c7a01216c36a09f7fb3fa3f5e
EXIT=0. Axioms [propext, Classical.choice, Quot.sound].

For place : NumberField.FinitePlace Q:

- S2055CompletionIntegralUnits place
    := (Integers (SourceAlgebraicClosure place))^x
  the actual units of the integral ring of the spectral-norm algebraic closure
  (not all units of the field; this replaces the S2035 all-units carrier).
- S2055CompletionIntegralUnits_nonempty : Nonempty.
- S2055CompletionOUnitsMu place := TimesMuQuotient (S2055CompletionIntegralUnits place),
  with S2055CompletionOUnitsMu_nonempty.
- Exact missing identification target:
  S2055IntegralUnitsIdentificationRequired place
    := S2055CompletionIntegralUnits place ≃* S2055QpIntegralUnits place,
  where S2055QpIntegralUnits place :=
    (Integers (AlgebraicClosure Q_[completionRationalPrime place]))^x.
- Exact missing rebased input:
  S2055RebasedPaperInputRequired D := S1978RebasedPaperInput D.

## Why the identification is the first missing

S2035's algClosureEquiv is only a ring equivalence between algebraic closures;
it does not preserve the integral subring/spectral norm. The tree does have
spectralNorm_algHom_eq and completion-embedding isometry
(Example36CompletionIsometry), but no isometric algebraic-closure equivalence
with the Q_p model. Therefore the carrier itself is now actual, but the
completion-to-Q_p integral-units group identification is not constructed.

After that, S1978RebasedPaperInput D is the remaining rebased-paper-input
object. No reduced/Q_p model is claimed as paper O.

## Related

S2053PaperORootStackAlignment.lean aligns component (d) with
S2040RootStackThetaPilotObject:
source SHA256 7c458b1a00df21cad0c5b004cd568d7bd0771cd91e2d5c2a9bdcbf024a117efe,
olean SHA256 1d6674bcdb976ea2faece5668d2ff6b5215ec4e7afec6f471571bda9468e9daf,
EXIT=0, axioms [propext, Classical.choice, Quot.sound].
