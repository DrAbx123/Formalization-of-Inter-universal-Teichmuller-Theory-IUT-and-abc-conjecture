# S2046 M1: exact bridge to corrected Otri p target

Layer: O (S2046 M1 / S2000 local integral monoid).
Source object: LocalIntegralMonoid.evaluatedUnitSubgroup p and (Integers (AlgebraicClosure Q_p))^x.
Domain: units of the actual local integral monoid.
Direction: actual conditional composition; exact bridge recorded.

BUILT:
- S2046EvaluatedUnitsToIntegersRequired: exact missing equivalence evaluatedUnitSubgroup p ≃* (Integers (AlgebraicClosure Q_p))^x.
- S2046OtriUnitsEquivEvaluated: actual library unitEvaluationEquiv (Otri p)^x ≃* evaluatedUnitSubgroup p.
- S2046LocalUnitsEquivOtriUnitsOfBridge: conditional actual (Otri p)^x ≃* LocalOFieldUnits p from the missing bridge.
- S2046LocalUnitsEquivOtriUnitsOfBridge_apply: actual computation rule.

MISSING exact: S2046EvaluatedUnitsToIntegersRequired (IsIntegral over Z_p versus norm≤1/Integers equivalence). The forward norm bound is available from localAlgebraicInteger_norm_le_one; the converse and the packaged unit equivalence are not yet constructed. No fake.

M4 H^2=Zhat remains missing.

Consumer: S2046 (b) corrected Otri p local units; S2046 action/PsiCns conditional reductions.

Lean: tmp/sheaf/xif/paper/S2046M1BridgeActual.lean
EXIT=0; SHA256 02B5D5598D2D56AC4816165C1D419655222D7EA0889DEB8731DA40F7FE85FF0D
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2046M1BridgeActual.olean
olean SHA256: 1657F7B1AEA560B587FF437ADE62ABB547CBE46EC115AC23121FE50674B1A232
axioms: propext, Classical.choice, Quot.sound (no sorryAx).