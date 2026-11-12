# S2147: M2c prosolvable shortcut audit

Layer: O (M2c commutator closedness).
Source object: G_L = Gal(Qbar_p/L), prosolvable local absolute Galois group; commutator closure.
Domain: profinite group theory / M2c.
Direction: audit of a prosolvable shortcut; no unconditional M2c claimed.

FINDINGS:
- G_L is prosolvable (local field with finite residue field), but no elementary prosolvable commutator-closed theorem is available/formalized in the tree.
- The effective sharp input remains bounded commutator width (S2116 CommutatorWidthInput), which implies commutator closedness via the compact image of commutatorWord.
- The f.g. + Nikolov-Segal width inputs are precisely S2116 TopologicallyFinitelyGenerated and NikolovSegalCommutatorWidth; the prosolvable route does not remove them in the current formalization.
- No literature theorem of the form 'finitely generated prosolvable => commutator subgroup closed' was located; standard closure results go through bounded width / Nikolov-Segal (and Segal's closed-subgroup theory).

BUILT:
- S2147M2cCommutatorClosedRequired := M2cFirstMissing.
- S2147ProsolvableShortcutRequired := CommutatorWidthInput.
- S2147_shortcut_sufficient: width input -> M2cFirstMissing.
- S2147TopologicallyFGRequired and S2147NikolovSegalWidthRequired aliases.
- S2147_m2c_of_nikolovSegal: named deep inputs -> M2cFirstMissing.

MISSING exact: an unconditional prosolvable commutator-closed theorem, or the two S2116 deep inputs. No fake; M2c not claimed unconditional.

Lean: tmp/sheaf/xif/paper/S2147M2cProsolvableActual.lean
EXIT=0; SHA256 0B5ABB729FB04FDF39A74A2C022A3D3A69F4A0971CB82E7C46BA3450E36985CE
olean: D:/lean/.lake/build/lib/lean/tmp/sheaf/xif/paper/S2147M2cProsolvableActual.olean
olean SHA256: B6C3D379BDFEA2F5F885A185D43B9DD0765E7026830CBB8807D17A01A6DCD411
axioms: propext, Classical.choice, Quot.sound (no sorryAx).