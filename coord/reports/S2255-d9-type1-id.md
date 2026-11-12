# S2255: Type 1 Q hom equalizer identification — not constructed; P/R actual

Date: 2026-11-02. Status: Type 1 P and R sheaves are actual. The maps f,g and the
ULift iso to the equalizer are not constructed. The file only records the
remaining input; no fake, no IsStack claim.

## 1. Actual Type 1 halves

S2255P = S2251P: constant sign group sheaf on (Over S)^op, values Type 1,
proved sheaf.

S2255R = S2251R: representable morphism sheaf T |-> Hom(T.left, S1726AffineOver),
proved sheaf at Type 0.

## 2. Missing identification

For M N in Q.obj (op S), one must construct:

- ULift of the Type 0 Q hom-presheaf at Type 1;
- natural transformations f,g : P ⟶ R encoding g |-> g . P_T and g |-> Q_T;
- iso : ULift(Q.presheafHom M N) ≅ Limits.equalizer f g.

This is not done.  The main difficulty is extracting P_T and Q_T from the action
category values of S2152Q and proving naturality of f,g through the ULift
bridge.

## 3. First missing

The exact first missing is the Type 1 equalizer identification above.
The file currently records S2255Type1EqualizerIdentification as an abstract
placeholder; it does not construct the data.

## 4. Status

| Item | Status |
|---|---|
| Type 1 P sheaf | PROVED |
| Type 1 R sheaf | PROVED |
| ULift Q hom presheaf | not constructed |
| f,g | MISSING |
| iso to equalizer | MISSING |
| IsStack | not claimed |
| pointwise/label-only substitution | not used |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 86128dffe5312c3e988e7af900e07f0d2592849818f8e1118f894635dbeb2895
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2255QHomEqualizerType1IdActual.olean, size 12664
- axioms: propext, Classical.choice, Quot.sound.
