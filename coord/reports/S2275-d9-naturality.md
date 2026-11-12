# S2275: naturality/equalizer final step — not completed; pointwise subtype re-exported

Date: 2026-11-02. Status: the pointwise subtype formula is re-exported actual.
The naturality of f,g and the ULift equalizer iso are not constructed. No fake,
no IsStack claim.

## 1. Actual re-export

S2275QHomObj_eq_subtype: re-export of S2271QHomObj_eq_subtype, i.e.

  (S2152Q.presheafHom M N).obj T =
    {g : SignGroup // g • S2267PT S M T = S2267QT S N T}.

## 2. Naturality attempt

The intended naturality square uses
  p : T1 ⟶ T2,
  p.unop.left ≫ P_T2 = P_T1
and the analogous formula for Q_T, followed by the R restriction map.

The explicit P_T/Q_T back formulas and the subtype formula are available, but the
orientation of R.map and the composition through the slice/ULift bridge were not
completed.  No naturality theorem is asserted.

## 3. Remaining first missing

- naturality of f,g as maps P ⟶ R;
- ULift(Q.presheafHom M N) ≅ Limits.equalizer f g.

## 4. Status

| Item | Status |
|---|---|
| pointwise subtype formula | PROVED (re-export) |
| P_T/Q_T | BUILT |
| pointwise f,g | BUILT |
| naturality | MISSING |
| ULift equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: 93429f11a57ef665fa8683a04a41447f33e3a4b8501161a4b6c4d40496c832c3
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2275QHomEqualizerFinal2Actual.olean, size 24000
- axioms: propext, Classical.choice, Quot.sound.
