# S2285: R.map formula, f/g naturality and natural transformations actual

Date: 2026-11-02. Status: R.map formula is actual; f and g are actual natural
transformations P0 ⟶ R. The ULift equalizer iso remains missing. No fake, no
IsStack claim.

## 1. Actual results

File: tmp/sheaf/xif/paper/S2285RMapNatActual.lean

- S2285R_map_apply:
    (S2192R S).map p h = p.unop.left ≫ h
  (rfl, for h : S2267Point S T1).

- S2285f_natural:
    (S2192R S).map p (S2267fPoint S M T1 g) = S2267fPoint S M T2 g.
  Proof: R.map formula; S2267smul_eq; associativity; S2278PT_natural.

- S2285g_natural:
    (S2192R S).map p (S2267gPoint S N T1 g) = S2267gPoint S N T2 g.
  Proof: R.map formula; S2278QT_natural.

- S2285f : S2206P0 S ⟶ S2192R S, natural transformation with
  app T g = S2267fPoint S M T g.

- S2285g : S2206P0 S ⟶ S2192R S, natural transformation with
  app T g = S2267gPoint S N T g.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Remaining exact first missing

Construct

  S2152Q.presheafHom M N ≅ Limits.equalizer (S2285f S M) (S2285g S N)

(or its ULift version).  The pointwise subtype is known from S2271, but the
equalizer object value is not definitionally that subtype under the current
Limits.equalizer construction; a pointwise-limit comparison lemma is missing.

## 3. Status

| Item | Status |
|---|---|
| R.map formula | PROVED |
| f naturality | PROVED |
| g naturality | PROVED |
| f,g natural transformations | BUILT |
| equalizer object comparison | MISSING |
| equalizer iso | MISSING |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: cb10fb8051ac4d0a55037a289fb400cefb94132c803455a87848b9b4507e51ce
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2285RMapNatActual.olean, size 63520
- axioms: propext, Classical.choice, Quot.sound.
