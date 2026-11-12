# S2332: pointwise subtype presheaf Psub is actual

Date: 2026-11-02. Status: the direction issue is resolved: Psub with g |-> g is a
presheaf, with map p : Psub T1 -> Psub T2 using
p.unop.left ≫ P_T1 = P_T2 and the same for Q. The NatIso to Q.presheafHom is not
completed (eqToIso cast naturality). No fake, no IsStack claim.

## 1. Actual Psub

File: tmp/sheaf/xif/paper/S2332PsubCorrectActual.lean

S2332Obj S M N T :=
  {g : SignGroup // S2267fPoint S M T g = S2267gPoint S N T g}

S2332Psub : (Over S)^op ⥤ Type with

  obj T := S2332Obj S M N T
  map p h := ⟨h.1, proof⟩

The proof starts from h : Psub T1, i.e. h.1 • P_T1 = Q_T1, and derives
h.1 • P_T2 = Q_T2:
- p.unop.left ≫ P_T1 = P_T2 (S2278PT_natural);
- p.unop.left ≫ Q_T1 = Q_T2 (S2278QT_natural);
- action on the right: g • P = P ≫ aut g.

map_id/map_comp are rfl.

Axioms: propext, Classical.choice, Quot.sound.

## 2. Missing NatIso

S2332NatIso:
  S2152Q.presheafHom M N ≅ S2332Psub S M N
via NatIso.ofComponents (fun T => eqToIso (S2271QHomObj_eq_subtype ...)).
Naturality after ext x has the eqToIso casts between
(presheafHom).map p ≫ eqToIso.hom and eqToIso.hom ≫ Psub.map p; rfl fails.

## 3. Status

| Item | Status |
|---|---|
| Psub functor | PROVED |
| Psub map direction | RESOLVED |
| NatIso Q hom ≅ Psub | MISSING naturality (eqToIso casts) |
| IsStack | not claimed |
| axioms | propext, Classical.choice, Quot.sound |

## Verification

- EXIT=0
- SHA256: fb120b2ad08b569985bc246579281691b5b3f234d42cf594b70690eda4b3f3f0
- olean: D:\lean\.lake\build\lib\lean\tmp\sheaf\xif\paper\S2332PsubCorrectActual.olean, size 78952
- axioms: propext, Classical.choice, Quot.sound.
