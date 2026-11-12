# S2849A6InputReductionActual — not actual; current first errors

Date: 2026-11-07. Current compile: EXIT=1, no olean.

```text
source 4788 B SHA F983296006B6220422D8268C4F1BCFB4F4F05FB7C353AE1E1DB21052DC040609
no olean
```

NOTE: the source changed while auditing (earlier 3745 B); errors below are for the
current 4788 B version.

## Error group 1 — `comap p` vs `p` is not definitional (lines 37-38)

```text
error: Not a definitional equality: comap p is not definitionally equal to p
error: rfl has type ?m = ?m but is expected to have type comap p = p
```

For A6, `F` and `Fmod` are not definitionally the same place type here; an
actual `comap`-identity/equality lemma is required instead of `rfl`.

## Error group 2 — bad-set membership type mismatch (line 55)

```text
error: rewrite failed: no occurrence of `comap ?p` in target
  p ∈ S2841PlaceSelection.V_mod_bad
Full error: argument p has type FinitePlace S2847A6.F
  but is expected to have type FinitePlace S2847A6.Fmod
```

The theorem quantifies `p : FinitePlace S2847A6.F`, but `V_mod_bad` is a set of
places of `Fmod`; the needed object is `comap p`, and the coercion cannot be
dropped. This is the central type blocker.

## Error group 3 — hp' / residue characteristic (lines 78, 87)

```text
error: hp' has type comap p = S2841Place but is expected p = S2841Place
error: rewrite failed: no occurrence of residueCharacteristic S2841PlaceF
  in target residueCharacteristic (comap S2841PlaceF) = 37
```

Both are downstream of group 1: substituting `p` for the Fmod place requires
the missing comap identity; the residue-characteristic rewrite must go through
`residueCharacteristic_comap` after that, not directly.

## Status

- S2849 NOT actual; EXIT=1, no olean.
- No citation until the comap/F-vs-Fmod type issue is fixed and a clean compile
  with axioms trio is produced.