# Generic `SourcePilotRegionDataL` over arbitrary V: status (A965)

## State

Draft `tmp/sheaf/xif/paper/Mzk1SourcePilotLGenericActual.lean` is written but NOT compiling
(EXIT=1, no olean).  It contains a structure copy of S1391's `SourcePilotRegionDataL` with
`{V : Type uv} (I : OriginalInput l V)` and the S1391 opens; the structure parameterization
attempt is blocked (see below).

## Precise blocker (first errors)

After copying all S1391 opens, the remaining errors are at the fields

- `qUnitAlgClosure_eq`: `concreteQUnitAlgebraicClosure (I := I) place` and
  `ConcreteQAlgebraicClosure (I := I) place` — application type mismatch / unresolved
  implicit `I` (different metavariables for the two occurrences);
- `roots`/`roots'`: `NatRootSystem (concreteQUnitAlgebraicClosure ...)` same issue;
- the `attribute [instance]` lines fail because the structure did not elaborate.

Root cause: the S1391 helper definitions (`concreteQCandidate`, `concreteThetaPacket`,
`concreteQUnit`, `concreteQUnitAlgebraicClosure`, `ConcreteQAlgebraicClosure`,
`concreteRootsAlgebraicClosure`, `concreteRootsPrimeAlgebraicClosure`,
`actualC3KummerClass`, `actualC3RootChange`, `concreteActualTensorUnit`,
`concreteTensorLanding`, `C3LGalois`, `galoisRootsAction`) are specialized to the concrete
configuration `I : OriginalInput l (FinitePrimePlace 2 7)` (the file header even states the
L carrier is specialized to the actual concrete q unit).  Re-instantiating them at arbitrary
`V` requires generalizing those helpers first; the structure fields itself reference only
`I`, `place`, `Fmod` and the tensor block, but the concrete helper defs fix V.

## What is V-agnostic (would survive a proper generic helper layer)

The field *types* depend on V only through `I : OriginalInput l V`:
`p`, `place : FinitePlaceAtPrime (I.initial.arithmetic.Fmod) p`, `q`,
`qUnit`/`qUnit_eq`, the root systems over the algebraic closure, the Galois-indexed
Kummer class/root change, the tensor index/places/tuple/unit/landing.  The obstruction is
in the helper *values* (concrete instantiations), not in the field shapes.

## Conclusion

- Plain structure copy over arbitrary V: BLOCKED by specialized concrete helpers
  (`concreteQUnitAlgebraicClosure`/`ConcreteQAlgebraicClosure` first).
- No generic `actualSourcePilotRegionDataL` constructed; C3L cannot yet be attached to the
  generic `QPilotLineGenericCore`.
- Next step: parameterize the concrete helpers over `V` (or add them as explicit fields
  in the generic structure), then re-run the copy.
- No sorry/axiom; draft unregistered.
