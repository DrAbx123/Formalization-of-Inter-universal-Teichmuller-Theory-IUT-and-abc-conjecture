# C9 / P6 frozen readout no-go: exact analysis

## 1. Counterexample exact assumptions/conclusion
File: tmp/sheaf/n8/closure/P6AdmRedesign.lean and P6ArchimedeanAdmNoGo.lean.
Theorem P6AdmRedesign.frozenP6Readout_impossible_of_archimedean_at:
- v : NativePlaces X.S;
- hv : NumberFieldPlace.IsInfinite (NumberFieldPlace.comap (k := X.S.arithmetic.Fmod) v.1);
- [NormedSpace R (localFieldAt X v)], [FiniteDimensional R ...], [Nontrivial ...];
- [forall w, NullSingletonClass (mu w)] (wrapper; used for measure_singleton at 0).
Conclusion: not Nonempty (P6Readout (X:=X) (mu:=mu)), via noP6Readout_of_archimedean_at.
Core cause: Adm requires a.e. localLog = 0 at every place, but at an archimedean place
the unit sphere {||x||=1} has Haar mass zero (Mathlib addHaar_sphere), so no positive-mass
region can be a.e. supported on localLog=0. This refutes frozen Adm, not mathlib.

## 2. Is a weakened readout enough for C9?
Two actual weakenings exist:
A. P6NonarchAdmActual.finitePlaceAdm: Adm conditions only at IsFiniteNativePlace;
   unitSphereAt_ae_localLog_zero is actual; finitePlaceAdm_sphere_of_mass reduces to exact
   missing donor: forall finite v, 0 < mu v (unitSphereAt v) and mu v (unitSphereAt v) < top.
   This keeps the finite/nonarchimedean ellOut and excludes the archimedean contradiction.
B. P6AdmRedesign.RelaxedP6Readout: drops a.e. localLog=0 entirely; keeps measurable positive
   finite reference/region; actual under [forall v, ProperSpace (localFieldAt X v)]. It uses
   actual balls, weight/dimension from finite residue data, support {badPlace X}. Exists unconditionally
   (relaxedP6Readout_actual).

C9PaperClosure uses the readout only through ThetaNamed R = R.ellOutValue and ValuesNamed
(the set of R.ellOutValue). Therefore value-level C9 target is preserved by either weakening.
If paper C9 only needs finite/nonarchimedean places, A is closer to paper; if it allows
archimedean support but only a real signed ellOut value, B is the minimal actual replacement.
Neither reconstruction asserts the frozen Adm condition; this is a semantic correction, not a workaround.

## 3. Can C9PaperClosure named sorries be changed to the weak version?
- paperC9Output_nonempty: PaperC9Output = {chainA : P6ChainAData, theta : P6Readout, valuesWitness : P6Readout}.
  Replace theta/valuesWitness by RelaxedP6Readout (or by finitePlace readout). Then existence reduces to
  Nonempty (P6ChainAData X) plus Nonempty RelaxedP6Readout. Relaxed readout is actual; P6ChainAData
  still requires GlobalLqDonor, whose named sorry p6ChainA.globalLqDonor_nonempty remains. So readout
  weakening removes only the Theta/Values donor, not the Q/ChainA donor.
- paperC9Comparison: P6Exact/P6Epsilon over SourceAllowedOutput. It does not mention P6Readout at all.
  Changing readout does not affect this sorry. Exact remaining: Nonempty (SourceAllowedOutput X)
  (P6Comparison.sourceAllowedOutput_nonempty named sorry) plus the hull/ellOut comparison.
- p6SourceClosure_nonempty: contains chainA, chainB, hull, readout, sheInd, tensor, alphaIndex,
  comparison, sourceExists. Replacing readout removes one component; GlobalLqDonor, source allowed output,
  and comparison remain named obligations.

## Minimal correction plan (no fake)
1. Introduce a corrected C9 output record whose theta/values fields are RelaxedP6Readout; define
   Theta/Values from relaxed.value. This is a target correction at the readout type level.
2. Prove corrected output nonempty from Nonempty (P6ChainAData) and relaxedP6Readout_actual
   (requires ProperSpace all places).
3. Keep paperC9Comparison and P6 source-object existence as separate remaining obligations;
   do not claim they follow from readout weakening.
4. If paper semantics require only finite/nonarchimedean places, use finitePlaceAdm plus unitSphereAt;
   expose the exact missing finite-place unit-sphere positive finite Haar mass donor.
5. Do not assert or restore frozen P6Readout; the no-go is mathematically correct.

## Status
- frozen P6Readout: refuted at archimedean place (actual no-go).
- RelaxedP6Readout: actual under ProperSpace.
- finitePlaceAdm: actual structure, conditional only on finite unit-sphere mass.
- C9 Q/ChainA: GlobalLqDonor still named sorry.
- C9 comparison: SourceAllowedOutput still named sorry, independent of readout.
No fake.