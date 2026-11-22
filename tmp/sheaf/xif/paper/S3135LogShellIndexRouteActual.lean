import tmp.sheaf.xif.paper.S3135HaarIndexActual

/-!
# task-66 route record: closing S3135LogShellScalingIndex via existing lattice-index tools

**Route record, not a paper object.**  Records the exact repo pointers for step (iii)
of the F4 (b1) index computation (the `p^{v(c)}` lattice-index shift), so the next
proof cycle starts from verified locations instead of searching.

Existing actual tools (citable, per Lead survey 2026-11-10):
* `LeanFormal/IUT/IUTII/Frobenioid/Example36LogShellLattice.lean:282`
  `concrete_measure_integralLogShell_eq_index_mul` (concrete completion form of the
  Haar index relation);
* `IntegralLogShellIndexArithmetic.lean:143`
  `measure_integralLogShell_eq_card_div_torsion_mul`, `:162`
  `integralLogShell_isometry_ringEquiv_symm`, `:181`
  `integralLogShellAddEquivOfRingEquiv`, `:194`
  `integralLogShell_map_integerSubgroup_eq`, `:238`
  `logShellIntegerIndex_eq_of_isometry_ringEquiv`;
* `IntegralLogShellHaarIndex.lean:51` `measure_integralLogShell_eq_index_mul`
  (already used in `S3135HaarIndexActual`);
* `IntegralLogShellIntegerQuotient.lean:56` `logShellIntegerIndex`, `:183`
  torsion*index identity; usage example `FinitePlaceLogShellDiscrepancy.lean:75`.

## Route for step (iii)

In the 1-dimensional normalized completion, identify `integralLogShell` with the
`Z_p`-lattice (`IntegralLogShellLattice.lean`) and compute the index of the scaled
lattice as the `Submodule`/`Ideal` index of the principal ideal `(p ^ v(c))` inside
`Z_p` (equivalently the ball-measure ratio if a p-adic ball measure lemma is
located).  This avoids needing a missing "measure of the scaled lattice" lemma.
Combined with the proved preimage-mass form
(`S3135ScalarFactorMassActual.s3135_scalarFactor_measure_preimage`) and the scalar
step (`S3135HaarUniquenessToolActual`), this pins `C = p ^ (-v(c)) = ||c||` and
closes `S3135LogShellScalingIndex`; then
`s3135_haar_normalized_of_unitScaling` gives `mu(lambda·O) = mu(O)`.

If the concrete case needs a named model datum (e.g. the ball-measure ratio in the
normalized completion), it will be stated as a minimal Prop with page references
(IUT III Proposition 3.9(i) p.115; Remark 3.9.5(i) pp.158-159) rather than faked.
-/

noncomputable section

open LeanFormal.IUT
open LeanFormal.IUT.XiFPaper.S3135HaarIndexActual

namespace LeanFormal.IUT.XiFPaper.S3135LogShellIndexRouteActual

/-- Route record for the `p^{v(c)}` lattice-index shift (F4 (b1) step iii). -/
def s3135LogShellIndexRoute : Audit.Obligation :=
  { id := "IUT-III.log-shell-scaling-index-route"
    source :=
      "IUT III Proposition 1.2; IUT III Proposition 3.9(i) p.115; IUT III Remark " ++
        "3.9.5(i) pp.158-159; IUT III Corollary 3.12 :10324-10353"
    status := Audit.VerificationStatus.interface
    note :=
      "ROUTE RECORD for S3135LogShellScalingIndex (the last F4 (b1) datum).  Closed " ++
        "already: preimage-mass form s3135_scalarFactor_measure_preimage (citable) + " ++
        "scalar step s3135_haarUniquenessScalarStep_proved (citable+probed).  Step " ++
        "(iii) lattice index p^{v(c)}: use the EXISTING actual tools " ++
        "Example36LogShellLattice.lean:282 " ++
        "concrete_measure_integralLogShell_eq_index_mul; " ++
        "IntegralLogShellIndexArithmetic.lean:143/162/181/194/238; " ++
        "IntegralLogShellHaarIndex.lean:51; IntegralLogShellIntegerQuotient.lean:56/183.  " ++
        "Concrete plan: identify integralLogShell as Z_p-lattice " ++
        "(IntegralLogShellLattice.lean) and compute Submodule/Ideal index of the " ++
        "principal ideal (p ^ v(c)) inside Z_p (or ball-measure ratio if a p-adic " ++
        "ball measure lemma exists) instead of a missing scaled-lattice measure lemma.  " ++
        "If a named model datum is needed it will be stated as a minimal Prop with " ++
        "pages (no faking).  Then s3135_haar_normalized_of_unitScaling closes (b1) and " ++
        "mu(lambda·O)=mu(O) follows; gate v4 will be a fresh re-pin (acceptance pkg " ++
        "settled: gate 22374 / registry 10314 / record 9503)."
    dependsOn := [ "IUT-III.cor312-to-ABC-conditional-interface" ]
    sorryItems :=
      [ "S3135LogShellScalingIndex (lattice index p^(-v c) = ||c||)",
        "S3135LogShellUnitSelfSimilarity (F4 b2)",
        "S3135ScalingLogDegreeZero (F4 b3)" ] }

#check s3135LogShellIndexRoute

end LeanFormal.IUT.XiFPaper.S3135LogShellIndexRouteActual
end
