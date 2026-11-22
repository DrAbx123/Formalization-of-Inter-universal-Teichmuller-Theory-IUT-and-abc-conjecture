$p='dag/watchdog/extra-targets.txt'
$lines = Get-Content $p
$parked = @(
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/AdicCompletionFractionField.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiResidueRingFinite.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiIntegralModelMinimality.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiMinimalModelCriterion.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiMinimalModelConverse.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiUniformizerAbsorptionFinal.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiReductionSpecialFiber.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiReductionModelComparison.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiGradedRingActual.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiActualMinimalModelReduction.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiCorrectedReductionSpecialFiber.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiIntegralModelReduction.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiReductionActualConstruct.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiReductionTypeActual.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiStableReductionFinal.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiStableReductionFinalConsumer.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiStableReductionFromSource.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiIntegralModel.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiActualMinimalModelInhabited.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiActualMinimality.lean',
 'LeanFormal/IUT/Foundations/AlgebraicGeometry/SourcePsiMinimalModelUniqueness.lean'
)
$kept = $lines | Where-Object { $parked -notcontains $_.Trim() }
Set-Content -Path $p -Value $kept -Encoding utf8
Write-Output ('before=' + $lines.Count + ' after=' + $kept.Count)
