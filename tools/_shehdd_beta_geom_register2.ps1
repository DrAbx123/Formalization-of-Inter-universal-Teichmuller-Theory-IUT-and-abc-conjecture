$f='coord/target-chain.routes.json'
$j = Get-Content $f -Raw | ConvertFrom-Json
$node = $j.nodes | Where-Object { $_.id -eq 'routes:problemC_nested_betaTrack' }
if ($node) {
  $nf1='tmp/sheaf/xif/paper/Mzk1NestedInductionBetaTrackingActual.lean'
  $nf2='tmp/sheaf/xif/paper/Mzk1NestedInductionBetaTrackingGeometricActual.lean'
  $node.declarations.$nf2 = @('BetaTrackingGeometricData','BetaTrackingGeometricInput','betaTrackingStepProvider_of_geometric','paperScopeLemma24Statement_of_geometric')
  $j | ConvertTo-Json -Depth 10 | Set-Content $f -Encoding utf8
  Write-Output 'declarations updated'
} else { Write-Output 'node missing' }
