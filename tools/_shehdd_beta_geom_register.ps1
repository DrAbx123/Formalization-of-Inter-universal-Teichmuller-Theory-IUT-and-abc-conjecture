$f='coord/target-chain.routes.json'
$j = Get-Content $f -Raw | ConvertFrom-Json
$node = $j.nodes | Where-Object { $_.id -eq 'routes:problemC_nested_betaTrack' }
if ($node) {
  $newFile='tmp/sheaf/xif/paper/Mzk1NestedInductionBetaTrackingGeometricActual.lean'
  if ($node.files -notcontains $newFile) { $node.files = @($node.files) + $newFile }
  if (-not $node.declarations) { $node.declarations = @{} }
  $decls=@('BetaTrackingGeometricData','BetaTrackingGeometricInput','betaTrackingStepProvider_of_geometric')
  if ($node.declarations.PSObject.Properties.Name -contains $newFile) { $node.declarations.$newFile = $decls } else { $node.declarations | Add-Member -NotePropertyName $newFile -NotePropertyValue $decls -Force }
  $node.note = $node.note + ' PLUS geometric reduction: BetaTrackingGeometricData -> BetaTrackingStepProvider PROVED via stepTransport_of_goal (CV law); construction of data NAMED.'
  $j | ConvertTo-Json -Depth 10 | Set-Content $f -Encoding utf8
  Write-Output 'node updated'
} else { Write-Output 'node missing' }
