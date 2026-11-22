$f='coord/target-chain.routes.json'
$j = Get-Content $f -Raw | ConvertFrom-Json
$newFile='tmp/sheaf/xif/paper/Mzk1NestedInductionBetaTrackingActual.lean'
$exists = $j.nodes | Where-Object { $_.id -eq 'routes:problemC_nested_betaTrack' }
if (-not $exists) {
  $node = [pscustomobject]@{
    id='routes:problemC_nested_betaTrack'
    kind='conditional'
    title='Paper-shaped beta-tracking StepProvider + assembly (Problem C)'
    status='CONDITIONAL'
    files=@($newFile)
    declarations=@{ $newFile=@('BetaTrackingStepProvider','paperScopeLemma24Statement_of_betaTrackingProviders') }
    note='NEW (shehdd): paper-shaped step provider (S'' independent of beta; beta'' with backward transport); assembly PROVED conditional on base + beta-tracking step; geometric construction NAMED. PENDING-VERIFY.'
  }
  $j.nodes = @($j.nodes) + $node
  $j.edges = @($j.edges) + [pscustomobject]@{ from='routes:problemC_nested_betaTrack'; to='routes:problemC_nested'; kind='statement' }
  $j | ConvertTo-Json -Depth 10 | Set-Content $f -Encoding utf8
  Write-Output 'node added'
} else { Write-Output 'node exists' }
$extra = Get-Content dag/watchdog/extra-targets.txt -ErrorAction SilentlyContinue
if ($extra -notcontains $newFile) { Add-Content dag/watchdog/extra-targets.txt -Value $newFile; Write-Output 'target added' } else { Write-Output 'target exists' }
