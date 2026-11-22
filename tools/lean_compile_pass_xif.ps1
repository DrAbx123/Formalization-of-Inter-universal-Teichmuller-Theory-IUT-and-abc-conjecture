param()
$root = 'D:\lean'
$queue = Join-Path $root 'tmp\xif_compile_queue.txt'
$log = Join-Path $root 'tmp\xif_pass.log'
$results = Join-Path $root 'tmp\xif_pass_results.log'
$tmpOut = Join-Path $root 'tmp\xif_pass_last.out'
function Write-Log([string]$text) { $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'; Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text) }
if (-not (Test-Path -LiteralPath $queue)) { Write-Log 'queue missing'; exit 1 }
$lines = @(Get-Content -LiteralPath $queue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
Set-Content -LiteralPath $queue -Value ''
Write-Log ('pass started files=' + $lines.Count)
$seen = @{}
foreach ($raw in $lines) {
  $rel = $raw.Trim()
  if ([IO.Path]::IsPathRooted($rel)) { try { $rel = [IO.Path]::GetRelativePath($root, $rel) } catch {} }
  if ($seen.ContainsKey($rel)) { continue }
  $seen[$rel] = $true
  $file = Join-Path $root $rel
  if (-not (Test-Path -LiteralPath $file)) { Add-Content -LiteralPath $results -Value ('MISSING ' + $rel); continue }
  $olean = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel, 'olean'))
  try {
    & lake env lean -j1 -R $root -o $olean $file *> $tmpOut
    $code = $LASTEXITCODE
    Add-Content -LiteralPath $results -Value ('EXIT=' + $code + ' FILE=' + $rel)
    if (Test-Path -LiteralPath $tmpOut) { Get-Content -LiteralPath $tmpOut -Tail 60 | Add-Content -LiteralPath $results }
    Write-Log ('done EXIT=' + $code + ' FILE=' + $rel)
  } catch {
    Add-Content -LiteralPath $results -Value ('EXCEPTION FILE=' + $rel + ' ' + $_.Exception.Message)
    Write-Log ('exception FILE=' + $rel)
  }
}
Write-Log 'pass done'
