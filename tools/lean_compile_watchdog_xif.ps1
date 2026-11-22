param([int]$PollSeconds = 10)
$root = 'D:\lean'
$queue = Join-Path $root 'tmp\xif_compile_queue.txt'
$log = Join-Path $root 'tmp\xif_watchdog.log'
$results = Join-Path $root 'tmp\xif_compile_results.log'
function Write-Log([string]$text) { $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'; Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text) }
Write-Log 'xi-f queue watchdog started'
while ($true) {
  if (Test-Path -LiteralPath $queue) {
    $lines = @(Get-Content -LiteralPath $queue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
    if ($lines.Count -gt 0) {
      Set-Content -LiteralPath $queue -Value ''
      $seen = @{}
      foreach ($raw in $lines) {
        $rel = $raw.Trim()
        if ([IO.Path]::IsPathRooted($rel)) { try { $rel = [IO.Path]::GetRelativePath($root, $rel) } catch {} }
        if ($seen.ContainsKey($rel)) { continue }
        $seen[$rel] = $true
        $file = Join-Path $root $rel
        if (-not (Test-Path -LiteralPath $file)) { Add-Content -LiteralPath $results -Value ("MISSING " + $rel); Write-Log ("MISSING " + $rel); continue }
        $olean = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel, 'olean'))
        Write-Log ("COMPILING " + $rel)
        $out = & lake env lean -j1 -R $root -o $olean $file 2>&1
        $code = $LASTEXITCODE
        Add-Content -LiteralPath $results -Value ("EXIT=" + $code + " FILE=" + $rel)
        if ($out) { $out | Add-Content -LiteralPath $results }
        Write-Log ("DONE EXIT=" + $code + " FILE=" + $rel)
      }
    }
  }
  Start-Sleep -Seconds $PollSeconds
}
