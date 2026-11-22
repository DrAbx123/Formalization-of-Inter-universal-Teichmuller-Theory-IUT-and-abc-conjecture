param([int]$PollSeconds = 10, [int]$FileTimeoutSeconds = 600)
$root = 'D:\lean'
$queue = Join-Path $root 'tmp\xif_compile_queue.txt'
$log = Join-Path $root 'tmp\xif_watchdog2.log'
$results = Join-Path $root 'tmp\xif_compile_results2.log'
$tmpOut = Join-Path $root 'tmp\xif_compile_last.out'
$tmpErr = Join-Path $root 'tmp\xif_compile_last.err'
function Write-Log([string]$text) { $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'; Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text) }
Write-Log 'xi-f queue watchdog2 started'
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
        Remove-Item -LiteralPath $tmpOut,$tmpErr -ErrorAction SilentlyContinue
        $proc = Start-Process -FilePath 'lake' -ArgumentList @('env','lean','-j1','-R',$root,'-o',$olean,$file) -WorkingDirectory $root -NoNewWindow -PassThru -RedirectStandardOutput $tmpOut -RedirectStandardError $tmpErr
        $exited = $proc.WaitForExit($FileTimeoutSeconds * 1000)
        if (-not $exited) { try { $proc.Kill() } catch {}; $code = -999 } else { $code = $proc.ExitCode }
        Add-Content -LiteralPath $results -Value ("EXIT=" + $code + " FILE=" + $rel)
        if (Test-Path -LiteralPath $tmpOut) { Get-Content -LiteralPath $tmpOut -Tail 200 | Add-Content -LiteralPath $results }
        if (Test-Path -LiteralPath $tmpErr) { Get-Content -LiteralPath $tmpErr -Tail 200 | Add-Content -LiteralPath $results }
        Write-Log ("DONE EXIT=" + $code + " FILE=" + $rel)
      }
    }
  }
  Start-Sleep -Seconds $PollSeconds
}
