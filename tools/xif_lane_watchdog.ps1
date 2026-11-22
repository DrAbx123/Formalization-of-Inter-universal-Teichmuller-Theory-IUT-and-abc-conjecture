param([string]$Lane = 'paper', [int]$PollSeconds = 3, [int]$FileTimeoutSeconds = 900)
$root = 'D:\lean'
$queue = Join-Path $root ('tmp\xif_guarded_queue_' + $Lane + '.txt')
$log = Join-Path $root ('tmp\xif_guarded_watchdog_' + $Lane + '.log')
$results = Join-Path $root ('tmp\xif_guarded_results_' + $Lane + '.log')
function Write-Log([string]$text) { $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'; Add-Content -LiteralPath $log -Value ("[" + $stamp + "] [" + $Lane + "] " + $text) }
function Get-MissingDeps([string]$file) {
  $missing = @()
  $lines = Get-Content -LiteralPath $file -ErrorAction SilentlyContinue
  foreach ($line in $lines) {
    if ($line -match '^\s*import\s+([A-Za-z0-9_\.]+)') {
      $mod = $Matches[1]
      if ($mod -match '^(tmp|LeanFormal|Iut)\.') {
        $rel = ($mod -replace '\.', '/') + '.olean'
        $olean = Join-Path $root ('.lake\build\lib\lean\' + $rel)
        if (-not (Test-Path -LiteralPath $olean)) { $missing += $mod }
      }
    } elseif ($line -notmatch '^\s*$' -and $line -notmatch '^\s*(/-|--|#)') { break }
  }
  return $missing
}
function Remove-OneLine([string]$path) {
  $cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue)
  $removed = $false
  $new = @()
  foreach ($line in $cur) {
    if (-not $removed -and $line.Trim() -eq $path) { $removed = $true; continue }
    $new += $line
  }
  Set-Content -LiteralPath $queue -Value $new
}
function Dedupe-Queue {
  $cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
  $uniq = @($cur | Select-Object -Unique)
  if ($uniq.Count -ne $cur.Count) { Set-Content -LiteralPath $queue -Value $uniq }
}
Write-Log ('worker started queue=' + $queue)
while ($true) {
  if (Test-Path -LiteralPath $queue) {
    Dedupe-Queue
    $lines = @(Get-Content -LiteralPath $queue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
    if ($lines.Count -gt 0) {
      $raw = $lines[0].Trim()
      $rel = $raw
      if ([IO.Path]::IsPathRooted($rel)) { try { $rel = [IO.Path]::GetRelativePath($root, $rel) } catch {} }
      $file = Join-Path $root $rel
      if (-not (Test-Path -LiteralPath $file)) {
        Add-Content -LiteralPath $results -Value ("MISSING_FILE " + $rel)
        Write-Log ("MISSING_FILE " + $rel)
        Remove-OneLine $raw
      } else {
        $missing = @(Get-MissingDeps $file)
        if ($missing.Count -gt 0) {
          $m = $missing -join ','
          Add-Content -LiteralPath $results -Value ("MISSING_DEP FILE=" + $rel + " DEPS=" + $m)
          Write-Log ("MISSING_DEP " + $rel + " DEPS=" + $m)
          Remove-OneLine $raw
        } else {
          $olean = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($rel, 'olean'))
          $fresh = $false
          if (Test-Path -LiteralPath $olean) {
            $ole = Get-Item -LiteralPath $olean
            $src = Get-Item -LiteralPath $file
            if ($ole.LastWriteTime -ge $src.LastWriteTime) { $fresh = $true }
          }
          if ($fresh) {
            Add-Content -LiteralPath $results -Value ("SKIP_FRESH " + $rel)
            Write-Log ('SKIP_FRESH ' + $rel)
            Remove-OneLine $raw
          } else {
            Write-Log ('COMPILING ' + $rel)
            $tmpOut = Join-Path $root ('tmp\xif_direct_last_' + $Lane + '.out')
            $tmpErr = Join-Path $root ('tmp\xif_direct_last_' + $Lane + '.err')
            Remove-Item -LiteralPath $tmpOut,$tmpErr -ErrorAction SilentlyContinue
            $proc = Start-Process -FilePath 'lake' -ArgumentList @('env','lean','-R',$root,'-o',$olean,$file) -WorkingDirectory $root -NoNewWindow -PassThru -RedirectStandardOutput $tmpOut -RedirectStandardError $tmpErr
            $exited = $proc.WaitForExit($FileTimeoutSeconds * 1000)
            if (-not $exited) { try { $proc.Kill() } catch {}; $code = -999 } else { $code = $proc.ExitCode }
            Add-Content -LiteralPath $results -Value ("EXIT=" + $code + " FILE=" + $rel)
            if (Test-Path -LiteralPath $tmpOut) { Get-Content -LiteralPath $tmpOut -Tail 120 | Add-Content -LiteralPath $results }
            if (Test-Path -LiteralPath $tmpErr) { Get-Content -LiteralPath $tmpErr -Tail 120 | Add-Content -LiteralPath $results }
            Write-Log ("DONE EXIT=" + $code + " FILE=" + $rel)
            Remove-OneLine $raw
          }
        }
      }
    }
  }
  Start-Sleep -Seconds $PollSeconds
}
