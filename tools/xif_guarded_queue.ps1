param([int]$MaxParallel = 3, [int]$FileTimeoutSeconds = 900)
$root = 'D:\lean'
$queue = Join-Path $root 'tmp\xif_guarded_queue.txt'
$log = Join-Path $root 'tmp\xif_guarded_watchdog.log'
$results = Join-Path $root 'tmp\xif_guarded_results.log'
$quarantineFile = Join-Path $root 'tmp\xif_guarded_quarantine.txt'
$priorityFile = Join-Path $root 'tmp\xif_priority.txt'
$holdFile = Join-Path $root 'tmp\xif_hold_files.txt'
function Get-HoldSet {
  $set = @()
  if (Test-Path -LiteralPath $holdFile) {
    foreach ($line in (Get-Content -LiteralPath $holdFile -ErrorAction SilentlyContinue)) {
      $t = $line.Trim()
      if ($t.Length -gt 0) { $set += $t }
    }
  }
  return $set
}
function Test-Hold([string]$rel) {
  $hold = Get-HoldSet
  foreach ($pat in $hold) { if ($rel -match $pat) { return $true } }
  return $false
}
$prioritySet = @{}
if (Test-Path -LiteralPath $priorityFile) {
  foreach ($p in (Get-Content -LiteralPath $priorityFile -ErrorAction SilentlyContinue)) {
    $t = $p.Trim()
    if ($t.Length -eq 0) { continue }
    $t = $t -replace '\\', '/'
    if ([IO.Path]::IsPathRooted($t)) { try { $t = [IO.Path]::GetRelativePath($root, $t) } catch {} }
    $t = $t -replace '\\', '/'
    $prioritySet[$t] = $true
  }
}
function Get-PrioritySet {
  $set = @{}
  if (Test-Path -LiteralPath $priorityFile) {
    foreach ($p in (Get-Content -LiteralPath $priorityFile -ErrorAction SilentlyContinue)) {
      $t = $p.Trim()
      if ($t.Length -eq 0) { continue }
      $t = $t -replace '\\', '/'
      if ([IO.Path]::IsPathRooted($t)) { try { $t = [IO.Path]::GetRelativePath($root, $t) } catch {} }
      $t = $t -replace '\\', '/'
      $set[$t] = $true
    }
  }
  return $set
}
$depCache = @{}
$missingCache = @{}
$mtimeCache = @{}
$running = @{}
function Write-Log([string]$text) { $stamp = Get-Date -Format 'yyyy-MM-dd HH:mm:ss'; Add-Content -LiteralPath $log -Value ("[" + $stamp + "] " + $text) }
function Get-DepModules([string]$file) {
  $mods = @()
  $lines = Get-Content -LiteralPath $file -ErrorAction SilentlyContinue
  foreach ($line in $lines) {
    if ($line -match '^\s*(?:public\s+|private\s+|protected\s+)?import\s+([A-Za-z0-9_\.]+)') {
      $m = $Matches[1]
      if ($m -match '^(tmp|LeanFormal|Iut)\.') { $mods += $m }
    } elseif ($line -notmatch '^\s*$' -and $line -notmatch '^\s*(/-|--|#)') { break }
  }
  return $mods
}
function Count-Missing([string[]]$mods) {
  $n = 0
  foreach ($m in $mods) {
    $srcRel = ($m -replace '\.', '/') + '.lean'
    $src = Join-Path $root $srcRel
    $rel = ($m -replace '\.', '/') + '.olean'
    $ole = Join-Path $root ('.lake\build\lib\lean\' + $rel)
    if (-not (Test-Path -LiteralPath $ole)) { $n++; continue }
    if (Test-Path -LiteralPath $src) {
      if ((Get-Item -LiteralPath $src).LastWriteTime -gt (Get-Item -LiteralPath $ole).LastWriteTime) { $n++ }
    }
  }
  return $n
}
function Ensure-Cache([string]$rel) {
  $file = Join-Path $root $rel
  if (-not (Test-Path -LiteralPath $file)) { return }
  $mt = (Get-Item -LiteralPath $file).LastWriteTime
  if (-not $depCache.ContainsKey($rel) -or $mtimeCache[$rel] -ne $mt) {
    $mods = @(Get-DepModules $file)
    $depCache[$rel] = $mods
    $mtimeCache[$rel] = $mt
    $missingCache[$rel] = (Count-Missing $mods)
  }
}
function Invalidate-All { $missingCache.Clear() }
function Add-MissingDepsToQueue([string[]]$mods) {
  $added = $false
  $qmap = Get-Quarantine
  foreach ($m in $mods) {
    $srcRel = ($m -replace '\.', '/') + '.lean'
    $src = Join-Path $root $srcRel
    $depKey = ($srcRel -replace '\\', '/')
    if ($qmap.ContainsKey($depKey)) {
      $depFp = Get-Fingerprint $srcRel
      if ($depFp -eq $qmap[$depKey]) { continue }
      $qmap.Remove($depKey)
      Clear-Quarantine $depKey
    }
    $orel = ($m -replace '\.', '/') + '.olean'
    $ole = Join-Path $root ('.lake\build\lib\lean\' + $orel)
    if (-not (Test-Path -LiteralPath $src)) { continue }
    $stale = -not (Test-Path -LiteralPath $ole)
    if (-not $stale -and ((Get-Item -LiteralPath $src).LastWriteTime -gt (Get-Item -LiteralPath $ole).LastWriteTime)) { $stale = $true }
    if ($stale) {
      $cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
      if ($cur -notcontains $srcRel) { Add-Content -LiteralPath $queue -Value $srcRel; $added = $true }
    }
  }
  return $added
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
  $norm = @($cur | ForEach-Object { ($_.Trim() -replace '\\', '/') })
  $uniq = @($norm | Select-Object -Unique)
  if ($uniq.Count -ne $cur.Count -or ($norm -join "`n") -ne ($cur -join "`n")) { Set-Content -LiteralPath $queue -Value $uniq }
}
function Get-Quarantine {
  $map = @{}
  if (Test-Path -LiteralPath $quarantineFile) {
    foreach ($line in (Get-Content -LiteralPath $quarantineFile -ErrorAction SilentlyContinue)) {
      if ($line -match '^(.+?)\t(\d+)$') { $map[($Matches[1] -replace '\\','/')] = $Matches[2] }
    }
  }
  return $map
}
function Save-Quarantine([hashtable]$map) {
  $out = @()
  foreach ($k in ($map.Keys | Sort-Object)) { $out += ($k + "`t" + $map[$k]) }
  Set-Content -LiteralPath $quarantineFile -Value $out
}
function Get-Fingerprint([string]$rel) {
  $file = Join-Path $root $rel
  if (-not (Test-Path -LiteralPath $file)) { return '0' }
  $fp = (Get-Item -LiteralPath $file).LastWriteTimeUtc.Ticks
  Ensure-Cache $rel
  $mods = @()
  if ($depCache.ContainsKey($rel)) { $mods = $depCache[$rel] }
  foreach ($m in $mods) {
    $orel = ($m -replace '\.', '/') + '.olean'
    $ole = Join-Path $root ('.lake\build\lib\lean\' + $orel)
    if (Test-Path -LiteralPath $ole) {
      $t = (Get-Item -LiteralPath $ole).LastWriteTimeUtc.Ticks
      if ($t -gt $fp) { $fp = $t }
    }
  }
  return [string]$fp
}
function Set-Quarantine([string]$rel, [string]$fp) {
  $map = Get-Quarantine
  $map[($rel -replace '\\','/')] = $fp
  Save-Quarantine $map
}
function Clear-Quarantine([string]$rel) {
  $map = Get-Quarantine
  $k = ($rel -replace '\\','/')
  if ($map.ContainsKey($k)) { $map.Remove($k); Save-Quarantine $map }
}
function Revive-Quarantine {
  $map = Get-Quarantine
  if ($map.Count -eq 0) { return }
  $cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
  $changed = $false
  foreach ($k in @($map.Keys)) {
    Ensure-Cache $k
    $fp = Get-Fingerprint $k
    if ($fp -ne $map[$k]) {
      $map.Remove($k)
      $changed = $true
      if (Test-Hold $k) { continue }
      if ($cur -notcontains $k) { Add-Content -LiteralPath $queue -Value $k }
      Write-Log ('REVIVE ' + $k)
    }
  }
  if ($changed) { Save-Quarantine $map }
}
function Wait-QueueChange {
  $dir = Split-Path -Parent $queue
  $name = Split-Path -Leaf $queue
  $w = New-Object System.IO.FileSystemWatcher $dir, $name
  $w.EnableRaisingEvents = $true
  [void]$w.WaitForChanged([System.IO.WatcherChangeTypes]::All, 30000)
  $w.Dispose()
}
Write-Log ('parallel watchdog started max=' + $MaxParallel)
while ($true) {
  Dedupe-Queue
  Revive-Quarantine
  $quarantine = Get-Quarantine
  $finished = @($running.Keys | Where-Object { $running[$_].Proc.HasExited })
  foreach ($raw in $finished) {
    $r = $running[$raw]
    $code = $r.Proc.ExitCode
    Add-Content -LiteralPath $results -Value ("EXIT=" + $code + " FILE=" + $r.Rel + " SIZE=" + $r.Size)
    if (Test-Path -LiteralPath $r.Out) { Get-Content -LiteralPath $r.Out -Tail 120 | Add-Content -LiteralPath $results }
    if (Test-Path -LiteralPath $r.Err) { Get-Content -LiteralPath $r.Err -Tail 120 | Add-Content -LiteralPath $results }
    Write-Log ("DONE EXIT=" + $code + " FILE=" + $r.Rel)
    if ($code -eq 0) {
      Invalidate-All
      Clear-Quarantine $r.Rel
    } else {
      if ($r.StartFp) { $qfp = $r.StartFp } else { $qfp = Get-Fingerprint $r.Rel }
      Set-Quarantine $r.Rel $qfp
      Write-Log ("QUARANTINE " + $r.Rel + " fp=" + $qfp)
    }
    Remove-OneLine $raw
    $running.Remove($raw)
  }
  $prioritySet = Get-PrioritySet
  $cur = @(Get-Content -LiteralPath $queue -ErrorAction SilentlyContinue | Where-Object { $_ -and $_.Trim().Length -gt 0 })
  $holdDropped = 0
  $kept = @()
  foreach ($line in $cur) { if (Test-Hold $line) { $holdDropped++ } else { $kept += $line } }
  if ($holdDropped -gt 0) {
    Set-Content -LiteralPath $queue -Value $kept
    Write-Log ('HOLD_DROPPED count=' + $holdDropped)
    $cur = $kept
  }
  $cands = @()
  foreach ($line in $cur) {
    $raw = $line.Trim()
    $rel = $raw
    if ([IO.Path]::IsPathRooted($rel)) { try { $rel = [IO.Path]::GetRelativePath($root, $rel) } catch {} }
    $file = Join-Path $root $rel
    $size = [long]0
    if (Test-Path -LiteralPath $file) { $size = (Get-Item -LiteralPath $file).Length }
    Ensure-Cache $rel
    $miss = 0
    if ($missingCache.ContainsKey($rel)) { $miss = [int]$missingCache[$rel] }
    $relNorm = $rel -replace '\\', '/'
    $quarantined = $false
    if ($quarantine.ContainsKey($relNorm)) {
      $qfp = Get-Fingerprint $rel
      if ($qfp -eq $quarantine[$relNorm]) { $quarantined = $true } else { $quarantine.Remove($relNorm); Clear-Quarantine $relNorm }
    }
    $prio = 0
    if ($prioritySet.ContainsKey($relNorm)) { $prio = 1 }
    $cands += [pscustomobject]@{ Raw = $raw; Rel = $rel; File = $file; Size = $size; Missing = $miss; Priority = $prio; Quarantined = $quarantined }
  }
  $cands = @($cands | Sort-Object @{Expression='Priority';Descending=$true}, Size)
  $startedAny = $false
  $addedBlocked = $false
  foreach ($c in $cands) {
    if ($running.Count -ge $MaxParallel) { break }
    if ($running.ContainsKey($c.Raw)) { continue }
    if ($c.Quarantined) {
      Remove-OneLine $c.Raw
      $startedAny = $true
      continue
    }
    if (-not (Test-Path -LiteralPath $c.File)) {
      Add-Content -LiteralPath $results -Value ("MISSING_FILE " + $c.Rel)
      Write-Log ("MISSING_FILE " + $c.Rel)
      Remove-OneLine $c.Raw
      $startedAny = $true
      break
    }
    if ($c.Missing -gt 0) {
      if (Add-MissingDepsToQueue $depCache[$c.Rel]) { $addedBlocked = $true }
      continue
    }
    $recheck = Count-Missing $depCache[$c.Rel]
    if ($recheck -gt 0) {
      $missingCache[$c.Rel] = $recheck
      if (Add-MissingDepsToQueue $depCache[$c.Rel]) { $addedBlocked = $true }
      continue
    }
    $olean = Join-Path $root ('.lake\build\lib\lean\' + [IO.Path]::ChangeExtension($c.Rel, 'olean'))
    $fresh = $false
    if (Test-Path -LiteralPath $olean) {
      $ole = Get-Item -LiteralPath $olean
      $src = Get-Item -LiteralPath $c.File
      if ($ole.LastWriteTime -ge $src.LastWriteTime) { $fresh = $true }
    }
    if ($fresh) {
      Add-Content -LiteralPath $results -Value ("SKIP_FRESH " + $c.Rel)
      Write-Log ('SKIP_FRESH ' + $c.Rel)
      Remove-OneLine $c.Raw
      $startedAny = $true
      break
    }
    $startFp = Get-Fingerprint $c.Rel
    $tag = [guid]::NewGuid().ToString('N').Substring(0,8)
    $out = Join-Path $root ('tmp\xif_par_' + $tag + '.out')
    $err = Join-Path $root ('tmp\xif_par_' + $tag + '.err')
    Write-Log ('COMPILING ' + $c.Rel + ' size=' + $c.Size + ' running=' + $running.Count)
    $proc = Start-Process -FilePath 'lake' -ArgumentList @('env','lean','-R',$root,'-o',$olean,$c.File) -WorkingDirectory $root -NoNewWindow -PassThru -RedirectStandardOutput $out -RedirectStandardError $err
    $task = $proc.WaitForExitAsync()
    $running[$c.Raw] = [pscustomobject]@{ Proc = $proc; Task = $task; Rel = $c.Rel; Size = $c.Size; Out = $out; Err = $err; StartFp = $startFp }
    $startedAny = $true
  }
  if ($running.Count -gt 0) {
    $tasks = @($running.Values | ForEach-Object { $_.Task })
    [System.Threading.Tasks.Task]::WaitAny([System.Threading.Tasks.Task[]]$tasks, 5000) | Out-Null
    continue
  }
  if ($startedAny) { continue }
  if ($addedBlocked) { continue }
  Add-Content -LiteralPath $results -Value ("ALL_BLOCKED count=" + $cands.Count)
  Write-Log ('ALL_BLOCKED count=' + $cands.Count)
  Wait-QueueChange
}
