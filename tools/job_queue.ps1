# job_queue.ps1 -- resident hardware-gated job queue for D:\lean (v1.1, 2026-10-16).
# v1.1: MinCommitHeadGB default 11 + heavy-lean serialization (no running lean/lake >= 1.5GB
# private at launch), matching build_guard v3.2; ColdGapSec default 12.
#
# Purpose: fire-and-forget admission control for heavy commands (lake build, lake env lean,
# dsh runs, python probes). Callers submit jobs; ONE resident watcher launches them only when
# the box has headroom: sampled CPU below -MaxCPU, free physical memory above -MinFreeGB, and
# at least -ColdGapSec since the last launch recorded in the shared stamp file. There is no
# fixed concurrency cap; -MaxConcurrent is only a high safety fuse. The production watcher
# shares the launch-pacing stamp and the sampling gate mutex with build_guard.ps1, so guarded
# builds and queued jobs together obey one hardware limit.
#
# Modes:
#   submit : append a job event and auto-start the watcher if it is not alive.
#            Prints 'job submitted: <id>'. Do NOT use a bare PS 'exit' keyword inside -Command;
#            it kills the wrapper before the exit code is recorded (use cmd /c exit 7 to test).
#   ensure : start the resident watcher if it is not alive.
#   watch  : run the watcher loop in the foreground (normally started hidden via ensure).
#   status : print a compact snapshot of the queue.
#   wait   : block until the job's .exit file appears (TimeoutSec=0 means no timeout) and exit
#            with the job's exit code. Exit 2 = wait timeout, 3 = unknown job.
#   stop   : ask the watcher to exit at its next tick (running children keep running).
#
# Parameters -NameSpace, -GateMutexName, -StampFile let a smoke-test instance run isolated
# from the production instance; keep the defaults for real work.
# State lives in <QueueDir>: queue.jsonl (append-only events), results\<id>.log/.err/.exit,
# daemon.log, daemon.pid, stop.flag.

param(
  [Parameter(Mandatory=$true)][ValidateSet('submit','ensure','watch','status','wait','stop')][string]$Mode,
  [string]$Command = '',
  [string]$Tag = '',
  [string]$WorkDir = 'D:\lean',
  [string]$QueueDir = 'D:\lean\tmp\job-queue',
  [int]$MinFreeGB = 8,
  [int]$MaxCPU = 80,
  [int]$ColdGapSec = 12,
  [int]$MinCommitHeadGB = 11,
  [ValidateRange(1,300)][int]$PollSec = 10,
  [int]$MaxConcurrent = 24,
  [int]$TimeoutSec = 0,
  [string]$JobId = '',
  [string]$NameSpace = 'prod',
  [string]$GateMutexName = 'Global\lean_build_guard_gate_v2',
  [string]$StampFile = 'D:\lean\tmp\build-guard-logs\.last-launch'
)

$ErrorActionPreference = 'Continue'

$queueFile = Join-Path $QueueDir 'queue.jsonl'
$resultsDir = Join-Path $QueueDir 'results'
$stopFile = Join-Path $QueueDir 'stop.flag'
$daemonPid = Join-Path $QueueDir 'daemon.pid'
$daemonLog = Join-Path $QueueDir 'daemon.log'
$appendMutexName = 'Global\lean_jobq_' + $NameSpace + '_append_v1'
$daemonMutexName = 'Global\lean_jobq_' + $NameSpace + '_daemon_v1'

function Ensure-Dirs {
  if (-not (Test-Path -LiteralPath $QueueDir)) { New-Item -ItemType Directory -Path $QueueDir -Force | Out-Null }
  if (-not (Test-Path -LiteralPath $resultsDir)) { New-Item -ItemType Directory -Path $resultsDir -Force | Out-Null }
}

function Write-Dlog {
  param([string]$m)
  Add-Content -LiteralPath $daemonLog -Value ((Get-Date).ToString('HH:mm:ss') + ' ' + $m)
}

function New-NamedMutex {
  param([string]$name)
  try { return [System.Threading.Mutex]::new($false, $name) }
  catch { return [System.Threading.Mutex]::new($false, ($name -replace '^Global\\', '')) }
}

function Append-Event {
  param($evObj)
  $mx = New-NamedMutex $appendMutexName
  $got = $false
  try { $got = $mx.WaitOne(20000) } catch [System.Threading.AbandonedMutexException] { $got = $true }
  try { Add-Content -LiteralPath $queueFile -Value ($evObj | ConvertTo-Json -Compress -Depth 5) }
  finally { if ($got) { try { $mx.ReleaseMutex() } catch {} } ; $mx.Dispose() }
}

function Read-Jobs {
  $jobs = @{}
  $lines = @()
  try {
    if (Test-Path -LiteralPath $queueFile) { $lines = @(Get-Content -LiteralPath $queueFile -ErrorAction Stop) }
  } catch { $lines = @() }
  foreach ($line in $lines) {
    if (-not $line -or -not $line.Trim()) { continue }
    try { $e = $line | ConvertFrom-Json } catch { continue }
    if ($e.ev -eq 'submit') {
      $jobs[[string]$e.id] = [pscustomobject]@{ id=[string]$e.id; tag=[string]$e.tag; cmd=[string]$e.cmd; cwd=[string]$e.cwd; state='pending'; pid=0; code=$null; tsubmit=[string]$e.ts; tlaunch='' }
    } elseif ($jobs.ContainsKey([string]$e.id)) {
      if ($e.ev -eq 'launch') { $jobs[[string]$e.id].state = 'running'; $jobs[[string]$e.id].pid = [int]$e.pid; $jobs[[string]$e.id].tlaunch = [string]$e.ts }
      elseif ($e.ev -eq 'exit') { $jobs[[string]$e.id].state = 'done'; $jobs[[string]$e.id].code = $e.code }
    }
  }
  return ,$jobs
}

function Get-Cpu { $c = (Get-CimInstance Win32_Processor | Measure-Object -Property LoadPercentage -Average).Average; return [double]$c }
function Get-FreeGB { return [math]::Round(((Get-CimInstance Win32_OperatingSystem).FreePhysicalMemory)/1MB,1) }
function Get-CommitHeadGB { $pm = Get-CimInstance Win32_PerfFormattedData_PerfOS_Memory; return [math]::Round(($pm.CommitLimit - $pm.CommittedBytes)/1GB,1) }
function Get-HeavyGB { $s = 0.0; Get-Process -Name lean -ErrorAction SilentlyContinue | ForEach-Object { if ($_.PrivateMemorySize64 -ge 1.5GB) { $s += $_.PrivateMemorySize64 } }; Get-Process -Name lake -ErrorAction SilentlyContinue | ForEach-Object { if ($_.PrivateMemorySize64 -ge 0.5GB) { $s += $_.PrivateMemorySize64 } }; return [math]::Round($s/1GB,1) }

function Test-DaemonAlive {
  if (-not (Test-Path -LiteralPath $daemonPid)) { return $false }
  $p = 0
  try { $p = [int]((Get-Content -LiteralPath $daemonPid -Raw).Trim()) } catch { return $false }
  if ($p -le 0) { return $false }
  return [bool](Get-Process -Id $p -ErrorAction SilentlyContinue)
}

function Start-Daemon {
  Ensure-Dirs
  $daemonArgs = @('-NoProfile','-File',$PSCommandPath,'-Mode','watch','-QueueDir',$QueueDir,'-MinFreeGB',$MinFreeGB,'-MaxCPU',$MaxCPU,'-ColdGapSec',$ColdGapSec,'-MinCommitHeadGB',$MinCommitHeadGB,'-PollSec',$PollSec,'-MaxConcurrent',$MaxConcurrent,'-NameSpace',$NameSpace,'-GateMutexName',$GateMutexName,'-StampFile',$StampFile)
  Start-Process -FilePath 'pwsh' -ArgumentList $daemonArgs -WindowStyle Hidden -RedirectStandardOutput (Join-Path $QueueDir 'daemon.out') -RedirectStandardError (Join-Path $QueueDir 'daemon.err')
  Start-Sleep -Seconds 2
  if (Test-DaemonAlive) { Write-Output ('daemon started pid=' + ((Get-Content -LiteralPath $daemonPid -Raw).Trim())) }
  else { Write-Output 'daemon start requested (pid file pending)' }
}

if ($Mode -eq 'watch') {
  Ensure-Dirs
  $dm = New-NamedMutex $daemonMutexName
  $dmGot = $false
  try { $dmGot = $dm.WaitOne(0) } catch [System.Threading.AbandonedMutexException] { $dmGot = $true }
  if (-not $dmGot) { Write-Output 'another watcher already holds the daemon mutex'; exit 9 }
  Remove-Item -LiteralPath $stopFile -Force -ErrorAction SilentlyContinue
  Set-Content -LiteralPath $daemonPid -Value $PID
  Write-Dlog ('watch start pid=' + $PID + ' ns=' + $NameSpace + ' maxCPU=' + $MaxCPU + ' minFreeGB=' + $MinFreeGB + ' minCommitHeadGB=' + $MinCommitHeadGB + ' coldGap=' + $ColdGapSec + ' poll=' + $PollSec + ' fuse=' + $MaxConcurrent)
  $consec = 0
  $lastGateState = 'init'
  $lastLogT = Get-Date
  while (-not (Test-Path -LiteralPath $stopFile)) {
    try {
      $jobs = Read-Jobs
      $running = 0
      foreach ($j in @($jobs.Values)) {
        if ($j.state -ne 'running') { continue }
        $exitFile = Join-Path $resultsDir ($j.id + '.exit')
        if (Test-Path -LiteralPath $exitFile) {
          $code = -1003
          try { $code = [int]((Get-Content -LiteralPath $exitFile -Raw).Trim()) } catch { $code = -1002 }
          Append-Event ([ordered]@{ ev='exit'; id=$j.id; ts=(Get-Date).ToString('o'); code=$code })
          Write-Dlog ('exit ' + $j.id + ' code=' + $code + ' tag=' + $j.tag)
        } elseif ($j.pid -gt 0 -and -not (Get-Process -Id $j.pid -ErrorAction SilentlyContinue)) {
          $age = 9999.0
          if ($j.tlaunch) { try { $age = ((Get-Date) - [datetime]::Parse($j.tlaunch)).TotalSeconds } catch { } }
          if ($age -gt 40) {
            Append-Event ([ordered]@{ ev='exit'; id=$j.id; ts=(Get-Date).ToString('o'); code=-1001 })
            Write-Dlog ('exit-unknown ' + $j.id + ' pid-gone-no-exitfile tag=' + $j.tag)
          } else { $running++ }
        } else { $running++ }
      }
      $pending = @(@($jobs.Values) | Where-Object { $_.state -eq 'pending' } | Sort-Object tsubmit)
      if ($pending.Count -gt 0 -and $running -lt $MaxConcurrent) {
        $gate = New-NamedMutex $GateMutexName
        $gateOK = $false
        try { $gateOK = $gate.WaitOne([TimeSpan]::FromSeconds(30)) } catch [System.Threading.AbandonedMutexException] { $gateOK = $true }
        if ($gateOK) {
          try {
            $cpu = Get-Cpu
            $freeGB = Get-FreeGB
            $commitHeadGB = Get-CommitHeadGB
            $heavyGB = Get-HeavyGB
            $pass = ($freeGB -gt $MinFreeGB) -and ($cpu -lt $MaxCPU) -and ($commitHeadGB -gt $MinCommitHeadGB) -and ($heavyGB -le 0.0)
            if ($pass) { $consec = $consec + 1 } else { $consec = 0 }
            $why = if ($freeGB -le $MinFreeGB) { 'low-mem' } elseif ($commitHeadGB -le $MinCommitHeadGB) { 'commit-tight' } elseif ($heavyGB -gt 0) { 'lean-running' } else { 'high-cpu' }
            $msg = if ($pass) { 'poll PASS ' + $consec + '/2 cpu=' + $cpu + ' freeGB=' + $freeGB + ' commitHead=' + $commitHeadGB + ' heavy=' + $heavyGB + ' pending=' + $pending.Count + ' running=' + $running } else { 'waiting(' + $why + ') cpu=' + $cpu + ' freeGB=' + $freeGB + ' commitHead=' + $commitHeadGB + ' heavy=' + $heavyGB + ' pending=' + $pending.Count + ' running=' + $running }
            $gateState = if ($pass) { 'pass' } else { 'wait' }
            $nowT = Get-Date
            if ($gateState -ne $lastGateState -or ($nowT - $lastLogT).TotalSeconds -ge 30) { Write-Dlog $msg ; $lastGateState = $gateState ; $lastLogT = $nowT }
            if ($pass -and $consec -ge 2) {
              $waitGap = 0.0
              if (Test-Path -LiteralPath $StampFile) { try { $lt2 = [datetime]::Parse((Get-Content -LiteralPath $StampFile -Raw).Trim()); $since2 = ((Get-Date) - $lt2).TotalSeconds; if ($since2 -lt $ColdGapSec) { $waitGap = $ColdGapSec - $since2 } } catch { } }
              if ($waitGap -gt 0.3) { Write-Dlog ('streak hot; slot-wait ' + [math]::Round($waitGap,1) + 's') ; Start-Sleep -Milliseconds ([int]($waitGap * 1000)) }
              $cpuNow = Get-Cpu
              $freeNow = Get-FreeGB
              $commitNow = Get-CommitHeadGB
              $heavyNow = Get-HeavyGB
              if (($freeNow -le $MinFreeGB) -or ($cpuNow -ge $MaxCPU) -or ($commitNow -le $MinCommitHeadGB) -or ($heavyNow -gt 0)) {
                Write-Dlog ('instant check held: cpu=' + $cpuNow + ' freeGB=' + $freeNow + ' commitHead=' + $commitNow + ' heavy=' + $heavyNow + '; streak reset')
                $consec = 0
              } else {
              $job = $pending[0]
              $logPath = Join-Path $resultsDir ($job.id + '.log')
              $errPath = Join-Path $resultsDir ($job.id + '.err')
              $exitPath = Join-Path $resultsDir ($job.id + '.exit')
              $exitQuoted = "'" + $exitPath + "'"
              $wrapped = $job.cmd + '; $ec = $LASTEXITCODE; if ($null -eq $ec) { $ec = 0 }; Set-Content -LiteralPath ' + $exitQuoted + ' -Value $ec; exit $ec'
              $enc = [Convert]::ToBase64String([Text.Encoding]::Unicode.GetBytes($wrapped))
              $cwd = $job.cwd
              if (-not $cwd) { $cwd = 'D:\lean' }
              $proc = Start-Process -FilePath 'pwsh' -ArgumentList @('-NoProfile','-EncodedCommand',$enc) -WorkingDirectory $cwd -RedirectStandardOutput $logPath -RedirectStandardError $errPath -PassThru -WindowStyle Hidden
              Set-Content -LiteralPath $StampFile -Value ((Get-Date).ToString('o'))
              Append-Event ([ordered]@{ ev='launch'; id=$job.id; ts=(Get-Date).ToString('o'); pid=$proc.Id })
              Write-Dlog ('launch ' + $job.id + ' pid=' + $proc.Id + ' tag=' + $job.tag)
              $consec = 0
              }
            }
          } finally { try { $gate.ReleaseMutex() } catch { } ; $gate.Dispose() }
        }
      } else { $consec = 0 }
    } catch {
      Write-Dlog ('tick error: ' + $_.Exception.Message)
    }
    Start-Sleep -Seconds $PollSec
  }
  Write-Dlog 'watch stop (stop.flag)'
  Remove-Item -LiteralPath $daemonPid -Force -ErrorAction SilentlyContinue
  try { $dm.ReleaseMutex() } catch { }
  exit 0
}
elseif ($Mode -eq 'ensure') {
  Ensure-Dirs
  if (Test-DaemonAlive) {
    $p = ''
    try { $p = (Get-Content -LiteralPath $daemonPid -Raw).Trim() } catch { }
    Write-Output ('daemon already running pid=' + $p)
  } else {
    if (Test-Path -LiteralPath $stopFile) { Remove-Item -LiteralPath $stopFile -Force }
    Start-Daemon
  }
}
elseif ($Mode -eq 'submit') {
  if (-not $Command) { Write-Error 'submit requires -Command'; exit 3 }
  Ensure-Dirs
  $id = ([guid]::NewGuid().ToString('N')).Substring(0,10)
  Append-Event ([ordered]@{ ev='submit'; id=$id; ts=(Get-Date).ToString('o'); tag=$Tag; cmd=$Command; cwd=$WorkDir })
  Write-Output ('job submitted: ' + $id)
  if (-not (Test-DaemonAlive)) {
    if (Test-Path -LiteralPath $stopFile) { Remove-Item -LiteralPath $stopFile -Force }
    Start-Daemon
  }
}
elseif ($Mode -eq 'status') {
  $jobs = Read-Jobs
  $pend = @(@($jobs.Values) | Where-Object { $_.state -eq 'pending' }).Count
  $runN = @(@($jobs.Values) | Where-Object { $_.state -eq 'running' }).Count
  $doneN = @(@($jobs.Values) | Where-Object { $_.state -eq 'done' }).Count
  $alive = if (Test-DaemonAlive) { 'yes' } else { 'no' }
  Write-Output ('queue ns=' + $NameSpace + ' daemon=' + $alive + ' pending=' + $pend + ' running=' + $runN + ' done=' + $doneN)
  foreach ($j in @(@($jobs.Values) | Sort-Object tsubmit)) {
    $c = if ($null -eq $j.code) { '-' } else { [string]$j.code }
    $cmdShort = [string]$j.cmd
    if ($cmdShort.Length -gt 70) { $cmdShort = $cmdShort.Substring(0,67) + '...' }
    Write-Output ('  ' + $j.id + ' ' + ([string]$j.state).PadRight(7) + ' code=' + $c + ' tag=' + $j.tag + ' :: ' + $cmdShort)
  }
}
elseif ($Mode -eq 'wait') {
  if (-not $JobId) { Write-Error 'wait requires -JobId'; exit 3 }
  $jobs = Read-Jobs
  if (-not $jobs.ContainsKey($JobId)) { Write-Error ('unknown job ' + $JobId); exit 3 }
  $exitFile = Join-Path $resultsDir ($JobId + '.exit')
  $t0 = Get-Date
  while (-not (Test-Path -LiteralPath $exitFile)) {
    if ($TimeoutSec -gt 0 -and ((Get-Date) - $t0).TotalSeconds -gt $TimeoutSec) { Write-Output ('timeout waiting for ' + $JobId); exit 2 }
    Start-Sleep -Seconds 3
  }
  $code = 0
  try { $code = [int]((Get-Content -LiteralPath $exitFile -Raw).Trim()) } catch { $code = 4 }
  Write-Output ('job ' + $JobId + ' exit=' + $code)
  exit $code
}
elseif ($Mode -eq 'stop') {
  Ensure-Dirs
  Set-Content -LiteralPath $stopFile -Value ((Get-Date).ToString('o'))
  Write-Output 'stop.flag written; watcher will exit at next tick'
}
