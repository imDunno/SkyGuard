<#
  SkyGuard 网络恢复 (V1.1.5-RC2)
  ==========================================================================
  这个脚本的存在意义只有一个: 万一 SkyGuard 断网期间被强杀/断电, 网卡卡在禁用状态,
  双击 恢复网络.bat 就**一定**能把网要回来。

  所以它按"多备选 + 每步自证"来写:
    · 每一步都不许因为失败而中断后面的步骤(全部 try/catch, ErrorActionPreference=Continue);
    · 打开网卡走四级阶梯, 一级不行就下一级:
        T1 Enable-NetAdapter      (Win8+; Win10/11 首选)
        T2 netsh interface set    (一直都有; 老系统上它是主路)
        T3 Enable-PnpDevice       (Win10 1809+/11; 管"设备管理器里被禁用"的那种)
        T4 Restart-NetAdapter     (Win10/11; 网卡是启用状态但没起来时用)
    · 每一级都打印"做了什么 / 结果如何 / 现在状态是什么" —— 不许"看起来在干活、实际没干";
    · 候选网卡来自四个来源的并集(guard.ini / 断网标记 / Get-NetAdapter / netsh+CIM+PnP 解析),
      任何一路拿不到都不会让候选集变成空;
    · 验证同时用 ICMP 和 TCP(53/80) —— Win10/11 上"ICMP 被过滤"很常见,
      只看 ping 会把"其实有网"判成"没恢复";
    · -Pass 1 只动 SkyGuard 自己的名单; -Pass 2 广扫兜底。
    · -DryRun 只检查、不动作, 换台电脑可以先跑它确认"这个脚本认得出你的网卡"。

  退出码: 0 = 已确认网络恢复   1 = 没能确认(网可能还没回来)   2 = 环境问题(非管理员等)

  注意: 本脚本不写注册表、不改 DNS 设置、不做 winsock reset(那需要重启, 只在你手动确认时才建议)。
#>
[CmdletBinding()]
param(
    [switch]$DryRun,
    [int]$Pass = 1
)

$ErrorActionPreference = 'Continue'
$ProgressPreference    = 'SilentlyContinue'

$script:DataDir = Join-Path $env:ProgramData 'SkyGuard'
$script:LogPath = Join-Path $script:DataDir 'RestoreNetwork.log'
$script:Results = New-Object System.Collections.ArrayList

function Say {
    param([string]$Text, [string]$Color = 'Gray')
    try { Write-Host $Text -ForegroundColor $Color } catch { Write-Host $Text }
}

function LogLine {
    param([string]$Text)
    # 写日志失败绝不能影响恢复流程本身
    try {
        if (-not (Test-Path $script:DataDir)) { return }
        $stamp = (Get-Date).ToString('yyyy-MM-dd HH:mm:ss.fff')
        Add-Content -LiteralPath $script:LogPath -Value ("[$stamp] " + $Text) -ErrorAction SilentlyContinue
    } catch { }
}

function Both {
    param([string]$Text, [string]$Color = 'Gray')
    Say $Text $Color
    LogLine $Text
}

function Have {
    param([string]$Name)
    try { return ($null -ne (Get-Command $Name -ErrorAction SilentlyContinue)) } catch { return $false }
}

function Get-Admin {
    try {
        $id = [System.Security.Principal.WindowsIdentity]::GetCurrent()
        return (New-Object System.Security.Principal.WindowsPrincipal($id)).IsInRole(
            [System.Security.Principal.WindowsBuiltInRole]::Administrator)
    } catch { return $false }
}

# ==========================================================================
#  0. 环境
# ==========================================================================
function Show-Environment {
    Both "---- 环境 ----"
    try {
        $os = Get-CimInstance Win32_OperatingSystem -ErrorAction SilentlyContinue
        if ($os) {
            Both ("  系统        = " + $os.Caption + " (build " + $os.BuildNumber + ")")
        } else {
            Both "  系统        = 读不到版本(不影响恢复)"
        }
    } catch { Both "  系统        = 读不到版本(不影响恢复)" }
    Both ("  PowerShell  = " + $PSVersionTable.PSVersion)
    $admin = Get-Admin
    Both ("  管理员权限  = " + $(if ($admin) { "有" } else { "没有 <== 打开网卡/续租 IP 都需要它" }))
    Both ("  本次模式    = " + $(if ($DryRun) { "只检查不动作 (DryRun)" } else { "轮次 " + $Pass + $(if ($Pass -ge 2) { " (广扫兜底)" } else { " (只动 SkyGuard 自己的名单)" }) }))
    $names = @('Get-NetAdapter','Enable-NetAdapter','Restart-NetAdapter','Get-PnpDevice','Enable-PnpDevice','Get-CimInstance','Get-NetRoute','Get-NetFirewallRule')
    Both "  可用的命令:"
    foreach ($n in $names) {
        $ok = Have $n
        Both ("    " + $n.PadRight(22) + " = " + $(if ($ok) { "有" } else { "没有" }))
    }
    Both ""
    return $admin
}

# ==========================================================================
#  1. 清掉 SkyGuard 留下的防火墙规则
# ==========================================================================
function Clear-FirewallRules {
    Both "---- [1/6] 清理 SkyGuard 的防火墙规则 ----"
    if ($DryRun) { Both "  [只检查] 会先删 SkyGuard-Panic-Block-Out, 再删所有 SkyGuard-Panic* 的规则"; return }

    $before = -1
    try {
        if (Have Get-NetFirewallRule) {
            $before = @(Get-NetFirewallRule -ErrorAction SilentlyContinue |
                        Where-Object { $_.DisplayName -like 'SkyGuard-Panic*' }).Count
        }
    } catch { }

    # 路 1: netsh 按精确名字删(最老、最通用)
    $out = & netsh advfirewall firewall delete rule name="SkyGuard-Panic-Block-Out" 2>&1
    LogLine ("  netsh 删除精确名: " + (($out | Out-String).Trim() -replace "`r?`n", " / "))

    # 路 2: PowerShell 按通配删(能清掉名字带后缀的残留)
    if (Have Get-NetFirewallRule) {
        try {
            $stale = @(Get-NetFirewallRule -ErrorAction SilentlyContinue |
                       Where-Object { $_.DisplayName -like 'SkyGuard-Panic*' })
            if ($stale.Count -gt 0) {
                $stale | Remove-NetFirewallRule -ErrorAction SilentlyContinue
                Both ("  按通配删掉 " + $stale.Count + " 条残留规则")
            } else {
                Both "  按通配检查: 没有残留规则"
            }
        } catch { Both ("  按通配删除失败(不影响后续): " + $_.Exception.Message) }
    } else {
        Both "  (这台机器没有 Get-NetFirewallRule, 只走了 netsh 那一条)"
    }

    # 只看不删地复查一遍
    try {
        if (Have Get-NetFirewallRule) {
            $after = @(Get-NetFirewallRule -ErrorAction SilentlyContinue |
                       Where-Object { $_.DisplayName -like 'SkyGuard-Panic*' }).Count
            $verdict = if ($after -eq 0) { "已清干净 (0 条)" } else { "还剩 " + $after + " 条 <== 需要留意" }
            Both ("  复查(只查不删): " + $verdict + $(if ($before -ge 0) { "   [删除前 " + $before + " 条]" } else { "" }))
        }
    } catch { }
    Both ""
}

# ==========================================================================
#  2. 枚举适配器(多来源, 互相补位)
# ==========================================================================
function Get-AdapterPicture {
    $pic = [ordered]@{}
    $pic['net']   = @()
    $pic['cim']   = @()
    $pic['pnp']   = @()
    $pic['netsh'] = @()

    try { if (Have Get-NetAdapter) { $pic['net'] = @(Get-NetAdapter -ErrorAction SilentlyContinue) } } catch { }
    try { $pic['cim'] = @(Get-CimInstance Win32_NetworkAdapter -ErrorAction SilentlyContinue) } catch { }
    try { if (Have Get-PnpDevice) { $pic['pnp'] = @(Get-PnpDevice -Class Net -ErrorAction SilentlyContinue) } } catch { }
    try {
        # netsh 输出: 前 3 行是表头, 每行形如 "已启用  已连接  WLAN"
        $raw = @(netsh interface show interface 2>&1)
        if ($raw.Count -gt 3) {
            foreach ($line in $raw[3..($raw.Count - 1)]) {
                $s = ("" + $line).TrimEnd()
                if ($s.Length -eq 0) { continue }
                $k = $s.LastIndexOf('  ')
                if ($k -gt 0) { $pic['netsh'] += $s.Substring($k).Trim() }
            }
        }
    } catch { }
    return $pic
}

function Get-DisabledNames {
    param($Pic)
    $out = New-Object System.Collections.ArrayList
    # Get-NetAdapter 的 AdminStatus 是 Win10/11 最准的来源
    foreach ($a in $Pic['net']) {
        try {
            if ("" + $a.AdminStatus -eq 'Disabled') { if (-not $out.Contains("" + $a.Name)) { $out.Add("" + $a.Name) | Out-Null } }
        } catch { }
    }
    # CIM: 不用 NetEnabled 判(实测会误报 —— 蓝牙网卡在蓝牙没开时 NetEnabled 也是 False,
    #      但它其实并没有被"禁用", 只是没连上)。
    #      只有 ConfigManagerErrorCode=22(CM_PROB_DISABLED,"该设备已被禁用")才是确凿证据。
    foreach ($a in $Pic['cim']) {
        try {
            $nm = "" + $a.NetConnectionID
            if ($nm -eq '') { continue }
            if ($a.ConfigManagerErrorCode -eq 22) {
                if (-not $out.Contains($nm)) { $out.Add($nm) | Out-Null }
            }
        } catch { }
    }
    # PnP: 设备被禁用(Status=Error 且 Problem=22 是"被禁用")
    foreach ($d in $Pic['pnp']) {
        try {
            if ("" + $d.Status -eq 'Error' -and ("" + $d.Problem) -eq '22') {
                $nm = "" + $d.FriendlyName
                if ($nm -ne '' -and -not $out.Contains($nm)) { $out.Add($nm) | Out-Null }
            }
        } catch { }
    }
    return @($out)
}

function Show-AdapterPicture {
    param($Pic)
    Both "---- 这台机器上的网络适配器 ----"
    $shown = 0
    if ($Pic['net'].Count -gt 0) {
        foreach ($a in $Pic['net']) {
            Both ("  " + ("" + $a.Name).PadRight(30) + " 状态=" + $a.Status + "  管理状态=" + $a.AdminStatus)
            $shown++
        }
    }
    if ($shown -eq 0) {
        Both "  (Get-NetAdapter 没报出东西, 下面用 CIM / netsh / PnP 的结果)"
        foreach ($a in $Pic['cim']) {
            try {
                if ("" + $a.NetConnectionID -ne '') {
                    Both ("  " + ("" + $a.NetConnectionID).PadRight(30) + " NetEnabled=" + $a.NetEnabled + "  Physical=" + $a.PhysicalAdapter)
                    $shown++
                }
            } catch { }
        }
    }
    if ($shown -eq 0 -and $Pic['netsh'].Count -gt 0) {
        foreach ($n in $Pic['netsh']) { Both ("  netsh 看到: " + $n); $shown++ }
    }
    $dis = Get-DisabledNames $Pic
    if ($dis.Count -gt 0) {
        Both ("  == 判定为「被禁用」的: " + ($dis -join ' / ')) 'Yellow'
    } else {
        Both "  == 没有判定出被禁用的网卡(可能本来就没被禁, 或数据源都没报出来)"
    }
    Both ""
    return $dis
}

# ==========================================================================
#  3. 候选名单(该打开谁)
# ==========================================================================
function Get-Candidates {
    param($Pic, [bool]$Broad)
    $preferred = New-Object System.Collections.ArrayList
    try {
        $ini = Join-Path $script:DataDir 'guard.ini'
        if (Test-Path $ini) {
            foreach ($line in (Get-Content -LiteralPath $ini -Encoding UTF8 -ErrorAction SilentlyContinue)) {
                if ($line -match '^\s*Nic\d+\s*=') {
                    $v = ($line -split '=', 2)[1].Trim()
                    if ($v -ne '' -and -not $preferred.Contains($v)) { $preferred.Add($v) | Out-Null }
                }
            }
        }
    } catch { }
    try {
        $st = Join-Path $script:DataDir '_netcut_state.txt'
        if (Test-Path $st) {
            foreach ($line in (Get-Content -LiteralPath $st -Encoding UTF8 -ErrorAction SilentlyContinue)) {
                if ($line -match '^\s*nic\s*=') {
                    $v = ($line -split '=', 2)[1].Trim()
                    if ($v -ne '' -and -not $preferred.Contains($v)) { $preferred.Add($v) | Out-Null }
                }
            }
        }
    } catch { }

    $mode = 'narrow'
    $list = New-Object System.Collections.ArrayList
    if (-not $Broad -and $preferred.Count -gt 0) {
        foreach ($n in $preferred) { $list.Add($n) | Out-Null }
    } else {
        $mode = 'broad'
        # 广扫: 四个来源的并集 + 明确被禁用的那些
        $all = New-Object System.Collections.ArrayList
        foreach ($a in $Pic['net'])   { try { $n = "" + $a.Name;            if ($n -ne '') { $all.Add($n) | Out-Null } } catch { } }
        foreach ($a in $Pic['cim'])   { try { $n = "" + $a.NetConnectionID; if ($n -ne '') { $all.Add($n) | Out-Null } } catch { } }
        foreach ($d in $Pic['pnp'])   { try { $n = "" + $d.FriendlyName;    if ($n -ne '') { $all.Add($n) | Out-Null } } catch { } }
        foreach ($n in $Pic['netsh']) { if ($n -ne '') { $all.Add($n) | Out-Null } }
        foreach ($n in (Get-DisabledNames $Pic)) { if ($n -ne '') { $all.Add($n) | Out-Null } }
        foreach ($n in $preferred) { $all.Add($n) | Out-Null }
        foreach ($n in $all) { if (-not $list.Contains($n)) { $list.Add($n) | Out-Null } }
    }
    return @{ Mode = $mode; Names = @($list) }
}

# ==========================================================================
#  4. 打开一张网卡: 四级阶梯
# ==========================================================================
function Get-NetAdapterStatus {
    param([string]$Name)
    try {
        if (-not (Have Get-NetAdapter)) { return $null }
        $a = Get-NetAdapter -Name $Name -ErrorAction SilentlyContinue
        if ($null -eq $a) { return $null }
        return "" + $a.AdminStatus
    } catch { return $null }
}

function Open-OneAdapter {
    param([string]$Name, [bool]$Broad)

    Both ("  --- " + $Name + " ---")
    $status0 = Get-NetAdapterStatus $Name
    if ($status0 -ne $null) {
        Both ("      当前管理状态 = " + $status0)
    } else {
        Both "      (拿不到 Get-NetAdapter 的状态; 下面靠 netsh/CIM 判断)"
    }
    if ($status0 -ne $null -and $status0 -ne 'Disabled') {
        Both "      已经不在「禁用」状态 -> 跳过(不动它)"
        return $true
    }

    $looksFound = $true
    if ($status0 -eq $null) {
        # 名字可能对不上(比如 PnP 的 FriendlyName 和 netsh 的连接名不同), 不当成失败
        $looksFound = $false
    }

    if ($DryRun) {
        Both "      [只检查] 会依次尝试: Enable-NetAdapter -> netsh -> Enable-PnpDevice -> Restart-NetAdapter"
        return $true
    }

    # ---- T1: Enable-NetAdapter ----
    if (Have Enable-NetAdapter) {
        try {
            $before = Get-NetAdapterStatus $Name
            if ($before -ne $null -and $before -ne 'Disabled') {
                Both "      T1 Enable-NetAdapter: 无需执行(已经不是禁用状态)"
                return $true
            }
            if ($before -ne $null) {
                Enable-NetAdapter -Name $Name -Confirm:$false -ErrorAction SilentlyContinue
                Start-Sleep -Milliseconds 400
                $after = Get-NetAdapterStatus $Name
                if ($after -ne 'Disabled') {
                    Both ("      T1 Enable-NetAdapter: 成功 (状态 -> " + $after + ")") 'Green'
                    return $true
                }
                Both ("      T1 Enable-NetAdapter: 没生效(状态仍是 " + $after + ") -> 换下一档") 'Yellow'
            } else {
                Both "      T1 Enable-NetAdapter: 这个名字下没有对应适配器 -> 换下一档"
            }
        } catch { Both ("      T1 Enable-NetAdapter 异常: " + $_.Exception.Message + " -> 换下一档") 'Yellow' }
    } else {
        Both "      T1 Enable-NetAdapter: 这台机器没有这个命令 -> 换下一档"
    }

    # ---- T2: netsh(一直都有) ----
    try {
        $o = & netsh interface set interface ('name=' + $Name) admin=enabled 2>&1
        $txt = (($o | Out-String).Trim() -replace "`r?`n", " / ")
        LogLine ("      T2 netsh " + $Name + " => " + $txt)
        Start-Sleep -Milliseconds 400
        $after = Get-NetAdapterStatus $Name
        if ($after -eq $null) {
            # 拿不到状态: 只能按 netsh 的退出码判断
            $rc = $LASTEXITCODE
            if ($rc -eq 0) {
                Both "      T2 netsh: 返回成功(这台机器没有 Get-NetAdapter, 以 netsh 为准)" 'Green'
                return $true
            }
            Both ("      T2 netsh: 返回 " + $rc + " -> 换下一档" + $(if ($txt -ne '') { "   [" + $txt + "]" } else { "" })) 'Yellow'
        } elseif ($after -ne 'Disabled') {
            Both ("      T2 netsh: 成功 (状态 -> " + $after + ")") 'Green'
            return $true
        } else {
            Both ("      T2 netsh: 没生效(状态仍是 " + $after + ")" + $(if ($txt -ne '') { "   [" + $txt + "]" } else { "" }) + " -> 换下一档") 'Yellow'
        }
    } catch { Both ("      T2 netsh 异常: " + $_.Exception.Message + " -> 换下一档") 'Yellow' }

    # ---- T3: Enable-PnpDevice(设备管理器里被禁用的那种, netsh 是打不开的) ----
    if (Have Enable-PnpDevice -and Have Get-PnpDevice) {
        try {
            $dev = @(Get-PnpDevice -Class Net -ErrorAction SilentlyContinue |
                     Where-Object { ("" + $_.FriendlyName) -eq $Name -or ("" + $_.FriendlyName) -like ("*" + $Name + "*") })
            if ($dev.Count -eq 0) {
                Both "      T3 Enable-PnpDevice: 按这个名字没找到网络设备 -> 换下一档"
            } else {
                $okAny = $false
                foreach ($d in $dev) {
                    try {
                        Enable-PnpDevice -InstanceId $d.InstanceId -Confirm:$false -ErrorAction SilentlyContinue
                        Start-Sleep -Milliseconds 500
                        $now = "" + (Get-PnpDevice -InstanceId $d.InstanceId -ErrorAction SilentlyContinue).Status
                        Both ("      T3 Enable-PnpDevice: " + $d.InstanceId + " -> Status=" + $now)
                        if ($now -eq 'OK') { $okAny = $true }
                    } catch { Both ("      T3 对 " + $d.InstanceId + " 失败: " + $_.Exception.Message) 'Yellow' }
                }
                $after = Get-NetAdapterStatus $Name
                if ($okAny -or ($after -ne $null -and $after -ne 'Disabled')) {
                    Both "      T3 Enable-PnpDevice: 成功" 'Green'
                    return $true
                }
                Both "      T3 Enable-PnpDevice: 没成功 -> 换下一档" 'Yellow'
            }
        } catch { Both ("      T3 异常: " + $_.Exception.Message + " -> 换下一档") 'Yellow' }
    } else {
        Both "      T3 Enable-PnpDevice: 这台机器没有这两个命令 -> 换下一档"
    }

    # ---- T4: Restart-NetAdapter(状态是启用但网卡没起来时) ----
    if (Have Restart-NetAdapter) {
        try {
            $cur = Get-NetAdapterStatus $Name
            if ($cur -eq $null) {
                Both "      T4 Restart-NetAdapter: 拿不到这个适配器 -> 跳过"
            } else {
                Restart-NetAdapter -Name $Name -Confirm:$false -ErrorAction SilentlyContinue
                Start-Sleep -Seconds 2
                $after = Get-NetAdapterStatus $Name
                Both ("      T4 Restart-NetAdapter: 执行完, 状态 = " + $after)
                if ($after -ne 'Disabled') {
                    Both "      T4 Restart-NetAdapter: 成功" 'Green'
                    return $true
                }
            }
        } catch { Both ("      T4 异常: " + $_.Exception.Message) 'Yellow' }
    } else {
        Both "      T4 Restart-NetAdapter: 这台机器没有这个命令"
    }

    Both ("      ==> " + $Name + " 四级都没成功" + $(if (-not $looksFound) { "(注意: 这个名字可能只是对不上, 不一定是真失败)" } else { "" })) 'Yellow'
    return $false
}

# ==========================================================================
#  5. 续租 IP / 刷新 DNS / 清 ARP
# ==========================================================================
function Renew-IpAndDns {
    param($Names, [bool]$Broad)
    Both "---- [4/6] 续租 IP / 刷新 DNS(可能要十几秒) ----"
    if ($DryRun) { Both "  [只检查] 会执行 ipconfig /renew、/flushdns、netsh 清 ARP 缓存"; return }

    try {
        $o = & ipconfig /renew 2>&1
        LogLine ("  ipconfig /renew: " + (($o | Out-String).Length) + " 字符输出")
        Both "  ipconfig /renew 已执行"
    } catch { Both ("  ipconfig /renew 异常: " + $_.Exception.Message) 'Yellow' }

    # 逐张补一次(整体 renew 有时会漏掉刚起来的网卡)
    foreach ($n in $Names) {
        try {
            $o = & ipconfig /renew $n 2>&1
            LogLine ("  ipconfig /renew " + $n + ": 已执行")
        } catch { }
    }

    try { & ipconfig /flushdns 2>&1 | Out-Null; Both "  ipconfig /flushdns 已执行" }
    catch { Both "  ipconfig /flushdns 异常(不影响)" 'Yellow' }

    try { & netsh interface ip delete arpcache 2>&1 | Out-Null; Both "  netsh 清 ARP 缓存 已执行" }
    catch { Both "  netsh 清 ARP 缓存 异常(不影响)" 'Yellow' }
    Both ""
}

# ==========================================================================
#  6. 验证: ICMP + TCP 双路
# ==========================================================================
function Test-Icmp {
    param([string]$Target, [int]$TimeoutMs = 1500)
    try {
        $p = New-Object System.Net.NetworkInformation.Ping
        $r = $p.Send($Target, $TimeoutMs)
        return ($r.Status -eq [System.Net.NetworkInformation.IPStatus]::Success)
    } catch { return $false }
}

function Test-Tcp {
    param([string]$Target, [int[]]$Ports = @(53, 80), [int]$TimeoutMs = 1200)
    foreach ($port in $Ports) {
        $c = $null
        try {
            $c = New-Object System.Net.Sockets.TcpClient
            $ar = $c.BeginConnect($Target, $port, $null, $null)
            $ok = $ar.AsyncWaitHandle.WaitOne($TimeoutMs, $false)
            if ($ok -and $c.Connected) { $c.Close(); return $true }
        } catch { } finally { try { if ($c) { $c.Close() } } catch { } }
    }
    return $false
}

function Get-Gateways {
    $gw = New-Object System.Collections.ArrayList
    try {
        if (Have Get-NetRoute) {
            foreach ($r in (Get-NetRoute -DestinationPrefix '0.0.0.0/0' -ErrorAction SilentlyContinue)) {
                $n = "" + $r.NextHop
                if ($n -ne '' -and $n -ne '0.0.0.0' -and -not $gw.Contains($n)) { $gw.Add($n) | Out-Null }
            }
        }
    } catch { }
    if ($gw.Count -eq 0) {
        try {
            foreach ($line in (& route print 0.0.0.0 2>&1)) {
                $s = ("" + $line).Trim()
                if ($s -match '^0\.0\.0\.0\s+0\.0\.0\.0\s+(\S+)') {
                    $n = $Matches[1]
                    if ($n -ne '' -and $n -ne '0.0.0.0' -and -not $gw.Contains($n)) { $gw.Add($n) | Out-Null }
                }
            }
        } catch { }
    }
    return @($gw)
}

function Confirm-Network {
    Both "---- [5/6] 验证网络(ICMP 与 TCP 两条都试) ----"
    $gw = Get-Gateways
    if ($gw.Count -eq 0) {
        Both "  == 没有找到默认网关 -> 现在确实还没连上网络" 'Yellow'
        return $false
    }
    $anyIcmp = $false
    $anyTcp  = $false
    foreach ($g in $gw) {
        $i = Test-Icmp $g
        $t = Test-Tcp $g
        if ($i) { $anyIcmp = $true }
        if ($t) { $anyTcp = $true }
        $verdict = if ($i -and $t) { "ICMP 通 + TCP 通" } elseif ($i) { "ICMP 通 (TCP 没连上)" } elseif ($t) { "ICMP 不通但 TCP 通" } else { "两条都不通" }
        Both ("  网关 " + ("" + $g).PadRight(16) + " -> " + $verdict)
    }
    $ok = ($anyIcmp -or $anyTcp)
    if ($ok) {
        Both "  == 结论: 网络已恢复" 'Green'
    } else {
        Both "  == 结论: 网关卡还不通, 网络还没恢复" 'Yellow'
    }
    Both ""
    return $ok
}

# ==========================================================================
#  7. 主流程
# ==========================================================================
$admin = Show-Environment
if (-not $DryRun -and -not $admin) {
    Both "没有管理员权限 —— 打开网卡、续租 IP 都会失败。" 'Red'
    Both "请右键 恢复网络.bat -> 以管理员身份运行(它会自己申请提权)。" 'Red'
    exit 2
}

if ($DryRun) { Say "================== 只检查不动作 (DryRun) ==================" 'Cyan'; LogLine "DryRun 模式启动" }

$pic = Get-AdapterPicture
$disabled = Show-AdapterPicture $pic
$cand = Get-Candidates $pic ([bool]($Pass -ge 2))

Both ("---- 本次要处理的网卡 (模式 = " + $cand.Mode + ") ----")
if ($cand.Names.Count -eq 0) {
    Both "  (候选为空)" 'Yellow'
} else {
    foreach ($n in $cand.Names) { Both ("  * " + $n) }
}
if ($cand.Mode -eq 'narrow') {
    Both "  说明: 第一轮只动 SkyGuard 自己禁用过的网卡(来自 guard.ini 与断网标记)。"
} else {
    Both "  说明: 这一轮是广扫兜底 —— 前面那轮没把网恢复时才会走到这里。"
}
Both ""

if (-not $DryRun) { Clear-FirewallRules }

Both "---- [3/6] 打开网卡(每张最多试四级) ----"
if ($DryRun) { Both "  [只检查] 下面是「如果真跑会怎么处理」" }
$opened = 0
$tried = 0
foreach ($n in $cand.Names) {
    $tried++
    if (Open-OneAdapter $n ([bool]($Pass -ge 2))) { $opened++ }
}
Both ""
Both ("  小结: 候选 " + $tried + " 张, 处理完成 " + $opened + " 张 (其中「本来就没被禁用」的算无需处理)")

if (-not $DryRun) {
    Renew-IpAndDns $cand.Names ([bool]($Pass -ge 2))
    $ok = Confirm-Network
    if (-not $DryRun) {
        if ($ok) {
            # 网络确实回来了: 把断网标记清掉, 免得下次开机又去"恢复"一次
            try {
                $st = Join-Path $script:DataDir '_netcut_state.txt'
                if (Test-Path $st) {
                    Remove-Item -LiteralPath $st -Force -ErrorAction SilentlyContinue
                    Both "  已清掉断网标记 _netcut_state.txt(下次启动不会再重复恢复)"
                }
            } catch { }
            Both "恢复完成。" 'Green'
            exit 0
        } else {
            Both "这一轮没能确认网络恢复。" 'Yellow'
            exit 1
        }
    }
} else {
    Both "---- [4/6] [5/6] [6/6] 只检查模式: 不续租 IP、不清 ARP、不验证 ----"
    Both ""
    Both "DryRun 结论 = 上面「本次要处理的网卡」就是真正运行时会被处理的名单(窄模式 = guard.ini + 断网标记);" 'Cyan'
    Both "              如果这份名单不对(少了自己的网卡), 请把上面的适配器表格截图发出来。" 'Cyan'
    exit 0
}
