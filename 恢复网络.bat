@echo off
chcp 936 >nul
setlocal enabledelayedexpansion
title SkyGuard 网络恢复

rem ======================================================================
rem  SkyGuard 网络恢复 (V1.1.5-RC2)
rem
rem  本文件只管三件事: 提权 / 找到同目录的 恢复网络.ps1 / 按轮次调用它(第 1 轮窄, 第 2 轮广扫)。
rem  真正的恢复逻辑在 恢复网络.ps1 里(纯文本, 可以逐行看) —— 那样才写得够细:
rem  四级备选阶梯(Enable-NetAdapter -> netsh -> Enable-PnpDevice -> Restart-NetAdapter)、
rem  四来源枚举网卡、ICMP+TCP 双路验证。这些塞进 .bat 的一行里会撞 cmd 的 8191 字符上限,
rem  而且引号转义本身就是脆弱点。
rem
rem  用法:  双击(会自己申请提权)   或   右键 -> 以管理员身份运行
rem         /dryrun   只检查不动作, 不需要管理员 —— 换台电脑先跑它, 确认这个脚本认得出你的网卡
rem  日志:  %ProgramData%\SkyGuard\RestoreNetwork.log
rem ======================================================================

set "PS1=%~dp0恢复网络.ps1"
set "DRYRUN="
if /i "%~1"=="/dryrun"  set "DRYRUN=1"
if /i "%~1"=="-dryrun" set "DRYRUN=1"

if not exist "%PS1%" goto :fallback

net session >nul 2>&1
if not errorlevel 1 goto :run
if defined DRYRUN goto :run
echo 需要管理员权限, 正在申请提权...
powershell -NoProfile -Command "Start-Process -FilePath '%~f0' -ArgumentList '%~1' -Verb RunAs"
echo 如果弹出 UAC 窗口, 请点[是]; 本窗口可以关掉, 提权后的新窗口会继续跑.
echo 如果没有弹窗: 请右键本文件 -> 以管理员身份运行.
pause
exit /b

:run
if defined DRYRUN (
    echo 只检查模式: 不会碰任何网卡.
    echo.
    powershell -NoProfile -ExecutionPolicy Bypass -File "%PS1%" -DryRun
    set "RC=!errorlevel!"
    echo.
    echo 检查完毕. 退出码 = !RC!
    goto :end
)

echo ================================================================
echo   第 1 轮: 只处理 SkyGuard 自己禁用过的网卡
echo ================================================================
echo.
powershell -NoProfile -ExecutionPolicy Bypass -File "%PS1%" -Pass 1
set "RC=!errorlevel!"
if "!RC!"=="0" goto :done
if "!RC!"=="2" goto :envfail

echo.
echo 第 1 轮没能确认网络恢复(退出码 !RC!). 等 8 秒后做第 2 轮(广扫兜底)...
ping -n 9 127.0.0.1 >nul 2>&1
echo.
echo ================================================================
echo   第 2 轮: 打开所有能识别的网卡(兜底)
echo ================================================================
echo.
powershell -NoProfile -ExecutionPolicy Bypass -File "%PS1%" -Pass 2
set "RC=!errorlevel!"
if "!RC!"=="0" goto :done

echo.
echo ----------------------------------------------------------------
echo  两轮都没能确认网络恢复. 请按顺序试(从最有效的开始):
echo    1) 重启电脑(最快、最有效)
echo    2) 设备管理器 - 网络适配器 - 右键[启用设备]; 或先[禁用]再[启用]
echo    3) 如果装了 VPN / 游戏加速器, 先退出它再重试
echo    4) 再运行一次本脚本
echo  日志: %ProgramData%\SkyGuard\RestoreNetwork.log
echo  把本窗口内容截图发给开发者即可.
echo ----------------------------------------------------------------
goto :end

:done
echo.
echo ================================================================
echo   网络已恢复.
echo ================================================================
goto :end

:envfail
echo.
echo 环境不足(多半是没提权), 没能执行. 请右键本文件 -^> 以管理员身份运行.
goto :end

rem ======================================================================
rem  兜底: 找不到 恢复网络.ps1 时用的最小应急路径(只用 netsh + ipconfig)
rem  这条路不依赖 Get-NetAdapter / Enable-PnpDevice 等任何新命令, 老系统上也能跑;
rem  代价是没有四级阶梯、没有 TCP 验证。发布包里两个文件是一对, 正常不会走到这里。
rem ======================================================================
:fallback
echo ======================================================================
echo  找不到 恢复网络.ps1
echo ======================================================================
echo.
echo  恢复网络.bat 和 恢复网络.ps1 必须放在同一个文件夹里.
echo  现在退到"最小应急路径": 只用 netsh 逐个接口试着启用 + 续租 IP + 刷新 DNS.
echo.
net session >nul 2>&1
if errorlevel 1 (
    echo 需要管理员权限, 正在申请提权...
    powershell -NoProfile -Command "Start-Process -FilePath '%~f0' -Verb RunAs"
    echo 如果弹出 UAC 窗口, 请点[是].
    pause
    exit /b
)
powershell -NoProfile -ExecutionPolicy Bypass -Command "$d=Join-Path $env:ProgramData 'SkyGuard'; New-Item -ItemType Directory -Force -Path $d | Out-Null; $log=Join-Path $d 'RestoreNetwork.log'; $names=@(); try { $names=(netsh interface show interface) | Select-Object -Skip 3 | ForEach-Object { $s=$_.TrimEnd(); $k=$s.LastIndexOf('  '); if($k -gt 0){ $s.Substring($k).Trim() } } } catch { }; foreach($nm in ($names | Where-Object { $_ })){ Write-Host ('    启用: ' + $nm); $o = & netsh interface set interface ('name=' + $nm) admin=enabled 2>&1; Add-Content -LiteralPath $log -Value ($o -join ' ') -ErrorAction SilentlyContinue }; Write-Host '    续租 IP...'; & ipconfig /renew 2>&1 | Add-Content -LiteralPath $log -ErrorAction SilentlyContinue; & ipconfig /flushdns 2>&1 | Add-Content -LiteralPath $log -ErrorAction SilentlyContinue; Write-Host '    完成.'"
echo.
echo  已执行. 请检查网络是否恢复; 还不行就重启电脑.
echo  日志: %ProgramData%\SkyGuard\RestoreNetwork.log

:end
echo.
pause
endlocal
exit /b