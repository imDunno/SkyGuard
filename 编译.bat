@echo off
chcp 936 >nul 2>&1
setlocal
cd /d "%~dp0"

rem =====================================================================
rem  编译 SkyGuard 图形版
rem  用什么编译: Windows 自带的 C# 编译器 csc.exe (.NET Framework 4.x)
rem             —— 不需要 Visual Studio, 不需要 .NET SDK, 不需要联网
rem  产物:       本目录下的 SkyGuardGUI.exe (单文件)
rem =====================================================================

echo =====================================================
echo    编译 SkyGuard 图形版
echo =====================================================

set "CSC=%SystemRoot%\Microsoft.NET\Framework64\v4.0.30319\csc.exe"
if not exist "%CSC%" set "CSC=%SystemRoot%\Microsoft.NET\Framework\v4.0.30319\csc.exe"
if not exist "%CSC%" goto :nocsc
echo   编译器: %CSC%

if not exist "SkyGuardGUI.cs" goto :nosrc

echo   正在编译 ...
"%CSC%" /nologo /target:winexe /platform:anycpu /optimize+ ^
        /codepage:65001 ^
        /out:SkyGuardGUI.exe ^
        /win32manifest:SkyGuardGUI.exe.manifest ^
        /reference:System.dll ^
        /reference:System.Core.dll ^
        /reference:System.Drawing.dll ^
        /reference:System.Windows.Forms.dll ^
        SkyGuardGUI.cs

if errorlevel 1 goto :failed
if not exist "SkyGuardGUI.exe" goto :failed

echo.
echo   编译成功: %~dp0SkyGuardGUI.exe
for %%F in ("SkyGuardGUI.exe") do echo   大小: %%~zF 字节
echo.
echo   下一步: 右键 SkyGuardGUI.exe - 以管理员身份运行
goto :done

:nocsc
echo   错误: 找不到 csc.exe。
echo   预期位置: %SystemRoot%\Microsoft.NET\Framework64\v4.0.30319\csc.exe
echo   本机应当自带 (.NET Framework 4.x)。
goto :done

:nosrc
echo   错误: 当前目录找不到 SkyGuardGUI.cs
goto :done

:failed
echo.
echo   错误: 编译失败。请把上面的报错原文保留下来。

:done
echo.
echo   窗口将在 15 秒后自动关闭
timeout /t 15 /nobreak >nul 2>&1
if errorlevel 1 ping -n 16 127.0.0.1 >nul 2>&1
endlocal
exit /b
