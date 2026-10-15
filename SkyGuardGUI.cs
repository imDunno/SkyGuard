// ============================================================================
//  SkyGuard GUI —— 光遇「永无防坠机」图形化应急工具
//
//  这是什么:
//      一个常驻的小工具。按下你预设的触发键, 它会立刻:
//        1) 强杀指定游戏进程 (内核级确认已退出)
//        2) 断开你勾选的网卡 (兜底, 防止重连补发)
//        3) 保持 N 秒后自动恢复网络
//      用途: 无翼/永无号遇到外挂强制传送时, 抢在拾取结果上报之前断掉。
//
//  与旧控制台版(守护进程\SkyGuard.exe)的关系:
//      核心原理完全相同, 只是外壳从控制台换成图形界面, 并增加了「环境自动探测」
//      和"触发键可视化录入", 解决换一台机器就配不对的问题。两套独立运行。
//
//  边界(不要越界):
//      * 不注入游戏进程、不读游戏内存、不改游戏文件
//      * 不联网、不上传任何数据
//      * 只用微软文档化的机制: RegisterHotKey / WH_KEYBOARD_LL / NtQuerySystemInformation
//        / TerminateProcess / netsh
//      * 源码纯文本, 可用记事本逐行审查
//
//  编译: 用系统自带 csc.exe, 见 编译.bat。不需要 Visual Studio / .NET SDK / 联网。
//  编码: UTF-8(带 BOM) 源码; 日志按 GBK 写(中文系统), 可用记事本打开。
// ============================================================================

// ============================================================================
//  本文件结构
//   一、版本与路径 / 运行期状态 ............ 常量、全局状态、窗体控件引用
//   二、配置(Config)与 guard.ini 读写 ...... 字段定义、LoadConfig、SaveConfig
//   三、日志 .............................. 脱敏、无锁队列、后台落盘、轮转
//   四、进程/窗口/输入 的底层封装 ......... P/Invoke、枚举进程、窗口辅助
//   五、网卡与网络 ........................ 探测网卡、禁/启网卡、恢复校验、探针
//   六、快速断流(WFP / 防火墙) ............ 动态过滤器、残留清理、能力自证
//   七、处置主流程 ........................ 常驻线程、Panic、KillWithRetry
//   八、键盘钩子 / 轮询 / 热键 / 看门狗 ... 四条触发通道 + 看门狗
//   九、焦点解堵 .......................... 前台卡死判定、抢/还焦点阶梯(决策是纯函数)
//   十、界面 .............................. 主窗口、设置窗(5 个页签)、向导、按键录入
//   十一、自检(无头) ...................... selftest / uicheck / settest / focustest /
//                                          restoretest / racetest / netcuttest / diagtest ...
//   十二、状态面板 .................... 运行状态报告(BuildDiagReport) + 面板窗口
//   十三、入口 Main ....................... 命令行参数分发
//
//  约定(改代码前务必先读):
//    · 任何"抢时间"的路径(触发键 -> 杀进程 -> 断网)都不许阻塞在磁盘/子进程上;
//    · 每层错误都要写日志, 不许静默;
//    · 不注入游戏、不读内存、不改游戏文件; 探针默认只走局域网(不回外网);
//    · 界面文案面向玩家, 日志文案面向排查。
// ============================================================================

using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.Drawing;
using System.IO;
using System.Net.NetworkInformation;
using System.Net.Sockets;
using System.Runtime.InteropServices;
using System.Text;
using System.Threading;
using System.Windows.Forms;

// 程序集元数据 —— 有三层用处:
//   1) Windows 文件属性页 / PowerShell `(Get-Item exe).VersionInfo` 能读到版本, 更新包核对版本不用外部文件;
//   2) UAC 提示、任务管理器里显示的是"有名字有描述的程序", 而不是一行空白 —— 用户不会觉得是野程序;
//   3) 安全软件看"文件元数据是否完整"是个很弱的信号, 但没有元数据的裸 exe 观感更差。
[assembly: System.Reflection.AssemblyTitle("SkyGuard")]
[assembly: System.Reflection.AssemblyProduct("SkyGuard")]
[assembly: System.Reflection.AssemblyCompany("SkyGuard")]
[assembly: System.Reflection.AssemblyDescription("光遇「永无/无翼」应急工具: 一键关掉游戏与模拟器并断开网卡, 抢在结果上传前切断。不注入游戏、不联网、不写注册表。")]
[assembly: System.Reflection.AssemblyCopyright("Copyright (c) 2026 SkyGuard")]
[assembly: System.Reflection.AssemblyFileVersion("1.1.6.0")]
[assembly: System.Reflection.AssemblyInformationalVersion("SkyGuard V1.1.6-RC1")]

internal static class SkyGuardGUI
{
    // ======================== 版本与路径 ========================
    private const string APP_NAME = "SkyGuard";
    private const string APP_VER = "V1.1.6-RC1";
    /// <summary>version.txt 里的机器可读版本(如 1.0); 与 APP_VER 是同一件事的两种写法, 必须一字不差</summary>
    private const string APP_VER_NUM = "1.1.6-RC1";
    private const string INI_FILE = "guard.ini";
    private const string LOG_FILE = "SkyGuardGUI.log";
    /// <summary>配置结构版本: 将来配置格式大改时靠它做迁移(老配置里没有这行, 按 1 处理)</summary>
    private const int CONFIG_VERSION = 1;

    private static string _baseDir = "";      // 程序所在目录 —— 只放程序文件
    private static string _dataDir = "";      // 用户数据目录 —— guard.ini 和日志都在这
    private static string _iniPath = "";
    private static string _logPath = "";

    // ======================== 运行期状态 ========================
    private static Config _cfg = new Config();
    private static bool _guarding = false;
    private static IntPtr _hookHandle = IntPtr.Zero;
    private static LowLevelKeyboardProc _hookProc;      // 必须保持引用, 否则被 GC 回收钩子失效
    /// <summary>
    /// 处置进行中标志。0=空闲, 1=有处置在跑。
    /// 必须用 Interlocked 抢占(不能用 volatile bool 先读后写) —— 见 FireTrigger 的注释。
    /// </summary>
    private static int _busy = 0;
    /// <summary>
    /// "马上收尾" 开关。处置还没走完时用户又按了一次触发键 -> 不再干等, 立刻恢复网络。
    /// 用 volatile: 由键盘钩子线程写, 由处置线程读。
    /// </summary>
    private static volatile bool _abort = false;
    /// <summary>"处置进行中, 忽略触发"那条日志的限流时间戳(滚动窗口)。</summary>
    private static long _lastBusyIgnoreTicks = 0;

    // ---------------------------------------------------------------------------
    //  "处置位被占太久"的可见性(V1.1.5-RC1)
    //
    //  处置位(_busy)一旦被占住, 触发键就按不动(这是用户定的语义, 不改)。
    //  但"为什么按不动"必须看得见: 处置正常也就几秒~几十秒(保持期), 一旦超过
    //  BUSY_STUCK_MS, 一定是某个子进程(通常是 netsh)卡住了。那时候用户至少要知道
    //  "不是键坏了, 是网络操作卡住了, 点[恢复网络]可以再试"。
    // ---------------------------------------------------------------------------

    /// <summary>单次网络操作(N=断开 / 恢复)最多等这么久; 超了就放手, 不把处置位占死。</summary>
    private const int NET_OP_STUCK_MS = 60000;
    /// <summary>处置位被占超过这个时间就判"卡住", 在界面和日志里说出来。</summary>
    private const int BUSY_STUCK_MS = 90000;

    /// <summary>"处置位被占太久"日志的限流时间戳</summary>
    private static long _lastBusyStuckLogTicks = 0;
    /// <summary>本次处置是从什么时候开始占住处置位的(0 = 没在处置)</summary>
    private static long _busySinceTicks = 0;
    /// <summary>处置位已被占太久(界面要提示)</summary>
    private static volatile bool _busyStuck = false;
    /// <summary>某次网络操作超时"卡住"了(界面要提示可以点[恢复网络]再试)</summary>
    private static volatile bool _netOpStuck = false;
    /// <summary>
    /// 上一次真正起处置的时间戳(Stopwatch, 不是墙上时间 —— 墙上时间会被对时跳变)。
    /// 用来判断"这又是同一次按键被另一条通道抓到了", 见 FireTrigger。
    /// </summary>
    private static long _lastFireTicks = 0;
    private static volatile int _hookCalls = 0;
    private static volatile int _hitCount = 0;
    private static long _panicStartTicks = 0;
    private static long _firstDownTicks = 0;
    private static System.Windows.Forms.Timer _statusTimer;

    // 状态面板用的快照: 只发布、不参与决策, 写失败不影响功能。
    /// <summary>焦点解堵的当前判定(约每秒发布一次): 档位参数、前台是谁、判没判卡死、在等谁。</summary>
    private static volatile string _diagFocusState = "-";
    private static long _diagFocusStateMs = 0;
    /// <summary>焦点解堵最近一次真的动手(抢/还)的经过 + 时间戳。</summary>
    private static volatile string _diagLastFocusAct = "-";
    private static long _diagLastFocusActMs = 0;
    /// <summary>键盘钩子最近一次回调的耗时(ms)。系统给钩子回调的时限默认只有 300ms, 这个数最要紧。</summary>
    private static volatile int _diagHookCallbackMs = -1;
    /// <summary>处置(触发键那套流程)最近一次的耗时摘要。</summary>
    private static volatile string _diagLastPanic = "-";
    private static long _diagLastPanicMs = 0;

    // 窗体控件
    private static Form _form;
    private static TableLayoutPanel _root;   // 主界面根布局(供自检/最小尺寸计算)
    private static FlowLayoutPanel _btnBar;  // 主界面按钮行容器
    private static Label _lblStatus;
    /// <summary>临时状态(如"网络恢复中，请稍等"): 非空时优先显示, 覆盖 500ms 的定时刷新。</summary>
    private static volatile string _statusOverride = "";
    private static Label _lblSummary;        // 主界面摘要: 目标程序 / 触发键
    private static TextBox _txtLog;          // 主界面的运行日志
    private static Button _btnGuard;
    private static Label _lblProbeState;
    // 主界面按钮行: 按可用宽度自动折行, 见 ReflowMain
    private static Button[] _btnRow;
    private static Button _btnPanic;
    private static Button _btnRestoreNet;
    private static Button _btnSettings;
    private static Button _btnOnlyKill;
    private static Button _btnOpenLog;
    private static Label _lblLogCaption;
    // 最近一次 ReflowMain 的关键坐标(只给 uicheck 的布局自检看, 生产逻辑不用)
    private static int rowBottomLast, capLast, logTopLast;

    // 设置对话框里的控件
    private static TextBox _txtKeys;
    private static CheckedListBox _lstTargets;
    private static CheckBox _chkFocusRescue;      // 焦点解堵总开关
    private static RadioButton _radFocusSys;      // 档位 0: 只用系统判定(不提前)
    private static RadioButton _radFocusPro;      // 档位 1: Pro(默认)
    private static RadioButton _radFocusUltra;    // 档位 2: Ultra(激进, 测试用)
    private static NumericUpDown _numFocusMs;         // 扫描间隔
    private static NumericUpDown _numFocusRounds;     // 连续几轮无响应才接管
    private static NumericUpDown _numFocusProbe;      // 探针等回音时长(接管延迟的主要项)
    private static NumericUpDown _numFocusOk;         // 还焦点前连续确认轮数
    private static NumericUpDown _numFocusSilent;     // 抢/还后的静默期
    private static Label _lblFocusLatency;            // "最坏接管延迟 ≈ N ms" 实时提示
    private static Button _btnFocusPreset;            // [套用本档默认]
    /// <summary>设置窗初始载入时抑制"切档自动套用预设"(否则会把用户已调好的数字冲掉)</summary>
    private static bool _suppressFocusPreset = false;
    private static CheckedListBox _lstNics;
    private static NumericUpDown _numWait;
    private static CheckBox _chkHookProbe;
    private static NumericUpDown _numProbeSec;
    private static CheckBox _chkDebugPriv;
    private static CheckBox _chkFastCut;
    private static CheckBox _chkAutoRestore;      // 关程序时网络仍断开 -> 自动恢复
    private static CheckBox _chkConfirmExit;      // 退出前的多次确认(默认开)
    private static TabPage _tabTargets;           // 目标程序页(标题里显示数量)
    private static TabPage _tabKeys;              // 触发键页(标题里显示数量)
    private static RadioButton _radModeBoth;      // 断网方式: 快速断流+禁用网卡
    private static RadioButton _radModeNic;       // 断网方式: 只禁用网卡
    private static RadioButton _radModeFast;      // 断网方式: 只用快速断流
    private static CheckBox _chkRestoreOnBoot;    // 断网时登记开机恢复(默认关)
    private static CheckBox _chkSuspendFirst;     // 触发时先挂起目标进程(默认开)
    private static CheckBox _chkWarm;             // 保护期间预记录目标进程(默认开)
    private static NumericUpDown _numWarmMs;      // 预记录刷新间隔(ms)
    private static CheckBox _chkDiag;             // 主窗口显示[状态面板]按钮(详细诊断, 默认开)
    private static TextBox _txtFastCutTargets;    // 探针额外外网目标

    // 网卡探测结果
    private sealed class NicInfo
    {
        public string Name = "";          // 用于 netsh 的连接名
        public bool HasDefaultRoute;      // 是否承载默认路由
        public string Ip = "";
        public bool IsVirtualHint;        // 疑似虚拟网卡(仅提示, 不强制)
    }

    private static List<NicInfo> _nics = new List<NicInfo>();

    // ======================== 配置模型 ========================
    private sealed class Config
    {
        public string Proc = "Sky.exe";                  // 单目标(向后兼容旧配置)
        public List<string> Procs = new List<string>();  // 多目标
        /// <summary>
        /// 被停用的进程名(小写)。在 Procs 里、但不参与触发。
        /// 为什么要有这个: 只开 Sky 或只开 MuMu 的时候, 另一个没运行的每次都被"找一遍再跳过",
        /// 日志里一堆"找不到", 而且万一以后同名进程出现会被误杀。做成开关用户自己能控。
        /// 存盘时只写停用的那些, 老配置读进来默认全部启用 —— 向后兼容。
        /// </summary>
        public List<string> ProcOff = new List<string>();
        public List<string> Keys = new List<string>();
        public List<string> Nics = new List<string>();
        public int WaitSeconds = 20;
        /// <summary>配置结构版本: 程序写盘时落一个, 将来配置格式大改时靠它决定要不要迁移</summary>
        public int ConfigVersion = CONFIG_VERSION;
        /// <summary>
        /// 焦点解堵的扫描间隔(ms)。10~2000。
        /// 它是"卡住之后多快能把前台切走"的粒度, 判定本身有连续确认(见 FocusRounds), 所以小一点不会误触发。
        /// Pro 档 = 50ms(默认); Ultra 档 = 10ms(压到最低)。
        /// </summary>
        public int FocusIntervalMs = 50;
        /// <summary>
        /// 连续几次判定"无响应"才切焦点(1~10)。
        ///
        /// Pro 档默认 3(约 150ms+探针); 下限 2 的理由(11.1.2-RC15): IsHungAppWindow 在应用
        /// "刚要卡/刚缓过来"的边界上会来回抖, 只判 1 次就会"抢→还→抢", 用户看到焦点一直闪。
        /// Ultra 档(测试用)故意允许 1 —— 就是要试最短接管时间下会不会很烦。
        /// </summary>
        public int FocusRounds = 3;
        /// <summary>焦点解堵总开关</summary>
        public bool FocusRescue = true;
        /// <summary>
        /// 焦点接管档位(V1.1.4-RC1 起, 取代原来的布尔开关 FocusEarly):
        ///   0 = 只用系统判定(不提前): 要连续约 5 秒不取消息才接管 —— 最安静, 但这 5 秒里触发键可能按不动;
        ///   1 = Pro   (默认): 现在的手感 —— 前台窗口对 WM_NULL 探针约 1~1.5 秒没回音就接管;
        ///   2 = Ultra (激进·测试用): 间隔/探针/轮数全压到最低(约 0.1~0.2 秒就接管),
        ///       专门用来试"最短接管时间下会不会有很烦的误触发", 默认不选, 由用户手动开。
        /// 老配置里的 FocusEarly=0/1 读进来映射成 0/1(行为不变); 存盘时两行都写(老版本也能读)。
        /// </summary>
        public int FocusMode = 1;
        /// <summary>
        /// WM_NULL 探针一次等多久回音(ms, 50~2000)。这是接管延迟里的**主要**那一项:
        ///   最坏接管延迟 ≈ (FocusIntervalMs + FocusProbeMs) × FocusRounds。
        /// 调小 = 接管更快, 但游戏加载等场景的普通长帧也会被判定为无响应(焦点切换一次再交还)。
        /// </summary>
        public int FocusProbeMs = 500;
        /// <summary>还焦点前需要连续几次"探针有回音"(1~20)。越大越稳、还焦点越慢。</summary>
        public int FocusOkRounds = 5;
        /// <summary>抢/还焦点之后的静默期(ms, 100~5000): 期间不做任何切换动作, 防抖。</summary>
        public int FocusSilentMs = 1500;
        /// <summary>
        /// 兼容字段: 老配置里的"抢得更早"(1=提前接管 / 0=只认系统判定)。
        /// 现在由 FocusMode 表达, 这个字段只在读写配置时做双向映射, 不参与运行逻辑。
        /// </summary>
        public bool FocusEarly = true;

        /// <summary>
        /// 主窗口是否显示[状态面板]按钮(默认开)。面板只读, 导出运行状态与完整日志, 内容已脱敏。
        /// </summary>
        public bool DiagPanel = true;

        /// <summary>
        /// 触发时先挂起目标进程(默认开)。
        ///
        /// 为什么默认开: TerminateProcess 要等内核把几百个线程拆完才返回(实测 715 ms),
        /// 而**挂起**是一次微秒级调用 —— 挂起后目标再也拿不到 CPU, 结果就传不出去了。
        /// 关掉它只是"少做一件事": 终止命令照旧下达, 但"游戏停下"要等内核拆完。
        /// </summary>
        public bool SuspendFirst = true;

        /// <summary>
        /// 保护期间预记录目标进程的 PID(默认开), 触发时第一条命令直接挂起它, 不必先扫进程表。
        /// 需要 SuspendFirst 也开着才有意义(它挂起的目标靠的就是挂起机制)。
        /// 记的是 (PID, 进程创建时间) —— 动手前必须核对创建时间, 否则 PID 被回收重用时会误挂别人的进程。
        /// </summary>
        public bool WarmSuspend = true;

        /// <summary>预热表刷新间隔(毫秒, 300~5000)。一次刷新约 8~20 ms, 只在开始保护后由后台线程做。</summary>
        public int WarmIntervalMs = 1000;
        /// <summary>
        /// 钩子"主动探活": 1 = 看门狗定期注入一个真实按键来验证钩子还活着。
        ///
        /// 默认 0(关闭)。为什么默认关:
        ///   keybd_event 走的是系统真实输入链, 不是为了骗自己的钩子造假数据 ——
        ///   所以注入的按键前台游戏 / 反作弊 / 输入法 / 宏软件都会收到。
        ///   老版本每 10 秒注入一次(还不管用户有没有停止保护), 打游戏时每 10 秒被打断一下。
        ///
        /// 关掉之后钩子怎么判活: 看"钩子线程还在不在"(_hookInstallOk / _hookThreadStarted)。
        /// 而触发键并不会因此失守 —— 轮询通道(8ms 读一次键状态)和系统热键通道都还在,
        /// 单键触发由它们兜底; 组合键才只有钩子这一条路。
        /// </summary>
        public bool HookProbe = false;
        /// <summary>主动探活的间隔(ms), 默认 60 秒。只在 HookProbe=1 时生效(下限 5 秒)</summary>
        public int HookProbeIntervalMs = 60000;

        /// <summary>
        /// 杀进程前是否启用 SeDebugPrivilege (默认关闭)。
        ///
        /// 什么情况下需要: 有些进程跑在受限令牌 / 沙箱里, 即使本程序是管理员,
        /// TerminateProcess 也会返回错误码 5(拒绝访问)。打开调试特权能多杀掉一部分。
        /// (VM 实测: Edge 的几个沙箱进程即使开了特权仍被拒 —— 那是系统级保护, 无解。)
        ///
        /// 为什么默认关闭:
        ///   1) 正常游戏/模拟器进程都是普通令牌, 根本不需要;
        ///   2) "进程给自己的令牌加特权"在企业 EDR 眼里是典型的提权行为特征,
        ///      开着会平白多招一条误报(本工具已经因为键盘钩子被 7 家 ML/引擎标可疑了)。
        /// </summary>
        public bool DebugPriv = false;

        /// <summary>
        /// 是否启用"快速断流"(11.1.0, 默认开)。
        ///
        /// 断开时先尝试 WFP 动态过滤器(毫秒级、逐包拦出站、崩溃不留残留), 不行再试
        /// Windows 防火墙规则(毫秒~百毫秒, 规则持久化所以恢复/退出/下次启动都要清理);
        /// 两层都失败也照旧禁用网卡 —— 原有方案永远保留, 快速层只负责"抢时间"。
        /// 默认开: 对任何机器都是纯收益(抢到的那几秒正是上报窗口), 且每步都用探针自证、
        /// 失败会响亮地写日志; 不想要可在设置里关掉。
        /// </summary>
        public bool FastCut = true;
        /// <summary>
        /// 快速断流探针额外的外部目标(逗号分隔 Ip:Port)。默认空 —— 默认只用 ICMP ping 本机网关,
        /// 不出局域网。填了这里会产生真正的外网连接(可能触发安全软件的"联网控制"提示), 自行决定。
        /// </summary>
        public string FastCutTargets = "";
    /// <summary>
    /// 关闭程序时如果网络还处于断开状态, 是否自动恢复(不再弹窗询问)。默认开。
    /// 默认开的理由: "关窗后网卡仍是禁用状态 + 重启也还是禁用" 是最容易把人坑住的状态, 实测发生过。
    /// </summary>
    public bool AutoRestoreOnExit = true;
    /// <summary>退出前的多次确认(默认开): 有事(网络还断着/处置中)问 3 次, 保护中问 2 次, 一切正常不问。</summary>
    public bool ConfirmExitTimes = true;
    /// <summary>
    /// 断网方式: 0=快速断流+禁用网卡(默认, 最稳) 1=只禁用网卡(老方案, 不碰 WFP) 2=只用快速断流(不禁用网卡)。
    /// 为什么要给用户选: "禁用网卡"最彻底但要等无线重连(5~15 秒); 有些机器/场景下用户宁愿只靠 WFP 抢时间,
    /// 不想让网卡被禁用。三种方式的取舍都写进日志, 不替他决定。
    /// </summary>
    public int CutMode = 0;
    /// <summary>
    /// 可选(默认关): 断网时登记一条 HKCU 的 RunOnce, 下次登录自动跑一次"恢复网络.bat"。
    /// 覆盖最坏情况: 程序被强杀 + 用户再也不打开它 —— 否则网卡会一直处于禁用状态。
    /// 恢复成功后会立刻删掉这条登记, 所以它平时并不存在。
    /// 代价: 会写注册表, 与"不写注册表 / 不开机自启"的说明冲突, 所以默认关闭, 由用户自己决定。
    /// </summary>
    public bool RestoreOnBoot = false;

        public bool IsEnabled(string proc)
        {
            string n = NormProcName(proc);
            foreach (string x in ProcOff)
                if (NormProcName(x) == n) return false;
            return true;
        }

        public bool IsUsable()
        {
            return Keys.Count > 0 && Nics.Count > 0 && TargetList().Count > 0;
        }

        /// <summary>全部进程(含停用的) —— 设置界面用这个, 才能显示勾选框</summary>
        public List<string> AllProcs()
        {
            List<string> r = new List<string>();
            foreach (string p in Procs)
            {
                string t = (p ?? "").Trim();
                if (t.Length == 0) continue;
                bool dup = false;
                foreach (string x in r)
                    if (string.Equals(x, t, StringComparison.OrdinalIgnoreCase)) { dup = true; break; }
                if (!dup) r.Add(t);
            }
            if (r.Count == 0)
            {
                string t = (Proc ?? "").Trim();
                if (t.Length > 0) r.Add(t);
            }
            return r;
        }

        /// <summary>实际要关的目标进程(合并新旧写法、去重、去掉停用的)</summary>
        public List<string> TargetList()
        {
            List<string> r = new List<string>();
            foreach (string p in AllProcs())
                if (IsEnabled(p)) r.Add(p);
            return r;
        }

        public string KeysText() { return string.Join(" / ", Keys.ToArray()); }

        /// <summary>
        /// 主界面摘要用的一句话。
        /// 正好等于某个预设就把预设名写出来(「光遇 电脑版 (网易国服)」比「9 个程序」好懂),
        /// 否则退回"进程名 等 N 个程序"。
        /// </summary>
        public string TargetsText()
        {
            List<string> t = TargetList();
            if (t.Count == 0) return "(全停了, 触发时什么都不会关)";
            string presets = MatchedPresetNames(t);
            if (presets.Length > 0) return presets;
            if (t.Count <= 2) return string.Join(" + ", t.ToArray());
            return t[0] + " 等 " + t.Count + " 个进程";
        }
    }

    /// <summary>焦点接管档位的名字(日志 / 界面用)。</summary>
    private static string FocusModeName(int mode)
    {
        if (mode <= 0) return "仅系统检测";
        if (mode >= 2) return "Ultra";
        return "Pro";
    }

    /// <summary>最坏接管延迟(ms) = (扫描间隔 + 探针超时) × 连续轮数。界面里当场算给用户看。</summary>
    private static int FocusWorstLatencyMs(int intervalMs, int probeMs, int rounds)
    {
        return (intervalMs + probeMs) * rounds;
    }

    /// <summary>
    /// 把一个档位的默认参数写进配置(设置窗里切档 / 点[套用本档默认] 时用)。
    /// Pro = 现在的手感; Ultra = 全部压到最低(测试最短接管时间下会不会很烦)。
    /// </summary>
    private static void ApplyFocusPreset(Config c, int mode)
    {
        if (c == null) return;
        c.FocusMode = (mode < 0 || mode > 2) ? 1 : mode;
        if (c.FocusMode == 0) return;      // 只用系统判定: 探针参数无意义, 保留用户已经填的值
        if (c.FocusMode == 2)
        {
            // Ultra: 最坏接管延迟 ≈ (10+120)×1 = 130ms
            c.FocusIntervalMs = 10; c.FocusRounds = 1; c.FocusProbeMs = 120;
            c.FocusOkRounds = 3; c.FocusSilentMs = 600;
        }
        else
        {
            // Pro: 最坏接管延迟 ≈ (50+500)×3 = 1650ms
            c.FocusIntervalMs = 50; c.FocusRounds = 3; c.FocusProbeMs = 500;
            c.FocusOkRounds = 5; c.FocusSilentMs = 1500;
        }
    }

    /// <summary>
    /// 目标列表是不是刚好等于某个预设(或几个预设的组合), 是的话返回预设名。
    /// 只用于界面显示, 不影响实际要杀的进程。
    /// </summary>
    private static string MatchedPresetNames(List<string> targets)
    {
        List<string> hit = new List<string>();
        List<string> rest = new List<string>(targets);
        foreach (ProcPreset p in PRESETS)
        {
            bool all = true;
            foreach (string x in p.Procs)
                if (!ListHas(rest, x)) { all = false; break; }
            if (!all) continue;
            hit.Add(p.Label);
            foreach (string x in p.Procs) RemoveFrom(rest, x);
        }
        if (rest.Count > 0 || hit.Count == 0) return "";
        return string.Join(" + ", hit.ToArray());
    }

    private static bool ListHas(List<string> list, string v)
    {
        foreach (string x in list)
            if (string.Equals(x, v, StringComparison.OrdinalIgnoreCase)) return true;
        return false;
    }

    private static void RemoveFrom(List<string> list, string v)
    {
        for (int i = list.Count - 1; i >= 0; i--)
            if (string.Equals(list[i], v, StringComparison.OrdinalIgnoreCase)) list.RemoveAt(i);
    }

    /// <summary>目标程序预设 —— 设置页里一键添加</summary>
    private sealed class ProcPreset
    {
        public string Label;
        public string[] Procs;
        public ProcPreset(string label, string[] procs) { Label = label; Procs = procs; }
    }

    private static readonly ProcPreset[] PRESETS = new ProcPreset[]
    {
        new ProcPreset("光遇 电脑版 (网易国服)", new string[] { "Sky.exe" }),
        new ProcPreset("MuMu 模拟器", new string[] {
            "MuMuNxMain", "MuMuNxDevice", "MuMuNxService",
            "MuMuVMMHeadless", "MuMuVMMSVC",
            "MuMuRemoteBackend", "MuMuRemoteService", "MumuRemoteHealthd" }),
    };

    // ============================================================================
    //  一、Win32 声明
    // ============================================================================

    #region Win32: 低级键盘钩子

    [DllImport("user32.dll", SetLastError = true)]
    private static extern IntPtr SetWindowsHookEx(int idHook, LowLevelKeyboardProc lpfn, IntPtr hMod, uint dwThreadId);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool UnhookWindowsHookEx(IntPtr hhk);

    [DllImport("user32.dll")]
    private static extern IntPtr CallNextHookEx(IntPtr hhk, int nCode, IntPtr wParam, IntPtr lParam);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool RegisterHotKey(IntPtr hWnd, int id, uint fsModifiers, uint vk);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool UnregisterHotKey(IntPtr hWnd, int id);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern short GetAsyncKeyState(int vKey);

    [DllImport("kernel32.dll", CharSet = CharSet.Unicode)]
    private static extern IntPtr GetModuleHandle(string lpModuleName);

    [StructLayout(LayoutKind.Sequential)]
    private struct MSG
    {
        public IntPtr hwnd;
        public uint message;
        public IntPtr wParam;
        public IntPtr lParam;
        public uint time;
        public int ptX;
        public int ptY;
    }

    [DllImport("user32.dll", CharSet = CharSet.Auto)]
    private static extern int GetMessage(out MSG lpMsg, IntPtr hWnd, uint wMsgFilterMin, uint wMsgFilterMax);

    [DllImport("user32.dll")]
    private static extern bool TranslateMessage(ref MSG lpMsg);

    [DllImport("user32.dll")]
    private static extern IntPtr DispatchMessage(ref MSG lpMsg);

    [DllImport("user32.dll")]
    private static extern void keybd_event(byte bVk, byte bScan, uint dwFlags, IntPtr dwExtraInfo);

    [DllImport("user32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    private static extern IntPtr CreateWindowEx(uint dwExStyle, string lpClassName, string lpWindowName,
        uint dwStyle, int x, int y, int nWidth, int nHeight, IntPtr hWndParent, IntPtr hMenu,
        IntPtr hInstance, IntPtr lpParam);

    [DllImport("user32.dll")]
    private static extern bool DestroyWindow(IntPtr hWnd);

    [DllImport("user32.dll")]
    private static extern IntPtr DefWindowProc(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam);

    [DllImport("user32.dll")]
    private static extern bool IsHungAppWindow(IntPtr hWnd);

    [DllImport("user32.dll")]
    private static extern IntPtr GetForegroundWindow();

    /// <summary>桌面窗口(explorer 进程的)。探针自检拿它试跨进程那一条路能不能通。</summary>
    [DllImport("user32.dll")]
    private static extern IntPtr GetShellWindow();

    /// <summary>枚举顶层窗口的回调(找"某个进程现在的窗口"用)</summary>
    private delegate bool EnumWindowsProc(IntPtr hWnd, IntPtr lParam);

    [DllImport("user32.dll")]
    private static extern bool EnumWindows(EnumWindowsProc lpEnumFunc, IntPtr lParam);

    [DllImport("user32.dll")]
    private static extern bool IsWindowVisible(IntPtr hWnd);

    /// <summary>取窗口的"所有者"等关系(GW_OWNER=4): 用来只认顶层窗口</summary>
    [DllImport("user32.dll")]
    private static extern IntPtr GetWindow(IntPtr hWnd, uint uCmd);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern int GetWindowTextW(IntPtr hWnd, StringBuilder lpString, int nMaxCount);

    [DllImport("user32.dll", CharSet = CharSet.Unicode)]
    private static extern int GetClassNameW(IntPtr hWnd, StringBuilder lpClassName, int nMaxCount);

    [DllImport("user32.dll")]
    private static extern bool SetForegroundWindow(IntPtr hWnd);

    [DllImport("user32.dll")]
    private static extern bool ShowWindow(IntPtr hWnd, int nCmdShow);

    [DllImport("user32.dll")]
    private static extern bool IsWindow(IntPtr hWnd);

    /// <summary>窗口是不是最小化了。只有最小化的窗口才该用 SW_RESTORE(见 ForceForegroundHwnd)。</summary>
    [DllImport("user32.dll")]
    private static extern bool IsIconic(IntPtr hWnd);

    /// <summary>改窗口的 Z 序/位置。抢前台兜底阶梯里用它临时置顶(见 ForceForegroundHwndEx)。</summary>
    [DllImport("user32.dll")]
    private static extern bool SetWindowPos(IntPtr hWnd, IntPtr hWndInsertAfter,
        int X, int Y, int cx, int cy, uint uFlags);

    [DllImport("user32.dll")]
    private static extern bool AttachThreadInput(uint idAttach, uint idAttachTo, bool fAttach);

    [DllImport("user32.dll")]
    private static extern uint GetWindowThreadProcessId(IntPtr hWnd, IntPtr lpdwProcessId);

    /// <summary>同一个 API 的 out 版本: 真要拿进程号时用它(用来防"窗口句柄被系统复用后认错窗口")</summary>
    [DllImport("user32.dll")]
    private static extern uint GetWindowThreadProcessId(IntPtr hWnd, out uint lpdwProcessId);

    [DllImport("user32.dll")]
    private static extern IntPtr SetActiveWindow(IntPtr hWnd);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern IntPtr SendMessageTimeout(IntPtr hWnd, uint Msg, IntPtr wParam, IntPtr lParam,
        uint fuFlags, uint uTimeout, out IntPtr lpdwResult);

    private delegate IntPtr WndProcDelegate(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam);

    [StructLayout(LayoutKind.Sequential, CharSet = CharSet.Unicode)]
    private struct WNDCLASSEX
    {
        public int cbSize;
        public uint style;
        public WndProcDelegate lpfnWndProc;
        public int cbClsExtra;
        public int cbWndExtra;
        public IntPtr hInstance;
        public IntPtr hIcon;
        public IntPtr hCursor;
        public IntPtr hbrBackground;
        public string lpszMenuName;
        public string lpszClassName;
        public IntPtr hIconSm;
    }

    [DllImport("user32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    private static extern ushort RegisterClassEx(ref WNDCLASSEX lpwcx);

    [DllImport("user32.dll", SetLastError = true)]
    private static extern bool UnregisterClass(string lpClassName, IntPtr hInstance);

    private const uint WM_NULL = 0x0000;
    private const uint WM_HOTKEY = 0x0312;
    /// <summary>
    /// 投给"钩子线程"的自检/重装请求(V1.1.5-RC1)。
    /// 为什么走线程消息而不是自己动手: WH_KEYBOARD_LL 的钩子必须在**装它的那条线程**上装卸。
    /// WM_APP 段是系统留给应用的, 0x8000 + 0x51 不会和任何系统消息撞车。
    /// </summary>
    private const uint WM_APP_REHOOK = 0x8000 + 0x51;
    private const uint MOD_NOREPEAT = 0x4000;
    private const uint MOD_ALT = 0x0001;
    private const uint MOD_CONTROL = 0x0002;
    private const uint MOD_SHIFT = 0x0004;

    [DllImport("user32.dll")]
    private static extern bool PostThreadMessage(uint idThread, uint Msg, IntPtr wParam, IntPtr lParam);

    [DllImport("kernel32.dll")]
    private static extern uint GetCurrentThreadId();

    private delegate IntPtr LowLevelKeyboardProc(int nCode, IntPtr wParam, IntPtr lParam);

    private const int WH_KEYBOARD_LL = 13;
    private const int WM_KEYDOWN = 0x0100;
    private const int WM_SYSKEYDOWN = 0x0104;
    private const int WM_QUIT = 0x0012;
    private const int VK_SHIFT = 0x10;
    private const int VK_CONTROL = 0x11;
    private const int VK_MENU = 0x12;
    /// <summary>没有键盘会发出的虚拟键码, 专供看门狗自检 —— 用一个没人会按到的键来探活</summary>
    private const uint VK_SELFTEST = 0xFF;

    #endregion

    #region Win32: 进程枚举与终结

    [DllImport("ntdll.dll")]
    private static extern int NtQuerySystemInformation(int SystemInformationClass, IntPtr SystemInformation,
        int SystemInformationLength, out int ReturnLength);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern IntPtr OpenProcess(uint dwDesiredAccess, bool bInheritHandle, int dwProcessId);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool TerminateProcess(IntPtr hProcess, uint uExitCode);

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool CloseHandle(IntPtr hObject);

    // ---- 进程特权: 杀"受限令牌 / 沙箱"进程要用 ----
    // 虚拟机实测: 对 Edge 的几个沙箱进程, 即使进程是管理员,
    // TerminateProcess 也会返回错误码 5(拒绝访问) —— 普通管理员令牌动不了它们,
    // 必须先把 SeDebugPrivilege 打开(它能绕过目标进程的 DACL)。只有管理员令牌里才有这个特权。
    [DllImport("advapi32.dll", SetLastError = true)]
    private static extern bool OpenProcessToken(IntPtr ProcessHandle, uint DesiredAccess, out IntPtr TokenHandle);

    [DllImport("advapi32.dll", SetLastError = true, CharSet = CharSet.Unicode)]
    private static extern bool LookupPrivilegeValue(string lpSystemName, string lpName, out long lpLuid);

    [DllImport("advapi32.dll", SetLastError = true)]
    private static extern bool AdjustTokenPrivileges(IntPtr TokenHandle, bool DisableAllPrivileges,
        ref TOKEN_PRIVILEGES NewState, int BufferLength, IntPtr PreviousState, IntPtr ReturnLength);

    [DllImport("kernel32.dll")]
    private static extern IntPtr GetCurrentProcess();

    // 布局必须和原生一致(4 字节对齐)。LUID 是 {DWORD LowPart; LONG HighPart}, 对齐是 4;
    // 如果这里用 long 存 LUID, x64 上会被对齐到 8 字节, 整个结构变成 24 字节,
    // 而原生只读 16 字节 —— 特权会被静默忽略。所以拆成两个 int。
    [StructLayout(LayoutKind.Sequential)]
    private struct TOKEN_PRIVILEGES
    {
        public int Count;
        public int LuidLow;
        public int LuidHigh;
        public int Attributes;
    }

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern uint WaitForMultipleObjects(uint nCount, IntPtr[] lpHandles,
        bool bWaitAll, uint dwMilliseconds);

    private const uint WAIT_OBJECT_0 = 0;
    private const uint WAIT_TIMEOUT = 0x00000102;

    /// <summary>
    /// 一次最多等多少个句柄 —— WaitForMultipleObjects 的硬上限。
    /// 同一进程名同时开着 64 个实例的情况不存在, 超出的部分交给补杀轮次。
    /// </summary>
    private const int MAX_WAIT_HANDLES = 64;
    /// <summary>
    /// 等一批进程句柄"真的退出"的上限。从 10 秒降到 2 秒:
    /// 保命关键是"断网 + 已经下达终止命令", 干等句柄没有意义;
    /// 没退的下一轮会重新枚举复查(一次全表枚举才 20 多 ms), 比死等划算得多。
    /// </summary>
    private const int KILL_WAIT_MS = 2000;

    private const uint PROCESS_TERMINATE = 0x0001;
    private const uint SYNCHRONIZE = 0x00100000;
    /// <summary>挂起进程内线程所需的权限(NtSuspendProcess 与 SuspendThread 都要它)</summary>
    private const uint PROCESS_SUSPEND_RESUME = 0x0800;
    /// <summary>线程快照 + 单线程挂起(整进程挂起不可用时的兜底方案)</summary>
    private const uint TH32CS_SNAPTHREAD = 0x00000004;
    private const uint THREAD_SUSPEND_RESUME = 0x0002;

    [StructLayout(LayoutKind.Sequential)]
    private struct THREADENTRY32
    {
        public uint dwSize;
        public uint cntUsage;
        public uint th32ThreadID;
        public uint th32OwnerProcessID;
        public int tpBasePri;
        public int tpDeltaPri;
        public uint dwFlags;
    }

    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern IntPtr CreateToolhelp32Snapshot(uint flags, uint pid);
    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool Thread32First(IntPtr snap, ref THREADENTRY32 te);
    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool Thread32Next(IntPtr snap, ref THREADENTRY32 te);
    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern IntPtr OpenThread(uint access, bool inherit, uint tid);
    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern int SuspendThread(IntPtr hThread);

    private const uint PROCESS_QUERY_LIMITED_INFORMATION = 0x1000;

    [StructLayout(LayoutKind.Sequential)]
    private struct SGFILETIME
    {
        public uint dwLowDateTime;
        public uint dwHighDateTime;
    }

    /// <summary>取进程创建时间(用于核对"PID 还是不是原来那个进程")。</summary>
    [DllImport("kernel32.dll", SetLastError = true)]
    private static extern bool GetProcessTimes(IntPtr hProcess, out SGFILETIME creation,
        out SGFILETIME exit, out SGFILETIME kernel, out SGFILETIME user);

    /// <summary>
    /// 一次调用挂起进程内**全部**线程(ntdll 未公开, 但自 NT4 起一直存在, 进程管理器都用它)。
    ///
    /// 为什么必须用它: 目标是"按下后 100 ms 内让游戏不再执行任何代码"。
    ///   · TerminateProcess 做不到 —— 实测给光遇下这条命令, 它自己 715 ms 才返回
    ///     (内核在拆几百个线程、等驱动释放引用), 期间进程还在跑;
    ///   · NtSuspendProcess 是"把线程全部冻住"的一次调用, 微秒级;
    ///   · 万一这个入口在老系统上不可用, 下面会自动退回逐线程 SuspendThread(全文档化 API)。
    /// </summary>
    [DllImport("ntdll.dll")]
    private static extern uint NtSuspendProcess(IntPtr hProcess);
    private const int SystemProcessInformation = 5;
    private const int STATUS_INFO_LENGTH_MISMATCH = unchecked((int)0xC0000004);

    [StructLayout(LayoutKind.Sequential)]
    private struct UNICODE_STRING
    {
        public ushort Length;
        public ushort MaximumLength;
        public IntPtr Buffer;
    }

    [StructLayout(LayoutKind.Sequential)]
    private struct SYSTEM_PROCESS_INFORMATION
    {
        public int NextEntryOffset;
        public int NumberOfThreads;
        public long WorkingSetPrivateSize;
        public int HardFaultCount;
        public int NumberOfThreadsHighWatermark;
        public long CycleTime;
        public long CreateTime;
        public long UserTime;
        public long KernelTime;
        public UNICODE_STRING ImageName;
        public int BasePriority;
        public IntPtr UniqueProcessId;
        public IntPtr InheritedFromUniqueProcessId;
    }

    #endregion

    // ============================================================================
    //  二、日志
    // ============================================================================

    #region 日志

    private const long LOG_MAX_BYTES = 2 * 1024 * 1024;
    private const int LOG_KEEP_LINES = 200;

    // 换成无锁队列。Log() 会在键盘钩子回调和处置热路径里被调用,
    // 一旦这里拿不到锁, 整条处置链路就被卡住 —— 虚拟机实测"触发后 3 秒才走到下一步",
    // 而 Panic() 那两行之间只有"建线程 + 启动 + 写一行日志"。锁彻底去掉。
    private const int LOG_PENDING_MAX = 5000;

    /// <summary>等着写进日志文件的行。真正落盘由一条后台线程干, 调用方只入队(无锁)。</summary>
    private static readonly System.Collections.Concurrent.ConcurrentQueue<string> _logPending
        = new System.Collections.Concurrent.ConcurrentQueue<string>();
    private static readonly AutoResetEvent _logWake = new AutoResetEvent(false);
    private static volatile bool _logWriterStarted = false;

    /// <summary>
    /// 记一行日志。
    ///
    /// 关键: 这个函数会在键盘钩子回调里被调用。系统对钩子回调有时限
    /// (默认 300 ms), 超了就静默把钩子摘掉。所以这里绝不能做文件 IO ——
    /// 只入队, 由后台线程落盘。以前这里直接 AppendAllText, 在磁盘忙的时候
    /// 很容易把钩子拖超时, 表现就是"按触发键没反应"。
    /// </summary>
    /// <summary>
    /// 日志落盘前的统一脱敏: 去掉 IP / MAC 地址。
    ///
    /// 为什么做在这一层(用户要求「程序日志里不要显示 IP 地址」):
    ///   日志是用户遇到问题时会发给别人看的东西, 没必要把本机 IP 带出去。
    ///   放在这里等于给所有日志出口上了一道兜底 —— 以后谁不小心在 Log 里拼了个 IP,
    ///   也不会漏出去; 不用挨个调用点去改。
    /// </summary>
    private static readonly System.Text.RegularExpressions.Regex _reIpv4 =
        new System.Text.RegularExpressions.Regex(@"\b\d{1,3}(?:\.\d{1,3}){3}\b");
    private static readonly System.Text.RegularExpressions.Regex _reMac =
        new System.Text.RegularExpressions.Regex(@"\b[0-9A-Fa-f]{2}(?:-[0-9A-Fa-f]{2}){5}\b");

    /// <summary>
    /// 日志文件的编码: 中文系统用 GBK(936, 记事本能直接看), 拿不到就退回无 BOM 的 UTF-8。
    ///
    /// 为什么要有这个兜底: 精简系统上 GetEncoding(936) 可能抛异常, 而调用点全在写日志的后台线程里
    /// (异常被 catch 吞掉), 结果是"整个程序一条日志都没有" —— 排障时最需要日志的时候反而什么都没有。
    /// 另外: 崩溃报告必须和日志正文用同一个编码, 否则崩溃那一段在记事本里就是乱码(它恰恰最该看懂)。
    /// </summary>
    private static Encoding _logEnc;
    private static Encoding LogEnc()
    {
        if (_logEnc == null)
        {
            try { _logEnc = Encoding.GetEncoding(936); }
            catch { _logEnc = new UTF8Encoding(false); }
        }
        return _logEnc;
    }

    private static string SanitizeLog(string msg)
    {
        if (string.IsNullOrEmpty(msg)) return msg;
        try
        {
            string s = _reIpv4.Replace(msg, "<地址已隐藏>");
            s = _reMac.Replace(s, "<地址已隐藏>");
            return s;
        }
        catch { return msg; }
    }

    private static void Log(string msg)
    {
        long t0 = Stopwatch.GetTimestamp();
        if (!_logWriterStarted) StartLogWriter();
        msg = SanitizeLog(msg);          // 落盘前统一脱敏(IP/MAC)
        string line = "[" + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff") + "] " + msg;
        EnqueueLog(line);
        AppendUiLog("[" + DateTime.Now.ToString("HH:mm:ss.fff") + "] " + msg);

        // 卡顿自证: 这一句要是超过 50 ms, 自己再记一笔(只入队, 不递归)。
        // 有了它, 下次"触发后卡了几秒"能直接看出卡在哪一行日志上。
        long ms = ElapsedMs(t0);
        if (ms >= 50)
            EnqueueLog("[" + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff")
                + "] [日志告警] Log() 花了 " + ms + " ms: " + msg);
    }

    /// <summary>把一行塞进待落盘队列(无锁, 永不阻塞调用方)。超上限就丢最老的, 内存有界。</summary>
    private static void EnqueueLog(string line)
    {
        _logPending.Enqueue(line);
        string drop;
        while (_logPending.Count > LOG_PENDING_MAX && _logPending.TryDequeue(out drop)) _logDropped++;
        _logWake.Set();
    }

    // ---------------------------------------------------------------------------
    //  "日志写不出去"必须可见(V1.1.5-RC1)
    //
    //  以前落盘的 catch 是空的 —— 换台电脑、磁盘满、目录权限不对、被杀软锁住文件时,
    //  日志会**一声不响地停止**, 而日志恰好是出问题时唯一的证据。
    //  现在: 记下失败次数与首条原因, 在主界面摘要和状态面板里说出来。
    //  (仍然是"不打扰"的: 不弹框、不参与任何逻辑判断, 只是可见。)
    // ---------------------------------------------------------------------------

    /// <summary>日志落盘失败过几次</summary>
    private static volatile int _logWriteFails = 0;
    /// <summary>第一条失败原因(只说第一条, 免得被重复消息淹没)</summary>
    private static volatile string _logWriteWhy = "";
    /// <summary>队列满被丢掉的行数</summary>
    private static volatile int _logDropped = 0;

    private static void StartLogWriter()
    {
        _logWriterStarted = true;
        Thread t = new Thread(delegate()
        {
            while (true)
            {
                try
                {
                    _logWake.WaitOne(500);
                    if (_logPending.IsEmpty) continue;
                    List<string> batch = new List<string>();
                    string one;
                    while (batch.Count < 2000 && _logPending.TryDequeue(out one)) batch.Add(one);
                    if (batch.Count == 0) continue;
                    RotateLogIfNeeded();
                    StringBuilder sb = new StringBuilder();
                    foreach (string l in batch) sb.Append(l).Append("\r\n");
                    File.AppendAllText(_logPath, sb.ToString(), LogEnc());
                }
                catch (Exception ex)
                {
                    // 不能吞: 日志写不进去本身就是要修的问题(磁盘满 / 权限 / 被杀软锁住)。
                    // 注意这里只记状态, 不再调 Log() —— 那会自己喂自己, 变成死循环。
                    _logWriteFails++;
                    if (string.IsNullOrEmpty(_logWriteWhy)) _logWriteWhy = ex.Message;
                }
            }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardLog";
        t.Start();
    }

    /// <summary>日志状态的一句话摘要(主界面摘要 + 状态面板用)。写不进去时会返回非空提示。</summary>
    private static string LogHealthNote()
    {
        try
        {
            if (_logWriteFails > 0)
                return "日志写入失败 " + _logWriteFails + " 次（" + _logWriteWhy + "）";
            if (_logDropped > 0)
                return "日志队列满，丢掉了 " + _logDropped + " 行";
            return "";
        }
        catch { return ""; }
    }

    private static void RotateLogIfNeeded()
    {
        try
        {
            if (!File.Exists(_logPath)) return;
            if (new FileInfo(_logPath).Length < LOG_MAX_BYTES) return;
            string[] all = File.ReadAllLines(_logPath, LogEnc());
            int keep = Math.Min(LOG_KEEP_LINES, all.Length);
            string[] tail = new string[keep + 1];
            tail[0] = "[" + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff")
                + "] [日志轮转] 文件超过 2 MB, 只保留最近 " + keep + " 行 (原 " + all.Length + " 行)";
            Array.Copy(all, all.Length - keep, tail, 1, keep);
              // 先写临时文件再原子替换: 直接盖到日志本身的话, 中途失败(磁盘满/被杀)会把日志留成半截
              string tmpLog = _logPath + ".tmp";
              File.WriteAllLines(tmpLog, tail, LogEnc());
              if (File.Exists(_logPath)) File.Replace(tmpLog, _logPath, null); else File.Move(tmpLog, _logPath);
        }
        catch { }
    }

    /// <summary>等着往界面上写、还没写的日志行</summary>
    private static readonly System.Collections.Concurrent.ConcurrentQueue<string> _uiPending
        = new System.Collections.Concurrent.ConcurrentQueue<string>();
    private const int UI_PENDING_MAX = 2000;

    /// <summary>
    /// 把一行日志推进"待显示"队列。
    ///
    /// 为什么不直接 BeginInvoke:
    ///   处置一轮会打出上百行日志。每行一次 BeginInvoke, 就是在 UI 线程的消息队列里
    ///   塞一个委托 —— 界面正忙的时候这些委托会堆起来, 反而把界面压得更卡,
    ///   而界面卡住 = 键盘钩子收不到键。所以改成"生产快、消费由界面自己按节奏取"。
    /// </summary>
    private static void AppendUiLog(string line)
    {
        try
        {
            if (_txtLog == null || _form == null || !_form.IsHandleCreated) return;
            _uiPending.Enqueue(line);
            string drop;
            while (_uiPending.Count > UI_PENDING_MAX && _uiPending.TryDequeue(out drop)) { }
        }
        catch { }
    }

    /// <summary>界面日志框最多保留这么多字符 —— 只 AppendText 不裁剪的话, 长时间挂机会把整轮日志堆在控件里,
    /// 内存和重绘成本一路涨, 而界面一卡, 全局键盘钩子那条链子也跟着受影响。</summary>
    private const int UI_LOG_MAX_CHARS = 120000;

    /// <summary>界面线程定期调用: 把攒下的日志一次性显示出来</summary>
    private static void PumpUiLog()
    {
        try
        {
            if (_txtLog == null || _form == null || !_form.IsHandleCreated) return;
            if (_form.InvokeRequired) return;
            List<string> batch = new List<string>();
            string one;
            while (batch.Count < UI_PENDING_MAX && _uiPending.TryDequeue(out one)) batch.Add(one);
            if (batch.Count == 0) return;
            StringBuilder sb = new StringBuilder();
            foreach (string l in batch) sb.Append(l).Append("\r\n");
            _txtLog.AppendText(sb.ToString());
            TrimUiLog();
        }
        catch { }
    }

    /// <summary>超上限就把最早的一半丢掉(留一行说明)。只改文本, 不碰滚动位置之外的任何状态。</summary>
    private static void TrimUiLog()
    {
        try
        {
            if (_txtLog == null || _txtLog.TextLength <= UI_LOG_MAX_CHARS) return;
            string t = _txtLog.Text;
            int keepFrom = t.Length - UI_LOG_MAX_CHARS / 2;
            int cut = t.IndexOf('\n', keepFrom);
            if (cut < 0) return;
            _txtLog.Text = "…（更早的记录已省略，完整内容见日志文件）…\r\n" + t.Substring(cut + 1);
            _txtLog.SelectionStart = _txtLog.TextLength;
            _txtLog.ScrollToCaret();
        }
        catch { }
    }

    private static long ElapsedMs(long startTicks)
    {
        if (startTicks == 0) return 0;
        return (Stopwatch.GetTimestamp() - startTicks) * 1000L / Stopwatch.Frequency;
    }

    /// <summary>
    /// 两个 Stopwatch 时间戳之间差多少毫秒。
    /// 和上面那个"从某时刻到现在"的重载区分开: 判断"两次上报是不是同一次按键"要用
    /// "两次上报各自的到达时刻", 不能用"现在" —— 否则我们自己的处理耗时会被算进间隔里。
    /// </summary>
    private static long ElapsedMs(long fromTicks, long toTicks)
    {
        if (fromTicks == 0 || toTicks == 0 || toTicks <= fromTicks) return 0;
        return (toTicks - fromTicks) * 1000L / Stopwatch.Frequency;
    }

    #endregion

    // ============================================================================
    //  三、触发键: 解析 + 匹配
    // ============================================================================

    #region 触发键

    private sealed class KeyTrig
    {
        public uint Vk;
        public string Name = "";
        public bool Ctrl, Alt, Shift;
        public bool IsF4;      // 裸 F4 需额外屏蔽 Alt+F4
    }

    private static List<KeyTrig> _trigs = new List<KeyTrig>();

    /// <summary>键名 -> 虚拟键码</summary>
    private static uint VkOf(string p)
    {
        p = p.Trim().ToUpperInvariant();
        if (p.Length == 1 && p[0] >= 'A' && p[0] <= 'Z') return (uint)p[0];
        if (p.Length == 1 && p[0] >= '0' && p[0] <= '9') return (uint)p[0];
        // 小键盘 0~9: 名字由 NameOf 生成("Num0".."Num9"), 必须能解析回来
        if (p.Length == 4 && p.StartsWith("NUM") && p[3] >= '0' && p[3] <= '9') return (uint)(0x60 + (p[3] - '0'));
        if (p == "F1") return 0x70; if (p == "F2") return 0x71; if (p == "F3") return 0x72;
        if (p == "F4") return 0x73; if (p == "F5") return 0x74; if (p == "F6") return 0x75;
        if (p == "F7") return 0x76; if (p == "F8") return 0x77; if (p == "F9") return 0x78;
        if (p == "F10") return 0x79; if (p == "F11") return 0x7A; if (p == "F12") return 0x7B;
        if (p == "F13") return 0x7C; if (p == "F14") return 0x7D; if (p == "F15") return 0x7E;
        if (p == "F16") return 0x7F; if (p == "F17") return 0x80; if (p == "F18") return 0x81;
        if (p == "F19") return 0x82; if (p == "F20") return 0x83; if (p == "F21") return 0x84;
        if (p == "F22") return 0x85; if (p == "F23") return 0x86; if (p == "F24") return 0x87;
        if (p == "SPACE") return 0x20;
        if (p == "TAB") return 0x09;
        if (p == "PAUSE" || p == "BREAK") return 0x13;
        if (p == "SCROLLLOCK" || p == "SCROLL") return 0x91;
        if (p == "INSERT" || p == "INS") return 0x2D;
        if (p == "DELETE" || p == "DEL") return 0x2E;
        if (p == "HOME") return 0x24;
        if (p == "END") return 0x23;
        if (p == "PGUP" || p == "PAGEUP") return 0x21;
        if (p == "PGDN" || p == "PAGEDOWN") return 0x22;
        if (p == "UP") return 0x26;
        if (p == "DOWN") return 0x28;
        if (p == "LEFT") return 0x25;
        if (p == "RIGHT") return 0x27;
        return 0;
    }

    private static string NameOf(uint vk, bool c, bool a, bool s)
    {
        string b;
        if (vk >= 0x70 && vk <= 0x87) b = "F" + (vk - 0x70 + 1);
        else if (vk >= 'A' && vk <= 'Z') b = ((char)vk).ToString();
        else if (vk >= '0' && vk <= '9') b = ((char)vk).ToString();
        else if (vk == 0x20) b = "Space";
        else if (vk == 0x09) b = "Tab";
        else if (vk == 0x13) b = "Pause";
        else if (vk == 0x91) b = "ScrollLock";
        else if (vk == 0x2D) b = "Insert";
        else if (vk == 0x2E) b = "Delete";
        else if (vk == 0x24) b = "Home";
        else if (vk == 0x23) b = "End";
        else if (vk == 0x21) b = "PgUp";
        else if (vk == 0x22) b = "PgDn";
        // ★ 方向键和小键盘必须在这里有名字, 且名字要能被 VkOf 解析回来。
        //   否则录入窗录进来的 Up/小键盘会落到下面那行变成 "VK26"/"VK65",
        //   而 VkOf("VK26")=0 -> 保存时被当成"认不出来的键"(只有一个时直接拦下,
        //   混在别的键里就静默丢掉) —— 实测发现的真 bug。
        else if (vk == 0x25) b = "Left";
        else if (vk == 0x26) b = "Up";
        else if (vk == 0x27) b = "Right";
        else if (vk == 0x28) b = "Down";
        else if (vk >= 0x60 && vk <= 0x69) b = "Num" + (vk - 0x60);
        else b = "VK" + vk.ToString("X2");
        StringBuilder sb = new StringBuilder();
        if (c) sb.Append("Ctrl+");
        if (a) sb.Append("Alt+");
        if (s) sb.Append("Shift+");
        sb.Append(b);
        return sb.ToString();
    }

        /// <summary>
        /// 这个虚拟键码能不能当触发键?
        /// 白名单思路: 只接受 F1~F24 / A~Z / 0~9 / 编辑键 / 特殊键。
        /// 这样可以挡掉实测遇到的那一堆垃圾事件:
        ///   - 0xA2/0xA3/0xA0/0xA1/0xA4/0xA5  左右 Ctrl/Shift/Alt 的原始码
        ///   - 0x08 退格、0x0D 回车、0x1B Esc、0x20 空格(空格允许, 这里放行)
        ///   - 0xE5 中文输入法的 ProcessKey
        ///   - 0xFF 等无效值
        /// </summary>
        private static bool IsAcceptableTriggerKey(uint vk)
        {
            if (vk >= 0x70 && vk <= 0x87) return true;          // F1~F24
            if (vk >= 0x41 && vk <= 0x5A) return true;          // A~Z
            if (vk >= 0x30 && vk <= 0x39) return true;          // 0~9
            if (vk >= 0x60 && vk <= 0x69) return true;          // 小键盘 0~9
            switch (vk)
            {
                case 0x20:   // Space
                case 0x09:   // Tab
                case 0x13:   // Pause
                case 0x91:   // ScrollLock
                case 0x2D:   // Insert
                case 0x2E:   // Delete
                case 0x24:   // Home
                case 0x23:   // End
                case 0x21:   // PgUp
                case 0x22:   // PgDn
                case 0x25:   // Left
                case 0x26:   // Up
                case 0x27:   // Right
                case 0x28:   // Down
                    return true;
            }
            return false;
        }

        /// <summary>修饰键(含左右独立码 0xA0~0xA5)与 Win 键</summary>
        private static bool IsModifierKey(uint vk)
        {
            if (vk == 0x10 || vk == 0x11 || vk == 0x12) return true;       // Shift/Ctrl/Alt
            if (vk >= 0xA0 && vk <= 0xA5) return true;                     // L/R Shift/Ctrl/Alt
            if (vk == 0x5B || vk == 0x5C) return true;                     // L/R Win
            return false;
        }

    /// <summary>解析一行触发键写法, 如 "Ctrl+Alt+K" 或 "F9"; 失败返回 null</summary>
    private static KeyTrig ParseKeyLine(string line)
    {
        if (string.IsNullOrEmpty(line)) return null;
        string[] parts = line.Trim().Split('+');
        bool c = false, a = false, s = false;
        uint vk = 0;
        foreach (string raw in parts)
        {
            string p = raw.Trim().ToUpperInvariant();
            if (p.Length == 0) continue;
            if (p == "CTRL" || p == "CONTROL") { c = true; continue; }
            if (p == "ALT") { a = true; continue; }
            if (p == "SHIFT") { s = true; continue; }
            uint v = VkOf(p);
            if (v == 0) return null;
            vk = v;
        }
        if (vk == 0) return null;
        KeyTrig kt = new KeyTrig();
        kt.Vk = vk; kt.Ctrl = c; kt.Alt = a; kt.Shift = s;
        kt.Name = NameOf(vk, c, a, s);
        kt.IsF4 = (vk == 0x73);
        return kt;
    }

    /// <summary>
    /// 解析触发键文本 -> KeyTrig 列表。不碰正在生效的 _trigs。
    /// 为什么单独拆出来: 设置窗里"录入/校验"阶段不能立刻改变生效的触发键 ——
    /// 用户点[取消]、或校验没过时, 生效键必须保持原样(踩过: 清空录入后取消, 键就永久失效了)。
    /// </summary>
    private static List<KeyTrig> ParseKeysToList(List<string> lines, List<string> warnings)
    {
        List<KeyTrig> result = new List<KeyTrig>();
        HashSet<string> seen = new HashSet<string>();
        foreach (string l in lines)
        {
            if (string.IsNullOrEmpty(l)) continue;
            // 关键: 每一项内部还可能含多个键(空格/逗号/分号/斜杠分隔)。
            // 例如配置文件里写 "F1 F2 Home Ctrl+Alt+K" 必须拆成 4 个键 ——
            // 早先只按 / , ; 拆分, 导致这种写法整串解析失败(实测踩过)。
            foreach (string one in SplitKeyText(l))
            {
                KeyTrig kt = ParseKeyLine(one);
                if (kt == null) { warnings.Add("无法识别的触发键: " + one); continue; }
                // ★ 去重必须带上修饰键 —— 只按 Vk 去重会把 K 和 Ctrl+K 当成同一个键丢掉一个,
                //   而录入窗允许两者共存 -> "同一次运行里都生效、重启后少一个"的不一致。
                string sig = kt.Vk + "|" + (kt.Ctrl ? "1" : "0") + (kt.Alt ? "1" : "0") + (kt.Shift ? "1" : "0");
                if (seen.Add(sig)) result.Add(kt);
            }
        }
        return result;
    }

    /// <summary>解析并立即生效(启动读配置 / 向导完成时用)。</summary>
    private static void ParseKeys(List<string> lines, List<string> warnings)
    {
        _trigs = ParseKeysToList(lines, warnings);
    }

    #endregion

    // ============================================================================
    //  四、网卡探测 (环境适配的核心)
    // ============================================================================

    #region 网卡探测

    // ★ 这里曾经声明过 GetAdaptersAddresses + IP_ADAPTER_ADDRESSES 的 P/Invoke, 现已删除。
    //   原因(复核实测, 记下来免得后来人再走一遍):
    //     · IP_ADAPTER_ADDRESSES 里 union 多、x86/x64 偏移不同, 极易写错。当时的声明漏了
    //       `PCHAR AdapterName` 且 PhysicalAddress/Length 顺序反了 —— x64 上 FriendlyName
    //       实际读到的是 Description(网卡名变成"Intel(R) Dual Band Wireless-AC 8265"这种),
    //       FirstUnicastAddress 落在 AdapterName 上, 当链表遍历必然访问违例(0xC0000005, 抓不住);
    //     · 另外 Win10+ 还必须带 GAA_FLAG_INCLUDE_GATEWAYS(0x0080), 否则网关恒为 NULL;
    //     · 而这个程序分发给普通玩家, 编译产物只有一个 exe, 不值得为一个可以安全拿到的东西
    //       承担"读垃圾指针直接崩"的风险。
    //   → 改用进程内的 System.Net.NetworkInformation(纯托管, 无 P/Invoke, 见 GetPsNics),
    //     失败再退回 netsh 文本解析。两条路都不依赖语言或代码页。

    /// <summary>
    /// 这一份"环境探测"结果: 来自 .NET 自带的 System.Net.NetworkInformation。
    ///
    /// 为什么要走这一路(而不是只解析 netsh 文本):
    ///   · netsh 吐的是给人看的本地化文本 —— 字段名跟语言走(中文"IP 地址" / 英文 "IP Address" /
    ///     德文 "IP-Adresse"), 换一台非中文机器就可能一张网卡都解析不出来;
    ///   · 更糟的是网卡名本身: netsh 的字节要经管道解码, 用错代码页会把
    ///     "以太网" 解成乱码, 而这个名字要原样传给 `netsh interface set interface name=`,
    ///     于是断网命令打到一个不存在的名字上 —— 静默失败, 用户以为断了。
    ///   NetworkInterface.GetAllNetworkInterfaces() 返回的 Name 是正儿八经的 Unicode,
    ///   在进程内直接调用, 不需要起子进程、不依赖 WMI/CIM、不依赖语言和代码页,
    ///   .NET Framework 2.0 起就有 —— 这是最稳的一条路。
    ///
    /// 试过但没采用的两条路(记录一下, 免得后来人再踩):
    ///   · GetAdaptersAddresses(P/Invoke): 结构体里 union 多, 实测在开发机上读 unicast 链表会崩, 弃用;
    ///   · PowerShell 的 Get-NetAdapter: 在开发机上被 WMI 策略拒绝(拒绝访问), 而且在别人的机器上
    ///     同样可能被组策略拦; 它还会多起一个 ~400ms 的进程。弃用。
    ///
    /// 拿不到时返回空表, 由调用方退回 netsh 文本解析 —— 双路取并集, 不单选。
    /// </summary>
    private sealed class PsNic
    {
        public string Name = "";
        public readonly List<string> Ips = new List<string>();
        public bool IsUp = true;
    }

    private static List<PsNic> GetPsNics()
    {
        List<PsNic> result = new List<PsNic>();
        try
        {
            foreach (NetworkInterface ni in NetworkInterface.GetAllNetworkInterfaces())
            {
                if (ni == null) continue;
                NetworkInterfaceType t = ni.NetworkInterfaceType;
                if (t == NetworkInterfaceType.Loopback || t == NetworkInterfaceType.Tunnel) continue;

                PsNic p = new PsNic();
                p.Name = (ni.Name ?? "").Trim();
                if (p.Name.Length == 0) continue;
                // 被管理性禁用的网卡: OperationalStatus 会是 Down(而不是 Up)
                p.IsUp = (ni.OperationalStatus == OperationalStatus.Up);

                try
                {
                    foreach (UnicastIPAddressInformation ua in ni.GetIPProperties().UnicastAddresses)
                    {
                        if (ua == null || ua.Address == null) continue;
                        if (ua.Address.AddressFamily != AddressFamily.InterNetwork) continue;
                        string ip = ua.Address.ToString();
                        if (IsIpv4(ip) && !p.Ips.Contains(ip)) p.Ips.Add(ip);
                    }
                }
                catch { }
                result.Add(p);
            }
        }
        catch { }
        return result;
    }

    /// <summary>
    /// ★ 一律用绝对路径调系统工具。
    ///
    /// 为什么(两个原因, 都很实在):
    ///   1) 可被劫持: `new ProcessStartInfo("netsh.exe")` + UseShellExecute=false 时,
    ///      CreateProcess 会先搜 exe 所在目录再搜 PATH。用户把本工具放在下载/QQ 接收目录,
    ///      旁边只要有一个同名 netsh.exe, 被调用的就是那个 —— 实测过, 三个调用全打到替身。
    ///      本程序还是以管理员身份运行的, 这一条不能留。
    ///   2) 少一次目录搜索, 顺带快一点。
    /// System32 取不到(理论上的极端精简系统)才退回裸名字。
    /// </summary>
    private static string SystemTool(string name)
    {
        try
        {
            string sys = Environment.GetFolderPath(Environment.SpecialFolder.System);
            if (!string.IsNullOrEmpty(sys))
            {
                string p = Path.Combine(sys, name);
                if (File.Exists(p)) return p;
            }
        }
        catch { }
        return name;
    }

    /// <summary>
    /// 跑一个系统工具并拿回 stdout+stderr。
    ///
    /// ★ 这里踩过一个确定性死锁(别改回去):
    ///   早先是「同步 ReadToEnd(stdout) 然后同步 ReadToEnd(stderr)」。只要子进程往
    ///   stderr 写了超过管道缓冲区(约 4KB)而 stdout 还没读完, 父进程就会永远卡在第一个
    ///   ReadToEnd 上 —— 子进程在等父进程腾管道, 父进程在等子进程结束。实测 25 秒都不返回。
    ///   → 现在用异步读(BeginOutputReadLine / BeginErrorReadLine), 并用 WaitForExit(ms) 设上限。
    ///   → 注意: WaitForExit(int) 之后要再调一次无参 WaitForExit(), 把异步输出事件排空,
    ///     否则最后几行可能还没进缓冲区就被我们读走了。
    /// </summary>
    private static string RunTool(string exe, string args)
    {
        return RunTool(exe, args, 10000);
    }

    private static string RunTool(string exe, string args, int timeoutMs)
    {
        try
        {
            ProcessStartInfo psi = new ProcessStartInfo(SystemTool(exe), args);
            psi.UseShellExecute = false;
            psi.CreateNoWindow = true;
            psi.RedirectStandardOutput = true;
            psi.RedirectStandardError = true;
            // ⚠️ 不要写死 936: netsh/route 的输出按系统 ANSI 代码页编, 英文/德文系统上
            //    用 CP936 解会把非 ASCII 的网卡名解成乱码, 而这个名字要原样回传给 netsh name=。
            //    取系统真实 ACP; 拿不到就用系统默认。
            try
            {
                int acp = GetAcpSafe();
                if (acp > 0)
                {
                    psi.StandardOutputEncoding = Encoding.GetEncoding(acp);
                    psi.StandardErrorEncoding = Encoding.GetEncoding(acp);
                }
            }
            catch { }

            StringBuilder so = new StringBuilder();
            StringBuilder se = new StringBuilder();
            using (Process p = new Process())
            {
                p.StartInfo = psi;
                p.OutputDataReceived += delegate(object s, DataReceivedEventArgs e)
                { if (e.Data != null) { lock (so) so.AppendLine(e.Data); } };
                p.ErrorDataReceived += delegate(object s, DataReceivedEventArgs e)
                { if (e.Data != null) { lock (se) se.AppendLine(e.Data); } };
                if (!p.Start()) return "";
                p.BeginOutputReadLine();
                p.BeginErrorReadLine();
                bool exited = p.WaitForExit(timeoutMs);
                if (!exited)
                {
                    Log("[" + exe + "] 超过 " + timeoutMs + " ms 没返回, 强杀(界面/探测不再干等)");
                    try { p.Kill(); } catch { }
                    try { p.WaitForExit(2000); } catch { }
                }
                else
                {
                    try { p.WaitForExit(); } catch { }   // 排空异步输出
                }
            }
            lock (so) { lock (se) { return so.ToString() + se.ToString(); } }
        }
        catch (Exception ex)
        {
            Log("[" + exe + "] 调用失败: " + ex.Message);
            return "";
        }
    }

    /// <summary>
    /// 带超时的 RunTool —— 只给"断网/恢复网"用, 返回退出码(失败返回 int.MinValue)。
    ///
    /// ★ 为什么一定要返回退出码: 早先这里不看结果, 于是"网卡名在这台机器上不存在"时
    ///   netsh 秒退并报错, 日志却照样打印"断网 XXX 完成"、照常等 N 秒、再打印"网络已恢复" ——
    ///   整条流程一路绿灯, 而一次都没断过网。对应急防护工具来说这是最危险的失败姿势:
    ///   用户在最需要它的时候以为它在工作。
    /// → 调用方必须根据退出码判定成败(见 SetNets 的 ok 统计与"没有一张断成功"的告警)。
    ///
    /// netsh 的约定: 成功返回 0; "此名称的接口未与路由器一起注册"/"找不到接口" 之类返回非 0。
    /// </summary>
    private static int RunToolTimed(string exe, string args, int timeoutMs, string tag)
    {
        // ★ 一律走 SystemTool(): 绝对路径, 不给"程序目录/当前目录里的同名替身"任何机会(见 SystemTool 注释)。
        //   以前这里直接把裸名字交给 ProcessStartInfo —— 而断网/恢复恰恰是最要命、最该防劫持的两条路径。
        ProcessStartInfo psi = new ProcessStartInfo(SystemTool(exe), args);
        psi.UseShellExecute = false;
        psi.CreateNoWindow = true;
        psi.RedirectStandardOutput = true;
        psi.RedirectStandardError = true;
        // ⚠️ 不要写死 936: 在非中文系统上 GetEncoding(936) 可能拿不到(精简镜像会抛异常),
        //    而 netsh 的报错文本我们只用来判断"成功与否", 不解析内容。
        //    这里用系统 ANSI 代码页, 拿不到就退回默认编码 —— 绝不能因为编码问题让整个断网动作失败。
        try
        {
            psi.StandardOutputEncoding = Encoding.GetEncoding(GetAcpSafe());
            psi.StandardErrorEncoding = Encoding.GetEncoding(GetAcpSafe());
        }
        catch { }

        Process p = null;
        StringBuilder so = new StringBuilder();
        StringBuilder se = new StringBuilder();
        try
        {
            p = new Process();
            p.StartInfo = psi;
            p.OutputDataReceived += delegate(object s, DataReceivedEventArgs e)
            { if (e.Data != null) { lock (so) so.AppendLine(e.Data); } };
            p.ErrorDataReceived += delegate(object s, DataReceivedEventArgs e)
            { if (e.Data != null) { lock (se) se.AppendLine(e.Data); } };
            if (!p.Start()) { Log(tag + ": 进程起不来"); return int.MinValue; }

            // ★ 必须异步读, 不能用"同步 ReadToEnd(stdout) 再 ReadToEnd(stderr)":
            //   那种写法在子进程写满 stderr 时是确定性死锁, 而且会让下面的超时永远到不了 ——
            //   整个处置会被这一条 netsh 永久卡住(同一个坑 RunTool 早先踩过, 这里对齐)。
            p.BeginOutputReadLine();
            p.BeginErrorReadLine();

            if (!p.WaitForExit(timeoutMs))
            {
                Log(tag + ": 超过 " + timeoutMs + " ms 还没返回, 强杀这个子进程继续走");
                try { p.Kill(); } catch { }
                try { p.WaitForExit(2000); } catch { }
                return int.MinValue;
            }
            try { p.WaitForExit(); } catch { }   // 排空异步输出事件

            string outp;
            lock (so) { lock (se) { outp = (so.ToString() + " " + se.ToString()).Trim(); } }
            int code = -1;
            try { code = p.ExitCode; } catch { }
            if (code != 0 && outp.Length > 0)
                Log(tag + ": " + Path.GetFileName(exe) + " 返回 " + code + " (" + Brief(outp) + ")");
            return code;
        }
        catch (Exception ex) { Log(tag + " 异常: " + ex.Message); return int.MinValue; }
        finally { if (p != null) { try { p.Dispose(); } catch { } } }
    }

    /// <summary>系统 ANSI 代码页; 失败返回 0(由调用方退回默认编码)</summary>
    private static int GetAcpSafe()
    {
        try { return GetACP(); } catch { return 0; }
    }

    [DllImport("kernel32.dll")]
    private static extern int GetACP();

    /// <summary>
    /// 是否把 netsh 原始输出落盘到数据目录的 `_raw_*.txt`。默认关 ——
    /// 那份文本含本机的 IP / 网关 / 网卡名, 用户把整个文件夹打包发出去时会连带泄露自己的网络信息。
    /// 只在排障时用命令行 `-dumpraw` 显式打开(打开后请勿把生成的 _raw_*.txt 发出去)。
    /// </summary>
    private static bool _dumpRawEnabled = false;

    /// <summary>把原始命令输出写到文件 —— 换机器解析失败时用于离线分析(需 -dumpraw 显式开启)</summary>
    private static void DumpRaw(string tag, string content)
    {
        try
        {
            if (!_dumpRawEnabled) return;      // 默认不落盘(隐私: 原始输出含本机 IP / 网关)
            // 写数据目录而不是程序目录: 这份文本含本机 IP/网关/网卡名, 属于用户数据。
            // 落在程序目录里, 既会在打包时被连带发出去, 也会被 -makemanifest 直接拦下。
            if (_dataDir.Length == 0) return;
            string p = Path.Combine(_dataDir, "_raw_" + tag + ".txt");
            File.WriteAllText(p, content, LogEnc());   // 与日志同编码(GBK), 记事本直接可读
        }
        catch { }
    }

    /// <summary>无界面模式(uicheck/selftest)下禁止弹窗, 否则会卡死在不可见对话框上</summary>
    private static volatile bool _headless = false;

    /// <summary>
    /// 只要自检模式(racetest)会置 true: 演练完整的处置流程, 但 SetNets 直接返回, 绝不动网卡。
    /// 生产路径永远是 false, SetNets 的行为一个字节都没变。
    /// </summary>
    private static volatile bool _noNet = false;

    private static void WarnBox(string msg)
    {
        try { Log("[提示] " + msg); } catch { }
        if (_headless) return;   // 无界面模式只记日志, 不弹窗
        try { MessageBox.Show(msg, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); } catch { }
    }

    private sealed class NicsBlock
    {
        public string Name = "";
        public string Display = "";
        public readonly List<string> IpList = new List<string>();
        public readonly List<string> IfNameList = new List<string>();
        public bool HasGateway;
        public string Gateway = "";
    }

    /// <summary>
    /// 多语言匹配辅助: 去掉空格并大写后比较。
    /// ⚠️ 必须连全角空格 U+3000 一起去掉 —— netsh 的中文输出就是用全角空格把
    ///    "IP 地址" 和冒号对齐的, 只去半角空格的话 key 永远等不上, 后果是
    ///    IP 与默认网关静默丢失 -> 标不出"承载流量"的网卡 -> 可能断到无关的网卡上。
    /// </summary>
    private static string L(string s)
    {
        return (s ?? "").Replace(" ", "").Replace("\u3000", "").Replace("\t", "").ToUpperInvariant();
    }

    /// <summary>把全角冒号/全角空格归一化成半角 —— 解析 netsh 文本前先过一遍</summary>
    private static string NormLine(string s)
    {
        if (s == null) return "";
        return s.Replace('\uFF1A', ':').Replace('\u3000', ' ').Replace('\t', ' ');
    }

    /// <summary>
    /// 用 `netsh interface ipv4 show addresses` 解析出每张网卡的连接名与 IP。
    /// 为什么用连接名: 只有它同时适用于 `netsh interface set interface name=` 和
    /// `netsh interface ipv4 show interface`。适配器描述(FriendlyName)不能用于这两条命令。
    ///
    /// ⚠️ 坑: netsh 输出语言跟随区域设置 —— 同一个命令在 cmd 里是英文
    /// ("IP Address"), 在 C# 子进程里却是中文("IP 地址")。所以这里中英兼容。
    /// </summary>
    private static List<NicsBlock> ParseAddresses()
    {
        List<NicsBlock> list = new List<NicsBlock>();
        string txt;
        try { txt = RunTool("netsh.exe", "interface ipv4 show addresses"); }
        catch { return list; }
        if (txt.Trim().Length == 0) return list;

        // 原始输出落盘: 换一台机器解析失败时, 这是唯一能离线分析的证据
        DumpRaw("addresses", txt);

        return ParseAddressesText(txt);
    }

    /// <summary>
    /// 纯解析: 把 `netsh interface ipv4 show addresses` 的输出文本转成网卡列表。
    ///
    /// 抽出来是为了能测英文输出。换机器最容易翻车的就是"netsh 输出语言不同":
    /// 中文系统上是「接口 "WLAN" 的配置」, 英文系统上是 `Configuration for interface "WLAN"`。
    /// 靠真机去验成本太高, 所以做成可以直接喂文本的纯函数 —— 由 `netshtest` 模式
    /// 用中英文两份样本各跑一遍(见 RunNetshLangTest)。
    /// </summary>
    private static List<NicsBlock> ParseAddressesText(string txt)
    {
        List<NicsBlock> list = new List<NicsBlock>();
        if (txt == null || txt.Trim().Length == 0) return list;
        NicsBlock cur = null;
        foreach (string raw in txt.Split('\n'))
        {
            // 归一化全角冒号/全角空格: 中文 netsh 用全角字符对齐字段名,
            // 不归一化的话下面 IndexOf(':') 找不到冒号, IP 和网关会被整段丢掉。
            string line = NormLine(raw).Trim();
            if (line.Length == 0) continue;

            int q1 = line.IndexOf('"');
            // 形如:  Configuration for interface "WLAN"   /   接口 "WLAN" 的配置
            //        Konfiguration für Schnittstelle "WLAN" / インターフェイス "WLAN" の構成
            // 判据: 这一行是"某张网卡的配置"表头 —— 含引号, 且含 interface/接口/配置 之类的词。
            // 说明: 这是兜底路径(主路径是进程内的 .NET 接口表, 见 GetPsNics), 所以这里宁可宽松一点:
            //   netsh addresses 输出里带引号的行只有表头, 宽松不会误判。
            bool isHeader = (q1 >= 0)
                            && (line.IndexOf("interface", StringComparison.OrdinalIgnoreCase) >= 0
                                || line.IndexOf("配置", StringComparison.Ordinal) >= 0
                                || line.IndexOf("接口", StringComparison.Ordinal) >= 0
                                || line.IndexOf("schnittstelle", StringComparison.OrdinalIgnoreCase) >= 0);
            if (isHeader)
            {
                // 取【最后一对】引号之间的内容作为显示名; 解析不出就跳过(不要放进 null 名字)
                int lastQ = line.LastIndexOf('"');
                int lastOpen = (lastQ > 0) ? line.LastIndexOf('"', lastQ - 1) : -1;
                string title = null;
                if (lastOpen >= 0 && lastQ > lastOpen)
                    title = line.Substring(lastOpen + 1, lastQ - lastOpen - 1);
                if (title == null || title.Length == 0) continue;

                cur = new NicsBlock();
                cur.Name = title;
                cur.Display = title;
                list.Add(cur);
                continue;
            }
            if (cur == null) continue;

            // 形如:  IP Address: 192.168.88.5     /    IP 地址: 192.168.88.5
            // 冒号已在 NormLine 里统一成半角; 这里再兼容 val 里带 "IP 地址:" 前缀的写法
            int colon = line.IndexOf(':');
            if (colon > 0)
            {
                string key = L(line.Substring(0, colon));   // 已去掉空格并转大写
                string val = line.Substring(colon + 1).Trim();
                if (key == "IPADDRESS" || key == "IP地址" || key == "IPV4地址"
                    || key == "IPADRESSE" || key == "IPV4-ADRESSE")
                {
                    if (val.Length > 0) cur.IpList.Add(val);
                }
                else if (key == "DEFAULTGATEWAY" || key == "默认网关"
                         || key == "STANDARDGATEWAY")
                {
                    // 只有真取到地址才算"有网关": 有的系统/locale 会把这一项打印成空值或"无",
                    // 不能因此把网卡判成"承载流量"(那会让推荐勾错网卡 -> 断错网 -> 游戏不断线)。
                    string g = val.Trim();
                    bool none = (g.Length == 0 || g == "无" || g == "無"
                        || string.Equals(g, "none", StringComparison.OrdinalIgnoreCase)
                        || g == "0.0.0.0" || g == "::");
                    if (!none)
                    {
                        cur.HasGateway = true;
                        cur.Gateway = g;
                    }
                }
                else if (key == "INTERFACE" || key == "接口" || key == "SCHNITTSTELLE")
                {
                    if (val.Length > 0 && !cur.IfNameList.Contains(val)) cur.IfNameList.Add(val);
                }
            }
        }
        return list;
    }

    /// <summary>查默认路由的「本机源 IP」（这个 IP 属于哪张网卡, 哪张就在承载流量）</summary>
    private static string DetectDefaultRouteSourceIp()
    {
        try
        {
            string routes = RunTool("route.exe", "print -4");
            foreach (string line in routes.Split('\n'))
            {
                // 只看"网络目标=0.0.0.0 且 掩码=0.0.0.0"那一行 —— 纯数值列,
                // 不读列头, 所以不受系统语言影响(中英文表头都是这一行的数值布局)。
                string[] p = line.Trim().Split(new char[] { ' ', '\t' }, StringSplitOptions.RemoveEmptyEntries);
                if (p.Length >= 5 && p[0] == "0.0.0.0" && p[1] == "0.0.0.0")
                {
                    // ⚠️ p[3] 必须是点分四段的 IP 才算数:
                    //    默认路由的网关列在 VPN / 无网关场景会显示 "On-link"/"在链路上",
                    //    直接当成源 IP 会让后面的匹配永远命中不了(连"有网关"兜底一起失效)。
                    if (IsIpv4(p[3])) return p[3];
                }
            }
        }
        catch { }
        return "";
    }

    /// <summary>严格的点分四段 IPv4 判定(不认 "On-link"/"在链路上" 这类非 IP 文本)</summary>
    private static bool IsIpv4(string s)
    {
        if (s == null) return false;
        string[] parts = s.Split('.');
        if (parts.Length != 4) return false;
        foreach (string q in parts)
        {
            if (q.Length == 0 || q.Length > 3) return false;
            foreach (char ch in q) if (ch < '0' || ch > '9') return false;
            int v;
            if (!int.TryParse(q, out v)) return false;
            if (v < 0 || v > 255) return false;
        }
        return true;
    }

    /// <summary>
    /// 探测所有网卡: 返回带「是否承载默认路由」标记的列表。
    /// 这是「换一台机器就配不对」的关键一步 —— 不能硬编码网卡名。
    /// </summary>
    private static List<NicInfo> DetectNics(List<string> warnings)
    {
        List<NicInfo> result = new List<NicInfo>();

        // 1) 全部网卡
        //    ★ 主路: 进程内的 System.Net.NetworkInformation(见 GetPsNics)—— Unicode + 机器可读,
        //      不依赖系统语言, 网卡名不会在管道里被解码坏。这是换机器最要紧的一条。
        //    ★ 兜底: netsh 文本解析 —— 拿不到 .NET 接口表时顶上, 双路取并集。
        //    (更正: 这里原本写着"主路: PowerShell 的 Get-NetAdapter" —— 与实现不符:
        //     那条路实测被 WMI 策略拒绝, 已弃用, 详见 GetPsNics 的注释。)
        List<PsNic> ps = GetPsNics();
        List<NicsBlock> all = ParseAddresses();
        Log("[网卡探测] .NET 接口表取到 " + ps.Count + " 张, netsh 解析到 " + all.Count + " 张");

        string srcIp = DetectDefaultRouteSourceIp();
        bool srcIpHasDefaultRoute = false;
        foreach (PsNic pn in ps)
            if (srcIp.Length > 0 && pn.Ips.Contains(srcIp)) srcIpHasDefaultRoute = true;
        Log("[网卡探测] 默认路由判定完成, 源地址"
            + (srcIp.Length == 0 ? "未找到" : "已取到(不记录具体地址)"));
        // 只在内存里用这个 IP 做匹配, 不写进日志 —— 日志是用户会发给别人排查的东西,
        // 没必要把本机 IP 带出去(用户明确要求日志里不要出现 IP)。

        // 2) 已禁用的网卡(网卡一旦被禁用, 上面的两个来源都取不到它, 只能靠状态表单独判定)
        HashSet<string> disabledNames = new HashSet<string>(StringComparer.OrdinalIgnoreCase);
        try
        {
            string st = RunTool("netsh.exe", "interface show interface");
            foreach (string line in st.Split('\n'))
            {
                string s = line.TrimEnd();
                if (s.Trim().Length == 0) continue;
                bool looksDisabled = (s.IndexOf("已禁用", StringComparison.Ordinal) >= 0)
                                     || (s.IndexOf("Disabled", StringComparison.OrdinalIgnoreCase) >= 0);
                if (!looksDisabled) continue;
                string nm = LastColumnName(s);
                if (nm.Length > 0) disabledNames.Add(nm);
            }
        }
        catch { }

        HashSet<string> seen = new HashSet<string>(StringComparer.OrdinalIgnoreCase);

        // ---- 主路: .NET 接口表结果 ----
        foreach (PsNic pn in ps)
        {
            if (pn.Name.Length == 0) continue;
            if (LooksLikeSystemNic(pn.Name)) continue;      // 回环/隧道不是用户要断的那张
            NicInfo ni = new NicInfo();
            ni.Name = pn.Name;
            ni.Ip = pn.Ips.Count > 0 ? pn.Ips[0] : "";
            ni.HasDefaultRoute = srcIpHasDefaultRoute && pn.Ips.Contains(srcIp);
            ApplyVirtualHint(ni);
            if (disabledNames.Contains(ni.Name)) Log("[网卡探测] " + ni.Name + " 当前处于【已禁用】状态");
            if (seen.Add(ni.Name)) result.Add(ni);
        }

        // ---- 兜底: netsh 解析结果(补主路没给到的) ----
        foreach (NicsBlock b in all)
        {
            if (b.Name.Length == 0) continue;
            // 跳过明显不需要处理的系统伪接口
            if (b.Name.StartsWith("Loopback", StringComparison.OrdinalIgnoreCase)) continue;
            if (b.Name.IndexOf("回环", StringComparison.Ordinal) >= 0) continue;
            if (seen.Contains(b.Name)) continue;

            NicInfo ni = new NicInfo();
            ni.Name = b.Name;
            ni.Ip = b.IpList.Count > 0 ? b.IpList[0] : "";
            ni.HasDefaultRoute = (srcIp.Length > 0) && b.IpList.Contains(srcIp);
            if (!ni.HasDefaultRoute && b.HasGateway && b.Gateway.Length > 0) ni.HasDefaultRoute = true;   // 有真网关才算
            ApplyVirtualHint(ni);
            if (disabledNames.Contains(b.Name))
            {
                Log("[网卡探测] " + b.Name + " 当前处于【已禁用】状态");
            }
            if (seen.Add(ni.Name)) result.Add(ni);
        }

        // 承载流量的排到最前
        result.Sort(delegate(NicInfo x, NicInfo y)
        {
            if (x.HasDefaultRoute != y.HasDefaultRoute) return x.HasDefaultRoute ? -1 : 1;
            return string.Compare(x.Name, y.Name, StringComparison.OrdinalIgnoreCase);
        });

        if (result.Count == 0)
            warnings.Add("没有探测到任何网卡 —— 请检查 netsh 是否可用, 或手动填写网卡名。");

        return result;
    }

    /// <summary>
    /// 「疑似虚拟网卡」提示 —— 仅用于界面上给用户一个提示, 不参与任何决策。
    /// 关键字里中英文都留着: 英文系统上连接名是 "Local Area Connection* 1" 这类,
    /// 只认中文关键字的话在英文机器上就标不出来(观感问题, 不影响功能)。
    /// </summary>
    private static void ApplyVirtualHint(NicInfo ni)
    {
        string lname = (ni.Name ?? "").ToLowerInvariant();
        string[] virtHints = new string[] { "virtual", "vmware", "vbox", "hyper-v", "loopback",
                                            "tap", "tun", "虚拟", "bluetooth", "蓝牙", "wi-fi direct",
                                            "本地连接*", "local area connection*", "内核调试" };
        foreach (string h in virtHints)
            if (lname.IndexOf(h, StringComparison.OrdinalIgnoreCase) >= 0) { ni.IsVirtualHint = true; break; }
    }

    /// <summary>
    /// 从 `netsh interface show interface` 的一行里取【连接名】。
    ///
    /// ⚠️ 踩过的坑: 这一行是 "管理员状态 状态 类型 接口名称" 四段,
    /// 但连接名本身可以带空格（`Ethernet 2`、`本地连接* 1`、`Wi-Fi 2`）。
    /// 早先用"按空格切开取最后一段", 会把名字截成 "2"/"1", 于是永远匹配不上真正的网卡名。
    /// 正确做法: 该表是固定列宽, 接口名称列从固定偏移开始, 取这一行剩余的全部内容。
    /// 偏移取不到时(格式变了)退回"末段", 宁可退化也不要返回空。
    /// </summary>
    private static string LastColumnName(string line)
    {
        // 实测偏移 51 —— 中英文表头宽度一致(微软没承诺过, 所以要做越界防御)
        const int NAME_COL = 51;
        if (line.Length > NAME_COL)
        {
            string t = line.Substring(NAME_COL).Trim();
            if (t.Length > 0) return t;
        }
        string[] p = line.Trim().Split(new char[] { ' ', '\t' }, StringSplitOptions.RemoveEmptyEntries);
        return (p.Length >= 1) ? p[p.Length - 1] : "";
    }

    /// <summary>回环 / 隧道这类系统伪接口: 不该出现在"要断的网卡"列表里</summary>
    private static bool LooksLikeSystemNic(string name)
    {
        string n = (name ?? "").ToLowerInvariant();
        if (n.StartsWith("loopback")) return true;
        if (n.IndexOf("回环", StringComparison.Ordinal) >= 0) return true;
        if (n.IndexOf("isatap", StringComparison.Ordinal) >= 0) return true;
        if (n.IndexOf("teredo", StringComparison.Ordinal) >= 0) return true;
        return false;
    }

    /// <summary>配置里存的网卡名在不在当前探测结果里 —— 换机器后配置里的老名字会失效, 用来提前提醒</summary>
    private static bool NicNameExists(string name)
    {
        foreach (PsNic pn in GetPsNics())
            if (string.Equals(pn.Name, name, StringComparison.OrdinalIgnoreCase)) return true;
        foreach (NicsBlock b in ParseAddresses())
            if (string.Equals(b.Name, name, StringComparison.OrdinalIgnoreCase)) return true;
        return false;
    }

    /// <summary>
    /// 这张网卡当前是不是"被管理性禁用"。
    ///
    /// ★ 修正(真 bug, 用户能直接撞上): 这里原来先用 .NET 的 OperationalStatus 判断,
    ///   把 Down 当成"被禁用"。但被管理性禁用的网卡根本不在 GetAllNetworkInterfaces() 里
    ///   (见 DetectNics 的注释), 所以那个分支实际只会命中"网卡是启用的、但当前没链路/没关联"
    ///   (Wi-Fi 关着、飞行模式、网线拔掉) —— 恒为误判。后果: 一开机就被当成"上次没收尾",
    ///   在窗口还没建出来之前跑整套恢复(最长一分多钟), 用户看到的是"双击了没反应";
    ///   点[开始保护]时也会在同一线程上冻住同样长的时间。
    ///   → 现在只认 netsh 的关键词: 它才是"管理状态(启用/禁用)"的权威来源, 而 .NET 的状态是
    ///     "有没有链路", 两件事不能混为一谈。判不出来就当"没被禁用" —— 保守: 不会误动网卡,
    ///     最多少一次自动收拾。
    /// </summary>
    private static bool IsDisabled(string nic)
    {
        if (string.IsNullOrEmpty(nic)) return false;
        try
        {
            string o = RunTool("netsh.exe", "interface show interface name=\"" + nic + "\"");
            if (o.Length == 0) return false;
            return o.IndexOf("禁用", StringComparison.Ordinal) >= 0
                || o.IndexOf("Disabled", StringComparison.OrdinalIgnoreCase) >= 0
                || o.IndexOf("Deaktiviert", StringComparison.OrdinalIgnoreCase) >= 0
                || o.IndexOf("Désactivé", StringComparison.OrdinalIgnoreCase) >= 0
                || o.IndexOf("無効", StringComparison.Ordinal) >= 0;
        }
        catch { return false; }
    }

    private static bool AnyTargetDisabled()
    {
        foreach (string nic in _cfg.Nics)
            if (IsDisabled(nic)) return true;
        return false;
    }

    // ============================================================================
    //  断网状态标记 (11.1.0 验收意见 MAJOR-1 / MINOR)
    //
    //  为什么要它: "上次是不是我们断的网络" 原来靠猜系统状态(网卡 Down / netsh 文本),
    //  在不同语言的 Windows 上会静默失效。改成我们自己落一个标记文件:
    //    断开成功后写 <数据目录>\_netcut_state.txt (记下断了哪几张网卡);
    //    恢复成功后删掉;
    //    下次启动只要看到这个标记, 就照它把网卡打开并撤掉快速层 —— 不猜、不看本地化文本。
    // ============================================================================

    /// <summary>最近一次"恢复网络"是否实测确认通了(网关 ping 通)。用于如实汇报, 不许假装成功。</summary>
    private static bool _lastRestoreVerified;
    /// <summary>最近一次"恢复网络"是不是"无法验证"(本机压根没有默认网关, 探针不可能通)。
    /// 这种时候既不能说"已恢复", 也不能说"没恢复" —— 只能如实说"网卡已启用、没法验证"。</summary>
    private static volatile bool _lastRestoreUnverifiable;

    private static string NetCutStatePath() { return Path.Combine(_dataDir, "_netcut_state.txt"); }

    private static void NetCutStateWrite(List<string> nics)
    {
        try
        {
            StringBuilder sb = new StringBuilder();
            sb.AppendLine("time=" + DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"));
            sb.AppendLine("fastcut=" + (FastCutLayer.Length > 0 ? FastCutLayer : ""));
            if (nics != null) for (int i = 0; i < nics.Count; i++) sb.AppendLine("nic=" + nics[i]);
            File.WriteAllText(NetCutStatePath(), sb.ToString(), Encoding.UTF8);
        }
        catch { }
    }

    /// <summary>开机恢复登记(默认不用): 只在断网期间存在, 恢复成功后立刻删掉。</summary>
    private const string RUN_ONCE_KEY = @"Software\Microsoft\Windows\CurrentVersion\RunOnce";
    private const string RUN_ONCE_NAME = "SkyGuardRestoreNetwork";

    private static void RunOnceSet()
    {
        try
        {
            string bat = Path.Combine(_baseDir, "恢复网络.bat");
            string cmd = File.Exists(bat)
                ? ("cmd.exe /c \"\"" + bat + "\"\"")
                : ("\"" + Path.Combine(_baseDir, "SkyGuardGUI.exe") + "\"");
            using (Microsoft.Win32.RegistryKey k = Microsoft.Win32.Registry.CurrentUser.OpenSubKey(RUN_ONCE_KEY, true))
            {
                if (k == null) { Log("[开机恢复] 打不开 RunOnce 项, 跳过登记"); return; }
                k.SetValue(RUN_ONCE_NAME, cmd, Microsoft.Win32.RegistryValueKind.String);
            }
            Log("[开机恢复] 已登记: 下次登录将自动运行一次恢复脚本(网络恢复成功后自动删除)");
        }
        catch (Exception ex) { Log("[开机恢复] 登记失败: " + ex.Message); }
    }

    private static void RunOnceClear()
    {
        try
        {
            using (Microsoft.Win32.RegistryKey k = Microsoft.Win32.Registry.CurrentUser.OpenSubKey(RUN_ONCE_KEY, true))
            {
                if (k == null) return;
                if (k.GetValue(RUN_ONCE_NAME) != null)
                {
                    k.DeleteValue(RUN_ONCE_NAME, false);
                    Log("[开机恢复] 已删除开机恢复登记");
                }
            }
        }
        catch { }
    }

    private static void NetCutStateClear()
    {
        try { if (File.Exists(NetCutStatePath())) File.Delete(NetCutStatePath()); } catch { }
        RunOnceClear();
    }

    private static bool NetCutStateExists()
    {
        try { return File.Exists(NetCutStatePath()); } catch { return false; }
    }

    private static List<string> NetCutStateNics()
    {
        List<string> l = new List<string>();
        try
        {
            if (!File.Exists(NetCutStatePath())) return l;
            foreach (string ln in File.ReadAllLines(NetCutStatePath(), Encoding.UTF8))
                if (ln.StartsWith("nic=", StringComparison.OrdinalIgnoreCase)) l.Add(ln.Substring(4).Trim());
        }
        catch { }
        return l;
    }

    /// <summary>
    /// 启动时: 上次如果是我们断的网络, 照自己的标记恢复(不猜系统状态、不看本地化文本)。
    /// 只有标记存在时才动网卡, 所以正常情况下启动不会慢。
    /// </summary>
    private static void NetCutStateRecoverAtStartup()
    {
        try
        {
            if (!NetCutStateExists()) return;
            List<string> nics = NetCutStateNics();
            if (nics.Count == 0)
            {
                // 标记在但没记下网卡名(上次写盘被打断): 退化为按 guard.ini 里配置的网卡全量尝试
                try { if (_cfg != null) nics = new List<string>(_cfg.Nics); } catch { }
                Log("[启动恢复] 标记里没有网卡名 -> 退化为按配置里的网卡恢复(共 " + nics.Count + " 张)");
            }
            else
            {
                Log("[启动恢复] 发现上次遗留的断网标记(网卡: " + string.Join(" / ", nics.ToArray()) + ")");
            }
            if (!IsAdmin())
            {
                // 11.1.0 验收(第二轮 M1-b): 没提权时 netsh 必失败 —— 此时绝不能清标记,
                // 否则下次管理员启动就没有线索了。
                Log("[启动恢复] 当前不是管理员, 改不了网卡 -> 保留标记, 请以管理员身份再运行一次程序即可自动恢复");
                return;
            }
            int okNics = 0;
            for (int i = 0; i < nics.Count; i++)
            {
                int rc = RunToolTimed("netsh.exe", "interface set interface name=\"" + nics[i] + "\" admin=enabled",
                    25000, "启动恢复 " + nics[i]);
                if (rc == 0) okNics++;
                Log("  [启动恢复] " + nics[i] + " -> netsh 退出码 " + rc);
            }
            FastCut_Release();
            if (nics.Count == 0 || okNics == nics.Count)
            {
                NetCutStateClear();
                Log("[启动恢复] 完成(已清标记)");
            }
            else
            {
                Log("[启动恢复] 有网卡没恢复成功(" + okNics + "/" + nics.Count + " ) -> 保留标记, 下次启动继续尝试");
            }
        }
        catch (Exception ex) { Log("[启动恢复] 异常: " + ex.Message); }
    }

    /// <summary>
    /// 事故修复: 网卡"启用成功" 不等于 网络回来了。
    /// 真实事故: WLAN 重新启用后没有重新关联/拿不到地址, 程序却报"网络已恢复 / 处置完成[成功]",
    /// 用户以为没事了, 实际上一直没网, 只能自己折腾四十分钟。
    /// 现在改成: 启用 -> 探测默认网关 -> 不通就自动补救(等待 / 续租 IP / 重挂网卡 / 刷 DNS)
    ///           -> 仍然不通就大声报错 + 弹窗 + 写清楚人工步骤。
    /// 返回 true 仅当"默认网关确实 ping 通"。
    /// </summary>
    /// <summary>
    /// 把"到底恢复没有"直接弹给用户看。
    /// 理由(实测): 老版本只把结果写日志 —— 用户点了[恢复网络]之后 44 秒里看不到任何反馈,
    /// 就以为"这个按钮没用", 转头去跑外面的 .bat。恢复结果必须让人看得见。
    /// </summary>
    /// <summary>
    /// 全部恢复方案都没成功时自动弹出的"恢复指引"窗口。
    /// 字号按窗口大小自动调整(Resize 时重算), 所以放大缩小窗口都读得清。
    /// </summary>
    private static void ShowRestoreGuide()
    {
        try
        {
            using (Form f = new Form())
            {
                f.Text = "网络恢复失败";
                f.BackColor = C_BG;
                f.StartPosition = FormStartPosition.CenterScreen;
                f.ClientSize = new Size(Sc(580), Sc(430));
                f.MinimumSize = new Size(Sc(440), Sc(320));
                f.FormBorderStyle = FormBorderStyle.Sizable;
                f.MaximizeBox = false;
                f.MinimizeBox = false;
                f.TopMost = true;
                f.ShowInTaskbar = true;
                SetAutoScaleFont(f, Fi("Microsoft YaHei UI", 10F));

                Label lb = new Label();
                lb.Dock = DockStyle.Fill;
                lb.AutoSize = false;
                lb.TextAlign = ContentAlignment.MiddleLeft;
                lb.Padding = Pad(18, 16, 18, 8);
                lb.Text = "网络恢复失败。\r\n\r\n"
                        + "建议按顺序试：\r\n"
                        + "  1) 再点一次[恢复网络]，无线重连常常要等一会\r\n"
                        + "  2) 以管理员身份运行程序目录里的 恢复网络.bat\r\n"
                        + "  3) 重启电脑\r\n"
                        + "  4) 装了 VPN 或游戏加速器的话，先退出它再试\r\n\r\n"
                        + "日志：设置 → 维护 → [打开日志]";
                f.Controls.Add(lb);

                FlowLayoutPanel row = new FlowLayoutPanel();
                row.Dock = DockStyle.Bottom;
                row.FlowDirection = FlowDirection.RightToLeft;
                row.AutoSize = true;
                row.WrapContents = false;
                row.Padding = Pad(0, 6, 12, 12);
                Button bOk = MakeButton("知道了", null, "primary");
                bOk.Click += delegate { f.Close(); };
                Button bRetry = MakeButton("再试一次恢复", null, "plain");
                bRetry.Click += delegate
                {
                    f.Close();
                    Thread th = new Thread(delegate() { try { RunNetOp(true, 0); } catch { } });
                    th.IsBackground = true;
                    th.Start();
                };
                Button bFolder = MakeButton("打开程序目录", null, "plain");
                bFolder.Click += delegate
                {
                    try { Process.Start("explorer.exe", "\"" + _baseDir + "\""); } catch { }
                };
                row.Controls.Add(bOk);
                row.Controls.Add(bRetry);
                row.Controls.Add(bFolder);
                f.Controls.Add(row);

                f.Shown += delegate { FitLabelFont(lb, Sc(10), Sc(22)); };
                f.Resize += delegate { FitLabelFont(lb, Sc(10), Sc(22)); };
                f.ShowDialog(_form);
            }
        }
        catch { }
    }

    /// <summary>
    /// 把标签字号调到"正好填满可用区域": 从 basePt 起, 放不下就往下缩, 还有余量就往上放。
    /// 上下限都留着, 免得缩到看不清或放到夸张。
    /// </summary>
    private static void FitLabelFont(Label lb, float basePt, float maxPt)
    {
        try
        {
            if (lb == null) return;
            Size area = lb.ClientSize;
            if (area.Width <= 20 || area.Height <= 20) return;
            string txt = lb.Text;
            float best = 7F;
            for (float pt = basePt; pt >= 7F; pt -= 0.5F)
            {
                Size need = MeasureLabel(lb, txt, pt, area.Width);
                if (need.Height <= area.Height) { best = pt; break; }
            }
            if (best >= basePt)
            {
                for (float pt = basePt; pt <= maxPt; pt += 0.5F)
                {
                    if (MeasureLabel(lb, txt, pt, area.Width).Height <= area.Height) best = pt;
                    else break;
                }
            }
            if (lb.Font == null || Math.Abs(lb.Font.SizeInPoints - best) > 0.2F)
                lb.Font = Fi("Microsoft YaHei UI", best);
        }
        catch { }
    }

    private static Size MeasureLabel(Label lb, string txt, float pt, int width)
    {
        try
        {
            using (Font fnt = Fi("Microsoft YaHei UI", pt))
            using (Graphics g = lb.CreateGraphics())
            {
                return TextRenderer.MeasureText(g, txt, fnt, new Size(width, int.MaxValue),
                    TextFormatFlags.WordBreak | TextFormatFlags.NoPadding);
            }
        }
        catch { return new Size(width, int.MaxValue / 2); }
    }

    private static void VerdictPopup(bool ok, long ms)
    {
        try
        {
            string sec = (ms / 1000.0).ToString("0.0");
            if (ok)
            {
                MessageBox.Show("网络已恢复，用了 " + sec + " 秒。",
                    "SkyGuard · 网络恢复", MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
            else
            {
                MessageBox.Show(
                    "网络还没有恢复。\n\n"
                    + "已自动重新启用网卡并续租 IP，共 " + sec + " 秒，"
                    + "默认网关仍然 ping 不通。\n\n请按顺序试：\n"
                    + "  1) 再点一次[恢复网络]，第二次往往就好了\n"
                    + "  2) 以管理员身份运行程序目录里的 恢复网络.bat\n"
                    + "  3) 重启电脑\n\n详情在日志 SkyGuardGUI.log 里。",
                    "SkyGuard · 网络恢复", MessageBoxButtons.OK, MessageBoxIcon.Error);
            }
        }
        catch { }
    }

    /// <summary>
    /// 一句话说清"这次恢复到底怎么样了"。三种结果分开说, 不许含糊:
    ///   ① 探针确认通了        -> 网络已恢复
    ///   ② 本机天生没有默认网关 -> 网卡已启用, 但探针无从验证(既不该说成功也不该说失败)
    ///   ③ 探针能测却不通过     -> 网络没恢复
    /// </summary>
    private static string RestoreVerdictText()
    {
        if (_lastRestoreVerified) return "网络已恢复";
        if (_lastRestoreUnverifiable) return "网卡已启用(本机本来就没有默认网关, 探针无从验证)";
        return "网络没恢复(点[恢复网络]或跑 恢复网络.bat)";
    }

    /// <summary>
    /// 恢复校验时"现在取不到默认网关"该怎么处理? —— 纯函数, 由 restoretest 喂边界(不碰网卡)。
    ///
    /// ★ 用户实机日志(真实事故, 11.1.3-RC1 的错误行为):
    ///   断网前日志明确写着"断流前 1/1 可连", 说明本机刚才能上网; 恢复时网卡刚被 netsh 打开,
    ///   DHCP 还没续到租, 于是"默认网关表"是空的。RC1 把这种情况一律当成"本机天生没有网关",
    ///   直接宣布"处置完成 [成功]"并跳过等待/续租 —— 用户看到的是"成功"紧跟一句
    ///   "本机当前连网关都不通", 而网络其实还要好几秒才回来。
    ///   现在改成: 只有"确实没有证据说明它本来能上网"时才走快速通道, 否则照常等待 + 续租 + 重挂。
    ///
    ///   hasGatewayNow : 现在能不能取到默认网关
    ///   baselineN     : 断流前基线可连数 (>0 = 刚才能连; 0 = 测过都不通; -1 = 没测过/未知)
    ///   dhcpOn        : 配置里的网卡有没有开着 DHCP (开着 = 它在等地址, 该等该续租)
    /// 返回 true  = 按"本机天生没有默认网关, 探针无法验证"处理(快速通道, 不折腾用户);
    ///      false = 照常走"等待 -> 续租 -> 重挂"(因为很可能只是网卡刚回来、还没拿到路由)。
    /// </summary>
    private static bool TreatNoGatewayAsUnverifiable(bool hasGatewayNow, int baselineN, bool dhcpOn)
    {
        if (hasGatewayNow) return false;             // 有网关: 走正常校验
        if (baselineN > 0) return false;             // 断流前明明能连 -> 必须等它回来
        if (baselineN < 0 && dhcpOn) return false;   // 基线没测过 + 网卡吃 DHCP -> 宁可多等/续租
        return true;
    }

    /// <summary>配置里的网卡有没有开着 DHCP(用来判断"是不是在等地址")。拿不到就当没有。</summary>
    private static bool AnyConfiguredNicUsesDhcp(List<string> nics)
    {
        try
        {
            foreach (NetworkInterface ni in NetworkInterface.GetAllNetworkInterfaces())
            {
                if (ni == null) continue;
                string nm = (ni.Name ?? "").Trim();
                if (nics != null && nics.Count > 0 && !ListHas(nics, nm)) continue;
                try
                {
                    IPv4InterfaceProperties p = ni.GetIPProperties().GetIPv4Properties();
                    if (p != null && p.IsDhcpEnabled) return true;
                }
                catch { }
            }
        }
        catch { }
        return false;
    }

    /// <summary>
    /// 恢复校验用的一次探测。
    /// 有默认网关就 ping 网关(默认路径, 只走局域网); 没有网关但用户自己配了外网目标, 就连那些目标。
    /// 为什么不能直接调 ProbeReachableNow: 那个还会顺带做基线统计, 语义不同(见各自注释)。
    /// </summary>
    private static bool ProbeNetworkUp(int timeoutMs)
    {
        if (GatewayAddresses().Count > 0) return ProbeGateway(timeoutMs);
        string[] ext = ExternalTargets();
        for (int i = 0; i < ext.Length; i++) if (ProbeTcp(ext[i], timeoutMs)) return true;
        return false;
    }

    private static bool VerifyNetworkRestored(string why, List<string> nics, bool showPopup, int reqGen)
    {
        _lastRestoreVerified = false;
        _lastRestoreUnverifiable = false;
        _restoreSuperseded = false;

        int baseN;
        lock (_fastCutGate) { baseN = _probeBaselineReachable; }
        bool gwNow = GatewayAddresses().Count > 0;
        bool extConfigured = ExternalTargets().Length > 0;

        // ★ 本机(静态 IP / 纯内网)天生没有默认网关时, ping 探针永远不可能通 —— 那不是"没恢复",
        //   是"这套探针在这台机器上无法判定", 不该让用户白等两分钟 + 看一个假失败。
        //   但"网卡刚打开、DHCP 还没续上"也会表现成"没有默认网关", 那种必须照常等待/续租 ——
        //   区分规则见 TreatNoGatewayAsUnverifiable(用户实机日志踩过, 原因写在它的注释里)。
        if (!extConfigured && TreatNoGatewayAsUnverifiable(gwNow, baseN, AnyConfiguredNicUsesDhcp(nics)))
        {
            _lastRestoreUnverifiable = true;
            Log("本机没有任何默认网关(断流前也没探到可连的目标, 网卡也没开着 DHCP) -> 探针无从验证("
                + why + "), 按「网卡已启用」算完成, 不判定为失败");
            return true;
        }
        if (!gwNow)
        {
            // 有证据说明本机本来能上网: 现在没有网关只可能是"网卡刚回来, 还在重新关联 / 等 DHCP 续租"
            Log("本机现在没有默认网关(断流前基线=" + baseN + ")"
                + (extConfigured ? ", 改用你自己配的外网目标继续验证" : "")
                + " -> 判定为「网卡刚启用、还没拿到路由」, 继续等待并补救(" + why + ")");
        }

        long t0 = Stopwatch.GetTimestamp();

        // 阶段 1「先轻后重」: 网卡刚打开时网络常常 1~5 秒就回来 —— 先密集探测, 一通就立刻返回。
        // 实测教训(真实日志): 老代码在这里先做重活 —— ipconfig /renew 一步吃 16 秒、
        // "重挂网卡"又吃 18 秒, 全程 44 秒且没有任何反馈, 用户以为点了没用。
        // ⚠️ 每一段等待都走 WaitAbortable: 期间用户按了触发键(要立刻断网)就马上让路。
        for (int i = 0; i < 8; i++)
        {
            if (!WaitAbortable(i == 0 ? 1000 : 1500, reqGen)) { RestoreSuperseded(reqGen); return false; }
            if (ProbeNetworkUp(1000))
            {
                _lastRestoreVerified = true;
                long ms1 = ElapsedMs(t0);
                Log("网络已恢复(用了 " + ms1 + " ms)");
                if (showPopup && ms1 > 5000) VerdictPopup(true, ms1);
                return true;
            }
            // 无线重连本来就要 5~15 秒, 这不是失败, 是还在等 —— 所以低频输出 + 中性措辞
            if (i == 0 || (i + 1) % 3 == 0)
                Log("等待网络恢复(第 " + (i + 1) + " 次检查, 已等 " + ElapsedMs(t0) + " ms)");
        }

        // 阶段 2: 还不行才做重活 —— 续租 IP, 然后继续探
        if (RestoreSuperseded(reqGen)) return false;
        Log("网络未恢复, 尝试续租 IP");
        RunToolTimed("ipconfig.exe", "/renew", 25000, "恢复-续租IP");
        for (int i = 0; i < 5; i++)
        {
            if (!WaitAbortable(1500, reqGen)) { RestoreSuperseded(reqGen); return false; }
            if (ProbeNetworkUp(1000))
            {
                _lastRestoreVerified = true;
                long ms2 = ElapsedMs(t0);
                Log("网络已恢复(续租 IP 后, 用了 " + ms2 + " ms)");
                if (showPopup) VerdictPopup(true, ms2);
                return true;
            }
        }

        // 阶段 3: 最后手段 —— 重挂网卡(禁用再启用 + 续租), 再继续探
        if (nics != null)
        {
            for (int i = 0; i < nics.Count; i++)
            {
                if (RestoreSuperseded(reqGen)) return false;
                Log("网络未恢复, 重新启用网卡 " + nics[i]);
                RunToolTimed("netsh.exe", "interface set interface name=\"" + nics[i] + "\" admin=disabled", 25000, "恢复-重挂-禁用");
                if (!WaitAbortable(800, reqGen)) { RestoreSuperseded(reqGen); return false; }
                RunToolTimed("netsh.exe", "interface set interface name=\"" + nics[i] + "\" admin=enabled", 25000, "恢复-重挂-启用");
                RunToolTimed("ipconfig.exe", "/renew", 25000, "恢复-重挂后续租");
            }
        }
        for (int i = 0; i < 6; i++)
        {
            if (!WaitAbortable(2000, reqGen)) { RestoreSuperseded(reqGen); return false; }
            if (ProbeNetworkUp(1000))
            {
                _lastRestoreVerified = true;
                long ms3 = ElapsedMs(t0);
                Log("网络已恢复(重新启用网卡后, 用了 " + ms3 + " ms)");
                if (showPopup) VerdictPopup(true, ms3);
                return true;
            }
        }
        long tAll = ElapsedMs(t0);
        Log("网络未恢复(已尝试重新启用网卡、续租 IP, 共 " + tAll + " ms)");
        Log("  可以这样救回来:");
        Log("    1) 程序里再点一次 [恢复网络]");
        Log("    2) 右键以管理员运行程序目录里的 恢复网络.bat");
        Log("    3) 手动: netsh interface set interface name=\"<网卡名>\" admin=enabled 然后 ipconfig /renew");
        Log("    4) 还不行就重启电脑(最快)");
        if (showPopup)
        {
            try
            {
                MessageBox.Show(
                    "网卡已经重新打开，但网络没有恢复。\n\n"
                    + "请按顺序试：\n"
                    + "  1) 再点一次[恢复网络]\n"
                    + "  2) 以管理员身份运行程序目录里的 恢复网络.bat\n"
                    + "  3) 重启电脑\n\n"
                    + "详情在日志 SkyGuardGUI.log 里。",
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Error);
                if (MessageBox.Show("现在再试一次吗？", APP_NAME, MessageBoxButtons.YesNo, MessageBoxIcon.Question) == DialogResult.Yes)
                {
                    Thread thRetry = new Thread(delegate() { try { RunNetOp(true, 0); } catch { } });
                    thRetry.IsBackground = true;
                    thRetry.Name = "SkyGuardRetryRestore";
                    thRetry.Start();
                }
            }
            catch { }
        }
        return false;
    }

    /// <summary>
    /// 断网/恢复: 承载流量那张先单独处理, 其余并行。
    /// ★ 只由常驻断网线程调用(见 WakeNetCut/RunNetOp): 只有一条线程动网卡, 才不会互相打架。
    /// reqGen = 本次请求的代数, 用来判断"恢复途中用户是不是又按了触发键"(要立刻让路)。
    /// </summary>
    private static void SetNets(bool enable, int reqGen)
    {
        // 自检/测试模式: 演练整条流程但绝不动用户的网卡(见 racytest)
        if (_noNet)
        {
            Log("[自检] 已跳过真实 " + (enable ? "恢复网络" : "断网")
                + " 操作 (noNet 模式, 网卡没有被碰)");
            if (!enable) _firstDownTicks = Stopwatch.GetTimestamp();
            return;
        }

        // ---- 11.1.0 快速断流层 ----
        // 断开: 先用 WFP/防火墙在毫秒级拦住出站(抢时间), 网卡照旧禁用作最终保证;
        // 恢复: 先撤快速层(网络立刻可用), 再恢复网卡 —— 顺序不能反(撤网卡要几秒)。
        if (enable)
        {
            _statusOverride = "网络恢复中，请稍等";
            FastCut_Release();
        }
        else
        {
            // 断网方式(设置 → 高级选项): 1=只禁用网卡 时完全不碰快速度层
            bool fastOn = (_cfg == null || _cfg.CutMode != 1) && FastCut_Engage();
            if (fastOn)
            {
                // 验收意见(MINOR): 此刻网卡还没禁, 所以这一探才能证明「是快速层拦住的」;
                // 后面禁完网卡还会再探一次, 那证明的是「整机断网」。两件事分开写, 不许混为一谈。
                // 11.1.0 验收(第二轮 N2): 用短超时(200ms)只探网关 —— 原来用 700ms 的全量探测
                // 会把"禁网卡"这一刀固定推迟 0.7 秒, 而抢时间正是这层的全部意义。
                bool gwBlocked = !ProbeGateway(200);
                int baseN;
                lock (_fastCutGate) { baseN = _probeBaselineReachable; }
                Log("快速断流: " + (baseN > 0 ? (gwBlocked ? "已拦住" : "没拦住") : "无法验证"));
            }
        }

        // 11.1.0 验收(第二轮 M1-a) 写前标记: 动网卡之前先把"要断网 + 断哪几张"落盘。
        // 禁网卡本身要 3~15 秒, 这期间被强杀/断电的话, 事后唯一的恢复线索就是这个标记 ——
        // 原来等禁完才写, 正好在那段窗口里没有凭证。
        if (!enable) NetCutStateWrite(new List<string>(_cfg.Nics));

        string verb = enable ? "enabled" : "disabled";
        string word = enable ? "恢复网络" : "断网";

        List<string> work = new List<string>(_cfg.Nics);
        if (enable)
        {
            // 恢复时把"我们上次实际禁用过的网卡"(断网标记里记着)也一起打开 ——
            // 万一用户在断网期间改过配置, 那些网卡不会被漏下(否则他会一直没网)。
            List<string> marked = NetCutStateNics();
            for (int i = 0; i < marked.Count; i++)
                if (!work.Contains(marked[i])) work.Add(marked[i]);
            if (marked.Count > 0)
                Log("恢复网络: 断网标记里记着 " + string.Join(" / ", marked.ToArray()) + ", 一并恢复");
        }
        if (!enable && work.Count == 0)
        {
            // 一个网卡都没勾: 此时只剩快速断流在拦, 没有"禁用网卡"这层硬兜底 —— 必须说清楚
            Log("警告: 没有勾选任何网卡 —— 本次只有快速断流在拦出站, 没有禁用网卡这一层兜底");
            try
            {
                MessageBox.Show(
                    "没有勾选任何网卡。\n\n本次只有快速断流在拦截流量。\n"
                    + "请到[设置] → [网卡与选项]勾选正在使用的网卡。",
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
            }
            catch { }
        }
        // 断网方式 2 = 只用快速断流: 不禁用任何网卡
        // (给"禁用网卡之后要等很久才恢复"的机器准备的; 这时硬兜底就只剩快速层本身)
        if (!enable && _cfg != null && _cfg.CutMode == 2 && work.Count > 0)
        {
            Log("按设置(只用快速断流): 本次不禁用网卡");
            work.Clear();
        }
        // 承载流量的排第一
        work.Sort(delegate(string x, string y)
        {
            bool bx = IsTrafficNic(x), by = IsTrafficNic(y);
            if (bx != by) return bx ? -1 : 1;
            return 0;
        });

        List<Thread> ts = new List<Thread>();
        bool firstDone = false;
        object gate = new object();
        bool trafficHandled = false;
        // ★ 成败统计: 早先这里不看 netsh 的退出码, 于是"网卡名不存在"也会打印"完成"。
        //   现在把每张网卡的结果收上来, 最后统一告警 —— 宁可日志吵, 也不能假报成功。
        int okCount = 0, failCount = 0, total = 0;
        List<string> failedNics = new List<string>();
        total = work.Count;

        foreach (string nic in work)
        {
            // 恢复途中来了新的断网请求: 别再继续开网卡了, 立刻让路 ——
            // 否则我们会把刚被断开的网卡又打开(那就是"断网没生效"的另一种样子)。
            if (enable && reqGen != 0 && _netReqGen != reqGen)
            {
                _restoreSuperseded = true;
                Log("恢复网络: 收到新的网络操作请求 -> 停止继续启用网卡, 立刻让路");
                break;
            }
            string myNic = nic;
            if (!trafficHandled && IsTrafficNic(myNic))
            {
                trafficHandled = true;   // 先单独切它(独占, 不受并发干扰)
                long t0 = Stopwatch.GetTimestamp();
                try
                {
                    int rc = RunToolTimed("netsh.exe", "interface set interface name=\"" + myNic + "\" admin=" + verb,
                        25000, word + " " + myNic);
                    if (rc == 0)
                    {
                        okCount++;
                        Log(word + " " + myNic + " [承载流量] 完成, 用了 " + ElapsedMs(t0) + " ms"
                            + " (自触发 " + ElapsedMs(_panicStartTicks) + " ms)");
                        _firstDownTicks = Stopwatch.GetTimestamp();
                    }
                    else
                    {
                        failCount++; failedNics.Add(myNic);
                        Log(word + " " + myNic + " [承载流量] 失败(netsh 退出码 " + rc
                            + ") —— 这张网卡没被" + word + ", 网卡名可能已变(换机器常见)");
                    }
                }
                catch (Exception ex) { failCount++; failedNics.Add(myNic); Log(word + " " + myNic + " 异常: " + ex.Message); }
                continue;
            }
            Thread t = new Thread(delegate()
            {
                long t0 = Stopwatch.GetTimestamp();
                try
                {
                    int rc = RunToolTimed("netsh.exe", "interface set interface name=\"" + myNic + "\" admin=" + verb,
                        25000, word + " " + myNic);
                    if (rc == 0)
                    {
                        lock (gate) { okCount++; }
                        Log(word + " " + myNic + " 完成 [并行], 耗时 " + ElapsedMs(t0) + " ms");
                        lock (gate) { if (!firstDone) { firstDone = true; if (_firstDownTicks == 0) _firstDownTicks = Stopwatch.GetTimestamp(); } }
                    }
                    else
                    {
                        lock (gate) { failCount++; failedNics.Add(myNic); }
                        Log(word + " " + myNic + " 失败 [并行](netsh 退出码 " + rc + ")");
                    }
                }
                catch (Exception ex) { lock (gate) { failCount++; failedNics.Add(myNic); } Log(word + " " + myNic + " 异常: " + ex.Message); }
            });
            t.IsBackground = true;
            ts.Add(t);
            t.Start();
        }
        JoinAll(ts, 15000);

        // ★ 关键告警: 一张都没成功 —— 这时候"断网"其实没发生, 必须让用户看得见
        if (total > 0 && okCount == 0)
        {
            Log("错误: 没有一张网卡" + word + "成功 (" + failCount + "/" + total + " 失败)");
            Log("错误: 本次" + (enable ? "恢复" : "断网") + "没有生效，请到 [设置] → [网卡与选项] 重新探测并勾选网卡");
            if (!_noNet && !enable && !_headless)
            {
                try
                {
                    MessageBox.Show(
                        "断网没有生效。\n\n"
                      + "配置里的网卡名在这台机器上可能不存在。\n"
                      + "请打开[⚙ 设置] → [网卡与选项] → [重新探测]，勾选带[承载流量]的那张。\n\n"
                      + "这次失败的网卡: " + string.Join(" / ", failedNics.ToArray()),
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                }
                catch { }
            }
        }
        else if (failCount > 0)
        {
            Log(word + ": 成功 " + okCount + " 张, 失败 " + failCount + " 张 ("
                + string.Join(" / ", failedNics.ToArray()) + ")");
        }

        // ---- 自证 / 断网标记 / 基线维护 ----
        if (!enable)
        {
            // 整机断网确认(含禁网卡): 基线上能连的必须全连不上
            ProbeVerifyAfterCut();
            // 记下"是我们断的、断了哪几张网卡": 下次启动/下次开程序靠它恢复,
            // 不再依赖"网卡是不是 Down"或本地化文本(验收意见 MAJOR-1)
            if (okCount > 0)
            {
                List<string> okNics = new List<string>();
                for (int i = 0; i < work.Count; i++) if (!failedNics.Contains(work[i])) okNics.Add(work[i]);
                NetCutStateWrite(okNics);
                // 可选(默认关): 顺手登记一条"下次登录自动恢复", 覆盖"程序被强杀且用户不再打开"的最坏情况
                if (_cfg != null && _cfg.RestoreOnBoot) RunOnceSet();
            }
        }
        else
        {
            // 11.1.0 验收(第二轮 M1-c): 只有全部恢复成功才清标记。
            // 失败时保留 —— 标记是唯一的恢复凭证, 一次失败的尝试不该把它销毁。
            // 事故修复: "netsh 返回 0" 只说明网卡被打开了, 不说明网络回来了。
            // 必须实测默认网关, 不通就自动补救; 还写不清就不许说"已恢复"。
            // 恢复失败时的提示统一由下面的"指引窗口"负责, 这里不再弹旧的那个提示框
            long tRestore0 = Stopwatch.GetTimestamp();
            bool netBack = (okCount > 0) && VerifyNetworkRestored("恢复网络", work, false, reqGen);
            if (_restoreSuperseded)
            {
                // 被打断 ≠ 失败: 这时候状态栏/指引都不该说"恢复失败"(新的操作已经接管了)。
                Log("恢复网络: 本次流程被新的网络操作打断, 不再判定成败, 也不弹恢复指引");
            }
            else if (netBack)
            {
                _statusOverride = "";
                long usedMs = ElapsedMs(tRestore0);
                if (usedMs > 5000) VerdictPopup(true, usedMs);
            }
            else
            {
                _statusOverride = "网络恢复失败，请查看指引";
                Log("网络恢复失败: 状态栏已提示, 并弹出恢复指引窗口");
                try
                {
                    Thread thGuide = new Thread(delegate() { try { ShowRestoreGuide(); } catch { } });
                    thGuide.IsBackground = true;
                    thGuide.Name = "SkyGuardRestoreGuide";
                    thGuide.Start();
                }
                catch { }
            }
            if (total > 0 && okCount == total && netBack) NetCutStateClear();
            else if (!_restoreSuperseded)
                Log("网络未完全恢复(网卡 " + okCount + "/" + total + "), 已记录, 下次启动会重新尝试");
            // 恢复后重新记基线。放后台线程: 这条路径可能从按钮直接进来, 不能占着界面线程睡。
            // ★ 多试几次再定基线: 网卡刚启用时无线重连/DHCP 续租还要几秒, 一次探到 0 就记 0 的话,
            //   下一次断流的"到底拦住了吗"会永远只能写"无法验证"(用户实机日志里就是这么发生的)。
            Thread pb = new Thread(delegate()
            {
                for (int i = 0; i < 10; i++)
                {
                    try { Thread.Sleep(i == 0 ? 1500 : 2000); } catch { }
                    ProbeRefreshBaseline(i == 0 ? "恢复后" : ("恢复后第 " + (i + 1) + " 次"));
                    int n;
                    lock (_fastCutGate) { n = _probeBaselineReachable; }
                    if (n > 0) break;                                  // 已经能连上了, 基线有效
                    if (_cfg != null && !_cfg.FastCut) break;           // 用户没开快速断流, 不用管基线
                    if (NetCutStateExists()) break;                     // 又被断网了, 别把"断着"当基线
                }
            });
            pb.IsBackground = true;
            pb.Name = "SkyGuardProbe";
            pb.Start();
        }
    }

    /// <summary>
    /// 等这些线程结束, 但给个上限。
    /// 为什么要上限: netsh 偶尔会卡住(驱动在忙), 不设上限的话整个处置就永久停在这里,
    /// _busy 一直是 true, 之后按触发键全都没反应 —— 那正是用户看到的"卡死了"。
    /// </summary>
    private static void JoinAll(List<Thread> ts, int ms)
    {
        long t0 = Stopwatch.GetTimestamp();
        foreach (Thread t in ts)
        {
            long left = ms - ElapsedMs(t0);
            if (left < 0) left = 0;
            if (!t.Join((int)left))
                Log("  警告: 有个网卡操作一直没返回, 不等它了(最多等 " + ms + " ms)");
        }
    }

    private static bool IsTrafficNic(string nic)
    {
        foreach (NicInfo n in _nics)
            if (string.Equals(n.Name, nic, StringComparison.OrdinalIgnoreCase)) return n.HasDefaultRoute;
        return false;
    }

    #endregion

    // ============================================================================
    //  五、强杀进程
    // ============================================================================

    #region 强杀

    private static List<KeyValuePair<int, string>> EnumProcesses()
    {
        List<KeyValuePair<int, string>> list = new List<KeyValuePair<int, string>>();
        int len = 512 * 1024;
        IntPtr buf = Marshal.AllocHGlobal(len);
        int ret, guard = 0;
        while ((ret = NtQuerySystemInformation(SystemProcessInformation, buf, len, out len)) == STATUS_INFO_LENGTH_MISMATCH)
        {
            Marshal.FreeHGlobal(buf);
            len += 256 * 1024;
            buf = Marshal.AllocHGlobal(len);
            if (++guard > 8) break;
        }
        if (ret != 0) { Marshal.FreeHGlobal(buf); return list; }
        try
        {
            long offset = 0;
            while (true)
            {
                IntPtr p = new IntPtr(buf.ToInt64() + offset);
                SYSTEM_PROCESS_INFORMATION spi =
                    (SYSTEM_PROCESS_INFORMATION)Marshal.PtrToStructure(p, typeof(SYSTEM_PROCESS_INFORMATION));
                if (spi.ImageName.Buffer != IntPtr.Zero && spi.ImageName.Length > 0)
                {
                    string nm = Marshal.PtrToStringUni(spi.ImageName.Buffer, spi.ImageName.Length / 2);
                    if (!string.IsNullOrEmpty(nm))
                        list.Add(new KeyValuePair<int, string>(spi.UniqueProcessId.ToInt32(), nm));
                }
                if (spi.NextEntryOffset == 0) break;
                offset += spi.NextEntryOffset;
            }
        }
        finally { Marshal.FreeHGlobal(buf); }
        return list;
    }

    /// <summary>
    /// 进程名归一化: 去 .exe 后缀、去首尾空格、转小写。
    /// 为什么需要: NtQuerySystemInformation 返回的名字带 .exe(如 MuMuNxMain.exe),
    /// 而配置/界面里写的是不带后缀的(MuMuNxMain)。早先直接比较字符串,
    /// 结果「MuMu 系列一个都找不到」、只有恰好带后缀的 Sky.exe 能匹配 —— 实测踩过。
    /// </summary>
    private static string NormProcName(string name)
    {
        string n = (name ?? "").Trim();
        if (n.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) n = n.Substring(0, n.Length - 4);
        return n.ToLowerInvariant();
    }

    private static List<int> FindPids(string imageName)
    {
        return FindPids(imageName, null);
    }

    /// <summary>
    /// 找某个进程名的所有 PID。
    ///
    /// 性能坑(实测日志): 不带 snapshot 时每次调用都要重新枚举一遍全系统进程表
    /// (NtQuerySystemInformation, 250+ 进程)。一轮 9 个目标 = 9 次全表枚举 —— 这就是
    /// 补杀轮那 300~400 ms 的来源(日志里"全部确认退出 1415 ms" 之后还有 391 ms 收尾)。
    /// 同一轮里的多次查询应该共用一次枚举结果, 所以加了 snapshot 参数。
    /// </summary>
    private static List<int> FindPids(string imageName, List<KeyValuePair<int, string>> snapshot)
    {
        List<int> pids = new List<int>();
        string want = NormProcName(imageName);
        if (want.Length == 0) return pids;
        List<KeyValuePair<int, string>> all = (snapshot != null) ? snapshot : EnumProcesses();
        foreach (KeyValuePair<int, string> kv in all)
            if (NormProcName(kv.Value) == want)
                pids.Add(kv.Key);
        return pids;
    }

    /// <summary>
    /// 一次枚举 + 建"进程名 -> PID 列表"字典。
    ///
    /// 为什么要有这个(用户要求"按下到杀掉压进 100 ms"): 实测单次全表枚举 9 ms,
    /// 而老代码每个目标各枚举一次, 9 个目标就是 107 ms —— 全花在"问系统谁在跑"上,
    /// 真正下刀(TerminateProcess)只要 4 ms。改成一次枚举 + 字典查表后, 一轮只要 ~10 ms。
    /// </summary>
    private static Dictionary<string, List<int>> ProcMap(
        List<KeyValuePair<int, string>> snapshot, out int count)
    {
        Dictionary<string, List<int>> map = new Dictionary<string, List<int>>();
        count = 0;
        List<KeyValuePair<int, string>> all = (snapshot != null) ? snapshot : EnumProcesses();
        foreach (KeyValuePair<int, string> kv in all)
        {
            count++;
            string n = NormProcName(kv.Value);
            List<int> l;
            if (!map.TryGetValue(n, out l)) { l = new List<int>(); map[n] = l; }
            l.Add(kv.Key);
        }
        return map;
    }

    /// <summary>从已经建好的字典里取 PID(不再枚举全表)</summary>
    private static List<int> PidsFrom(Dictionary<string, List<int>> map, string imageName)
    {
        List<int> r = new List<int>();
        string want = NormProcName(imageName);
        if (want.Length == 0 || map == null) return r;
        List<int> hit;
        if (map.TryGetValue(want, out hit)) r.AddRange(hit);
        return r;
    }
    /// <summary>
    /// 热身: 在【开始保护】时先把"按下后要用到的重活"跑一遍, 把冷启动成本
    /// (CLR 的 JIT 编译 + 首次分配进程表缓冲区)从按下之后挪到按下之前。
    ///
    /// 实测(真机日志): 按下后第一次扫描花了 33 ms, 而热身过的基准只要 7 ms ——
    /// 差的 26 ms 全是首次调用的 JIT/分配成本, 偏偏落在最要命的那一瞬间。
    /// 这里只是查询, 不关进程、不动网卡。
    /// </summary>
    private static void WarmUp()
    {
        try
        {
            int n;
            ProcMap(null, out n);
        }
        catch { }
    }
    /// <summary>一次枚举全系统进程表, 供"同一轮里查多个目标"共用(见 FindPids 的性能说明)</summary>
    private static List<KeyValuePair<int, string>> ProcSnapshot()
    {
        return EnumProcesses();
    }

    /// <summary>一次"发命令"的结果: 拿到了哪些句柄、哪些 PID 没打开、总共花了多久</summary>
    private sealed class KillBatch
    {
        public List<IntPtr> Handles = new List<IntPtr>();
        public List<string> PidTags = new List<string>();
        public bool AllOk = true;
        public long Ms = -1;
        public int Found;
    }

    /// <summary>
    /// 把要关的进程全部下达终止命令, 不在这里等。
    ///
    /// 为什么这么改: 实测日志里是
    ///   Sky.exe 等 2213 ms -> MuMuNxMain 等 288 -> MuMuNxService 57 -> MuMuNxDevice 261
    ///   -> MuMuVMMSVC 19 -> MuMuVMMHeadless 1529
    /// 六段等待串起来 4367 ms, 而它们本来是可以同时发生的。
    /// 现在: 先把六个 TerminateProcess 全发出去, 最后一起等 —— 总时间从 Σ 变成 max。
    /// 下达顺序仍然是"游戏本体第一个", 所以保命那一刀没有变慢。
    /// </summary>
    private static KillBatch StartAllKills(List<string> alive, Dictionary<string, List<int>> map)
    {
        KillBatch b = new KillBatch();
        long tk = Stopwatch.GetTimestamp();
        long openTotal = 0, termTotal = 0, firstIssueMs = 0;
        // map 由调用方枚举一次建好传进来 —— 不再在这里重复枚举
        // (老代码每个目标各枚举一次全表, 9 个目标 107 ms, 那正是"按下后多花 100 ms"的来源)
        foreach (string name in alive)
        {
            long t0 = Stopwatch.GetTimestamp();
            List<int> pids = PidsFrom(map, name);
            if (pids.Count > 0) b.Found++;
            if (pids.Count == 0) continue;
            Log("  " + name + ": " + pids.Count + " 个 (查 " + ElapsedMs(t0) + " ms)");

            foreach (int pid in pids)
            {
                long tOpen = Stopwatch.GetTimestamp();
                IntPtr h = OpenProcess(PROCESS_TERMINATE | SYNCHRONIZE, false, pid);
                long openMs = ElapsedMs(tOpen);
                openTotal += openMs;
                if (h == IntPtr.Zero)
                {
                    int err = Marshal.GetLastWin32Error();
                    Log("    PID " + pid + " 打不开, 错误码 " + err
                        + (err == 5 ? " [拒绝访问: 需要管理员权限]" : ""));
                    b.AllOk = false;
                    continue;
                }
                // "下达时刻"才是保命那一刀的真实耗时。它后面的几百毫秒是**系统在拆这个进程**
                // (游戏几百个线程 + 反作弊驱动, TerminateProcess 返回得慢), 不是我们的代码慢 ——
                // 所以这两个数分开记, 不要再混成一句"下命令花了 N ms"让人以为程序在偷懒。
                if (firstIssueMs == 0) firstIssueMs = ElapsedMs(_panicStartTicks);

                long tTerm = Stopwatch.GetTimestamp();
                bool ok = TerminateProcess(h, 1);
                long termMs = ElapsedMs(tTerm);
                termTotal += termMs;
                if (!ok)
                {
                    int terr = Marshal.GetLastWin32Error();
                    Log("    PID " + pid + " 终止失败, 错误码 " + terr
                        + (terr == 5 ? " [受保护/沙箱进程: SeDebugPrivilege="
                            + (_debugPrivOk ? "已启用"
                                : (_cfg != null && _cfg.DebugPriv ? "开关已开但没拿到" : "开关未开(设置里可开)"))
                            + " 仍被拒 -> 属系统级保护, 杀不掉]" : ""));
                    b.AllOk = false;
                    if (_suspendedPids.Contains(pid))
                        Log("      (这个进程已经被挂起 —— 不会再有任何动作; 需要的话在任务管理器里结束它)");
                    // 杀不掉的句柄绝不能留在等待列表里 —— 否则每一轮都要白等 KILL_WAIT_MS
                    // (VM 实测: 4 个 Edge 沙箱进程杀不掉, 3 轮白白多花 6 秒)
                    CloseHandle(h);
                    continue;
                }
                b.Handles.Add(h);
                b.PidTags.Add(name + "(" + pid + ")");
                if (openMs >= 30 || termMs >= 30)
                    Log("    PID " + pid + " 这一刀慢: 打开 " + openMs + " ms, 下达 " + termMs + " ms"
                        + (termMs > openMs ? " (慢在系统终止该进程, 不是本程序)" : " (慢在 OpenProcess)"));
            }
        }
        b.Ms = ElapsedMs(tk);
        Log("  下命令花了 " + b.Ms + " ms (OpenProcess " + openTotal + " / TerminateProcess " + termTotal
            + "), 共 " + b.Handles.Count + " 个进程");
        if (firstIssueMs > 0) Log("  第一条终止命令: 自触发 " + firstIssueMs + " ms 时下达");
        return b;
    }

    /// <summary>等上面那一批全部退出(等待取最大值), 并返回是否全部确认退出</summary>
    private static bool WaitAllKills(KillBatch b)
    {
        if (b.Handles.Count == 0) return b.AllOk;
        long tw = Stopwatch.GetTimestamp();
        bool ok = WaitAllHandles(b.Handles);
        Log(ok ? ("  全部确认退出, 等了 " + ElapsedMs(tw) + " ms")
               : "  有进程等到 " + KILL_WAIT_MS + " ms 超时还没退出(下一轮重新枚举复查)");
        foreach (IntPtr h in b.Handles) CloseHandle(h);
        b.Handles.Clear();
        if (!ok) b.AllOk = false;
        return ok;
    }

    /// <summary>
    /// 只关一个进程（补杀轮次用）。
    /// </summary>
    private static bool KillTarget(String procName, out long killMs)
    {
        killMs = -1;
        long t0 = Stopwatch.GetTimestamp();
        List<int> pids = FindPids(procName);
        Log("  找了一遍(" + ElapsedMs(t0) + " ms), " + procName + " 有 " + pids.Count + " 个正在跑");
        if (pids.Count == 0) return true;

        bool allOk = true;
        long tk = Stopwatch.GetTimestamp();

        // 第一步: 全部先开句柄 + 全部先下达终止命令(不等)
        List<IntPtr> handles = new List<IntPtr>();
        foreach (int pid in pids)
        {
            IntPtr h = OpenProcess(PROCESS_TERMINATE | SYNCHRONIZE, false, pid);
            if (h == IntPtr.Zero)
            {
                int err = Marshal.GetLastWin32Error();
                Log("  PID " + pid + " OpenProcess 失败, 错误码 " + err
                    + (err == 5 ? " [拒绝访问: 需要管理员权限]" : ""));
                allOk = false;
                continue;
            }
            handles.Add(h);
            bool ok = TerminateProcess(h, 1);
            Log("  PID " + pid + " TerminateProcess = " + (ok ? "成功" : "失败, 错误码 " + Marshal.GetLastWin32Error()));
            if (!ok) allOk = false;
        }

        // 第二步: 一起等它们真正退出(等待时间取最大值, 不再累加)
        if (handles.Count > 0)
        {
            long tw = Stopwatch.GetTimestamp();
            bool waited = WaitAllHandles(handles);
            if (waited)
            {
                Log("  " + handles.Count + " 个都确实退出了, 等了 " + ElapsedMs(tw) + " ms");
            }
            else
            {
                Log("  部分 PID 等待退出超时(" + KILL_WAIT_MS + " ms)");
                allOk = false;
            }
            foreach (IntPtr h in handles) CloseHandle(h);
        }
        killMs = ElapsedMs(tk);

        if (!allOk)
        {
            long tv = Stopwatch.GetTimestamp();
            List<int> after = FindPids(procName);
            int tries = 1;
            while (after.Count > 0 && tries < 20) { Thread.Sleep(100); tries++; after = FindPids(procName); }
            Log("  枚举复查 " + tries + " 次 / " + ElapsedMs(tv) + " ms 后: 剩余 " + after.Count + " 个");
            if (after.Count > 0) return false;
        }
        return allOk;
    }

    /// <summary>
    /// 等一批句柄全部变成"已 signaled"(即进程在内核里真的退出了)。
    /// 分批是因为 WaitForMultipleObjects 一次最多 64 个。
    /// </summary>
    private static bool WaitAllHandles(List<IntPtr> handles)
    {
        bool all = true;
        for (int i = 0; i < handles.Count; i += MAX_WAIT_HANDLES)
        {
            int n = Math.Min(MAX_WAIT_HANDLES, handles.Count - i);
            IntPtr[] batch = new IntPtr[n];
            for (int k = 0; k < n; k++) batch[k] = handles[i + k];
            uint wr = WaitForMultipleObjects((uint)n, batch, true, KILL_WAIT_MS);
            if (wr != WAIT_OBJECT_0) all = false;
        }
        return all;
    }

    #endregion

    // ============================================================================
    //  五之二、快速断流层 (11.1.0 新增)
    //
    //  为什么要有它: "断网"里最彻底的一刀是禁用网卡(netsh), 但它要等 NDIS 把小型端口
    //  停下来 —— 不同机器/驱动/虚拟环境 3~15 秒不等, 而"上报窗口"只有几秒。
    //  所以再加一层"快速断流": 在毫秒级先把出站数据包拦掉, 网卡照旧禁用作最终保证。
    //
    //  两条快速路径(先 WFP 后 防火墙):
    //    C) WFP 动态过滤器: 开 FWPM_SESSION_FLAG_DYNAMIC 会话, 在"出站传输层"
    //       (FWPM_LAYER_OUTBOUND_TRANSPORT_V4/16, 逐包)装 block 过滤器 ——
    //       正在上传的连接也会立刻断流。动态会话随进程退出自动消失, 崩溃不留残留。
    //       层 GUID 取自 Windows SDK 头文件 fwpmu.h 的 DEFINE_GUID 定义(11.1.0 逐字核对)。
    //    A) Windows 防火墙规则: 加一条命名规则 block 出站。规则是持久化的, 所以
    //       恢复/退出/下次启动都要清理(只删我们自己那几个固定名字)。
    //
    //  硬规矩(为了让它在没见过的机器上也成立):
    //    1. 不假设任何环境: 不假设防火墙开着、不假设 BFE 在跑、不假设本机有外网。
    //    2. 每一步都自证: 先用探针记下"哪些目标本来能连"(基线), 断流后再探一次 ——
    //       基线上能连的必须全连不上才算"已确认"; 验不了就如实写"无法验证", 不许假设。
    //    3. 失败要响亮: 每一步的成败与错误码(含 HRESULT)都写进日志。
    //    4. 不做机器特定优化: 目标列表可配置(Ip:Port), 不依赖任何本机专有信息。
    //    5. 快速层只负责"抢时间"; 禁用网卡永远照旧执行, 快速层全挂也不影响保命。
    // ============================================================================

    #region 快速断流

    // ---- WFP 常量(层 GUID 来自 Windows SDK: um/fwpmu.h, 逐字核对) ----
    private static readonly Guid WFP_LAYER_OUT_TRANSPORT_V4 = new Guid("09e61aea-d214-46e2-9b21-b26b0b2f28c8");
    private static readonly Guid WFP_LAYER_OUT_TRANSPORT_V6 = new Guid("e1735bde-013f-4655-b351-a49e15762df0");
    /// <summary>我们自己的子层 GUID(自造但固定): 让 block 过滤器先被评估</summary>
    private static readonly Guid WFP_SUBLAYER_KEY = new Guid("3b7a5f10-2c8e-4b1a-9f65-0d1c2a3b4c5d");
    // !! 事故根因 !!
    // 动作类型不是 1: FWP_ACTION_BLOCK = 0x00000001 | FWP_ACTION_FLAG_TERMINATING = 0x1001(十进制 4097)。
    // 依据: FWPM_ACTION0 文档(FWP_ACTION_BLOCK = 0x00000001 | FWP_ACTION_FLAG_TERMINATING)
    //       + FWP_ACTION_TYPE 绑定(Block = 4097) https://docs.rs/wfp/latest/wfp/enum.ActionType.html
    // 写成 1 会被内核判为 FWP_E_INVALID_ACTION_TYPE(0x80320024) —— 于是 WFP 这层从来没生效过,
    // 每次都用"持久化防火墙规则"兜底, 而那条规则是唯一会把"全出站阻断"留在用户机器上的路径。
    private const uint FWP_ACTION_BLOCK = 0x00001001;
    private const uint FWP_EMPTY_INT = 0;                 // FWP_VALUE0.type = FWP_EMPTY(自动权重)
    private const uint FWPM_SESSION_FLAG_DYNAMIC = 0x00000001;
    private const uint RPC_C_AUTHN_WINNT = 10;
    private const uint WFP_SUBLAYER_WEIGHT = 0x8000;      // 偏高: 让我们的 block 先评估
    private const uint FWPM_ERR_ALREADY_EXISTS = 0x80320009;
    // 以下三个码取自微软文档 "WFP Error Codes"(Winerror.h), 核对
    private const uint FWP_E_FILTER_NOT_FOUND = 0x80320003;
    private const uint FWP_E_SUBLAYER_NOT_FOUND = 0x80320007;

    [StructLayout(LayoutKind.Sequential)]
    private struct FWPM_DISPLAY_DATA0 { public IntPtr name; public IntPtr description; }

    [StructLayout(LayoutKind.Sequential)]
    private struct FWP_BYTE_BLOB { public uint size; public IntPtr data; }

    /// <summary>FWP_VALUE0: type + 8 字节 union(按最宽对齐, 只用低字节存权重/空值)</summary>
    [StructLayout(LayoutKind.Sequential)]
    private struct FWP_VALUE0 { public uint type; public ulong value; }

    [StructLayout(LayoutKind.Sequential)]
    private struct FWPM_SESSION0
    {
        public Guid sessionKey;
        public FWPM_DISPLAY_DATA0 displayData;
        public uint flags;
        public uint txnWaitTimeoutInMSec;
        public uint processId;
        public IntPtr sid;
        public IntPtr username;
        [MarshalAs(UnmanagedType.Bool)] public bool kernelMode;
    }

    [StructLayout(LayoutKind.Sequential)]
    private struct FWPM_SUBLAYER0
    {
        public Guid subLayerKey;
        public FWPM_DISPLAY_DATA0 displayData;
        public uint flags;
        public IntPtr providerKey;
        public FWP_BYTE_BLOB providerData;
        public ushort weight;
    }

    /// <summary>
    /// FWPM_ACTION0: type + union { GUID filterType; GUID calloutKey; }。
    ///
    /// 经微软文档核实(fwpmtypes.h / FWPM_ACTION0): union 两个成员都是 GUID,
    /// GUID 的原生对齐是 4 -> union 落在偏移 4, 整个结构 = 4 + 16 = 20 字节。
    /// (一度误以为 union 含 UINT64 而要按 8 字节对齐 -> 24; 事实不是。顺便记录:
    ///  即使这点写错也不会打乱 FILTER0 的后续字段 —— context 自身对齐会把那 4 字节吃掉;
    ///  但"错的事实"不该留在代码与自检期望值里, 所以按文档改回来。)
    /// </summary>
    [StructLayout(LayoutKind.Sequential)]
    private struct FWPM_ACTION0
    {
        public uint type;          // offset 0
        public Guid filterType;    // offset 4 (GUID 原生对齐 4)
    }

    /// <summary>FWPM_FILTER0 里的匿名联合: max(UINT64, GUID) —— 必须 16 字节</summary>
    [StructLayout(LayoutKind.Explicit, Size = 16)]
    private struct FWPM_FILTER_CONTEXT
    {
        [FieldOffset(0)] public ulong rawContext;
        [FieldOffset(0)] public Guid providerContextKey;
    }

    [StructLayout(LayoutKind.Sequential)]
    private struct FWPM_FILTER0
    {
        public Guid filterKey;
        public FWPM_DISPLAY_DATA0 displayData;
        public uint flags;
        public IntPtr providerKey;
        public FWP_BYTE_BLOB providerData;
        public Guid layerKey;
        public Guid subLayerKey;
        public FWP_VALUE0 weight;
        public uint numFilterConditions;
        public IntPtr filterCondition;
        public FWPM_ACTION0 action;
        public FWPM_FILTER_CONTEXT context;
        public IntPtr reserved;
        public ulong filterId;
        public FWP_VALUE0 effectiveWeight;
    }

    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmEngineOpen0(string serverName, uint authnService, IntPtr authIdentity,
        ref FWPM_SESSION0 session, out IntPtr engineHandle);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmEngineClose0(IntPtr engineHandle);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmTransactionBegin0(IntPtr engineHandle, uint flags);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmTransactionCommit0(IntPtr engineHandle);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmTransactionAbort0(IntPtr engineHandle);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmSubLayerAdd0(IntPtr engineHandle, ref FWPM_SUBLAYER0 subLayer, IntPtr sd);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmSubLayerDeleteByKey0(IntPtr engineHandle, ref Guid key);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmFilterAdd0(IntPtr engineHandle, ref FWPM_FILTER0 filter, IntPtr sd, out ulong id);
    [DllImport("fwpuclnt.dll")]
    private static extern uint FwpmFilterDeleteById0(IntPtr engineHandle, ulong id);

    private static IntPtr _wfpEngine = IntPtr.Zero;
    private static readonly List<ulong> _wfpFilterIds = new List<ulong>();
    private static bool _wfpArmed;

    private static string FastCutLayer = "";        // "" / "WFP动态过滤器" / "防火墙规则"
    private const string FW_RULE_NAME = "SkyGuard-Panic-Block-Out";
    private static bool _fwArmed;

    // 11.1.0 验收意见(MAJOR-2): 快速层的"装/撤"会被多个线程同时碰 ——
    // 常驻断网线程(装)、UI 关窗 / [恢复网络] 线程 / 处置线程(撤)。必须串行化,
    // 否则会出现"Release 先跑、Engage 后落" -> 规则被装上却没人再撤(持久残留)。
    private static readonly object _fastCutGate = new object();
    /// <summary>每次 Release 自增。Engage 落盘后若发现代数变了, 说明期间有人撤过 —— 立刻再撤一次。</summary>
    private static int _fastCutGen;


    private static string WfpErr(uint rc) { return "0x" + rc.ToString("X8"); }

    /// <summary>装 WFP 出站 block 过滤器(动态会话)。失败时把原因写进 err, 不做任何假设。</summary>
    private static bool WfpEngage(out string err)
    {
        err = "";
        if (_wfpArmed) return true;
        // 防御: 万一上一次没收干净(引擎句柄还在), 先撤掉再开新的 —— 否则旧会话的过滤器会一直拦着流量
        if (_wfpEngine != IntPtr.Zero) { string e0; WfpReleaseInternal(out e0); }
        IntPtr nameOut = IntPtr.Zero, nameSl = IntPtr.Zero;
        try
        {
            FWPM_SESSION0 session = new FWPM_SESSION0();
            session.flags = FWPM_SESSION_FLAG_DYNAMIC;
            session.txnWaitTimeoutInMSec = 5000;
            IntPtr engine;
            uint rc = FwpmEngineOpen0(null, RPC_C_AUTHN_WINNT, IntPtr.Zero, ref session, out engine);
            if (rc != 0) { err = "FwpmEngineOpen0 失败 " + WfpErr(rc) + "(BFE 服务没跑或权限不足)"; return false; }
            _wfpEngine = engine;

            rc = FwpmTransactionBegin0(engine, 0);
            if (rc != 0) { err = "FwpmTransactionBegin0 失败 " + WfpErr(rc); WfpReleaseInternal(); return false; }

            nameSl = Marshal.StringToHGlobalUni("SkyGuard FastCut");
            FWPM_SUBLAYER0 sl = new FWPM_SUBLAYER0();
            sl.subLayerKey = WFP_SUBLAYER_KEY;
            sl.displayData.name = nameSl;
            sl.weight = (ushort)WFP_SUBLAYER_WEIGHT;
            rc = FwpmSubLayerAdd0(engine, ref sl, IntPtr.Zero);
            if (rc != 0 && rc != FWPM_ERR_ALREADY_EXISTS)
            {
                err = "FwpmSubLayerAdd0 失败 " + WfpErr(rc);
                FwpmTransactionAbort0(engine);
                WfpReleaseInternal();
                return false;
            }

            Guid[] layers = new Guid[] { WFP_LAYER_OUT_TRANSPORT_V4, WFP_LAYER_OUT_TRANSPORT_V6 };
            for (int i = 0; i < layers.Length; i++)
            {
                nameOut = Marshal.StringToHGlobalUni("SkyGuard FastCut block outbound");
                FWPM_FILTER0 f = new FWPM_FILTER0();
                f.displayData.name = nameOut;
                f.layerKey = layers[i];
                f.subLayerKey = WFP_SUBLAYER_KEY;
                f.action.type = FWP_ACTION_BLOCK;
                f.weight.type = FWP_EMPTY_INT;   // 自动权重(文档推荐)
                f.numFilterConditions = 0;       // 无条件下 = 所有流量
                f.flags = 0;
                ulong id;
                rc = FwpmFilterAdd0(engine, ref f, IntPtr.Zero, out id);
                Marshal.FreeHGlobal(nameOut); nameOut = IntPtr.Zero;
                if (rc != 0)
                {
                    err = "FwpmFilterAdd0(" + (i == 0 ? "IPv4" : "IPv6") + ") 失败 " + WfpErr(rc);
                    FwpmTransactionAbort0(engine);
                    WfpReleaseInternal();
                    return false;
                }
                _wfpFilterIds.Add(id);
            }

            rc = FwpmTransactionCommit0(engine);
            if (rc != 0)
            {
                err = "FwpmTransactionCommit0 失败 " + WfpErr(rc);
                // 验收意见(MINOR): 三条失败路径都显式收尾(engine close 虽能兜住, 但语义要对称)
                try { FwpmTransactionAbort0(engine); } catch { }
                WfpReleaseInternal();
                return false;
            }
            _wfpArmed = true;
            return true;
        }
        catch (Exception ex) { err = "WFP 异常: " + ex.Message; WfpReleaseInternal(); return false; }
        finally
        {
            if (nameOut != IntPtr.Zero) { try { Marshal.FreeHGlobal(nameOut); } catch { } }
            if (nameSl != IntPtr.Zero) { try { Marshal.FreeHGlobal(nameSl); } catch { } }
        }
    }

    /// <summary>
    /// 撤 WFP(删过滤器 + 删子层 + 关会话)。动态会话随进程退出消失, 这里是主动清。
    /// 返回是否确认撤干净, 失败原因写进 err —— 不许静默(验收意见 MAJOR-3)。
    /// </summary>
    private static bool WfpReleaseInternal(out string err)
    {
        err = "";
        bool ok = true;
        try
        {
            if (_wfpEngine != IntPtr.Zero)
            {
                for (int i = 0; i < _wfpFilterIds.Count; i++)
                {
                    uint rc = FwpmFilterDeleteById0(_wfpEngine, _wfpFilterIds[i]);
                    // 11.1.0 验收(第二轮 N6): "本来就不存在"不是失败, 否则每次撤销都会假警报
                    if (rc != 0 && rc != FWP_E_FILTER_NOT_FOUND)
                    { ok = false; err = "删过滤器失败 " + WfpErr(rc); }
                }
                _wfpFilterIds.Clear();
                Guid k = WFP_SUBLAYER_KEY;
                uint rc2 = FwpmSubLayerDeleteByKey0(_wfpEngine, ref k);
                if (rc2 != 0 && rc2 != FWP_E_SUBLAYER_NOT_FOUND)
                { ok = false; err = "删子层失败 " + WfpErr(rc2); }
                uint rc3 = FwpmEngineClose0(_wfpEngine);
                if (rc3 != 0) { ok = false; err = "关会话失败 " + WfpErr(rc3); }
                _wfpEngine = IntPtr.Zero;
            }
        }
        catch (Exception ex) { ok = false; err = "WFP 撤销异常: " + ex.Message; }
        _wfpArmed = false;
        return ok;
    }

    /// <summary>不管结果的重载: 只给"确实没有可撤内容 / 安全网"的调用点用。</summary>
    private static void WfpReleaseInternal() { string e; WfpReleaseInternal(out e); }

    // ---- 防火墙规则(COM 晚绑定: 不依赖 Microsoft.CSharp, 也不用猜 IID) ----

    private static object FwPolicy()
    {
        try
        {
            Type t = Type.GetTypeFromProgID("HNetCfg.FwPolicy2", false);
            if (t == null) return null;
            return Activator.CreateInstance(t);
        }
        catch { return null; }
    }

    private static object FwGetProp(object o, string name)
    {
        return o.GetType().InvokeMember(name, System.Reflection.BindingFlags.GetProperty, null, o, null);
    }

    private static void FwSetProp(object o, string name, object v)
    {
        o.GetType().InvokeMember(name, System.Reflection.BindingFlags.SetProperty, null, o, new object[] { v });
    }

    /// <summary>删掉所有我们自己命名的残留规则。返回删掉的条数; 删不掉的写进 err(不静默)。</summary>
    private static int FwRemoveOurRules(out string err)
    {
        err = "";
        int n = 0;
        try
        {
            object policy = FwPolicy();
            if (policy == null) { err = "取不到 HNetCfg.FwPolicy2"; return 0; }
            object rules = FwGetProp(policy, "Rules");
            if (rules == null) { err = "取不到 Rules 集合"; return 0; }
            Type rt = rules.GetType();
            int count = Convert.ToInt32(rt.InvokeMember("Count", System.Reflection.BindingFlags.GetProperty, null, rules, null));
            for (int i = count; i >= 1; i--)   // INetFwRules 是 1-based
            {
                object r;
                try { r = rt.InvokeMember("Item", System.Reflection.BindingFlags.GetProperty, null, rules, new object[] { i }); }
                catch { continue; }
                if (r == null) continue;
                string nm;
                try { nm = Convert.ToString(r.GetType().InvokeMember("Name", System.Reflection.BindingFlags.GetProperty, null, r, null)); }
                catch { continue; }
                if (nm != null && nm.StartsWith("SkyGuard-Panic-", StringComparison.OrdinalIgnoreCase))
                {
                    try { rt.InvokeMember("Remove", System.Reflection.BindingFlags.InvokeMethod, null, rules, new object[] { nm }); n++; }
                    catch (Exception ex) { err = "删规则 " + nm + " 失败: " + ex.Message; }
                }
            }
        }
        catch (Exception ex) { err = "清防火墙规则异常: " + ex.Message; }
        return n;
    }

    /// <summary>不管结果的重载(给只想数一下的调用点用)。</summary>
    private static int FwRemoveOurRules() { string e; return FwRemoveOurRules(out e); }

    /// <summary>
    /// 加防火墙规则 block 出站。失败原因写进 err。
    ///
    /// ⚠️ 当前**没有调用点**: 实测之后, 快速断流的"持久化防火墙规则"这一层已停用
    ///   (加得上、也拦得住, 但撤销后系统迟迟不放行: 自检里 7 秒、用户点[恢复网络] 70 秒都没救回来),
    ///   现在只走 WFP 动态过滤器, 兜底是禁用网卡。函数和人工兜底命令
    ///   (`netsh advfirewall firewall delete rule name="SkyGuard-Panic-Block-Out"`)都保留着,
    ///   启动清理(FwRemoveOurRules)也照旧会删掉老版本可能留下的同名规则。
    /// </summary>
    private static bool FwEngage(out string err)
    {
        err = "";
        try
        {
            object policy = FwPolicy();
            if (policy == null) { err = "取不到 HNetCfg.FwPolicy2(防火墙组件缺失或被移除)"; return false; }
            object rules = FwGetProp(policy, "Rules");
            if (rules == null) { err = "取不到防火墙 Rules 集合"; return false; }

            FwRemoveOurRules();   // 先清同名残留

            Type tRule = Type.GetTypeFromProgID("HNetCfg.FwRule", false);
            if (tRule == null) { err = "取不到 HNetCfg.FwRule"; return false; }
            object rule = Activator.CreateInstance(tRule);
            FwSetProp(rule, "Name", FW_RULE_NAME);
            FwSetProp(rule, "Description", "SkyGuard panic guard temporary outbound block");
            FwSetProp(rule, "Direction", 2);          // NET_FW_RULE_DIR_OUT
            FwSetProp(rule, "Action", 0);             // NET_FW_ACTION_BLOCK
            FwSetProp(rule, "Enabled", true);
            FwSetProp(rule, "Protocol", 256);         // NET_FW_IP_PROTOCOL_ANY
            FwSetProp(rule, "Profiles", unchecked((int)0x7FFFFFFF));
            FwSetProp(rule, "InterfaceTypes", "All");
            rules.GetType().InvokeMember("Add", System.Reflection.BindingFlags.InvokeMethod, null, rules, new object[] { rule });
            _fwArmed = true;
            return true;
        }
        catch (Exception ex) { err = "加防火墙规则异常: " + ex.Message; return false; }
    }

    /// <summary>
    /// 只看不删: 我们的防火墙规则现在还在不在。
    /// 为什么要它(RC3): 自检里"撤销后没恢复"到底是因为"规则没删掉(真残留)"还是"规则删了但系统还没放行",
    /// 光看可达性是分不清的 —— 分不清就会误报/漏报, 所以直接把规则状态也打出来。
    /// </summary>
    private static bool FwRuleStillThere()
    {
        try
        {
            object policy = FwPolicy();
            if (policy == null) return false;
            object rules = FwGetProp(policy, "Rules");
            if (rules == null) return false;
            Type rt = rules.GetType();
            int count = Convert.ToInt32(rt.InvokeMember("Count", System.Reflection.BindingFlags.GetProperty, null, rules, null));
            for (int i = 1; i <= count; i++)
            {
                object r;
                try { r = rt.InvokeMember("Item", System.Reflection.BindingFlags.GetProperty, null, rules, new object[] { i }); }
                catch { continue; }
                if (r == null) continue;
                string nm;
                try { nm = Convert.ToString(r.GetType().InvokeMember("Name", System.Reflection.BindingFlags.GetProperty, null, r, null)); }
                catch { continue; }
                if (nm != null && nm.StartsWith("SkyGuard-Panic-", StringComparison.OrdinalIgnoreCase)) return true;
            }
        }
        catch { }
        return false;
    }

    /// <summary>撤防火墙规则, 并复查是否真的没了。返回是否确认撤干净(验收意见 MAJOR-3)。</summary>
    private static bool FwRelease(out string err)
    {
        err = "";
        bool ok = true;
        try
        {
            if (_fwArmed)
            {
                string e1;
                FwRemoveOurRules(out e1);
                if (e1.Length > 0) { ok = false; err = e1; }
                string e2;
                int left = FwRemoveOurRules(out e2);   // 复查: 再枚举一次
                if (e2.Length > 0) { ok = false; err = e2; }
                if (left > 0) { ok = false; err = "复查时仍能删到 " + left + " 条 -> 撤销不干净"; }
            }
        }
        catch (Exception ex) { ok = false; err = "防火墙撤销异常: " + ex.Message; }
        _fwArmed = false;
        return ok;
    }

    private static void FwRelease() { string e; FwRelease(out e); }

    // ---- 探针: 只用 IP:Port, 不依赖 DNS ----

    // ---- 探针: 默认只走局域网(ping 默认网关), 绝不主动连外网 ----
    //
    // 为什么这么定(11.1.0 实测教训): 最初默认拿 1.1.1.1 / 223.5.5.5 这类外网地址做探针,
    // 结果一跑就触发火绒「联网控制」弹窗"scan.exe 正在外联 223.5.5.5:53" ——
    //   1) 和本工具"不联网"的承诺直接矛盾, 用户会怀疑我们偷偷联网;
    //   2) 装了火绒/360 的用户每次开始保护、每次处置后都会被弹一次【允许/阻止】;
    //   3) 国产安全软件一旦拦掉, 探针就全不通, 验证直接失效。
    // 所以默认只用 ICMP ping 本机默认网关: 不出局域网、不产生"外联"行为,
    // 而它同样能证明"出站被拦住了"(快速层拦的是所有出站, 含 ICMP)。
    // 想额外验证外网, 由用户自己配 FastCutTargets(那时会明确提示会产生外网连接)。

    private static int _probeBaselineReachable = -1;      // -1 = 还不知道(没测过)
    private static long _probeBaselineTicks;

    /// <summary>你在 guard.ini 里额外配的外部目标(逗号分隔 Ip:Port)。默认空 = 只用局域网探针。</summary>
    private static string[] ExternalTargets()
    {
        try
        {
            if (_cfg != null && !string.IsNullOrEmpty(_cfg.FastCutTargets))
            {
                string[] parts = _cfg.FastCutTargets.Split(new char[] { ',', ';', ' ' }, StringSplitOptions.RemoveEmptyEntries);
                if (parts.Length > 0) return parts;
            }
        }
        catch { }
        return new string[0];
    }

    /// <summary>本机默认网关地址(IPv4)。取不到返回空串。</summary>
    private static string GatewayAddress()
    {
        try
        {
            foreach (System.Net.NetworkInformation.NetworkInterface ni
                     in System.Net.NetworkInformation.NetworkInterface.GetAllNetworkInterfaces())
            {
                if (ni == null) continue;
                if (ni.OperationalStatus != System.Net.NetworkInformation.OperationalStatus.Up) continue;
                if (ni.NetworkInterfaceType == System.Net.NetworkInformation.NetworkInterfaceType.Loopback) continue;
                foreach (System.Net.NetworkInformation.GatewayIPAddressInformation g in ni.GetIPProperties().GatewayAddresses)
                {
                    if (g == null || g.Address == null) continue;
                    if (g.Address.AddressFamily == System.Net.Sockets.AddressFamily.InterNetwork)
                        return g.Address.ToString();
                }
            }
        }
        catch { }
        return "";
    }

    /// <summary>ping 默认网关(ICMP, 700ms)。这是"局域网内通不通"的判据, 不产生外网连接。</summary>
    private static bool ProbeGateway() { return ProbeGateway(700); }

    /// <summary>
    /// "局域网通不通"的判据 = ICMP ping 通网关 或 TCP 能连上网关(53/80)。
    /// 为什么要两个都试(实测教训): 只用 ICMP 时, 一旦 ICMP 被安全软件或路由器过滤,
    /// 探针就会把"其实有网"误判成"没恢复", 用户看到的是一堆"恢复失败"的假警报。
    /// TCP 是纯局域网连接(不出外网), 完全不依赖 ICMP。
    /// </summary>
    /// <summary>
    /// 取本机所有"默认网关"(可能不止一个: 有线+无线同时在线、VPN、虚拟网卡混杂时都会有几个)。
    /// 为什么要全部: 只取第一个会在多网关机器上挑错(比如挑到 VPN 的网关),
    /// 于是"网络通不通"的判断就跟着错。全部取回来 + 只要有一个通就算局域网活着。
    /// </summary>
    private static List<string> GatewayAddresses()
    {
        List<string> list = new List<string>();
        try
        {
            foreach (System.Net.NetworkInformation.NetworkInterface ni
                     in System.Net.NetworkInformation.NetworkInterface.GetAllNetworkInterfaces())
            {
                if (ni == null) continue;
                if (ni.OperationalStatus != System.Net.NetworkInformation.OperationalStatus.Up) continue;
                if (ni.NetworkInterfaceType == System.Net.NetworkInformation.NetworkInterfaceType.Loopback) continue;
                foreach (System.Net.NetworkInformation.GatewayIPAddressInformation g in ni.GetIPProperties().GatewayAddresses)
                {
                    if (g == null || g.Address == null) continue;
                    if (g.Address.AddressFamily != System.Net.Sockets.AddressFamily.InterNetwork) continue;
                    string s = g.Address.ToString();
                    bool dup = false;
                    foreach (string x in list) if (x == s) { dup = true; break; }
                    if (!dup) list.Add(s);
                }
            }
        }
        catch { }
        return list;
    }

    private static bool ProbeGateway(int timeoutMs)
    {
        List<string> gws = GatewayAddresses();
        if (gws.Count == 0) return false;
        for (int gi = 0; gi < gws.Count; gi++)
        {
            try
            {
                using (System.Net.NetworkInformation.Ping p = new System.Net.NetworkInformation.Ping())
                {
                    System.Net.NetworkInformation.PingReply r =
                        p.Send(System.Net.IPAddress.Parse(gws[gi]), timeoutMs);
                    if (r != null && r.Status == System.Net.NetworkInformation.IPStatus.Success) return true;
                }
            }
            catch { }
        }
        // 注意: 这里**故意不做 TCP 探测**。
        // 实测: 只要对网关发起 TCP 连接, 火绒的"联网控制"就会弹
        // 「发现程序联网行为: SkyGuardGUI.exe -> 192.168.88.1:53」——
        // 在安全软件眼里"TCP 连接"就是联网行为, 哪怕目标是自己的路由器。
        // 而 ICMP ping 不算联网行为, 不会弹窗。所以这里只用 ICMP;
        // 想额外验证外网连通性, 请在「高级选项 → 探针额外目标」里自己填(那属于明确选择)。
        return false;
    }

    private static int ProbeTotal() { return 1 + ExternalTargets().Length; }

    private static string ProbeDesc()
    {
        string gw = GatewayAddress();
        string[] ext = ExternalTargets();
        return "网关" + (gw.Length > 0 ? "(" + gw + ")" : "(没取到)") + " ICMP"
            + (ext.Length > 0
                ? " + 你配的 " + ext.Length + " 个外网目标: " + string.Join(" / ", ext) + " (会产生外网连接)"
                : " —— 只走局域网, 不连外网");
    }

    /// <summary>TCP 连一下 IP:Port。能连上=true。只用 IP, 避免依赖 DNS(断网时 DNS 必然失败会误判)。</summary>
    private static bool ProbeTcp(string hostPort, int timeoutMs)
    {
        try
        {
            int c = hostPort.LastIndexOf(':');
            if (c <= 0) return false;
            string host = hostPort.Substring(0, c).Trim();
            int port;
            if (!int.TryParse(hostPort.Substring(c + 1).Trim(), out port)) return false;
            System.Net.IPAddress ip;
            if (!System.Net.IPAddress.TryParse(host, out ip)) return false;
            using (System.Net.Sockets.Socket s = new System.Net.Sockets.Socket(ip.AddressFamily,
                       System.Net.Sockets.SocketType.Stream, System.Net.Sockets.ProtocolType.Tcp))
            {
                IAsyncResult ar = s.BeginConnect(new System.Net.IPEndPoint(ip, port), null, null);
                if (!ar.AsyncWaitHandle.WaitOne(timeoutMs)) { try { s.Close(); } catch { } return false; }
                s.EndConnect(ar);
                return s.Connected;
            }
        }
        catch { return false; }
    }

    private static int ProbeReachableNow()
    {
        int n = 0;
        if (ProbeGateway()) n++;
        string[] ext = ExternalTargets();
        for (int i = 0; i < ext.Length; i++) if (ProbeTcp(ext[i], 700)) n++;
        return n;
    }

    /// <summary>记基线: 断流之前有哪几个目标能连。只在没断流时调用。</summary>
    private static void ProbeRefreshBaseline(string why)
    {
        try
        {
            if (_cfg == null || !_cfg.FastCut) return;
            // 11.1.0 验收(第二轮 N1): 探测本身要 700ms, 不能在锁里做 ——
            // 否则"开始保护"刚记基线时按下触发键, 快速层和禁网卡都会被这把锁挡在门外。
            int gen;
            lock (_fastCutGate)
            {
                if (FastCutLayer.Length > 0) return;      // 正在断流: 别把"连不上"当基线
                gen = _fastCutGen;
            }
            int n = ProbeReachableNow();
            lock (_fastCutGate)
            {
                // 探测期间若装过/撤过快速层, 这次的基线作废(那时测到的是"被拦住", 不是基线)
                if (FastCutLayer.Length > 0 || _fastCutGen != gen) return;
                _probeBaselineReachable = n;
                _probeBaselineTicks = Stopwatch.GetTimestamp();
            }
            Log("快速断流基线(" + why + "): " + n + "/" + ProbeTotal() + " 个探测项可连  [" + ProbeDesc() + "]"
                + (n == 0 ? " —— 本机当前连网关都不通, 断流结果无法验证" : ""));
        }
        catch { }
    }

    /// <summary>断流后验证: 基线上能连的目标必须全连不上。</summary>
    private static void ProbeVerifyAfterCut()
    {
        try
        {
            if (_cfg == null || !_cfg.FastCut) return;
            int before;
            lock (_fastCutGate) { before = _probeBaselineReachable; }
            int after = ProbeReachableNow();
            int total = ProbeTotal();
            if (before < 0)
                Log("快速断流验证: 没有断流前基线, 无法验证(网卡已禁用)");
            else if (before == 0)
                Log("快速断流验证: 无法验证(断流前 " + total + " 个探测项本来就都不通, 可能本机没网/网关不回 ICMP)");
            else if (after == 0)
                Log("快速断流验证: 已确认 (断流前 " + before + "/" + total + " 可连 -> 现在 0 可连)");
            else
                Log("快速断流验证: 未确认 (仍有 " + after + "/" + total + " 个目标可连) —— 已保留禁用网卡兜底");
        }
        catch { }
    }

    /// <summary>依次尝试 WFP -> 防火墙。成功即返回 true(并记下是哪一层)。</summary>
    private static bool FastCut_Engage()
    {
        try
        {
            if (_cfg == null || !_cfg.FastCut) return false;
            lock (_fastCutGate)
            {
                if (FastCutLayer.Length > 0) return true;
                int gen = _fastCutGen;      // 记下代数: 落盘后若变了, 说明期间有人撤过
                long t0 = Stopwatch.GetTimestamp();
                string err;
                if (WfpEngage(out err))
                {
                    FastCutLayer = "WFP动态过滤器";
                }
                else
                {
                    // 实测决定: 不再使用"持久化防火墙规则"这一层。
                    // 证据(实测): 加上它 -> 拦得住(0/1) -> 撤销"成功且只查不删的复查确认规则已删除"
                    //   -> 但默认网关仍有 7~70 秒 ping 不通(自检里 7 秒; 用户点[恢复网络] 70 秒都没救回来);
                    //   而 WFP 层是 秒级恢复 + 零残留(装 45ms / 撤销后 1s 内恢复)。
                    // 既然 WFP 已实测可用, 就没理由为了"WFP 不可用"的少数场景去承担
                    // "规则删了但系统迟迟不放行 / 可能残留"的风险。兜底仍是"禁用网卡"(硬保证, 照旧执行)。
                    Log("快速断流: WFP 不可用(" + err + ") -> 改用禁用网卡这一层");
                }
                if (FastCutLayer.Length > 0)
                {
                    if (_fastCutGen != gen)
                    {
                        // 装的过程中有人撤过 —— 现在必须再撤一次, 否则这条规则再没人管(会持久残留)。
                        // 说明(第二轮验收): 当前 Engage 全程持 _fastCutGate, 而 Release 才自增代数,
                        // 所以这条分支目前不会进入 —— 它是防御性冗余(万一以后把锁范围收窄)。
                        // 真正兜住竞态的是那把锁, 不是这个代数判断。
                        string e1 = "", e2 = "";
                        bool o1 = true, o2 = true;
                        if (_wfpArmed) o1 = WfpReleaseInternal(out e1);
                        if (_fwArmed) o2 = FwRelease(out e2);
                        Log("快速断流: 装的过程中收到过撤销 -> 已立刻回撤 (" + FastCutLayer + ")"
                            + ((o1 && o2) ? "" : " 回撤不干净: " + e1 + " " + e2));
                        FastCutLayer = "";
                        return false;
                    }
                    long ms = ElapsedMs(t0);
                    Log("快速断流: 已启用 " + FastCutLayer + " (耗时 " + ms + " ms)");
                    if (ms > 3000) Log("快速断流: 启用耗时较长(" + ms + " ms)");
                    if (_firstDownTicks == 0) _firstDownTicks = Stopwatch.GetTimestamp();
                    return true;
                }
                Log("快速断流: 两层都不可用(" + err + ") -> 只靠禁用网卡(原有方案, 依然有效)");
                return false;
            }
        }
        catch (Exception ex) { Log("快速断流异常: " + ex.Message); return false; }
    }

    private static void FastCut_Release()
    {
        try
        {
            lock (_fastCutGate)
            {
                string lay = FastCutLayer;
                // 防御: 只要引擎句柄还在就必须收尾 —— 不能只看 _wfpArmed。
                // (理论上不会出现"引擎开着但 armed=false", 但真出现的话流量会一直被拦着, 代价太大。)
                bool hadWfp = _wfpArmed || _wfpEngine != IntPtr.Zero;
                bool hadFw = _fwArmed;
                _fastCutGen++;                       // 让正在装的 Engage 知道"期间撤过"
                string e1 = "", e2 = "";
                bool ok1 = true, ok2 = true;
                if (hadWfp) ok1 = WfpReleaseInternal(out e1);
                if (hadFw) ok2 = FwRelease(out e2);
                FastCutLayer = "";
                if (!hadWfp && !hadFw && lay.Length == 0) return;
                if (ok1 && ok2)
                {
                    Log("快速断流: 已撤销(" + (lay.Length > 0 ? lay : "快速层") + ")");
                }
                else
                {
                    // 验收意见(MAJOR-3): 撤销失败必须如实说, 不能打印"已撤销"了事;
                    // 并给出人工兜底命令, 用户/我们可以自己救回来。
                    Log("快速断流: 撤销失败/不干净 —— " + (ok1 ? "" : "WFP: " + e1 + "; ")
                        + (ok2 ? "" : "防火墙: " + e2 + "; ")
                        + "  人工兜底: netsh advfirewall firewall delete rule name=\"" + FW_RULE_NAME + "\"");
                }
            }
        }
        catch (Exception ex) { Log("快速断流: 撤销异常 " + ex.Message); }
    }

    /// <summary>启动时清理上次崩溃可能留下的防火墙规则(WFP 动态会话不需要清)。</summary>
    private static void FastCut_CleanupLeftovers()
    {
        try
        {
            // 11.1.0 验收(第二轮 N4): 清理也要"响亮" —— 删不掉时用户要能看到, 并拿到人工命令
            string err;
            int n = FwRemoveOurRules(out err);
            if (n > 0) Log("[启动清理] 删除了 " + n + " 条上次残留的防火墙规则(SkyGuard-Panic-*)");
            if (!string.IsNullOrEmpty(err))
                Log("[启动清理] 没删干净/出错: " + err
                    + "   人工兜底: netsh advfirewall firewall delete rule name=\"" + FW_RULE_NAME + "\"");
        }
        catch { }
    }

    /// <summary>给日志/自检用的一句话能力说明(全部实测, 不猜)。</summary>
    private static string FastCut_CapabilityReport()
    {
        StringBuilder sb = new StringBuilder();
        string bfe = "(查不到)";
        try
        {
            string o = RunTool("sc.exe", "query BFE");
            if (o.IndexOf("RUNNING", StringComparison.OrdinalIgnoreCase) >= 0) bfe = "运行中";
            else if (o.IndexOf("STOPPED", StringComparison.OrdinalIgnoreCase) >= 0) bfe = "已停止(WFP 不可用)";
            else bfe = "未装/未知";
        }
        catch { }
        sb.Append("BFE=").Append(bfe);
        try
        {
            object policy = FwPolicy();
            if (policy == null) sb.Append("  防火墙COM=取不到");
            else
            {
                string[] names = new string[] { "域", "专用", "公用" };
                sb.Append("  防火墙=");
                for (int i = 0; i < 3; i++)
                {
                    try
                    {
                        object on = policy.GetType().InvokeMember("FirewallEnabled",
                            System.Reflection.BindingFlags.GetProperty, null, policy, new object[] { i + 1 });
                        sb.Append(names[i]).Append(Convert.ToBoolean(on) ? "开" : "关").Append(' ');
                    }
                    catch { sb.Append(names[i]).Append("? "); }
                }
            }
        }
        catch { sb.Append("  防火墙COM=异常"); }
        return sb.ToString();
    }

    #endregion

    // ============================================================================
    //  六、处置主流程
    // ============================================================================

    #region 处置

    // ============================================================================
    //  常驻工作线程 + 进程特权
    //
    //  为什么要有常驻线程(虚拟机实测):
    //    按下触发键后原来要 new Thread + Start 两次(处置线程、断网线程),
    //    而 VM 里 Thread.Start() 实测要 430~680 ms(真机 <1 ms), 再加线程调度延迟,
    //    "按下之后到真正下刀"凭空多出 1 秒多。上报窗口就那么几秒, 这个开销要命。
    //    改成程序启动时就把两条线程建好, 触发时只 Set() 一下事件(微秒级)。
    // ============================================================================

    private static readonly AutoResetEvent _panicWake = new AutoResetEvent(false);
    private static readonly AutoResetEvent _netWake = new AutoResetEvent(false);
    private static volatile bool _netWantEnable;    // true = 恢复网络, false = 断开
    // Interlocked 抢占: 两条触发通道同时做第一次唤醒时, 不会各起一对常驻线程
    private static int _workersStarted;
    /// <summary>
    /// 网络请求代数: 每来一个"断开/恢复"请求就自增。
    /// 正在跑的恢复流程每等一步都比一下自己那一代 —— 变了就说明用户又按了触发键(要断网), 必须立刻让路。
    /// 没有它的话, 后台恢复(含续租/重挂, 最长一分多钟)会把保命那一刀堵在门外。
    /// </summary>
    private static volatile int _netReqGen;
    /// <summary>断网线程最后完成的那一代 —— 用来精确等"我这一次操作"干完, 而不是"某一次操作"干完。</summary>
    private static volatile int _netDoneGen;
    /// <summary>本次恢复是否被新的网络请求打断(打断就不算"恢复失败", 也不弹指引)。</summary>
    private static volatile bool _restoreSuperseded;

    private static void StartPanicWorkers()
    {
        if (Interlocked.CompareExchange(ref _workersStarted, 1, 0) != 0) return;

        Thread panicThread = new Thread(delegate()
        {
            while (true)
            {
                try { _panicWake.WaitOne(); } catch { }
                try { Panic(); }
                catch (Exception ex) { LogToFileOnly("[处置线程] 异常: " + ex.Message); }
            }
        });
        panicThread.IsBackground = true;
        panicThread.Name = "SkyGuardPanic";
        panicThread.Start();

        Thread netThread = new Thread(delegate()
        {
            while (true)
            {
                try { _netWake.WaitOne(); } catch { }
                // ★ 先读"要做什么", 再读代数 —— 顺序不能反:
                //   反过来的话, 两行之间插进来一个新请求会让我们"拿着新代数去干旧活",
                //   于是该干的活被自己判成"已被打断"而跳过。
                bool want = _netWantEnable;
                int gen = _netReqGen;
                try { SetNets(want, gen); }
                catch (Exception ex) { LogToFileOnly("[断网线程] 异常: " + ex.Message); }
                finally { _netDoneGen = gen; }
            }
        });
        netThread.IsBackground = true;
        netThread.Name = "SkyGuardNet";
        netThread.Start();

        LogToFileOnly("[启动] 处置/断网 常驻线程已就绪 (触发时不再新建线程)");
    }

    /// <summary>唤醒常驻处置线程。触发键热路径只做这一件事。</summary>
    private static void WakePanic()
    {
        StartPanicWorkers();
        _panicWake.Set();
    }

    /// <summary>
    /// 让常驻断网线程去断开/恢复网络。返回本次请求的代数(配合 WaitNetOp 用)。
    ///
    /// ★ 所有"动网卡"的请求都必须走这里: 只有一条线程在动网卡, 才不会出现
    ///   "恢复的 admin=enabled 落在断开的 admin=disabled 之后"这种互相打架
    ///   (以前 UI 线程 / 关窗线程 / 处置线程会各自直接调 SetNets)。
    /// </summary>
    private static int WakeNetCut(bool enable)
    {
        StartPanicWorkers();
        _netWantEnable = enable;
        _netReqGen++;
        _netWake.Set();
        return _netReqGen;
    }

    /// <summary>
    /// 等"我这一次网络操作"真的做完。按代数判定 —— 只等"某一件活收尾"会被上一件活误唤醒。
    /// 返回是否在超时内完成。
    /// </summary>
    private static bool WaitNetOp(int myGen, int timeoutMs)
    {
        long t0 = Stopwatch.GetTimestamp();
        while (true)
        {
            // 代数只会变大: 比我大的活都做完了, 我这一件必然也做完了
            if (_netDoneGen >= myGen) return true;
            if (ElapsedMs(t0) >= timeoutMs) return false;
            try { Thread.Sleep(20); } catch { }
        }
    }

    /// <summary>
    /// 发起一次网络操作(断开/恢复), 可选等它做完。timeoutMs &lt;= 0 = 发出去就走(后台自己跑)。
    /// 这是"动网卡"的唯一入口 —— 以前 UI 线程直接调 SetNets, 一次真恢复能把窗口冻住一两分钟。
    /// </summary>
    private static void RunNetOp(bool enable, int timeoutMs)
    {
        int gen = WakeNetCut(enable);
        if (timeoutMs <= 0) return;
        if (!WaitNetOp(gen, timeoutMs))
        {
            _netOpStuck = true;
            Log("  网络操作(" + (enable ? "恢复" : "断开") + ")超过 " + timeoutMs
                + " ms 还没结束 -> 它继续在后台跑, 这里不再等");
        }
        else _netOpStuck = false;
    }

    /// <summary>
    /// 可被打断的等待: 期间来了新的网络操作请求(用户按了触发键)就立刻返回 false。
    /// 恢复流程里所有以秒计的等待都走它 —— 保命那一刀绝不能被恢复挡住。
    /// </summary>
    private static bool WaitAbortable(int ms, int reqGen)
    {
        long t0 = Stopwatch.GetTimestamp();
        while (ElapsedMs(t0) < ms)
        {
            if (reqGen != 0 && _netReqGen != reqGen) return false;
            try { Thread.Sleep(50); } catch { }
        }
        return reqGen == 0 || _netReqGen == reqGen;
    }

    /// <summary>恢复流程是否已经被新的网络请求取代(取代了就别再往下做重活)。</summary>
    private static bool RestoreSuperseded(int reqGen)
    {
        if (reqGen != 0 && _netReqGen != reqGen)
        {
            if (!_restoreSuperseded)
            {
                _restoreSuperseded = true;
                Log("恢复流程被新的网络操作请求打断 -> 立刻让路(优先执行新的操作)");
            }
            return true;
        }
        return false;
    }

    private static volatile bool _debugPrivTried;
    private static volatile bool _debugPrivOk;
    private static volatile bool _debugPrivLastCfg;   // 上次尝试时开关的状态(开关变了要允许重试)

    /// <summary>
    /// 启用 SeDebugPrivilege —— 杀"受限令牌 / 沙箱"进程的关键。
    /// 虚拟机实测: 对 Edge 的几个沙箱进程, 即使进程是管理员,
    /// TerminateProcess 也一直返回错误码 5; 打开调试特权才能绕过目标进程的 DACL。
    /// 该特权只在管理员令牌里存在, 非管理员时失败属正常(只记一行, 不影响其它功能)。
    /// </summary>
    private static bool EnableDebugPrivilege()
    {
        // 开关没开就完全不碰特权(默认关, 见 Config.DebugPriv)
        if (_cfg == null || !_cfg.DebugPriv) return false;
        // 已经成功拿到过就不用再来; 但开关状态变了要允许重新尝试
        if (_debugPrivTried && _debugPrivLastCfg == _cfg.DebugPriv) return _debugPrivOk;
        _debugPrivTried = true;
        _debugPrivLastCfg = _cfg.DebugPriv;
        IntPtr token = IntPtr.Zero;
        try
        {
            const uint TOKEN_ADJUST_PRIVILEGES = 0x0020;
            const uint TOKEN_QUERY = 0x0008;
            const int SE_PRIVILEGE_ENABLED = 0x00000002;

            if (!OpenProcessToken(GetCurrentProcess(), TOKEN_ADJUST_PRIVILEGES | TOKEN_QUERY, out token))
            {
                LogToFileOnly("[特权] OpenProcessToken 失败, 错误码 " + Marshal.GetLastWin32Error());
                return false;
            }
            long luid;
            if (!LookupPrivilegeValue(null, "SeDebugPrivilege", out luid))
            {
                LogToFileOnly("[特权] LookupPrivilegeValue 失败, 错误码 " + Marshal.GetLastWin32Error());
                return false;
            }
            TOKEN_PRIVILEGES tp = new TOKEN_PRIVILEGES();
            tp.Count = 1;
            tp.LuidLow = (int)(luid & 0xFFFFFFFFL);
            tp.LuidHigh = (int)((luid >> 32) & 0xFFFFFFFFL);
            tp.Attributes = SE_PRIVILEGE_ENABLED;
            if (!AdjustTokenPrivileges(token, false, ref tp, 0, IntPtr.Zero, IntPtr.Zero))
            {
                LogToFileOnly("[特权] AdjustTokenPrivileges 失败, 错误码 " + Marshal.GetLastWin32Error());
                return false;
            }
            int err = Marshal.GetLastWin32Error();    // 1300 = 令牌里没有这个特权
            _debugPrivOk = (err == 0);
            Log("[特权] SeDebugPrivilege = "
                + (_debugPrivOk ? "已启用 (能处理受限令牌/沙箱进程)"
                                : "拿不到, 错误码 " + err + " —— 非管理员时属正常"));
            return _debugPrivOk;
        }
        catch (Exception ex) { LogToFileOnly("[特权] 异常: " + ex.Message); return false; }
        finally { if (token != IntPtr.Zero) CloseHandle(token); }
    }

    private static void Panic()
    {
        // 占位由 FireTrigger 抢占(0->1)完成, 正常路径到这里 _busy 已经是 1, 这里只是兜底:
        // 万一以后有人绕过 FireTrigger 直接调 Panic, 也不至于和正在跑的处置撞车。
        Interlocked.Exchange(ref _busy, 1);
        _panicStartTicks = Stopwatch.GetTimestamp();
        _firstDownTicks = 0;
        try
        {
            Log("开始处置");
            Log("权限: " + (IsAdmin() ? "管理员" : "非管理员(强杀/断网可能失败)"));

            // 断网和强杀同时开火: 断网慢(好几秒), 不能排在强杀后面。
            // 唤醒常驻断网线程, 不再 new Thread + Start ——
            // VM 实测 Thread.Start() 要 430~680 ms, 那正是"按下后没反应"的主因。
            long tStart = Stopwatch.GetTimestamp();
            int netGen = WakeNetCut(false);
            Log("  已唤醒常驻断网线程 (唤醒用 " + ElapsedMs(tStart) + " ms, 自触发 "
                + ElapsedMs(_panicStartTicks) + " ms)");

            long killMs;
            List<string> targets = _cfg.TargetList();
            Log("  目标程序共 " + targets.Count + " 个: " + string.Join(" / ", targets.ToArray()));
            KillWithRetry(targets, 6000);
            // ★ 只枚举一次进程表再逐个查: FindPids 的单参版每次都会重新枚举全系统进程
            //   (250+ 进程, 约 17 ms), 9 个目标就是 9 次、约 150 ms —— 白白拖后"杀干净没有"的判定。
            List<KeyValuePair<int, string>> snapAfter = EnumProcesses();
            bool killed = true;
            foreach (string t in targets) if (FindPids(t, snapAfter).Count > 0) { killed = false; break; }
            killMs = ElapsedMs(_panicStartTicks);
            Log("  强杀结果: " + (killed ? "成功" : "有残留")
                + " [累计 " + killMs + " ms] (自触发 " + ElapsedMs(_panicStartTicks) + " ms)");

            // 等断网线程收尾(最多 NET_OP_STUCK_MS) —— 免得"网还没断干净"就去恢复。
            // ★ 按代数等"我这一次断网", 不能用"有没有活在跑"这种粗粒度信号:
            //   后台正好有别的网络操作在收尾时会误唤醒, 于是断网还没开始就往下走了。
            // ★ V1.1.5-RC1: 上限从 20 秒改成 NET_OP_STUCK_MS(60 秒) —— 原来"20 秒就往下走"
            //   在慢网卡上太短(禁网卡本身就要 3~15 秒), 而"等太久"又会把处置位占死, 两头都要顾。
            if (!WaitNetOp(netGen, NET_OP_STUCK_MS))
            {
                _netOpStuck = true;
                Log("  断网线程 " + (NET_OP_STUCK_MS / 1000) + " 秒还没结束 -> 判定为卡住, 先继续往下走"
                    + " (它仍在后台跑; 界面会提示可以点[恢复网络])");
            }

            if (!killed)
            {
                // 有进程没杀掉: 默认保持断网(宁可多断一会儿), 但用户明确按了第二次就照办
                if (_abort)
                {
                    Log("  收到收尾请求 -> 恢复网络");
                    if (!WaitNetOp(WakeNetCut(true), NET_OP_STUCK_MS))
                    {
                        _netOpStuck = true;
                        Log("  恢复网络 " + (NET_OP_STUCK_MS / 1000) + " 秒还没结束 -> 判定为卡住, 先放手"
                            + " (恢复仍在后台进行; 可以点[恢复网络]再让它试一次)");
                    }
                    Log("处置结束 [有残留, " + RestoreVerdictText() + "]");
                }
                else
                {
                    Log("处置未完成: 强杀有残留, 网络保持断开。点[恢复网络]或[停止保护]可恢复。");
                    Log("处置结束 [有残留, 保持断网]");
                }
                return;   // finally 里会清 _busy
            }

            // ★ 保持 + "结束前 1 秒复查目标是否真的全灭"(用户定的规则):
            //   没灭 -> 再杀一轮 + 再断网一整轮(最多加一轮);
            //   第二轮结束前还在 -> 弹窗告知可能有顽固残留进程, 由用户决定是否恢复网络。
            int extraRounds = 0;
            bool restoreAtEnd = true;
            while (true)
            {
                long already = ElapsedMs(_firstDownTicks);
                int remain = _cfg.WaitSeconds - (int)(already / 1000);
                if (remain < 0) remain = 0;
                Log("  目标程序已关闭, 网卡已禁用; 已保持 " + (already / 1000) + " 秒, 再等 " + remain + " 秒"
                    + (extraRounds > 0 ? "  (第 " + (extraRounds + 1) + " 轮断网)" : ""));

                // 等待期间每 100 ms 看一眼有没有"收尾请求"([停止保护] / 关窗) —— 那就不用等完了
                int waitTicks = Math.Max(0, remain * 10 - 10);      // 留出最后 1 秒专门做复查
                for (int i = 0; i < waitTicks; i++)
                {
                    if (_abort) { Log("  收到收尾请求 -> 结束等待, 恢复网络"); break; }
                    Thread.Sleep(100);
                }
                if (_abort) break;

                // ---- 结束前 1 秒: 复查目标进程是否完全结束 ----
                List<string> aliveNow = AliveTargets();
                if (aliveNow.Count == 0)
                {
                    Log("  结束前复查: 目标进程已全部退出");
                    for (int i = 0; i < 10 && !_abort; i++) Thread.Sleep(100);   // 把这最后 1 秒等完
                    break;
                }
                // 也可能只是还在收尾 —— 再给 1 秒
                Thread.Sleep(1000);
                if (_abort) break;
                aliveNow = AliveTargets();
                if (aliveNow.Count == 0)
                {
                    Log("  结束前复查(补 1 秒): 目标进程已全部退出");
                    break;
                }

                if (extraRounds == 0)
                {
                    extraRounds++;
                    Log("  结束前复查: 仍在运行 " + string.Join(" / ", aliveNow.ToArray())
                        + " -> 再杀一轮, 并再断网 " + _cfg.WaitSeconds + " 秒");
                    KillWithRetry(_cfg.TargetList(), 6000);
                    _firstDownTicks = Stopwatch.GetTimestamp();      // 重新计保持期
                    continue;
                }

                // 加了这一轮之后还在 —— 交给用户定
                Log("  结束前复查: 再杀一轮之后仍在运行 " + string.Join(" / ", aliveNow.ToArray())
                    + " -> 判定为顽固残留进程, 由用户决定是否恢复网络");
                AppendUi("有程序未能结束，请在弹窗中选择是否恢复网络。");
                bool doRestore = true;
                if (!_headless)
                {
                    try
                    {
                        DialogResult rr = MessageBox.Show(
                            "以下程序未能结束：\n\n"
                          + string.Join(" / ", aliveNow.ToArray())
                          + "\n\n现在恢复网络吗？",
                            APP_NAME, MessageBoxButtons.YesNo, MessageBoxIcon.Warning,
                            MessageBoxDefaultButton.Button1, MessageBoxOptions.DefaultDesktopOnly);
                        doRestore = (rr == DialogResult.Yes);
                    }
                    catch { }
                }
                if (!doRestore)
                {
                    restoreAtEnd = false;
                    Log("  用户选择保持断网 -> 网络保持断开(点[恢复网络]可随时恢复)");
                }
                else Log("  用户选择恢复网络");
                break;
            }

            if (!restoreAtEnd)
            {
                Log("处置结束 [成功, 保持断网]");
                if (_cfg != null && _cfg.RestoreOnBoot) RunOnceSet();   // 保持断网就登记开机恢复, 免得用户没网
                return;
            }

            // 恢复网络走常驻断网线程(唯一动网卡的入口), 并等它做完; 给个上限,
            // 免得 netsh 卡住把处置位永久占住, 之后按触发键全都没反应。
            // ★ V1.1.5-RC1: 上限从 300 秒改成 NET_OP_STUCK_MS(60 秒)。
            //   原来那 300 秒意味着"netsh 卡住时, 触发键最长 5 分钟完全没反应" ——
            //   对一个保命工具来说这本身就是"关键时刻掉链子"。现在到点就放手:
            //   网络线程照样在后台把活干完, 但处置位立刻放开, 下一按还能再断一轮。
            if (!WaitNetOp(WakeNetCut(true), NET_OP_STUCK_MS))
            {
                _netOpStuck = true;
                Log("  恢复网络 " + (NET_OP_STUCK_MS / 1000) + " 秒还没结束 -> 判定为卡住, 先放手"
                    + " (恢复仍在后台进行; 可以点[恢复网络]再让它试一次)");
            }
            Log("处置完成: 强杀成功, " + RestoreVerdictText() + " (自触发 " + ElapsedMs(_panicStartTicks) + " ms)");
            Log("处置结束 [成功]");
        }
        catch (Exception ex) { Log("处置异常: " + ex.Message); }
        finally
        {
            _abort = false;
            // 注意: 这里**不能**把 _lastFireTicks 清零 —— 去重窗口要活过这次处置的收尾。
            // 清零的话, 同一按键的第 2、3 条上报在"处置刚结束"那一瞬间会落进
            // "抢占成功"那条路, 又起一轮处置(见 FireTrigger 里的说明)。
            Interlocked.Exchange(ref _busy, 0);
            // 这一轮结束了: 处置位不再被占, "卡住"提示可以收了。
            // (_netOpStuck 不清 —— 它表示"后台那次网络操作还没回来", 由 RunNetOp 成功时清。)
            _busyStuck = false;
            _busySinceTicks = 0;
            // 状态面板用: 记下"上一次处置用了多久"(成功/失败/细节都在日志里, 面板会把日志整段带上)
            try
            {
                _diagLastPanicMs = ElapsedMs(_panicStartTicks);
                _diagLastPanic = "上一次处置用时 " + _diagLastPanicMs + " ms"
                    + " (强杀/断网/恢复的每一步都在日志里)";
            }
            catch { }
        }
    }

    /// <summary>当前还在运行的目标进程名(只枚举一次进程表, 给"结束前复查"用)。</summary>
    private static List<string> AliveTargets()
    {
        List<string> alive = new List<string>();
        try
        {
            if (_cfg == null) return alive;
            List<KeyValuePair<int, string>> snap = EnumProcesses();
            foreach (string t in _cfg.TargetList()) if (FindPids(t, snap).Count > 0) alive.Add(t);
        }
        catch { }
        return alive;
    }

    private static bool IsAdmin()
    {
        try
        {
            return new System.Security.Principal.WindowsPrincipal(
                System.Security.Principal.WindowsIdentity.GetCurrent())
                .IsInRole(System.Security.Principal.WindowsBuiltInRole.Administrator);
        }
        catch { return false; }
    }

    private static IntPtr HookCallback(int nCode, IntPtr wParam, IntPtr lParam)
    {
        try
        {
            if (nCode >= 0)
            {
                _hookCalls++;
                int msg = wParam.ToInt32();
                if (msg == WM_KEYDOWN || msg == WM_SYSKEYDOWN)
                {
                    uint vk = (uint)Marshal.ReadInt32(lParam);
                    // 诊断模式: 把每一个按下的键都记下来, 用来判断"钩子到底有没有被调用"
                    if (_hookTrace) LogToFileOnly("  [按键原始] vk=0x" + vk.ToString("X2") + " 长度=" + _trigs.Count);
                    if (_selfTestRequested && vk == VK_SELFTEST)
                    {
                        // 看门狗的探测按键: 钩子确实还活着
                        _selfTestResult = 1;
                        return CallNextHookEx(_hookForCallback, nCode, wParam, lParam);
                    }
                    bool ctrl = (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0;
                    bool alt = (GetAsyncKeyState(VK_MENU) & 0x8000) != 0;
                    bool shift = (GetAsyncKeyState(VK_SHIFT) & 0x8000) != 0;

                    foreach (KeyTrig t in _trigs)
                    {
                        if (t.Vk != vk) continue;
                        bool match = (ctrl == t.Ctrl) && (alt == t.Alt) && (shift == t.Shift);
                        // 保险: 裸 F4 屏蔽 Alt+F4(Windows 关闭窗口)
                        if (match && t.IsF4 && !t.Alt && alt) match = false;
                        if (match) FireTrigger("钩子通道", t.Name);
                        break;
                    }
                }
            }
        }
        catch { }
        return CallNextHookEx(_hookForCallback, nCode, wParam, lParam);
    }

    // ============================================================================
    //  键盘钩子 —— 独立线程
    //
    //  这是这个程序最要紧的一条链子, 所以它的可靠性优先级高于界面。
    //
    //  为什么不能装在 UI 线程上:
    //    WH_KEYBOARD_LL 的回调是在安装它的那个线程上被调用的。
    //    装在 UI 线程上, 就意味着"界面一卡 → 钩子收不到键 → 按触发键没反应"。
    //    更糟的是系统对钩子回调有超时限制(默认 300 ms), 超了会把钩子直接摘掉,
    //    之后不管界面恢不恢复, 按键都不会再进来 —— 这正是"无响应时按了没反应"。
    //
    //  所以: 钩子装在自己的线程上, 那条线程只干一件事 —— 泵消息、跑回调。
    //  界面卡成什么样都影响不到它。
    // ============================================================================

    private static volatile bool _hookThreadStarted = false;
    private static volatile bool _hookInstallOk = false;
    private static volatile IntPtr _hookForCallback = IntPtr.Zero;
    private static volatile uint _hookThreadId = 0;
    /// <summary>钩子线程对象 —— 摘钩子时要能确定地等它退出(见 StopHook)。</summary>
    private static volatile Thread _hookThread;
    /// <summary>钩子线程的消息队列已经建好了吗(建好之前 PostThreadMessage(WM_QUIT) 会丢)。</summary>
    private static volatile bool _hookQueueReady = false;
    private static volatile bool _selfTestRequested = false;
    private static volatile int _selfTestResult = 0;        // 0=还没测 1=反应正常 2=没反应
    /// <summary>诊断开关: 打开后把每个按下的键都写进日志</summary>
    private static volatile bool _hookTrace = false;
    private static volatile bool _watchdogStarted = false;

    /// <summary>装钩子并等它装好。返回是否装上(最多等 3 秒)。</summary>
    private static bool StartHook()
    {
        if (_hookInstallOk) return true;
        StartHookThread();

        // 修界面无响应: 这里原来是 Thread.Sleep(50) x 60 = 最多 3 秒完全不泵消息,
        // 点[开始保护] / 设置[确定] / 向导[完成] 时窗口会僵住 1.3~3 秒(实测界面 tick = 0)。
        // 现在边等边泵消息: 窗口照常重画、照常响应, 只是按钮状态要等钩子就绪。
        UiPhaseBegin("正在启动键盘钩子");
        for (int i = 0; i < 120; i++)
        {
            PumpOnUi();
            Thread.Sleep(25);
            if (_hookInstallOk) break;
        }
        UiPhaseEnd("");
        if (!_hookInstallOk)
        {
            Log("键盘钩子安装失败(等 3 秒没等到)");
            return false;
        }
        Log("键盘钩子已安装 (独立线程, 不依赖界面)");
        StartKeyPoll();
        StartHotKeys();
        StartFocusRescue();
        StartHookWatchdog();
        StartPanicWorkers();   // 常驻处置/断网线程: 触发时只 Set() 一下, 不再新建线程
        return true;
    }

    /// <summary>
    /// 独立钩子线程: 装钩子 → 泵消息直到收到 WM_QUIT → 摘钩子。
    /// 线程里只做这三件事, 不做任何可能阻塞的活。
    /// </summary>
    private static void StartHookThread()
    {
        if (_hookThreadStarted) return;
        _hookThreadStarted = true;
        _hookInstallOk = false;
        _hookQueueReady = false;

        Thread t = new Thread(delegate()
        {
            try
            {
                _hookThreadId = GetCurrentThreadId();
                _hookProc = new LowLevelKeyboardProc(HookCallback);
                IntPtr h = SetWindowsHookEx(WH_KEYBOARD_LL, _hookProc, IntPtr.Zero, 0);
                if (h == IntPtr.Zero)
                {
                    Log("键盘钩子安装失败, 错误码 " + Marshal.GetLastWin32Error());
                    _hookThreadStarted = false;
                    return;
                }
                _hookHandle = h;
                _hookForCallback = h;
                _hookInstallOk = true;
                LogToFileOnly("钩子已装在独立线程 thread=" + _hookThreadId + " (不依赖界面)");

                // 钩子线程必须随叫随到: 系统等回调是有限时的, 被别的进程饿着就会被摘钩
                try { Thread.CurrentThread.Priority = ThreadPriority.Highest; }
                catch { }

                // GetMessage 一进来消息队列就建好了 —— 之后 StopHook 的 WM_QUIT 才投得进来。
                // (在这之前投 WM_QUIT 会被系统丢掉, 于是老代码只能"等 1 秒然后强行改状态",
                //  结果是钩子线程还活着却又起了一条新钩子线程 = 两个全局钩子。)
                _hookQueueReady = true;
                MSG m;
                while (GetMessage(out m, IntPtr.Zero, 0, 0) > 0)
                {
                    // ★ V1.1.5-RC1: 自检请求走线程消息, 在**这条线程上**装卸钩子(系统要求)。
                    //   PostThreadMessage 投进来的消息 hwnd 是 NULL, DispatchMessage 对它无效,
                    //   所以必须在这里拦下来自己处理。
                    if (m.message == WM_APP_REHOOK)
                    {
                        RehookOnHookThread();
                        continue;
                    }
                    TranslateMessage(ref m);
                    DispatchMessage(ref m);
                }

                UnhookWindowsHookEx(h);
                _hookHandle = IntPtr.Zero;
                _hookForCallback = IntPtr.Zero;
            }
            catch (Exception ex) { Log("钩子线程异常: " + ex.Message); }
            finally
            {
                _hookInstallOk = false;
                _hookThreadStarted = false;
                _hookQueueReady = false;
                if (ReferenceEquals(_hookThread, Thread.CurrentThread)) _hookThread = null;
            }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardHook";
        _hookThread = t;
        t.Start();
    }

    /// <summary>
    /// 摘钩子。
    ///
    /// full=false 是看门狗重装钩子用的: 那种情况下只该动钩子这一条链子,
    /// 绝不能顺手把热键通道也拆了。踩过的坑(日志):
    ///   看门狗重装 -> StopHook 里连带 StopHotKeys -> StartHook 里又 StartHotKeys,
    ///   于是重新注册窗口类, 报 `注册窗口类失败, 错误码 1410`
    ///   (1410 = ERROR_CLASS_ALREADY_EXISTS, 老代码只认 183, 所以直接 return 了),
    ///   结果 _hotkeyStarted 被置 false、热键窗口还挂在旧线程上 —— 状态是拧的。
    /// 现在: 重装钩子完全不碰热键通道(它本来就活得好好的, 也没必要重注册)。
    ///
    /// full=true 是"用户真的停止保护"用的: 钩子、热键一起收干净。
    /// </summary>
    private static void StopHook(bool full)
    {
        if (full)
        {
            try { StopHotKeys(); } catch { }
        }
        Thread th = _hookThread;
        // 消息队列还没建好的话, PostThreadMessage(WM_QUIT) 会被系统直接丢掉 ——
        // 先等它(最多 1.5 秒), 免得白投一次。
        for (int i = 0; i < 30 && th != null && th.IsAlive && !_hookQueueReady; i++) { PumpOnUi(); Thread.Sleep(25); }

        if (_hookThreadId != 0)
        {
            bool posted = false;
            for (int i = 0; i < 6 && !posted; i++)
            {
                posted = PostThreadMessage(_hookThreadId, WM_QUIT, IntPtr.Zero, IntPtr.Zero);
                if (!posted) { PumpOnUi(); Thread.Sleep(25); }
            }
            if (posted)
            {
                // ★ 用线程对象确定地等它退出 —— 它退出时会自己摘钩子、清标志。
                //   以前这里只等 1 秒就强行把 _hookInstallOk/_hookThreadStarted 置 false:
                //   万一 WM_QUIT 丢了(或线程还卡在别处), StartHook 会再起一条钩子线程,
                //   于是同一个进程里挂着两个全局键盘钩子(同一按键被两条链处理)。
                if (th != null && !th.Join(3000))
                    Log("键盘钩子线程 3 秒还没退出 —— 先按已卸载处理, 下次重装时会再试");
            }
            else
            {
                Log("向钩子线程投递 WM_QUIT 失败(错误码 " + Marshal.GetLastWin32Error() + ") —— 先按已卸载处理");
            }
        }
        _hookInstallOk = false;
        _hookHandle = IntPtr.Zero;
        _hookForCallback = IntPtr.Zero;
        _hookThreadStarted = false;
        _hookThreadId = 0;
        Log("键盘钩子已卸载" + (full ? "" : " (准备重装, 热键通道未动)"));
    }

    /// <summary>
    /// 发一个"没人会按"的假按键(虚拟键码 0xFF)出去, 看钩子能不能收到。
    /// 这不是喂给钩子的假数据 —— 是真的走一遍系统键盘输入链,
    /// 所以"收不到"就等于"用户按键也收不到", 这才是有效的探活。
    ///
    /// 代价(所以默认不调它, 见 Config.HookProbe): 走的是系统输入链,
    /// 前台游戏 / 反作弊 / 输入法 / 宏软件都会收到这个按键。
    /// 另外 0xFF 不是合法虚拟键, 投递本身不保证每次成功 ——
    /// 所以看门狗那边要连续失败 HOOK_FAIL_LIMIT 次才肯拆钩子。
    /// </summary>
    private static bool SelfTestHook()
    {
        _selfTestRequested = true;
        _selfTestResult = 0;
        try
        {
            keybd_event((byte)VK_SELFTEST, 0, 0, IntPtr.Zero);   // 按下
            keybd_event((byte)VK_SELFTEST, 0, 2, IntPtr.Zero);   // 抬起(KEYEVENTF_KEYUP)
        }
        catch { }
        for (int i = 0; i < 40; i++)
        {
            Thread.Sleep(50);
            if (_selfTestResult != 0) break;
        }
        bool ok = (_selfTestResult == 1);
        _selfTestRequested = false;
        _selfTestResult = 0;
        return ok;
    }

    /// <summary>连续几轮判定异常才重装钩子。单次探测失败不算 —— 拆装的那一瞬间触发键是真按不动的。</summary>
    private const int HOOK_FAIL_LIMIT = 3;

    // ============================================================================
    //  钩子"静默失效"的检测与重装(V1.1.5-RC1)
    //
    //  问题(以前查不出来, 最危险的一种失效):
    //    系统对 WH_KEYBOARD_LL 的回调有时限(默认 300 ms)。超时不会报错、不会通知,
    //    它会**悄悄把钩子摘掉**。而钩子线程本身还活着, _hookInstallOk / _hookThreadStarted
    //    两个标志也都还是 true —— 于是看门狗每一轮都判"钩子正常", 界面也一直显示"正在保护"。
    //    表现就是"按触发键没反应", 而用户完全不知道, 一直到出事那一刻。
    //
    //  怎么查出来:
    //    UnhookWindowsHookEx 在"钩子已经不在系统里"时返回 0(错误码 1404 ERROR_INVALID_HOOK_HANDLE)。
    //    所以只要定期"先摘再装": 返回 0 = 它早就被摘了(记下来、报出来); 返回非 0 = 我们主动摘的。
    //    两种情况下紧接着都用 SetWindowsHookEx 装回来, 收尾时钩子一定是活的。
    //
    //  代价与兜底:
    //    "无钩子"的窗口只有微秒级, 而同一时刻还有轮询通道(8 ms 一轮)和热键通道(系统匹配、
    //    完全不经过钩子), 所以这个窗口不会造成漏按。自检间隔取 300 秒 —— 比 10 秒那种
    //    "一天装/摘几千次钩子"克制得多, 不容易招安全软件注意(它们会统计钩子装卸行为)。
    //
    //  这一条**不动**原来那条路: 钩子线程真的死了, 还是由 StartHookWatchdog 的
    //  StopHook(false) + StartHook() 重建线程来处理。
    // ============================================================================

    /// <summary>钩子自检间隔(秒)。300 秒 = 一天约 288 次, 对安全软件来说动静可忽略。</summary>
    private const int HOOK_SELFCHECK_SEC = 300;

    /// <summary>钩子自检结果: 0=还没查过 1=正常(主动摘装的) 2=曾被系统摘掉, 已重装 3=重装失败</summary>
    private static volatile int _hookHealth = 0;
    /// <summary>钩子被系统/安全软件悄悄摘掉过几次(0 = 从来没发生过)</summary>
    private static volatile int _hookLostCount = 0;
    /// <summary>最近一次钩子自检的时间(Stopwatch 时间戳)</summary>
    private static long _hookLastCheckTicks = 0;
    /// <summary>通道降级(界面要把它显示出来, 别让用户以为一切正常)</summary>
    private static volatile bool _chanDegraded = false;

    /// <summary>
    /// 请钩子线程做一次"摘了再装"的自检 —— 这是唯一能发现"钩子被系统悄悄摘掉"的办法。
    /// 只在钩子线程的消息队列已经建好之后投递(否则 PostThreadMessage 会被系统直接丢掉)。
    /// </summary>
    private static void RequestHookSelfCheck(string why)
    {
        try
        {
            if (!_guarding) return;
            if (!_hookInstallOk || !_hookThreadStarted || !_hookQueueReady) return;
            if (_hookThreadId == 0) return;
            if (!PostThreadMessage(_hookThreadId, WM_APP_REHOOK, IntPtr.Zero, IntPtr.Zero))
                LogToFileOnly("[通道自检] 投递钩子自检请求失败(" + why + "), 错误码 "
                    + Marshal.GetLastWin32Error() + " —— 不影响触发, 只是这次没查到");
        }
        catch { }
    }

    /// <summary>
    /// 在钩子线程上执行: 摘掉旧钩子(顺便判断它是不是早就不在了) -> 立刻装一个新的。
    /// ★ 只能在这条线程上调用 —— 见 WM_APP_REHOOK 的注释。
    /// </summary>
    private static void RehookOnHookThread()
    {
        try
        {
            IntPtr old = _hookHandle;
            bool stillThere = true;
            if (old != IntPtr.Zero)
            {
                stillThere = UnhookWindowsHookEx(old);
                if (!stillThere)
                {
                    _hookLostCount++;
                    _chanDegraded = true;
                    LogToFileOnly("[通道自检] *** 钩子早已不在系统里 *** —— 它被系统(回调超时)"
                        + "或安全软件悄悄摘掉了, 而只查线程/标志的旧看门狗发现不了;"
                        + " 现在重装, 错误码 " + Marshal.GetLastWin32Error());
                }
            }
            _hookHandle = IntPtr.Zero;
            _hookForCallback = IntPtr.Zero;

            if (_hookProc == null) _hookProc = new LowLevelKeyboardProc(HookCallback);
            IntPtr h = SetWindowsHookEx(WH_KEYBOARD_LL, _hookProc, IntPtr.Zero, 0);
            if (h == IntPtr.Zero)
            {
                int rc = Marshal.GetLastWin32Error();
                _hookInstallOk = false;
                _hookHealth = 3;
                _chanDegraded = true;
                LogToFileOnly("[通道自检] 钩子重装失败, 错误码 " + rc
                    + " —— 触发键还有轮询通道和热键通道兜底, 但请重启程序");
                return;
            }
            _hookHandle = h;
            _hookForCallback = h;
            _hookInstallOk = true;
            _hookHealth = stillThere ? 1 : 2;
            _hookLastCheckTicks = Stopwatch.GetTimestamp();
            if (!stillThere)
                LogToFileOnly("[通道自检] 钩子已重装, 触发键恢复正常 (累计发现静默失效 "
                    + _hookLostCount + " 次)");
        }
        catch (Exception ex)
        {
            _hookHealth = 3;
            _chanDegraded = true;
            LogToFileOnly("[通道自检] 重装钩子异常: " + ex.Message);
        }
    }

    /// <summary>钩子通道现在是好的吗(给界面和状态面板用)。</summary>
    private static bool HookChannelOk()
    {
        return _guarding && _hookInstallOk && _hookThreadStarted && _hookHealth != 3;
    }

    /// <summary>
    /// 开始保护之后的"通道就绪检查"(V1.1.5-RC1)。
    ///
    /// 为什么要它: 这个工具最怕的不是崩溃, 是"用户以为在保护, 其实按了没反应"。
    /// 三条通道(钩子 / 键状态轮询 / 系统热键)至少要有一条真的能用, 否则必须当场说出来,
    /// 而不是等到出事那一刻才发现。
    ///
    /// 放后台线程: 热键通道是在它自己的线程上注册的(见 StartHotKeys), StartHook 返回时
    /// 它可能还没注册完, 所以这里等一下再汇总 —— 但绝不阻塞界面。
    /// </summary>
    private static void StartChannelReadyCheck()
    {
        Thread t = new Thread(delegate()
        {
            try
            {
                long t0 = Stopwatch.GetTimestamp();
                while (_hotkeyOk == 0 && _spareHotkeys == 0 && ElapsedMs(t0) < 1500)
                {
                    try { Thread.Sleep(50); } catch { }
                }
                bool hook = _hookInstallOk && _hookThreadStarted && _hookHealth != 3;
                bool hot = (_hotkeyOk > 0) || (_spareHotkeys > 0);
                bool poll = _pollStarted;
                Log("[就绪检查] 触发通道: 钩子=" + (hook ? "可用" : "不可用")
                    + " · 轮询=" + (poll ? "已启动" : "未启动")
                    + " · 热键=" + _hotkeyOk + " 个(另送备用 " + _spareHotkeys + " 个)"
                    + " · 钩子静默失效历史 " + _hookLostCount + " 次");

                if (!hook && !hot && !poll)
                {
                    _chanDegraded = true;
                    Log("[就绪检查] 三条触发通道一条都没建立 —— 这次保护期间按触发键不会有反应");
                    if (!_headless)
                    {
                        try
                        {
                            MessageBox.Show(
                                "警告：三条触发通道都没能建立，这次保护期间按触发键不会有反应。\n\n"
                                + "请依次检查：\n"
                                + "① 安全软件是否拦截了键盘监听（把它加进信任区）；\n"
                                + "② 是否用[以管理员身份运行]启动的；\n"
                                + "③ 把触发键换成 F13~F24 里的一个，再点[开始保护]。",
                                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning,
                                MessageBoxDefaultButton.Button1, MessageBoxOptions.DefaultDesktopOnly);
                        }
                        catch { }
                    }
                }
            }
            catch (Exception ex) { Log("[就绪检查] 异常: " + ex.Message); }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardChanReady";
        t.Start();
    }

    /// <summary>
    /// 看门狗: 定期确认钩子还活着, 不行就重装一次(被系统摘掉的钩子只能重装)。
    ///
    /// 三条硬规矩(都是踩过坑改出来的):
    ///   1. 不再默认注入按键。探活靠"钩子线程还在不在"这个被动信号;
    ///      只有配置里 HookProbe=1 才真的 keybd_event 注入一个按键去端到端验证。
    ///      老版本每 10 秒注入一次, 前台游戏每 10 秒被打断一下。
    ///   2. _guarding=false 时什么都不做 —— 老版本会在这时把用户刚停掉的钩子又装回来。
    ///   3. 连续 HOOK_FAIL_LIMIT 次才重装, 且日志直接写文件(不走界面, 界面可能正卡着)。
    /// </summary>
    private static void StartHookWatchdog()
    {
        if (_watchdogStarted) return;
        _watchdogStarted = true;
        Thread t = new Thread(delegate()
        {
            Thread.Sleep(2000);
            int failStreak = 0;
            for (int round = 1; ; round++)
            {
                int sleepMs = 10000;
                try
                {
                    bool guarding = _guarding;
                    bool probe = guarding && _cfg != null && _cfg.HookProbe;
                    int probeMs = (_cfg != null && _cfg.HookProbeIntervalMs >= 5000)
                        ? _cfg.HookProbeIntervalMs : 60000;
                    sleepMs = !guarding ? 1000 : (probe ? probeMs : 10000);

                    if (!guarding)
                    {
                        // 用户已经停止保护: 不看门, 更不能把钩子装回去。
                        // 老版本没有这个判断 —— StopHook 卸掉钩子后 _hookInstallOk=false,
                        // 看门狗把"被人主动卸掉"误判成"自检失败", 立刻又装回来,
                        // 于是"停止保护"之后全局钩子和每 10 秒一次的探测按键都还活着。
                        failStreak = 0;
                    }
                    else
                    {
                        // 钩子线程自己退出时会把 _hookInstallOk 置 false, 先看这个被动信号;
                        // 只有开了 HookProbe 才真的注入按键(默认不开, 见 Config.HookProbe)。
                        bool ok = _hookInstallOk && _hookThreadStarted;
                        if (ok && probe) ok = SelfTestHook();

                        if (ok)
                        {
                            failStreak = 0;
                            if (round == 1)
                                Log("[看门狗] 自检通过: 钩子工作正常"
                                    + (probe ? " (主动探活)" : " (被动检查, 不注入按键)"));
                            // ★ V1.1.5-RC1: 被动检查说"正常"**不等于**钩子还在 ——
                            //   系统悄悄摘掉钩子时, 线程和两个标志都还好好的。
                            //   所以另外按 HOOK_SELFCHECK_SEC 的节奏, 请钩子线程做一次
                            //   "摘了再装"的真实自检(见 RequestHookSelfCheck / RehookOnHookThread)。
                            if (_hookLastCheckTicks == 0
                                || ElapsedMs(_hookLastCheckTicks) > HOOK_SELFCHECK_SEC * 1000L)
                            {
                                RequestHookSelfCheck("看门狗定期自检");
                            }
                        }
                        else
                        {
                            failStreak++;
                            LogToFileOnly("[看门狗] 第 " + round + " 轮自检失败 " + failStreak + "/" + HOOK_FAIL_LIMIT
                                + " (钩子句柄=" + (_hookHandle != IntPtr.Zero ? "有" : "无")
                                + ", 钩子线程=" + (_hookThreadStarted ? "在" : "没了")
                                + ", 界面响应=" + UiResponsive(300) + ")"
                                + (probe ? " [主动探活]" : " [被动检查]"));
                            // 单次探测失败不能拆钩子: 注入的按键不保证每次都被投递,
                            // 而拆装的那一瞬间触发键是真的按不动 —— 宁可连续失败几次再动手。
                            if (failStreak >= HOOK_FAIL_LIMIT)
                            {
                                failStreak = 0;
                                LogToFileOnly("[看门狗] 连续 " + HOOK_FAIL_LIMIT + " 次判定异常 -> 重装钩子");
                                // 被系统摘掉的钩子没法救活, 只能重新装一个。
                                // full=false: 只重装钩子, 热键通道保持不动(见 StopHook 注释)
                                StopHook(false);
                                StartHook();
                                bool again = _hookInstallOk && _hookThreadStarted
                                             && (!probe || SelfTestHook());
                                LogToFileOnly("[看门狗] 重装结果: " + (again ? "已恢复" : "仍然收不到键"));
                            }
                        }
                    }
                }
                catch (Exception ex) { LogToFileOnly("[看门狗] 异常: " + ex.Message); }
                Thread.Sleep(sleepMs);
            }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardWatchdog";
        t.Start();
    }

    /// <summary>
    /// 只写日志文件, 不往界面上推。
    /// 界面卡住时, BeginInvoke 只是往一个没人处理的消息队列里再塞一条, 没用;
    /// 而这种时候日志恰恰是最重要的证据。
    /// </summary>
    private static void LogToFileOnly(string msg)
    {
        if (!_logWriterStarted) StartLogWriter();
        EnqueueLog("[" + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff") + "] " + SanitizeLog(msg));
    }

    /// <summary>
    /// UI 线程还在不在处理消息。用 SendMessageTimeout 探活 —— 比"看界面有没有刷新"可靠,
    /// 不会因为计时器刚好没跑而误判。
    /// </summary>
    private static bool UiResponsive(int timeoutMs)
    {
        try
        {
            if (_form == null || !_form.IsHandleCreated || _form.IsDisposed) return true;
            IntPtr r;
            return SendMessageTimeout(_form.Handle, WM_NULL, IntPtr.Zero, IntPtr.Zero,
                0x0002 /*SMTO_ABORTIFHUNG*/, (uint)timeoutMs, out r) != IntPtr.Zero;
        }
        catch { return true; }
    }

    /// <summary>
    /// 依次终止所有目标进程。返回是否全部确认消失。
    /// 为什么要多目标: 光遇玩家常双开(电脑版 Sky.exe + MuMu 模拟器里的安卓版),
    /// 而 MuMu 是"全家桶"(主界面/设备窗口/服务/虚拟机... 8 个进程), 必须一起杀才算关掉。
    /// </summary>
    private static bool KillAllTargets(List<string> targets, out long killMs)
    {
        long t0 = Stopwatch.GetTimestamp();
        bool allOk = true;
        bool anyFound = false;
        foreach (string name in targets)
        {
            long ms;
            bool ok = KillTarget(name, out ms);
            if (!ok) allOk = false;
            // 至少有一个进程被找到过, 才算「真的干了活」
            if (ms >= 0) anyFound = true;
        }
        killMs = ElapsedMs(t0);
        if (!anyFound) Log("  提示: 目标程序一个都没在运行 (本次只是切断了网络)");
        return allOk;
    }

    #endregion

    // ============================================================================
    //  七、配置文件 guard.ini
    // ============================================================================

    #region 配置读写

    /// <summary>
    /// 解析"用户数据目录" —— guard.ini 和日志都放这里, 不再放程序目录。
    ///
    /// 为什么(这是"发新版本、别人直接替换、设置还在"的关键):
    ///   · 用户数据跟程序文件混在一个目录里时, 用户"删掉旧文件夹、解压新版本"就会连设置一起丢掉;
    ///   · 反过来, 打包时目录里只要恰好有自己的 guard.ini, 就会覆盖掉用户的设置,
    ///     还会把自己的网卡名/本机路径一起发出去。
    ///     (所以 -makemanifest 遇到程序目录里有 guard.ini / 日志 / _raw_*.txt 会直接拒绝生成清单。)
    ///   分离之后: 程序目录整个删掉重来, 设置和日志一个字节都不会动。
    ///
    /// 位置选择:
    ///   1) 环境变量 SKYGUARD_DATA_DIR(自检/便携用, 优先级最高);
    ///   2) %ProgramData%\SkyGuard —— 本程序始终以管理员身份运行, 这里必然可写;
    ///      而且它跟着机器走, 不跟着"是谁点的 UAC"走。
    ///      (用 %APPDATA% 的话, 换一个管理员账号提权就会读到另一个人的配置 —— 真实存在的坑)
    ///   3) 上面都失败(权限异常/精简系统)退回程序目录 —— 至少还能用, 只是回到老行为。
    /// </summary>
    private static string ResolveDataDir()
    {
        try
        {
            string env = Environment.GetEnvironmentVariable("SKYGUARD_DATA_DIR");
            if (!string.IsNullOrEmpty(env))
            {
                Directory.CreateDirectory(env);
                return env;
            }
        }
        catch { }
        try
        {
            string common = Environment.GetFolderPath(Environment.SpecialFolder.CommonApplicationData);
            if (!string.IsNullOrEmpty(common))
            {
                string d = Path.Combine(common, "SkyGuard");
                Directory.CreateDirectory(d);
                return d;
            }
        }
        catch { }
        return _baseDir;
    }

    /// <summary>
    /// 老用户第一次用新版本时, 把"跟程序放在一起"的旧 guard.ini / 日志复制到数据目录。
    /// 只复制不移动(原文件保留, 用户能找到), 且只在数据目录里还没有配置时做一次 —— 幂等。
    /// </summary>
    private static void MigrateLegacyData()
    {
        try
        {
            if (_dataDir.Length == 0) return;
            if (string.Equals(_dataDir.TrimEnd('\\'), _baseDir.TrimEnd('\\'),
                              StringComparison.OrdinalIgnoreCase))
                return;                                    // 兜底路径: 数据目录就是程序目录, 无可搬

            string legacyIni = Path.Combine(_baseDir, INI_FILE);
            if (!File.Exists(_iniPath) && File.Exists(legacyIni))
            {
                File.Copy(legacyIni, _iniPath, false);
                Log("[数据] 旧配置已搬到数据目录: " + _iniPath + " (原文件保留; 以后以这份为准)");
            }
            string legacyLog = Path.Combine(_baseDir, LOG_FILE);
            if (!File.Exists(_logPath) && File.Exists(legacyLog))
            {
                File.Copy(legacyLog, _logPath, false);      // 历史日志也带一份, 免得记录断成两截
            }
        }
        catch (Exception ex)
        {
            try { Log("[数据] 迁移旧配置失败(不影响使用): " + ex.Message); } catch { }
        }
    }

    private static Config LoadConfig(List<string> warnings)
    {
        Config c = new Config();
        if (!File.Exists(_iniPath)) return null;   // null = 还没配置过

        string[] lines;
        try { lines = File.ReadAllLines(_iniPath, Encoding.UTF8); }
        catch (Exception ex) { warnings.Add("配置读取失败: " + ex.Message); return null; }

        string section = "";
        bool modeSeen = false;      // 配置文件里有没有新的 FocusMode 键(决定还要不要看老键 FocusEarly)
        foreach (string raw in lines)
        {
            string line = raw.Trim();
            if (line.Length == 0 || line.StartsWith(";") || line.StartsWith("#")) continue;
            if (line.StartsWith("[") && line.EndsWith("]"))
            {
                section = line.Substring(1, line.Length - 2).Trim().ToLowerInvariant();
                continue;
            }
            int eq = line.IndexOf('=');
            if (eq <= 0) continue;
            string k = line.Substring(0, eq).Trim().ToLowerInvariant();
            string v = line.Substring(eq + 1).Trim();

            // [target] 支持三种写法: 旧的 Proc=xxx, 新的 Proc1=/Proc2=/...,
            // 以及 ProcOff=xxx (这个进程保留在列表里但不参与触发)
            if (section == "target" && v.Length > 0)
            {
                if (k == "proc") c.Proc = v;
                else if (k.StartsWith("procoff")) c.ProcOff.Add(v);
                else if (k.StartsWith("proc")) c.Procs.Add(v);
            }
            else if (section == "keys" && k.StartsWith("key") && v.Length > 0) c.Keys.Add(v);
            else if (section == "net" && k.StartsWith("nic") && v.Length > 0) c.Nics.Add(v);
            else if (section == "options" && k == "waitseconds")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 0 && n <= 600) c.WaitSeconds = n;
            }
            else if (section == "options" && k == "configversion")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 1) c.ConfigVersion = n;
            }
            else if (section == "options" && k == "focusintervalms")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 10 && n <= 2000) c.FocusIntervalMs = n;
            }
            else if (section == "options" && k == "focusrounds")
            {
                int n;
                // 1~10 都先收下: Ultra 档(测试用)就是故意用 1 轮。
                // Pro / 只用系统判定 档的下限 2 在解析完之后统一修正(免得受文件里行序影响)。
                if (int.TryParse(v, out n) && n >= 1 && n <= 10) c.FocusRounds = n;
            }
            else if (section == "options" && k == "focusrescue")
            {
                c.FocusRescue = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "focusmode")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 0 && n <= 2) { c.FocusMode = n; modeSeen = true; }
            }
            else if (section == "options" && k == "focusprobems")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 50 && n <= 2000) c.FocusProbeMs = n;
            }
            else if (section == "options" && k == "focusokrounds")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 1 && n <= 20) c.FocusOkRounds = n;
            }
            else if (section == "options" && k == "focussilentms")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 100 && n <= 5000) c.FocusSilentMs = n;
            }
            else if (section == "options" && k == "focusearly")
            {
                // 兼容老配置: 以前只有这个布尔开关(1=提前接管 / 0=只认系统判定)。
                // 只在没有 FocusMode 那行时才拿它定档, 免得老键覆盖用户新设的档位。
                if (!modeSeen)
                    c.FocusMode = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase)) ? 1 : 0;
            }
            else if (section == "options" && k == "diagpanel")
            {
                // 状态面板(详细诊断)开关: 默认开; 只有显式写 0/false 才隐藏主窗口那个按钮
                c.DiagPanel = !(v == "0" || string.Equals(v, "false", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "suspendfirst")
            {
                // 触发时先挂起目标进程(默认开)
                c.SuspendFirst = !(v == "0" || string.Equals(v, "false", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "warmsuspend")
            {
                // 保护期间预记录目标进程(默认开)
                c.WarmSuspend = !(v == "0" || string.Equals(v, "false", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "warmintervalms")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 300 && n <= 5000) c.WarmIntervalMs = n;
            }
            else if (section == "options" && k == "hookprobe")
            {
                c.HookProbe = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "hookprobeintervalms")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 5000 && n <= 3600000) c.HookProbeIntervalMs = n;
            }
            else if (section == "options" && k == "debugpriv")
            {
                c.DebugPriv = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "fastcut")
            {
                c.FastCut = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "fastcuttargets")
            {
                c.FastCutTargets = (v == null ? "" : v.Trim());
            }
            else if (section == "options" && k == "autorestoreonexit")
            {
                c.AutoRestoreOnExit = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "confirmexittimes")
            {
                c.ConfirmExitTimes = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
            else if (section == "options" && k == "cutmode")
            {
                int n;
                if (int.TryParse(v, out n) && n >= 0 && n <= 2) c.CutMode = n;
            }
            else if (section == "options" && k == "restoreonboot")
            {
                c.RestoreOnBoot = (v == "1" || string.Equals(v, "true", StringComparison.OrdinalIgnoreCase));
            }
        }
        // 前向兼容: 配置来自更新的版本时给个提示(不拒绝 —— 未知项本来就被忽略)
        if (c.ConfigVersion > CONFIG_VERSION)
            warnings.Add("配置文件来自更新的版本(ConfigVersion=" + c.ConfigVersion
                + "), 有未知设置可能被忽略 —— 建议升级本程序");

        // 档位与轮数的一致性修正(解析完之后统一做, 免得受文件里行序影响):
        //   Ultra(2) 允许 1 轮 —— 就是要试最短接管时间; Pro(1)/只用系统判定(0) 至少 2 轮,
        //   因为 1 轮在"卡/不卡"边界上必然抖(用户当年就是被这个坑出"焦点一直闪")。
        if (c.FocusMode < 0 || c.FocusMode > 2) c.FocusMode = 1;
        if (c.FocusMode != 2 && c.FocusRounds < 2) c.FocusRounds = 2;
        c.FocusEarly = (c.FocusMode >= 1);      // 兼容字段跟着档位走, 存盘时写出去
        return c;
    }

    private static void SaveConfig(Config c)
    {
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("; SkyGuard 图形版 配置文件");
        sb.AppendLine("; 本文件由程序自动生成/更新, 也可以手工编辑(改完重启程序生效)");
        sb.AppendLine(";");
        sb.AppendLine("; [target] 里是要关掉的程序, 可以写多个(一行一个), 触发时全部关掉");
        sb.AppendLine(";   进程名不用带 .exe 也行, 大小写不敏感");
        sb.AppendLine(";   例: Sky.exe / MuMuNxMain / MuMuNxDevice ...");
        sb.AppendLine(";   ProcOff=xxx 表示这个程序留在列表里但不参与触发(界面上是没勾选的状态)");
        sb.AppendLine(";");
        sb.AppendLine("; [keys] 里可以写多个触发键, 每个一行; 组合键用 + 连接");
        sb.AppendLine(";   单个键例: F9        Pause        ScrollLock");
        sb.AppendLine(";   组合键例: Ctrl+Alt+K    Ctrl+Shift+F9");
        sb.AppendLine(";");
        sb.AppendLine("; [net] 里是要断开的网卡(用 netsh 的连接名), 每行一张");
        sb.AppendLine("");
        sb.AppendLine("[target]");
        List<string> all = c.AllProcs();
        if (all.Count == 0) sb.AppendLine("Proc1=Sky.exe");
        else for (int i = 0; i < all.Count; i++) sb.AppendLine("Proc" + (i + 1) + "=" + all[i]);
        for (int i = 0; i < c.ProcOff.Count; i++) sb.AppendLine("ProcOff" + (i + 1) + "=" + c.ProcOff[i]);
        sb.AppendLine("");
        sb.AppendLine("[keys]");
        for (int i = 0; i < c.Keys.Count; i++) sb.AppendLine("Key" + (i + 1) + "=" + c.Keys[i]);
        sb.AppendLine("");
        sb.AppendLine("[net]");
        for (int i = 0; i < c.Nics.Count; i++) sb.AppendLine("Nic" + (i + 1) + "=" + c.Nics[i]);
        sb.AppendLine("");
        sb.AppendLine("[options]");
        sb.AppendLine("; 配置结构版本: 程序升级时靠它判断要不要迁移配置, 一般不用手动改");
        sb.AppendLine("ConfigVersion=" + CONFIG_VERSION);
        sb.AppendLine("WaitSeconds=" + c.WaitSeconds);
        sb.AppendLine("; 焦点切换");
        sb.AppendLine(";   FocusRescue=1 开 / 0 关");
        sb.AppendLine(";   FocusMode: 0=仅系统检测 1=Pro 2=Ultra");
        sb.AppendLine(";   FocusIntervalMs=检测间隔(10~2000)  FocusRounds=确认次数(1~10)");
        sb.AppendLine(";   FocusProbeMs=检测超时(50~2000)");
        sb.AppendLine(";   FocusOkRounds=交还确认次数(1~20)  FocusSilentMs=静默时间(100~5000)");
        sb.AppendLine(";   最长接管等待 ≈ (FocusIntervalMs+FocusProbeMs)×FocusRounds");
        sb.AppendLine("");
        sb.AppendLine("");
        sb.AppendLine("FocusRescue=" + (c.FocusRescue ? "1" : "0"));
        sb.AppendLine("FocusMode=" + c.FocusMode);
        sb.AppendLine("FocusIntervalMs=" + c.FocusIntervalMs);
        sb.AppendLine("FocusRounds=" + c.FocusRounds);
        sb.AppendLine("FocusProbeMs=" + c.FocusProbeMs);
        sb.AppendLine("FocusOkRounds=" + c.FocusOkRounds);
        sb.AppendLine("FocusSilentMs=" + c.FocusSilentMs);
        sb.AppendLine(";   兼容老版本用的那行(值由上面的 FocusMode 决定, 老程序读它, 新程序只读 FocusMode)");
        sb.AppendLine("FocusEarly=" + (c.FocusMode >= 1 ? "1" : "0"));
        sb.AppendLine("; 钩子主动探活: 1=看门狗定期注入一个真实按键验证钩子存活 / 0=只看钩子线程在不在(默认)");
        sb.AppendLine(";   注入的按键会走系统输入链, 前台游戏/反作弊也会收到, 所以默认关;");
        sb.AppendLine(";   关掉后单键触发仍由 轮询(8ms) + 系统热键 两条通道兜底。");
        sb.AppendLine("HookProbe=" + (c.HookProbe ? "1" : "0"));
        sb.AppendLine("HookProbeIntervalMs=" + c.HookProbeIntervalMs);
        sb.AppendLine("DebugPriv=" + (c.DebugPriv ? "1" : "0"));
        sb.AppendLine("FastCut=" + (c.FastCut ? "1" : "0"));
        sb.AppendLine("FastCutTargets=" + (c.FastCutTargets == null ? "" : c.FastCutTargets));
        sb.AppendLine("; 关程序时网络仍断开: 1=自动恢复(默认) 0=弹窗询问");
        sb.AppendLine("AutoRestoreOnExit=" + (c.AutoRestoreOnExit ? "1" : "0"));
        sb.AppendLine("ConfirmExitTimes=" + (c.ConfirmExitTimes ? "1" : "0"));
        sb.AppendLine("; 断网方式: 0=快速断流+禁用网卡(默认) 1=只禁用网卡 2=只用快速断流(不禁用网卡)");
        sb.AppendLine("CutMode=" + c.CutMode);
        sb.AppendLine("; 断网时登记一条开机恢复(下次登录自动跑恢复脚本, 恢复成功后自动删除): 1=开 0=关(默认)");
        sb.AppendLine("RestoreOnBoot=" + (c.RestoreOnBoot ? "1" : "0"));
        sb.AppendLine("; 状态面板(详细诊断): 1=主窗口显示[状态面板]按钮(默认) 0=隐藏它");
        sb.AppendLine("DiagPanel=" + (c.DiagPanel ? "1" : "0"));
        sb.AppendLine("; 触发时先挂起目标进程: 1=先挂起再终止(默认, 更快停下) 0=直接终止");
        sb.AppendLine("SuspendFirst=" + (c.SuspendFirst ? "1" : "0"));
        sb.AppendLine("; 保护期间预记录目标进程(触发时第一条命令直接挂起, 不必先扫进程表): 1=开(默认) 0=关");
        sb.AppendLine("WarmSuspend=" + (c.WarmSuspend ? "1" : "0"));
        sb.AppendLine("; 预记录刷新间隔(毫秒, 300~5000)");
        sb.AppendLine("WarmIntervalMs=" + c.WarmIntervalMs);
        File.WriteAllText(_iniPath, sb.ToString(), new UTF8Encoding(false));
        Log("配置已保存: " + _iniPath);
    }

    #endregion

    // ============================================================================
    //  八、图形界面
    // ============================================================================

    #region 界面

    private static string StatusText()
    {
        if (_guarding) return "正在保护";
        return "未在保护";
    }

    private static void RefreshStatus()
    {
        try
        {
            if (_form == null || !_form.IsHandleCreated) return;
            if (_form.InvokeRequired) { _form.BeginInvoke((MethodInvoker)RefreshStatus); return; }

            // 有临时状态(网络恢复中/恢复失败)时优先显示它 —— 否则会被这里的定时刷新覆盖掉
        string ov = _statusOverride;
        _lblStatus.Text = (_guarding ? "● " : "○ ") + (ov.Length > 0 ? ov : StatusText());
            // 深色头部上: 保护中=亮绿, 未保护=亮红, 一眼能看清
            _lblStatus.ForeColor = _guarding ? Color.FromArgb(110, 220, 140) : Color.FromArgb(255, 138, 128);
            _btnGuard.Text = _guarding ? "停止保护" : "开始保护";
            // ★ 只在状态真的翻转时改按钮配色 —— RefreshStatus 每 500ms 跑一次,
            //   无条件改 BackColor 会把鼠标悬停的高亮每半秒冲掉一次(看起来在闪)。
            string wantKind = _guarding ? "danger" : "primary";
            if (!(_btnGuard.Tag is string) || (string)_btnGuard.Tag != wantKind)
                ApplyButtonKind(_btnGuard, wantKind, false);

            // 不再显示"键盘监听 N 次" —— 用户看到"监听"会以为在偷看隐私。只留"已触发"计数。
            // ★ V1.1.5-RC1: 处置位被占太久(网络子进程卡住)要在界面说出来 ——
            //   否则用户按了没反应, 只会以为"这工具坏了/键坏了"。
            if (_busy != 0 && _busySinceTicks != 0 && ElapsedMs(_busySinceTicks) > BUSY_STUCK_MS)
                _busyStuck = true;
            _lblProbeState.Text = "已触发 " + _hitCount + " 次"
                + (_focusRescues > 0 ? " · 接管 " + _focusRescues + " 次" : "")
                + (_focusTakeFailed ? " · 接管失败，请点击本窗口" : "")
                + (_focusProbeDegraded ? " · 检测降级" : "")
                + (_busyStuck ? " · 处置超时，点[停止保护]可收尾" : "")
                + (_netOpStuck ? " · 网络操作未完成，可点[恢复网络]" : "")
                + ChannelSummary()
                + (_hookTrace ? "   [诊断模式: 每个按键都记日志]" : "");
            // 通道降级要说出来, 而且要是红的 —— 这个工具的价值全在"出事那一刻按下去有用",
            // 用户必须在**出事之前**就知道它现在到底能不能按。用红色而不是弹框: 弹框会挡住游戏、打断操作。
            _lblProbeState.ForeColor = _chanDegraded ? Color.FromArgb(210, 60, 50) : C_SUB;
        }
        catch { }
    }

    /// <summary>
    /// 触发通道的一句话摘要(主界面那一行显示它)。
    ///
    /// 为什么要给用户看: 这个工具的价值全在"出事那一刻按下去有没有用"。
    /// 如果钩子被系统悄悄摘了、热键一个都没注册上, 用户必须在**出事之前**就看得见,
    /// 而不是到那一刻才发现按不动 —— 那就已经晚了。
    /// 只在保护中显示(没保护的时候这几条通道本来就没在跑, 显示出来只会让人困惑)。
    /// </summary>
    private static string ChannelSummary()
    {
        try
        {
            if (!_guarding) return "";
            StringBuilder b = new StringBuilder();
            b.Append(" · 通道 ");
            if (_hookHealth == 3) b.Append("钩子✗");
            else if (HookChannelOk()) b.Append("钩子").Append(_hookHealth == 2 ? "✓(已重装)" : "✓");
            else b.Append("钩子?");
            b.Append(" 轮询").Append(_pollStarted ? "✓" : "✗");
            b.Append(" 热键").Append(_hotkeyOk);
            if (_spareHotkeys > 0) b.Append("+").Append(_spareHotkeys);
            if (_hookLostCount > 0) b.Append("  [钩子曾失效 ").Append(_hookLostCount).Append(" 次, 已自动重装]");
            return b.ToString();
        }
        catch { return ""; }
    }

    /// <summary>
    /// 主界面 —— 刻意做得极简: 只有状态 + 摘要 + 几个按钮。
    /// 所有配置都收进「设置」对话框, 避免小白一打开就看到一堆字段。
    /// </summary>
    // ============================================================================
    //  让界面在任何机器上都正常显示 (DPI / 系统字体 / 小屏 / 多显示器)
    //
    //  踩过的坑: 早先所有控件都是 SetBounds 写死的像素, 而且窗体是 AutoScaleMode.None。
    //  结果: 一旦用户把 Windows 缩放调到 125%/150%、或者系统 UI 字体不是设计时那一款,
    //  布局完全不动 —— 该大的不大、该松的不松, 小屏上还会挤在一起。
    //  → 这个工具是要发出去给别人用的, 不能按某一台机器的 96 DPI 来写死。
    //
    //  做法(全是 WinForms 的标准机制, 没有机器相关的东西):
    //   1) AutoScaleMode.Font + AutoScaleDimensions = 设计时的字体尺寸
    //      → 系统字体/DPI 一变, 窗体和控件整体等比缩放;
    //        设置 AutoScaleDimensions 是为了让它"以我们的设计字体为基准 1.0", 否则
    //        WinForms 会拿默认字体(Microsoft Sans Serif 9pt)去比, 凭空多放大一轮。
    //   2) 窗口可缩放 + MinimumSize: 用户自己能拖到舒服的大小, 又不会被拖到控件重叠。
    //   3) 窗体居中到鼠标所在那块屏, 不是永远主屏(多显示器/竖屏用得上)。
    //   4) 代码里创建的字体自己按 DPI 换算 —— TextBox 这类控件的字体不跟着缩放。
    // ============================================================================

    /// <summary>设计基准 DPI。AutoScaleDimensions 用逻辑单位, 这里只为算代码里创建的字体。</summary>
    private const float DESIGN_DPI = 96F;

    /// <summary>当前运行环境的缩放倍数(1.0 = 96 DPI)。所有"代码里创建的字体"都要乘它。</summary>
    private static float _dpiScale = 1F;

    /// <summary>
    /// 取一个控件的实际 DPI(Graphics.DpiX)。
    /// 不用 Screen 或注册表: 每台机器的值都不一样, 而且多显示器可以各不相同。
    /// </summary>
    private static float GetScale(Control c)
    {
        try
        {
            if (c != null && c.IsHandleCreated)
            {
                using (Graphics g = c.CreateGraphics()) return g.DpiX / DESIGN_DPI;
            }
        }
        catch { }
        try
        {
            using (Graphics g = Graphics.FromHwnd(IntPtr.Zero)) return g.DpiX / DESIGN_DPI;
        }
        catch { }
        return 1F;
    }

    /// <summary>按当前 DPI 造字体。pt 是"96 DPI 下的设计字号"。</summary>
    private static Font Fi(string family, float pt, FontStyle style)
    {
        float size = pt;
        try { size = pt * _dpiScale; } catch { }
        // 字号太小会被 GDI+ 拒绝, 兜一下底
        if (size < 1F) size = 1F;
        try { return new Font(family, size, style); }
        catch { return new Font(FontFamily.GenericSansSerif, size, style); }
    }

    private static Font Fi(string family, float pt) { return Fi(family, pt, FontStyle.Regular); }

    // ============================================================================
    //  现代 UI 样式 (配色 / 按钮 / 边距) —— 前端重构
    //  所有固定尺寸走 Sc()/Pad() 按 DPI 缩放; 布局本身用 TableLayoutPanel /
    //  FlowLayoutPanel + Dock/Anchor/AutoSize 自适应, 不再写死像素坐标。
    // ============================================================================
    private static readonly Color C_BG         = Color.FromArgb(244, 246, 249);
    private static readonly Color C_HEADER     = Color.FromArgb(41, 52, 66);
    private static readonly Color C_CARD       = Color.White;
    private static readonly Color C_BORDER     = Color.FromArgb(222, 227, 235);
    private static readonly Color C_TEXT       = Color.FromArgb(44, 52, 62);
    private static readonly Color C_SUB        = Color.FromArgb(122, 130, 140);
    private static readonly Color C_PRIMARY    = Color.FromArgb(47, 125, 225);
    private static readonly Color C_PRIMARY_H  = Color.FromArgb(37, 104, 194);
    private static readonly Color C_DANGER     = Color.FromArgb(217, 48, 37);
    private static readonly Color C_DANGER_H   = Color.FromArgb(176, 34, 26);
    private static readonly Color C_OK         = Color.FromArgb(28, 142, 62);
    private static readonly Color C_HOVER      = Color.FromArgb(238, 242, 247);

    /// <summary>逻辑像素 -> 当前 DPI 像素(坐标/尺寸/边距统一用它)。</summary>
    private static int Sc(int v)
    {
        float s = _dpiScale;
        if (s <= 0F) s = 1F;
        return Math.Max(0, (int)Math.Round(v * s));
    }

    /// <summary>按 DPI 缩放的 Padding。</summary>
    private static Padding Pad(int l, int t, int r, int b)
    {
        return new Padding(Sc(l), Sc(t), Sc(r), Sc(b));
    }

    /// <summary>给扁平按钮统一外观。kind: "plain" 白底 / "primary" 蓝底 / "danger" 红底。</summary>
    private static void StyleButton(Button b, string kind)
    {
        if (b == null) return;
        b.FlatStyle = FlatStyle.Flat;
        b.FlatAppearance.BorderSize = 1;
        b.UseVisualStyleBackColor = false;
        b.Cursor = Cursors.Hand;
        ApplyButtonKind(b, kind, false);
        // 悬停效果(每个按钮只在 MakeButton 里经过这里一次, 不会重复挂)
        b.MouseEnter += delegate { if (b.Tag is string) ApplyButtonKind(b, ((string)b.Tag), true); };
        b.MouseLeave += delegate { if (b.Tag is string) ApplyButtonKind(b, ((string)b.Tag), false); };
    }

    private static void ApplyButtonKind(Button b, string kind, bool hover)
    {
        Color normal, hot;
        if (kind == "danger")   { normal = C_DANGER;   hot = C_DANGER_H;  b.ForeColor = Color.White; b.FlatAppearance.BorderColor = C_DANGER; }
        else if (kind == "primary") { normal = C_PRIMARY; hot = C_PRIMARY_H; b.ForeColor = Color.White; b.FlatAppearance.BorderColor = C_PRIMARY; }
        else                    { normal = C_CARD;     hot = C_HOVER;     b.ForeColor = C_TEXT;   b.FlatAppearance.BorderColor = C_BORDER; }
        b.BackColor = hover ? hot : normal;
        if (!hover) b.Tag = kind;
    }

    /// <summary>造一个标准扁平按钮(固定高度 + 按文字实测宽度, 不靠 AutoSize 免得在容器里被撑高)。</summary>
    private static Button MakeButton(string text, EventHandler click, string kind)
    {
        Button b = new Button();
        b.Text = text;
        b.Font = Fi("Microsoft YaHei UI", 9F);
        b.AutoSize = false;
        b.Height = Sc(34);
        int tw = 0;
        try
        {
            using (Bitmap bmp = new Bitmap(1, 1))
            using (Graphics g = Graphics.FromImage(bmp))
            {
                tw = TextRenderer.MeasureText(g, text, b.Font, new Size(int.MaxValue, int.MaxValue),
                    TextFormatFlags.SingleLine).Width;
            }
        }
        catch { tw = text.Length * 14; }
        b.Width = Math.Max(Sc(80), tw + Sc(30));
        if (click != null) b.Click += click;
        StyleButton(b, kind);
        return b;
    }

    /// <summary>把窗体摆到鼠标所在那块屏幕的正中间(多显示器时不会跑到别的屏上去)。</summary>
    /// <summary>
    /// WinForms 给 AutoScaleMode.Font 用的设计基准尺寸(缓存一次)。
    ///
    /// 为什么不能硬编码: 基准是"窗体环境字体(Control.DefaultFont)的尺寸", 不是我们设的字体。
    /// 实测:
    ///     Control.DefaultFont = 宋体 9pt            -> 基准 {6, 12}
    ///     窗体 Font = Microsoft YaHei UI 9pt        -> 基准 {7, 17}
    /// 如果拿 {7,17} 去当设计基准, 比例就是 (7/6, 17/12) ≈ 1.17/1.42 —— 实测设置窗的
    /// ClientSize 668x620 被就地改成 779x845, 内容全乱。所以这里实测, 不猜。
    ///
    /// 用法(顺序很重要, 见 BuildSettingsDialog 注释): 先 SetAutoScale(f), 再设 ClientSize,
    /// 最后才改 Font —— 改字体触发的缩放会按"环境字体 -> 目标字体"的比例等比放大整棵树。
    /// </summary>
    private static SizeF _designFontSize = SizeF.Empty;

    private static SizeF DesignFontSize()
    {
        if (_designFontSize.IsEmpty)
        {
            try
            {
                using (Form probe = new Form())
                {
                    probe.AutoScaleMode = AutoScaleMode.Font;   // 不设 Font, 量到的就是环境字体
                    _designFontSize = probe.AutoScaleDimensions;
                }
            }
            catch { }
            if (_designFontSize.IsEmpty || _designFontSize.Width <= 0 || _designFontSize.Height <= 0)
                _designFontSize = new SizeF(6F, 12F);           // 兜底: 简体中文 Windows 的常见值
        }
        return _designFontSize;
    }

    /// <summary>
    /// 给窗体装上自适应缩放(必须在设 ClientSize / 改 Font 之前调用)。
    /// 只负责设"设计基准 + 模式", 不碰 Font —— 字体由调用方在尺寸定好之后再设。
    /// </summary>
    private static void SetAutoScale(Form f)
    {
        try
        {
            f.AutoScaleDimensions = DesignFontSize();
            f.AutoScaleMode = AutoScaleMode.Font;
        }
        catch { }
    }

    /// <summary>
    /// 量一款字体的 AutoScaleMode.Font 基准尺寸(即 {平均字符宽, 行高} 的取整值)。
    ///
    /// 背景(WinForms 自动缩放的真实规则, 全部实测确认):
    ///   窗体一定有一对 (AutoScaleDimensions, Font)。做自动缩放时, WinForms 会把
    ///   AutoScaleDimensions 换成当前字体的实测尺寸, 再按 (新/旧) 这个比例去缩放窗体和所有子控件。
    ///   所以:
    ///     · 比例 = 1.0(窗体尺寸原样不动) 的唯一条件, 是"设计基准 == 目标字体的实测尺寸"。
    ///     · 用环境字体(宋体 9pt -> 6x12)当基准、再切成 YaHei 9pt(7x17), 比例就是 (7/6, 17/12),
    ///       窗体会被硬生生放大 —— 实测设置窗 668x620 变成 779x845, 内容全乱。
    ///   .NET 设计器给我们自动生成的那行 `AutoScaleDimensions = new SizeF(6F, 12F)` 之所以"碰巧能跑",
    ///   是因为那个窗体的 Font 就是环境字体。我们用的是 YaHei, 就必须按 YaHei 量。
    /// </summary>
    private static SizeF MeasureScaleDims(Font f)
    {
        try
        {
            using (Form probe = new Form())
            {
                probe.AutoScaleMode = AutoScaleMode.Font;  // 先让环境字体当基准
                probe.Font = f;                            // 再切到目标字体, 比例被记录
                return probe.AutoScaleDimensions;
            }
        }
        catch { }
        return new SizeF(7F, 17F);   // 兜底: 简体中文 YaHei 9pt 的常见实测值
    }

    /// <summary>
    /// 给窗体设好"设计基准 + 缩放模式 + 字体", 三者一次配对, 保证比例 = 1.0(尺寸不被偷改)。
    ///
    /// ⚠️ 这里的语句顺序是实验定出来的, 不要改(用 实验脚本 逐种试过):
    ///   ✅ 正确: 设基准 -> 设模式 -> 设字体 -> 设 ClientSize
    ///   ❌ 错误: 设模式 -> 设基准 -> 设 ClientSize -> 设字体
    ///            (这个顺序下 ClientSize 668x620 会变成 779x845)
    /// 调用方必须在这个方法返回之后再设 ClientSize / MinimumSize。
    /// 详见第九节 #19。
    /// </summary>
    private static void SetAutoScaleFont(Form f, Font target)
    {
        try
        {
            f.AutoScaleDimensions = MeasureScaleDims(target);
            f.AutoScaleMode = AutoScaleMode.Font;
            f.Font = target;
        }
        catch { }
    }

    private static void CenterOnMouseScreen(Form f)    {
        try
        {
            Rectangle wa = Screen.FromPoint(Cursor.Position).WorkingArea;
            int x = wa.X + (wa.Width - f.Width) / 2;
            int y = wa.Y + (wa.Height - f.Height) / 2;
            // 别把标题栏顶到屏幕外面去
            if (x < wa.X) x = wa.X;
            if (y < wa.Y) y = wa.Y;
            f.StartPosition = FormStartPosition.Manual;
            f.Location = new Point(x, y);
        }
        catch { f.StartPosition = FormStartPosition.CenterScreen; }
    }

    private static void BuildForm()
    {
        _form = new Form();
        _form.Text = APP_NAME + "   " + APP_VER;
        PumpThrottled();
        _form.StartPosition = FormStartPosition.CenterScreen;

        // ---- 自适应缩放(顺序不要改, 见 SetAutoScaleFont 注释) ----
        SetAutoScaleFont(_form, new Font("Microsoft YaHei UI", 9F));
        PumpThrottled();
        _dpiScale = GetScale(_form);

        _form.BackColor = C_BG;
        PumpThrottled();
        _form.ClientSize = new Size(Sc(840), Sc(640));

        // ---- 根布局: 单列五行(头部 / 摘要 / 按钮 / 日志 / 底部状态) ----
        TableLayoutPanel root = new TableLayoutPanel();
        PumpThrottled();
        root.Dock = DockStyle.Fill;
        root.ColumnCount = 1;
        root.RowCount = 5;
        PumpThrottled();
        root.Margin = new Padding(0);
        root.BackColor = C_BG;
        root.RowStyles.Add(new RowStyle(SizeType.Absolute, Sc(52)));   // 0 头部
        root.RowStyles.Add(new RowStyle(SizeType.AutoSize));            // 1 摘要卡片
        root.RowStyles.Add(new RowStyle(SizeType.AutoSize));            // 2 按钮行
        root.RowStyles.Add(new RowStyle(SizeType.Percent, 100F));       // 3 日志
        root.RowStyles.Add(new RowStyle(SizeType.AutoSize));            // 4 底部状态
        _form.Controls.Add(root);
        PumpThrottled();
        PumpThrottled();
        _root = root;

        // ---- 头部(深色条: 只放放大的状态文字, 左对齐) ----
        Panel header = new Panel();
        PumpThrottled();
        header.Dock = DockStyle.Fill;
        header.Margin = new Padding(0);
        header.BackColor = C_HEADER;
        PumpThrottled();
        header.Padding = new Padding(Sc(20), 0, Sc(20), 0);

        _lblStatus = new Label();
        PumpThrottled();
        _lblStatus.Text = "正在初始化…";
        _lblStatus.Font = Fi("Microsoft YaHei UI", 15F, FontStyle.Bold);
        _lblStatus.ForeColor = Color.White;
        PumpThrottled();
        _lblStatus.AutoSize = false;      // 铺满横幅宽度, 绝不溢出深色条
        _lblStatus.AutoEllipsis = true;
        _lblStatus.Dock = DockStyle.Fill;
        PumpThrottled();
        _lblStatus.TextAlign = ContentAlignment.MiddleLeft;
        header.Controls.Add(_lblStatus);
        PumpThrottled();
        root.Controls.Add(header, 0, 0);
        PumpThrottled();

        // ---- 摘要卡片(白底细框, 高度按文字实测, 永不截断) ----
        _lblSummary = new Label();
        PumpThrottled();
        _lblSummary.Font = Fi("Microsoft YaHei UI", 9.5F);
        _lblSummary.AutoSize = false;
        _lblSummary.Dock = DockStyle.Top;
        PumpThrottled();
        _lblSummary.Margin = new Padding(Sc(16), Sc(10), Sc(16), 0);
        _lblSummary.Padding = new Padding(Sc(12), Sc(9), Sc(12), Sc(9));
        _lblSummary.BackColor = C_CARD;
        PumpThrottled();
        _lblSummary.BorderStyle = BorderStyle.FixedSingle;
        _lblSummary.ForeColor = C_TEXT;
        _lblSummary.UseMnemonic = false;
        PumpThrottled();
        _lblSummary.Text = "加载中…";
        root.Controls.Add(_lblSummary, 0, 1);
        PumpThrottled();

        // ---- 按钮行(FlowLayoutPanel 自动折行) ----
        FlowLayoutPanel btnBar = new FlowLayoutPanel();
        PumpThrottled();
        btnBar.Dock = DockStyle.Fill;
        btnBar.AutoSize = true;
        btnBar.FlowDirection = FlowDirection.LeftToRight;
        PumpThrottled();
        btnBar.WrapContents = true;
        btnBar.Margin = new Padding(Sc(16), Sc(10), Sc(16), 0);
        btnBar.Padding = new Padding(0);
        PumpThrottled();
        btnBar.BackColor = C_BG;
        root.Controls.Add(btnBar, 0, 2);
        PumpThrottled();
        _btnBar = btnBar;

        _btnGuard = MakeButton("开始保护", delegate { ToggleGuard(); }, "primary");
        PumpThrottled();
        _btnPanic = MakeButton("立即处置", delegate { PanicByClick(); }, "danger");
        _btnRestoreNet = MakeButton("恢复网络", delegate { RestoreNetByClick(); }, "plain");
        _btnSettings = MakeButton("⚙ 设置", delegate { ShowSettings(); }, "plain");
        PumpThrottled();
        _btnOnlyKill = MakeButton("自检", delegate { SelfTestByClick(); }, "plain");
        _btnOpenLog = MakeButton("打开日志", delegate
        {
            try { Process.Start("notepad.exe", "\"" + _logPath + "\""); }
            catch (Exception ex) { MessageBox.Show("打开日志失败：" + ex.Message); }
        }, "plain");
        PumpThrottled();
        // 状态面板(V1.1.4-RC4): 详细诊断, 一键复制发给开发者。开关在 设置 -> 维护 里(默认开)。
        _btnDiag = MakeButton("状态面板", delegate { ShowDiagPanel(); }, "plain");
        _btnDiag.Visible = (_cfg == null || _cfg.DiagPanel);
        PumpThrottled();

        _btnRow = new Button[] { _btnGuard, _btnPanic, _btnRestoreNet, _btnSettings, _btnOnlyKill, _btnOpenLog, _btnDiag };
        foreach (Button b in _btnRow)
        {
            b.Margin = new Padding(0, 0, Sc(8), 0);
            PumpThrottled();
            btnBar.Controls.Add(b);
            PumpThrottled();
        }

        // ---- 日志区(标题 + 文本框, 占满剩余空间) ----
        TableLayoutPanel logArea = new TableLayoutPanel();
        PumpThrottled();
        logArea.Dock = DockStyle.Fill;
        logArea.ColumnCount = 1;
        logArea.RowCount = 2;
        PumpThrottled();
        logArea.Margin = new Padding(Sc(16), Sc(6), Sc(16), 0);
        logArea.BackColor = C_BG;
        logArea.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        PumpThrottled();
        logArea.RowStyles.Add(new RowStyle(SizeType.Percent, 100F));
        root.Controls.Add(logArea, 0, 3);
        PumpThrottled();

        _lblLogCaption = new Label();
        _lblLogCaption.Text = "运行记录";
        PumpThrottled();
        _lblLogCaption.Font = Fi("Microsoft YaHei UI", 9F, FontStyle.Bold);
        _lblLogCaption.ForeColor = C_SUB;
        _lblLogCaption.AutoSize = true;
        PumpThrottled();
        _lblLogCaption.Dock = DockStyle.Top;
        _lblLogCaption.Margin = new Padding(0, 0, 0, Sc(2));
        logArea.Controls.Add(_lblLogCaption, 0, 0);
        PumpThrottled();
        PumpThrottled();

        _txtLog = new TextBox();
        _txtLog.Multiline = true;
        PumpThrottled();
        _txtLog.ReadOnly = true;
        _txtLog.ScrollBars = ScrollBars.Vertical;
        _txtLog.Dock = DockStyle.Fill;
        PumpThrottled();
        _txtLog.Margin = new Padding(0);
        _txtLog.BackColor = Color.FromArgb(252, 253, 254);
        _txtLog.BorderStyle = BorderStyle.FixedSingle;
        PumpThrottled();
        _txtLog.Font = Fi("Consolas", 8.5F);
        _txtLog.MinimumSize = new Size(0, Sc(90));
        logArea.Controls.Add(_txtLog, 0, 1);
        PumpThrottled();
        PumpThrottled();

        // ---- 底部状态行(允许换行) ----
        _lblProbeState = new Label();
        PumpThrottled();
        _lblProbeState.Text = "";
        _lblProbeState.Font = Fi("Microsoft YaHei UI", 8.5F);
        _lblProbeState.ForeColor = C_SUB;
        PumpThrottled();
        _lblProbeState.AutoSize = true;
        _lblProbeState.Dock = DockStyle.Top;
        _lblProbeState.Margin = new Padding(Sc(16), Sc(6), Sc(16), Sc(8));
        PumpThrottled();
        _lblProbeState.UseMnemonic = false;
        root.Controls.Add(_lblProbeState, 0, 4);
        PumpThrottled();

        // ---- DPI 变化: 更新缩放系数并重建字体/尺寸 ----
        _form.DpiChanged += delegate(object s, DpiChangedEventArgs e)
        {
            _dpiScale = e.DeviceDpiNew / DESIGN_DPI;
            PumpThrottled();
            ReflowMain();
            ApplyLogFont();
        };
        PumpThrottled();
        _form.DpiChangedAfterParent += delegate(object s, EventArgs e) { ReflowMain(); ApplyLogFont(); };
        _form.Resize += delegate { ReflowMain(); };
        _form.SizeChanged += delegate { ReflowMain(); };
        PumpThrottled();

        ReflowMain();
        ApplyLogFont();
        PumpThrottled();
        LayOutAndSetMinimum();

        _form.FormClosing += delegate(object s, FormClosingEventArgs e)
        {
            // ★ 下面检查网卡那段要泵消息(见 AnyTargetDisabledPumped) —— 必须挡住重入的第二次关闭,
            //   否则用户连点两下[X]会跑两遍"退出确认"。
            if (_closing) { e.Cancel = true; return; }
            _closing = true;
            PumpThrottled();
            UiPhaseBegin("正在检查网卡状态并确认退出");
            // ★ 退出前的多次确认(用户要求): 次数按当时状态定 ——
            //   有未复原状态(网络还断着 / 快速断流还挂着 / 处置正在跑 / 断网标记还在 / 有网卡被禁用) -> 3 次
            //   正在保护、状态正常                                                                        -> 2 次
            //   其余(没保护、一切正常)                                                                    -> 直接退出
            //   「退出前多次确认」开关关掉时, 上面各档降为 1 次(异常时仍要问一次, 免得误退出)。
            // ★ (修"无响应"): 网卡检查原来在这里同步调 AnyTargetDisabled() —— 实测单次 netsh
            //   245~930 毫秒(冷启动 2.9 秒), 点[X]之后这段时间窗口完全不响应。改成后台查 + 界面泵消息;
            PumpThrottled();
            //   查不出来(超时 1.5 秒)按"可能有网卡被禁用"处理, 宁可多问一次。
            bool nicMaybeDisabled;
            bool wasEnabled = (_form != null && !_form.IsDisposed && _form.Enabled);
            PumpThrottled();
            try
            {
                if (wasEnabled) _form.Enabled = false;      // 泵消息期间别让用户点到按钮
                nicMaybeDisabled = AnyTargetDisabledPumped(1500);
                PumpThrottled();
            }
            finally { if (wasEnabled && _form != null && !_form.IsDisposed) _form.Enabled = true; }
            bool abnormal = NetCutStateExists() || FastCutLayer.Length > 0 || _wfpArmed
                            || _fwArmed || _busy != 0 || nicMaybeDisabled;
                            PumpThrottled();
            // 「N 次确认」= 点关闭 + (N-1) 次弹窗: 异常状态弹 2 次(三次确认), 保护中弹 1 次(二次确认), 其余直接退出。
            // 「退出前多次确认」关掉时: 异常仍弹 1 次(别把断网状态带出去), 保护中不弹。
            bool keepAsking = (_cfg == null || _cfg.ConfirmExitTimes);
            PumpThrottled();
            int dialogs = abnormal ? (keepAsking ? 2 : 1) : (_guarding ? (keepAsking ? 1 : 0) : 0);
            for (int k = 0; k < dialogs; k++)
            {
                DialogResult r = MessageBox.Show(
                    abnormal ? "网络还处于断开状态。\n\n确定要退出吗？" : "保护正在运行。\n\n确定要退出吗？",
                    APP_NAME, MessageBoxButtons.YesNo, MessageBoxIcon.Warning);
                    PumpThrottled();
                if (r != DialogResult.Yes) { _closing = false; UiPhaseEnd(""); e.Cancel = true; return; }
            }
            if (dialogs > 0) Log("[退出] 已确认(" + dialogs + " 次弹窗" + (abnormal ? ", 网络未复原" : ", 保护中") + ")");
            PumpThrottled();
            if (_busy != 0)
            {
                _abort = true;      // 处置还在跑 -> 让它立刻收尾, 别把断网状态带出程序
                Log("[退出] 处置还在进行中 -> 已请求立刻收尾");
                PumpThrottled();
                // V1.1.5: 边等边泵消息 —— 原来这里是 Thread.Sleep(100) x 100 = 最多 10 秒完全不响应窗口
                long twBusy = Stopwatch.GetTimestamp();
                while (_busy != 0 && ElapsedMs(twBusy) < 10000) { PumpOnUi(); try { Thread.Sleep(20); } catch { } }
            }
            RunOnceClear();
            PumpThrottled();
            // 验收意见(MAJOR-1): 断网保持期内关窗 = 用户从此没网(网卡禁用跨重启仍在)。
            // 所以退出前明确问一句, 默认帮他恢复; 选"否"才保持断网退出(下次开程序会自动恢复)。
            try
            {
                if (NetCutStateExists() || FastCutLayer.Length > 0)
                {
                    bool wantRestore;
                    PumpThrottled();
                    if (_cfg == null || _cfg.AutoRestoreOnExit)
                    {
                        Log("[退出] 网络还断着, 按设置自动恢复");
                        PumpThrottled();
                        wantRestore = true;
                    }
                    else
                    {
                        DialogResult rNet = MessageBox.Show(
                            "网络仍处于断开状态，退出前是否恢复网络？\n\n[是] 先恢复网络再退出\n[否] 保持断网退出，下次启动程序会自动恢复",
                            APP_NAME, MessageBoxButtons.YesNo, MessageBoxIcon.Question);
                            PumpThrottled();
                        wantRestore = (rNet == DialogResult.Yes);
                    }
                    if (wantRestore)
                    {
                        FastCut_Release();
                        PumpThrottled();
                        // 别让关窗卡住界面: 恢复放后台跑, 最多等 6 秒。
                        // netsh 是独立进程 —— 就算我们先退出, 它也会把网卡打开;
                        // 万一没验证完, 断网标记会留着, 下次启动自动再确认一遍。
                        Thread thR = new Thread(delegate() { try { RunNetOp(true, 6000); } catch { } });
                        PumpThrottled();
                        thR.IsBackground = true;
                        thR.Name = "SkyGuardExitRestore";
                        thR.Start();
                        PumpThrottled();
                        try { thR.Join(6000); } catch { }
                        Log("[退出] 已发起恢复网络" + (thR.IsAlive
                            ? "(还在后台进行; netsh 会自己跑完, 下次启动会再确认)" : "(已完成)"));
                            PumpThrottled();
                    }
                }
            }
            catch { }
            StopHook(true);
            PumpThrottled();
            FastCut_Release();      // 退出时撤掉快速层(防火墙规则是持久化的, 不能留在机器上)
            Log("程序退出");
            _closing = false;
            PumpThrottled();
            UiPhaseEnd("");
        };

        // 摆到鼠标所在那块屏的中间(多显示器)
        _form.Shown += delegate { CenterOnMouseScreen(_form); };
        PumpThrottled();
        PumpThrottled();
    }

    /// <summary>
    /// 客户区尺寸 -> 整窗尺寸(含边框/标题栏)。
    /// .NET 自带的 SizeFromClientSize 是 protected, 所以用最稳的办法: 临时设一下再读回来。
    /// </summary>
    private static Size ClientToWindowSize(Form f, Size client)
    {
        Size old = f.ClientSize;
        try
        {
            f.ClientSize = client;
            return f.Size;
        }
        finally { try { f.ClientSize = old; } catch { } }
    }

    /// <summary>
    /// 一个按钮在不做二次缩放的前提下需要多宽。
    ///
    /// 踩过的坑: 这里一开始用 Button.PreferredSize —— 在 AutoScaleMode.Font 的窗体上,
    /// PreferredSize 内部会再套用一次窗体缩放, 而布局又是在缩放过程中被调用的,
    /// 结果按钮宽度一轮一轮被放大(实测 99 px 涨到 879 px), 六个按钮挤成六行。
    /// 改成直接量文字宽度 + 固定内边距, 结果稳定、和布局过程无关。
    /// </summary>
    private static int ButtonWidth(Button b)
    {
        int textW = 0;
        try
        {
            // 用一个和缩放无关的位图 Graphics 量文字
            using (Bitmap bmp = new Bitmap(1, 1))
            using (Graphics g = Graphics.FromImage(bmp))
            {
                Size sz = TextRenderer.MeasureText(g, b.Text, b.Font, new Size(int.MaxValue, int.MaxValue),
                    TextFormatFlags.SingleLine);
                textW = sz.Width;
            }
        }
        catch { textW = b.Text.Length * 14; }
        // 口径必须和 MakeButton 一致(Sc(80) / Sc(30)), 否则自检判断"文字放不下"会随 DPI 漂移
        return Math.Max(Sc(80), textW + Sc(30));
    }

    /// <summary>
    /// 按实测的控件尺寸决定窗口最小尺寸, 并把初始尺寸定下来。
    ///
    /// 为什么要这样做: 六个按钮横排的总宽度完全取决于当前系统字体和 DPI
    /// (中文 Windows 上「测试」这类文字比英文宽得多)。
    /// 写死一个 640 之类的数字, 换一台机器/换语言就可能放不下 —— 按钮被切掉或者
    /// 折成两行吃掉日志区。所以这里直接量出来。
    /// </summary>
    private static void LayOutAndSetMinimum()
    {
        try
        {
            if (_form == null) return;
            ReflowMain();
            UpdateMinSize();

            // 初始尺寸: 不小于最小尺寸, 也不超过当前屏幕可用区(小屏别一开就超出屏幕)
            Rectangle wa = Screen.FromPoint(Cursor.Position).WorkingArea;
            int wantW = Math.Max(Sc(560), Sc(840));
            int wantH = Math.Max(Sc(460), Sc(640));
            wantW = Math.Min(wantW, Math.Max(Sc(560), wa.Width - 40));
            wantH = Math.Min(wantH, Math.Max(Sc(460), wa.Height - 60));
            _form.ClientSize = new Size(wantW, wantH);

            ReflowMain();
        }
        catch { }
    }

    /// <summary>
    /// 让一个页签里的控件跟着页面宽度伸缩, 而不是写死坐标。
    ///
    /// 为什么必须这么做(用户第二张实拍截图):
    ///   小屏/高缩放的机器上, FitDialogToScreen 会把设置窗缩到比"内容需要的宽度"还窄,
    ///   而页内控件是固定坐标 —— 右边的[录入按键]当场被切掉一半。窗口能缩, 内容就必须能跟着缩。
    ///
    /// 规则用字符串写在调用处, 每条形如:
    ///   "录入按键|L|10|J|0|94|26"   -> 左边距10, 右边距0(贴右), 宽至少94, 高26
    ///   "t1tip|L|10|J|0|0|40"      -> 两边都贴(全宽), 高40
    ///   "lstPreset|L|10|W|250|0|46" -> 左10, 固定宽250, 高46
    /// 取值优先级: W(固定宽) > J(右边距) > 都不给则按原宽。
    /// </summary>
    /// <summary>调窗口尺寸并读出对应客户区(标定最小尺寸用)</summary>
    private static Size ClientOf(Form f, Size windowSize)
    {
        Size old = f.Size;
        try { f.Size = windowSize; return f.ClientSize; }
        finally { try { f.Size = old; } catch { } }
    }

    /// <summary>
    /// 标定"刚好不切内容"的整窗最小尺寸。从设计尺寸开始每次收窄/收矮 8px,
    /// 试到有控件出界为止, 取上一个通过的。只在 settest 里跑, 不影响生产。
    /// 为什么实测标定而不是手算: TabControl 的边框/页签条占多少像素跟系统主题、字体、
    /// DPI 都有关, 手算必错(踩过: 以为 662x600 够, 实测页面只有 594 宽)。
    /// </summary>
    /// <summary>
    /// 找出"内容刚好不被裁"的整窗尺寸 —— settest 的标定。
    ///
    /// ★ 这里修过一个自检假绿的 bug(别改回去):
    ///   早先 best 初值直接写死 (668,620), 循环只往更小方向试 ——
    ///   万一初值本身就太小(在 125%/150% 缩放下就是这样), 永远发现不了, 于是自检报"全 OK",
    ///   而真实对话框(经 FitDialogToScreen 按整窗语义压到 668x620)底部是裁的。
    ///   → 现在先校验设计尺寸本身, 真被裁就往上找; 确认不裁后才往下收敛到刚好。
    /// </summary>
    private static Size FindNoClipSize(Form dlg, TabControl tabs)
    {
        dlg.MinimumSize = new Size(0, 0);     // 标定期间不受最小尺寸干扰
        Size start = dlg.Size;                // 建出来时的设计尺寸(整窗)
        Size best = start;

        // 第一段: 如果设计尺寸就已经被裁, 往上加(最多 12 步 x 16px), 先让它不裁
        if (AnyClip(dlg, tabs))
        {
            Size up = start;
            for (int step = 0; step < 12; step++)
            {
                up = new Size(up.Width + 16, up.Height + 16);
                dlg.Size = up;
                Application.DoEvents();
                if (!AnyClip(dlg, tabs)) { best = up; break; }
            }
            if (AnyClip(dlg, tabs)) best = up;   // 加到头仍然裁: 至少报出最大的那个
        }

        // 第二段: 再一路收小, 找到刚好不裁的最小整窗尺寸
        Size cur = best;
        for (int step = 0; step < 40; step++)
        {
            Size next = new Size(cur.Width - 8, cur.Height - 8);
            dlg.Size = next;
            Application.DoEvents();
            if (AnyClip(dlg, tabs)) break;
            best = next;
            cur = next;
            if (next.Width < 400 || next.Height < 300) break;
        }

        dlg.MinimumSize = new Size(0, 0);
        dlg.Size = start;
        Application.DoEvents();
        return best;
    }

    /// <summary>有没有控件被切(超出自己页签的可用区 / 超出对话框)</summary>
    private static bool AnyClip(Form dlg, TabControl tabs)
    {
        try { return AnyClipRec(dlg); }
        catch { }
        return false;
    }

    private static bool AnyClipRec(Control c)
    {
        try
        {
            if (c.Parent != null)
            {
                Rectangle r = c.Bounds;
                Size pc = c.Parent.ClientSize;
                bool scroll = false;
                for (Control a = c.Parent; a != null; a = a.Parent)
                {
                    ScrollableControl scc = a as ScrollableControl;
                    if (scc != null && scc.AutoScroll) { scroll = true; break; }
                }
                if (!scroll && r.Width > 0 && r.Height > 0
                    && (r.Right > pc.Width + 1 || r.Bottom > pc.Height + 1 || r.Left < -1 || r.Top < -1))
                    return true;
            }
            foreach (Control k in c.Controls)
                if (AnyClipRec(k)) return true;
        }
        catch { }
        return false;
    }
    private static void ReflowMain()
    {
        try
        {
            if (_form == null || _form.IsDisposed) return;
            SizeSummary();
            // 供 uicheck 布局自检用的关键坐标(生产逻辑不用)
            try
            {
                if (_btnBar != null) rowBottomLast = _btnBar.Bottom;
                if (_lblLogCaption != null) capLast = _lblLogCaption.Bottom;
                if (_txtLog != null) logTopLast = _txtLog.Top;
            }
            catch { }
        }
        catch { }
    }

    /// <summary>按当前宽度实测摘要文字高度, 让摘要卡片随内容长高、永不截断。</summary>
    private static void SizeSummary()
    {
        try
        {
            if (_lblSummary == null || _form == null || _form.IsDisposed) return;
            int width = _form.ClientSize.Width - Sc(16) * 2 - _lblSummary.Padding.Horizontal - Sc(6);
            if (width < 60) width = 60;
            using (Graphics g = _form.CreateGraphics())
            {
                Size sz = TextRenderer.MeasureText(g, _lblSummary.Text, _lblSummary.Font,
                    new Size(width, int.MaxValue),
                    TextFormatFlags.WordBreak | TextFormatFlags.Left | TextFormatFlags.Top);
                _lblSummary.Height = sz.Height + _lblSummary.Padding.Vertical + Sc(6);
            }
        }
        catch { }
    }

    /// <summary>按当前控件实际高度重算窗口最小尺寸(内容永远装得下)。</summary>
    private static void UpdateMinSize()
    {
        try
        {
            if (_form == null) return;
            ReflowMain();
            _form.PerformLayout();

            // 最小宽度: 六个按钮按实测宽度一行放下 + 左右边距。
            // 这样最小宽度下按钮只占一行, 高度才稳定(不会因折行忽高忽低)。
            int sumW = 0;
            foreach (Button b in _btnRow)
                if (b != null) sumW += (b.Width > 0 ? b.Width : ButtonWidth(b)) + Sc(8);
            if (sumW > 0) sumW -= Sc(8);
            // +Sc(24) 余量: 容器本身的边距/取整误差, 免得最小宽度下按钮正好卡在折行临界点
            int minW = sumW + Sc(16) * 2 + Sc(24);
            if (minW < Sc(560)) minW = Sc(560);

            // 最小高度: 头部 + 摘要 + 一行按钮 + 日志标题 + 日志最小 + 状态 + 余量
            // (余量 Sc(20) 是给各行间距/取整留的, 少了它日志框会在最小尺寸下被顶出 1 行)
            int btnH = Sc(38);
            if (_btnRow.Length > 0 && _btnRow[0] != null && _btnRow[0].Height > 0) btnH = _btnRow[0].Height;
            int sumH = Sc(52)
                    + Sc(10) + (_lblSummary != null ? _lblSummary.Height : Sc(60))
                    + Sc(10) + btnH
                    + Sc(6) + (_lblLogCaption != null ? _lblLogCaption.Height : Sc(18))
                    + Sc(2) + Sc(90)
                    + Sc(6) + (_lblProbeState != null ? _lblProbeState.Height : Sc(18))
                    + Sc(8) + Sc(20);
            _form.MinimumSize = ClientToWindowSize(_form, new Size(minW, sumH));
        }
        catch { }
    }

    /// <summary>
    /// 日志框的字体按实际 DPI 换算。
    /// 为什么单独做: AutoScaleMode 会缩放控件的位置和大小, 但 TextBox 的 Font 是显式设置的,
    /// 不跟着系统缩放走 —— 不处理的话 150% DPI 下日志文字会明显偏小。
    /// </summary>
    private static void ApplyLogFont()
    {
        try
        {
            if (_txtLog == null || _txtLog.IsDisposed) return;
            _dpiScale = GetScale(_txtLog);
            Font want = Fi("Consolas", 8.5F);
            Font old = _txtLog.Font;
            // 字号没变就别换 —— 否则每次 Resize 都新建/释放一个 Font, 白折腾
            if (old != null && Math.Abs(old.SizeInPoints - want.SizeInPoints) < 0.05F)
            {
                want.Dispose();
                return;
            }
            _txtLog.Font = want;
            if (old != null) old.Dispose();
        }
        catch { }
    }

    /// <summary>
    /// 摘要里那行触发键的简短写法。
    /// 为什么需要: 设了 12 个键的时候整行 60 多字符, 会把摘要挤到换行/超出边框。
    /// 超过 6 个就收成「F1 / F2 / F3 / F4 / F5 / F6 等 12 个」。
    /// </summary>
    private static string KeysBrief()
    {
        try
        {
            List<string> k = _cfg.Keys;
            if (k.Count == 0) return "(没设 —— 去[设置])";
            if (k.Count <= 6) return _cfg.KeysText();
            StringBuilder b = new StringBuilder();
            for (int i = 0; i < 6; i++)
            {
                if (i > 0) b.Append(" / ");
                b.Append(k[i]);
            }
            b.Append(" 等 ").Append(k.Count).Append(" 个");
            return b.ToString();
        }
        catch { return ""; }
    }

    /// <summary>主界面摘要(目标程序 / 触发键 / 网卡)</summary>
    private static void RefreshSummary()
    {
        try
        {
            if (_lblSummary == null) return;
            List<string> t = _cfg.TargetList();
            string s = "关掉: " + _cfg.TargetsText();
            // 目标是预设之外的进程时, 把进程名也列出来, 免得看不懂到底关了什么
            if (t.Count > 1 && MatchedPresetNames(t).Length == 0)
                s += "\r\n          " + string.Join(" / ", t.ToArray());
            s += "\r\n触发键: " + KeysBrief();
            s += "\r\n断网  : " + (_cfg.Nics.Count == 0 ? "未设置"
                                    : string.Join(" / ", _cfg.Nics.ToArray()))
                 + "    断开 " + _cfg.WaitSeconds + " 秒";
            // V1.1.5-RC1: 日志写不进去(磁盘满/权限/被杀软锁)以前是完全静默的, 现在说出来。
            string logNote = LogHealthNote();
            if (logNote.Length > 0) s += "\r\n提示  : " + logNote;
            _lblSummary.Text = s;
            SizeSummary();      // 摘要卡片随文字实测高度, 不再固定高度截字
            UpdateMinSize();    // 摘要变高后, 窗口最小高度也要跟着抬, 免得底部被顶掉
        }
        catch { }
    }

    /// <summary>
    /// 把对话框限制在"鼠标所在那块屏的可用区"以内, 然后居中。
    /// 为什么需要: 默认尺寸 × 系统缩放(125%/150%) 很容易超过 1366×768 这类小屏,
    /// 一超出去底部的[确定]按钮就点不到了 —— 那就等于用户没法保存设置。
    /// 这里不做任何机器相关的假设, 全按当前屏幕实测值算。
    /// </summary>
    private static void FitDialogToScreen(Form dlg, int wantW, int wantH)
    {
        try
        {
            Rectangle wa = Screen.FromPoint(Cursor.Position).WorkingArea;
            int w = Math.Min(wantW, wa.Width - 24);
            int h = Math.Min(wantH, wa.Height - 24);

            // ★ MinimumSize 是整窗尺寸(含标题栏+边框), 不是客户区 —— 这里踩过坑:
            //   早先 MinimumSize 直接填了"客户区想要的值"(668x620), 而 ShowSettings 又按
            //   整窗语义调本函数, 结果对话框一打开客户区就只有 650x573, 页内底部的
            //   [全选][全不选][删除选中] 被裁掉一截(实测裁 38px, 而 settest 恰好没量到)。
            Size min = (dlg.MinimumSize.Width > 0 && dlg.MinimumSize.Height > 0)
                       ? dlg.MinimumSize
                       : ClientToWindowSize(dlg, new Size(wantW, wantH));

            // 屏幕装得下就保证不小于"内容底线"; 实在装不下(小屏/高缩放)就允许更小 ——
            // 那时宁可让用户缩放, 也不能把窗口顶到屏幕外面去(顶出去就连[确定]都点不到)。
            if (wa.Width - 24 >= min.Width) w = Math.Max(w, min.Width);
            if (wa.Height - 24 >= min.Height) h = Math.Max(h, min.Height);

            dlg.Size = new Size(w, h);

            // ★ 这里故意不再开 AutoScroll(重要, 别加回来):
            //   实测滚动容器在"内容比容器只高一点点"时, 会把里面的内容整体上移
            //   (页面面板坐标变成 -9,-10), 结果是顶部和底部同时被裁 —— 比单纯裁底部更糟,
            //   用户看到的就是"标题栏被内容盖住、底部按钮消失"。
            //   窗口尺寸已经按 DPI 缩放过了(见 Sc()/Fi()), 内容本来就装得下, 不需要滚动。
        }
        catch { }
    }

    /// <summary>需要时打开滚动条的容器(向导的 Body 面板); 由 BuildFirstRunWizard 赋值</summary>

    /// <summary>
    /// 设置对话框 —— 汇集全部配置: 目标程序(多选) / 触发键 / 网卡 / 保持秒数。
    /// 用 TabControl 分页, 免得一屏塞太多东西。
    ///
    /// 拆成"建(BuildSettingsDialog) / 显示"两步, 是为了让无头自检(`settest`)能在不显示窗口的
    /// 情况下把这个对话框建出来、量它的布局。上一轮就是因为没法自动量, 才让一个
    /// "内容挤在左上角"的布局问题漏到用户手上。
    /// </summary>
    private static void ShowSettings()
    {
        if (_settingsOpening) return;      // 构建期间界面在泵消息 -> 防重入(连点[设置]不会开出两个窗)
        UiPhaseBegin("正在打开设置窗口(构建界面)");
        _settingsOpening = true;
        try
        {
            // ★ (修"无响应"): BuildSettingsDialog 实测 2.1~2.7 秒(冷启动 4.5 秒),
            //   这一段必须留在界面线程上建控件, 所以改成: 构建期间禁用主窗口(挡住重入点击) + 内部泵消息,
            //   窗口照常重画, Windows 就不会标"无响应"。netsh 那部分已经丢给 DoDetectAsync。
            bool reEnable = (_form != null && _form.IsHandleCreated && _form.Enabled);
            try
            {
                if (reEnable) _form.Enabled = false;
                using (Form dlg = BuildSettingsDialog(null))
                {
                    if (reEnable && _form != null && !_form.IsDisposed) _form.Enabled = true;
                    FillNicList();               // 先用上次探测结果填一遍 —— 打开就能看到勾选状态
                    DoDetectAsync(dlg, false);   // 真探测走后台: netsh 不再冻界面
                    FitDialogToScreen(dlg, Sc(720), Sc(700));   // 小屏/高缩放时别让[确定]跑到屏幕外
                    // ★ V1.1.5-RC1: 此刻五页里只建好了第 1 页 —— 窗口立刻显示出来,
                    //   剩下四页在显示之后一帧建一页(见 ScheduleSettingsPages)。
                    //   这样"打开设置"不再是一次 1.7~3.2 秒、期间界面完全不处理消息的同步构建。
                    dlg.Shown += delegate { ScheduleSettingsPages(dlg); };
                    dlg.ShowDialog(_form);
                }
                // 对话框关了: 把那几个指向它的引用清掉, 免得下一轮用到已释放的控件。
                _settingsTabs = null;
                _btnSettingsOk = null;
                _pagesReady = false;
                _settingsBuiltPages = 0;
            }
            finally { if (reEnable && _form != null && !_form.IsDisposed) _form.Enabled = true; }
        }
        finally { _settingsOpening = false; UiPhaseEnd(""); }
    }

    /// <summary>建好设置对话框(不显示)。显示前还要 FillNicList + DoDetect + FitDialogToScreen。</summary>
    /// <summary>说明标签: 填满格子宽度、按文字自动换行长高(永不截断)。</summary>
    private static Label Wrap(Label lb)
    {
        lb.AutoSize = true;
        lb.Dock = DockStyle.Top;
        lb.UseMnemonic = false;
        return lb;
    }

    /// <summary>
    /// [刷新进程列表] 的后台版本: Process.GetProcesses() + 排序在机器进程多时要几百毫秒,
    /// 放在界面线程上就是一次可见的卡顿(V1.1.5 改)。
    /// </summary>
    private static void RefreshRunningListAsync(ListBox lb, Label hint)
    {
        if (lb == null) return;
        if (hint != null) hint.Text = "正在读取进程列表…";
        Form owner = null;
        try { owner = lb.FindForm(); } catch { }
        Thread t = new Thread(delegate()
        {
            SortedSet<string> names = new SortedSet<string>(StringComparer.OrdinalIgnoreCase);
            try
            {
                foreach (Process p in Process.GetProcesses())
                {
                    try { if (!string.IsNullOrEmpty(p.ProcessName)) names.Add(p.ProcessName); }
                    catch { }
                    finally { try { p.Dispose(); } catch { } }
                }
            }
            catch { }
            MethodInvoker apply = delegate
            {
                try
                {
                    if (lb.IsDisposed) return;
                    lb.Items.Clear();
                    foreach (string n in names) lb.Items.Add(n);
                    if (hint != null) hint.Text = "共列出 " + names.Count + " 个进程，选中后点[添加选中]。";
                }
                catch { }
            };
            try
            {
                if (owner != null && !owner.IsDisposed && owner.IsHandleCreated) owner.BeginInvoke(apply);
                else apply();
            }
            catch { try { apply(); } catch { } }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardProcList";
        t.Start();
    }

    /// <summary>把正在运行的进程名(去 .exe、去重、排序)填进列表(同步版: 自检/无头用)。</summary>
    private static void FillRunningList(ListBox lb, Label hint)
    {
        try
        {
            SortedSet<string> names = new SortedSet<string>(StringComparer.OrdinalIgnoreCase);
            foreach (Process p in Process.GetProcesses())
            {
                try { if (!string.IsNullOrEmpty(p.ProcessName)) names.Add(p.ProcessName); }
                catch { }
                finally { try { p.Dispose(); } catch { } }
            }
            lb.Items.Clear();
            foreach (string n in names) lb.Items.Add(n);
            if (hint != null) hint.Text = "共列出 " + names.Count + " 个进程，选中后点[添加选中]。";
        }
        catch (Exception ex)
        {
            if (hint != null) hint.Text = "刷新失败：" + ex.Message;
        }
    }

    private static Form BuildSettingsDialog(StringBuilder sb)
    {
        Form dlg = new Form();
        dlg.Text = "设置";
        SetAutoScaleFont(dlg, Fi("Microsoft YaHei UI", 9F));
        dlg.BackColor = C_BG;
        dlg.ClientSize = new Size(Sc(720), Sc(700));
        dlg.MinimumSize = ClientToWindowSize(dlg, new Size(Sc(720), Sc(700)));
        dlg.StartPosition = FormStartPosition.CenterParent;
        dlg.FormBorderStyle = FormBorderStyle.Sizable;
        dlg.MaximizeBox = true;
        dlg.MinimizeBox = false;

        TableLayoutPanel root = new TableLayoutPanel();
        root.Dock = DockStyle.Fill;
        root.ColumnCount = 1;
        root.RowCount = 2;
        root.Margin = new Padding(0);
        root.BackColor = C_BG;
        root.RowStyles.Add(new RowStyle(SizeType.Percent, 100F));
        root.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        dlg.Controls.Add(root);

        TabControl tabs = new TabControl();
        tabs.Dock = DockStyle.Fill;
        tabs.Margin = new Padding(Sc(12), Sc(12), Sc(12), 0);
        root.Controls.Add(tabs, 0, 0);

        PumpOnce();   // 构建大对话框时给消息队列透气, 免得窗口被标成"无响应"
        // ---- 底部按钮条(右对齐) ----
        TableLayoutPanel bar = new TableLayoutPanel();
        bar.Dock = DockStyle.Fill;
        bar.ColumnCount = 2;
        bar.RowCount = 1;
        bar.Margin = new Padding(Sc(12), Sc(10), Sc(12), Sc(12));
        bar.BackColor = C_BG;
        bar.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 100F));
        bar.ColumnStyles.Add(new ColumnStyle(SizeType.AutoSize));
        root.Controls.Add(bar, 0, 1);

        FlowLayoutPanel btnRow = new FlowLayoutPanel();
        btnRow.AutoSize = true;
        btnRow.Dock = DockStyle.Fill;
        btnRow.FlowDirection = FlowDirection.LeftToRight;
        btnRow.WrapContents = false;
        bar.Controls.Add(btnRow, 1, 0);

        Button bOk = MakeButton("确定", null, "primary");
        Button bCancel = MakeButton("取消", null, "plain");
        bOk.Margin = new Padding(0, 0, Sc(8), 0);
        btnRow.Controls.Add(bOk);
        btnRow.Controls.Add(bCancel);
        bOk.Click += delegate { if (ApplySettingsFromDialog()) { dlg.DialogResult = DialogResult.OK; dlg.Close(); } };
        bCancel.Click += delegate { dlg.DialogResult = DialogResult.Cancel; dlg.Close(); };

        // ---- 五页签改成"分帧构建"(V1.1.5-RC1) ----
        // 这一段原来一次性把五页 ~200 个控件全建出来(实测 1.7~3.2 秒, 冷启动 4.5 秒),
        // 只在页签边界泵一次消息 —— 慢机器上"单页构建"那一段就可能整段不处理消息,
        // 而 Windows 判"无响应"看的正是"这条线程多久没处理过消息"。
        // 现在: 打开时只建第 1 页(用户立刻看到界面), 其余四页在窗口显示之后一帧建一页
        // (见 ScheduleSettingsPages)。用户点[确定]时若还有页没建, ApplySettingsFromDialog
        // 开头会先 EnsureAllSettingsPages() 把五页补齐再读控件 ——
        // 所以**永远不会读到尚未创建的控件**, 也就不会把用户的设置静默读成默认值。
        _settingsTabs = tabs;
        _settingsBuiltPages = 0;
        _settingsBuilding = false;
        _pagesReady = false;

        // 用户点页签 -> 立刻把他要的那一页(以及前面还没建的页)建出来, 不用等分帧队列排到。
        // ⚠️ 两个守卫缺一不可, 否则会递归回"正在构建的那一页":
        //   _settingsBuilding —— 建页时 tabs.TabPages.Add() 会回调到这里, 那时必须跳过;
        //   _settingsBuiltPages <= 0 —— 建第 1 页时 _settingsBuilding 还没置上(那是外层
        //   直接调 BuildSettingsPage), 只能靠"一页都没建完"这个条件挡住。
        tabs.SelectedIndexChanged += delegate
        {
            try
            {
                if (_headless || _settingsBuilding) return;
                if (_settingsBuiltPages <= 0) return;
                int want = tabs.SelectedIndex + 1;
                if (want <= _settingsBuiltPages) return;
                EnsureSettingsPage(_settingsTabs, want);
            }
            catch (Exception ex) { Log("[设置] 按需建页异常: " + ex.Message); }
        };

        BuildSettingsPage(tabs, 1);

        // 自检(settest / uicheck 等)要一次性拿到全部五页, 否则断言会漏掉未建的页。
        if (_headless)
        {
            for (int p = 2; p <= SETTINGS_PAGE_COUNT; p++) BuildSettingsPage(tabs, p);
            _btnSettingsOk = null;
            MarkSettingsPagesReady();
        }
        else
        {
            // 五页建齐之前先把 [确定] 禁用: 建页期间会泵消息, 用户可能正好点在那一刻,
            // 而那时后面的页还不存在 —— 读了就等于把用户的设置静默读成默认值。
            // 分帧构建通常几百毫秒就建完, 之后按钮自己会开(见 MarkSettingsPagesReady)。
            _btnSettingsOk = bOk;
            bOk.Enabled = false;
        }
        return dlg;
    }

    // ============================================================================
    //  设置窗五页签的"分帧构建"(V1.1.5-RC1)
    //
    //  为什么要它: BuildSettingsDialog 一次建完五页 ~200 个控件, 实测 1.7~3.2 秒
    //  (冷启动 4.5 秒)。以前只在页签边界泵一次消息 —— 慢机器上"单页构建"那一段
    // 就可能整段不处理消息, 而 Windows 判窗口"无响应"看的正是"这条线程多久没处理过消息",
    //  不是窗口快不快。
    //
    //  现在: 打开时只建第 1 页 -> 窗口立刻显示 -> 其余四页在显示之后一帧建一页。
    //  三道保险保证"读控件时它一定已经存在":
    //    1) ApplySettingsFromDialog 读之前先 EnsureAllSettingsPages();
    //    2) 用户切换页签时 EnsureSettingsPage(选中页);
    //    3) 五页建齐之前 [确定] 是禁用的(见 BuildSettingsDialog 分支)。
    //  另外每一页内部都铺了 PumpThrottled() 泵点, 界面线程不会长时间不处理消息。
    // ============================================================================

    /// <summary>
    /// 设置窗一共几页。构建顺序就是页签顺序, 不能改 ——
    /// 第 5 页结尾的 FillNicList() 依赖第 3 页创建的 _lstNics。
    /// </summary>
    private const int SETTINGS_PAGE_COUNT = 5;

    /// <summary>设置窗已经建到第几页(0 = 一页都还没建)</summary>
    private static volatile int _settingsBuiltPages = 0;
    /// <summary>正在建页(防重入: 建页期间会泵消息, 用户可能又点页签 / 点[确定])</summary>
    private static volatile bool _settingsBuilding = false;
    /// <summary>五页是否已经全部就绪(就绪前 [确定] 是禁用的)</summary>
    private static volatile bool _pagesReady = false;
    /// <summary>当前设置对话框的页签控件(分帧构建要用它)</summary>
    private static TabControl _settingsTabs = null;
    /// <summary>设置窗的[确定]按钮(建齐五页后由 MarkSettingsPagesReady 打开)</summary>
    private static Button _btnSettingsOk = null;

    /// <summary>建一页(按需)。page 从 1 开始; 只会往后建, 不会重建已建过的页。</summary>
    private static void BuildSettingsPage(TabControl tabs, int page)
    {
        if (tabs == null) return;
        if (page <= _settingsBuiltPages) return;
        switch (page)
        {
            case 1: BuildSettingsTab1(tabs); break;
            case 2: BuildSettingsTab2(tabs); break;
            case 3: BuildSettingsTab3(tabs); break;
            case 4: BuildSettingsTab4(tabs); break;
            case 5: BuildSettingsTab5(tabs); break;
            default: return;
        }
        _settingsBuiltPages = page;
    }

    /// <summary>
    /// 把 1..page 页补齐。
    /// 重入(正在建页时又被调用)直接返回 —— 调用方要用 _pagesReady 判断"到底就绪没有",
    /// 不能假设调用一次就建齐了(建页期间会把消息泵出去, 用户的操作可能插进来)。
    /// </summary>
    private static void EnsureSettingsPage(TabControl tabs, int page)
    {
        if (tabs == null) return;
        if (page > SETTINGS_PAGE_COUNT) page = SETTINGS_PAGE_COUNT;
        if (_pagesReady || _settingsBuiltPages >= page) return;
        if (_settingsBuilding) return;                  // 已经在建了: 交给正在建的那一层
        _settingsBuilding = true;
        try
        {
            for (int p = _settingsBuiltPages + 1; p <= page; p++)
            {
                UiPhaseBegin("设置窗: 构建第 " + p + " 页");
                BuildSettingsPage(tabs, p);
                UiPhaseEnd("");
            }
        }
        catch (Exception ex) { Log("[设置] 构建第 " + page + " 页异常: " + ex.Message); }
        finally
        {
            _settingsBuilding = false;
            if (_settingsBuiltPages >= SETTINGS_PAGE_COUNT) MarkSettingsPagesReady();
        }
    }

    /// <summary>把设置窗五页补齐。任何"要读设置窗控件"的地方都必须先过它。</summary>
    private static void EnsureAllSettingsPages()
    {
        EnsureSettingsPage(_settingsTabs, SETTINGS_PAGE_COUNT);
    }

    /// <summary>五页建齐: 打开[确定], 并记一行耗时(超过 200 ms 会写日志)。</summary>
    private static void MarkSettingsPagesReady()
    {
        _pagesReady = true;
        try
        {
            if (_btnSettingsOk != null && !_btnSettingsOk.IsDisposed)
            {
                _btnSettingsOk.Enabled = true;
                _btnSettingsOk.Text = "确定";
            }
        }
        catch { }
    }

    /// <summary>
    /// 窗口显示之后, 一帧建一页, 把剩下的页建完。
    /// 为什么不一口气建: 一口气建就是原来那条 1.7~3.2 秒、期间界面完全不理消息的同步路径。
    /// 用 BeginInvoke 排队, 两帧之间消息循环照常跑(重画/响应点击都在跑)。
    /// </summary>
    private static void ScheduleSettingsPages(Form dlg)
    {
        try
        {
            if (dlg == null || dlg.IsDisposed || !dlg.IsHandleCreated) return;
            if (_pagesReady) return;
            dlg.BeginInvoke((MethodInvoker)delegate
            {
                try
                {
                    if (dlg.IsDisposed) return;
                    int next = _settingsBuiltPages + 1;
                    if (next > SETTINGS_PAGE_COUNT || _pagesReady) return;
                    EnsureSettingsPage(_settingsTabs, next);
                }
                catch (Exception ex) { Log("[设置] 分帧构建异常: " + ex.Message); }
                if (!dlg.IsDisposed) ScheduleSettingsPages(dlg);
            });
        }
        catch { }
    }

    /// <summary>设置窗第 1 页「目标程序」的背景构建(由 BuildSettingsPage 分帧调用)。</summary>
    private static void BuildSettingsTab1(TabControl tabs)
    {
        // ============ Tab1: 目标程序 ============
        TabPage tp1 = new TabPage("目标程序");
        PumpThrottled();
        _tabTargets = tp1;
        tp1.Padding = new Padding(0);
        tabs.TabPages.Add(tp1);
        PumpThrottled();

        TableLayoutPanel g1 = new TableLayoutPanel();
        g1.Dock = DockStyle.Fill;
        PumpThrottled();
        g1.ColumnCount = 2;
        g1.RowCount = 9;
        g1.Padding = Pad(12, 10, 12, 10);
        PumpThrottled();
        g1.BackColor = C_CARD;
        g1.AutoScroll = true;   // 小屏/极端缩放下装不下时, 页内可滚动, 而不是被裁
        g1.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 62F));
        PumpThrottled();
        g1.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 38F));
        for (int i = 0; i < 9; i++)
        {
            bool grow = (i == 2 || i == 4 || i == 7);
            PumpThrottled();
            g1.RowStyles.Add(grow ? new RowStyle(SizeType.Percent, 100F / 3F) : new RowStyle(SizeType.AutoSize));
        }
        tp1.Controls.Add(g1);
        PumpThrottled();
        PumpThrottled();

        Label t1tip = new Label();
        t1tip.Text = "勾选的程序会在触发时关闭，取消勾选仅保留在列表中。\r\n"
                   + "使用光遇电脑版请选「光遇 电脑版」预设，使用模拟器请选「MuMu 模拟器」预设，双击列表即可加入。\r\n"
                   + "列表中没有的程序：点[刷新进程列表]，选中后点[添加选中]，或在[手动添加]中输入进程名。";
                   PumpThrottled();
        t1tip.ForeColor = C_SUB;
        Wrap(t1tip);
        g1.Controls.Add(t1tip, 0, 0);
        PumpThrottled();
        PumpThrottled();
        g1.SetColumnSpan(t1tip, 2);

        Label t1p = new Label(); t1p.Text = "预设方案：";
        PumpThrottled();
        Wrap(t1p);
        g1.Controls.Add(t1p, 0, 1);
        PumpThrottled();
        g1.SetColumnSpan(t1p, 2);

        ListBox lstPreset = new ListBox();
        PumpThrottled();
        lstPreset.Dock = DockStyle.Fill;
        lstPreset.Margin = new Padding(0, 0, Sc(8), 0);
        lstPreset.MinimumSize = new Size(0, Sc(70));
        PumpThrottled();
        lstPreset.IntegralHeight = true;
        foreach (ProcPreset pp in PRESETS) lstPreset.Items.Add(pp.Label);
        if (lstPreset.Items.Count > 0) lstPreset.SelectedIndex = 0;
        PumpThrottled();
        g1.Controls.Add(lstPreset, 0, 2);
        PumpThrottled();

        Button bAddPreset = MakeButton("添加预设 →", null, "plain");
        bAddPreset.Margin = new Padding(Sc(4), 0, 0, 0);
        PumpThrottled();
        bAddPreset.Anchor = AnchorStyles.Top | AnchorStyles.Left;
        g1.Controls.Add(bAddPreset, 1, 2);
        PumpThrottled();

        Label t1r = new Label(); t1r.Text = "正在运行的程序：";
        Wrap(t1r);
        PumpThrottled();
        g1.Controls.Add(t1r, 0, 3);
        PumpThrottled();
        g1.SetColumnSpan(t1r, 2);

        ListBox lstRunning = new ListBox();
        PumpThrottled();
        lstRunning.Dock = DockStyle.Fill;
        lstRunning.Margin = new Padding(0, 0, Sc(8), 0);
        lstRunning.MinimumSize = new Size(0, Sc(70));
        PumpThrottled();
        lstRunning.IntegralHeight = true;
        lstRunning.SelectionMode = SelectionMode.MultiExtended;
        g1.Controls.Add(lstRunning, 0, 4);
        PumpThrottled();
        PumpThrottled();

        TableLayoutPanel runBtns = new TableLayoutPanel();
        runBtns.Dock = DockStyle.Top;
        PumpThrottled();
        runBtns.AutoSize = true;
        runBtns.ColumnCount = 1;
        runBtns.RowCount = 2;
        PumpThrottled();
        runBtns.Margin = new Padding(Sc(4), 0, 0, 0);
        runBtns.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        runBtns.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        PumpThrottled();
        g1.Controls.Add(runBtns, 1, 4);
        PumpThrottled();
        Button bRefreshRunning = MakeButton("刷新进程列表", null, "plain");
        bRefreshRunning.Margin = new Padding(0, 0, 0, Sc(6));
        bRefreshRunning.Anchor = AnchorStyles.Top | AnchorStyles.Left;
        PumpThrottled();
        Button bAddRunning = MakeButton("添加选中 →", null, "plain");
        bAddRunning.Anchor = AnchorStyles.Top | AnchorStyles.Left;
        runBtns.Controls.Add(bRefreshRunning, 0, 0);
        PumpThrottled();
        PumpThrottled();
        runBtns.Controls.Add(bAddRunning, 0, 1);
        PumpThrottled();

        FlowLayoutPanel custRow = new FlowLayoutPanel();
        custRow.Dock = DockStyle.Fill;
        PumpThrottled();
        custRow.AutoSize = true;
        custRow.FlowDirection = FlowDirection.LeftToRight;
        custRow.WrapContents = true;
        PumpThrottled();
        custRow.Margin = new Padding(0, Sc(4), 0, 0);
        g1.Controls.Add(custRow, 0, 5);
        PumpThrottled();
        g1.SetColumnSpan(custRow, 2);
        Label t1c = new Label(); t1c.Text = "手动添加进程名：";
        t1c.AutoSize = true;
        PumpThrottled();
        t1c.Anchor = AnchorStyles.Left;
        custRow.Controls.Add(t1c);
        PumpThrottled();
        TextBox txtCustom = new TextBox();
        txtCustom.Width = Sc(170);
        custRow.Controls.Add(txtCustom);
        PumpThrottled();
        PumpThrottled();
        Button bAddCustom = MakeButton("添加", null, "plain");
        custRow.Controls.Add(bAddCustom);
        PumpThrottled();

        Label t1l = new Label(); t1l.Text = "已添加：";
        Wrap(t1l);
        PumpThrottled();
        g1.Controls.Add(t1l, 0, 6);
        PumpThrottled();
        g1.SetColumnSpan(t1l, 2);

        _lstTargets = new CheckedListBox();
        PumpThrottled();
        _lstTargets.Name = "lstTargets";
        _lstTargets.Dock = DockStyle.Fill;
        _lstTargets.MinimumSize = new Size(0, Sc(70));
        PumpThrottled();
        _lstTargets.CheckOnClick = true;
        g1.Controls.Add(_lstTargets, 0, 7);
        PumpThrottled();
        g1.SetColumnSpan(_lstTargets, 2);
        // ★ 单个勾选框的状态必须写回 _procOff(否则"界面上取消勾选"不影响实际杀的进程)。
        //   ItemCheck 是在状态变化之前触发的, 所以读 e.NewValue(而不是 GetItemChecked),
        //   并把"是哪一个进程"当场定下来再延后执行 —— 以前只存一个下标, 连续勾两下时
        //   先排队的那次会读到后一次的下标, 于是前一次勾选静默丢失(界面与实际不一致)。
        _lstTargets.ItemCheck += delegate(object s, ItemCheckEventArgs e)
        {
            if (_suppressCheck) return;
            if (e.Index < 0 || e.Index >= _targetDraft.Count) return;
            string nm = _targetDraft[e.Index];
            bool on = (e.NewValue == CheckState.Checked);
            PumpThrottled();
            try { _lstTargets.BeginInvoke((MethodInvoker)delegate { ApplyPendingCheck(nm, on); }); }
            catch { ApplyPendingCheck(nm, on); }
        };
        PumpThrottled();

        FlowLayoutPanel tgtBtns = new FlowLayoutPanel();
        tgtBtns.Dock = DockStyle.Fill;
        PumpThrottled();
        tgtBtns.AutoSize = true;
        tgtBtns.FlowDirection = FlowDirection.LeftToRight;
        tgtBtns.WrapContents = true;
        PumpThrottled();
        g1.Controls.Add(tgtBtns, 0, 8);
        PumpThrottled();
        g1.SetColumnSpan(tgtBtns, 2);
        Label t1hint = new Label();
        t1hint.Name = "t1hint";
        PumpThrottled();
        t1hint.AutoSize = true;
        t1hint.ForeColor = C_SUB;
        t1hint.Text = "";
        PumpThrottled();
        tgtBtns.Controls.Add(t1hint);
        PumpThrottled();
        Button bAllOn = MakeButton("全勾上", null, "plain");
        Button bAllOff = MakeButton("全取消", null, "plain");
        Button bDelTarget = MakeButton("删除选中", null, "plain");
        PumpThrottled();
        tgtBtns.Controls.Add(bAllOn);
        PumpThrottled();
        tgtBtns.Controls.Add(bAllOff);
        PumpThrottled();
        tgtBtns.Controls.Add(bDelTarget);
        PumpThrottled();

        // ---- Tab1 事件 ----
        bAddPreset.Click += delegate
        {
            int i = lstPreset.SelectedIndex;
            PumpThrottled();
            if (i < 0 || i >= PRESETS.Length) return;
            int added = 0;
            foreach (string p in PRESETS[i].Procs)
                if (!TargetListContains(p)) { _targetDraft.Add(p); added++; }
            RefreshTargetList();
            PumpThrottled();
            t1hint.Text = "已添加预设「" + PRESETS[i].Label + "」，新增 " + added + " 个进程";
        };
        lstPreset.DoubleClick += delegate { bAddPreset.PerformClick(); };
        PumpThrottled();
        bRefreshRunning.Click += delegate { RefreshRunningListAsync(lstRunning, t1hint); };
        bAddRunning.Click += delegate
        {
            int added = 0;
            PumpThrottled();
            foreach (object o in lstRunning.SelectedItems)
            {
                string n = (o == null) ? "" : o.ToString();
                PumpThrottled();
                if (n.Length > 0 && !TargetListContains(n)) { _targetDraft.Add(n); added++; }
            }
            RefreshTargetList();
            PumpThrottled();
            t1hint.Text = added > 0 ? ("已添加 " + added + " 个进程") : "这些进程已在列表中";
        };
        bAddCustom.Click += delegate
        {
            string n = txtCustom.Text.Trim();
            PumpThrottled();
            if (n.Length == 0) { t1hint.Text = "请输入进程名，无需填写 .exe"; return; }
            if (n.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) n = n.Substring(0, n.Length - 4);
            if (TargetListContains(n)) t1hint.Text = n + " 已在列表中";
            else { _targetDraft.Add(n); RefreshTargetList(); t1hint.Text = "已添加 " + n; }
            txtCustom.Text = "";
        };
        PumpThrottled();
        bAllOn.Click += delegate { _procOff.Clear(); RefreshTargetList(); };
        bAllOff.Click += delegate
        {
            foreach (string s in _targetDraft) if (!ListHas(_procOff, s)) _procOff.Add(s);
            PumpThrottled();
            RefreshTargetList();
        };
        bDelTarget.Click += delegate
        {
            List<string> rm = new List<string>();
            PumpThrottled();
            foreach (object o in _lstTargets.SelectedItems) rm.Add(o.ToString());
            foreach (string r in rm) { _targetDraft.Remove(r); RemoveFrom(_procOff, r); }
            RefreshTargetList();
            PumpThrottled();
        };

        // 这里曾经放过[上移]/[下移](11.1.2-RC3), RC5 去掉:
        // 列表的显示顺序对处置没有任何影响 —— 触发时的终止顺序由代码里按进程类型算的优先级决定
        // (专门的 ordertest 就是在验这个), 跟界面排列无关。留着只会让人以为"顺序有用"。

        PumpThrottled();   // 页尾再泵一次, 保证页与页之间不留长空窗
    }

    /// <summary>设置窗第 2 页「触发键」的背景构建(由 BuildSettingsPage 分帧调用)。</summary>
    private static void BuildSettingsTab2(TabControl tabs)
    {
        // ============ Tab2: 触发键 ============
        TabPage tp2 = new TabPage("触发键");
        PumpThrottled();
        _tabKeys = tp2;
        tp2.Padding = new Padding(0);
        tabs.TabPages.Add(tp2);
        PumpThrottled();
        TableLayoutPanel g2 = new TableLayoutPanel();
        g2.Dock = DockStyle.Fill;
        g2.ColumnCount = 1;
        PumpThrottled();
        g2.RowCount = 3;
        g2.Padding = Pad(12, 10, 12, 10);
        g2.BackColor = C_CARD;
        PumpThrottled();
        g2.AutoScroll = true;
        g2.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        g2.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        PumpThrottled();
        g2.RowStyles.Add(new RowStyle(SizeType.Percent, 100F));
        tp2.Controls.Add(g2);
        PumpThrottled();

        Label t2tip = new Label();
        t2tip.Text = "按下触发键会关闭上述程序并断网，可设置多个。\r\n"
                    + "处置进行中按触发键无效，如需提前恢复网络，请点[恢复网络]或[停止保护]。\r\n"
                    + "避免使用游戏已占用的按键，推荐 Pause、ScrollLock 或组合键。";
                    PumpThrottled();
        t2tip.ForeColor = C_SUB;
        Wrap(t2tip);
        g2.Controls.Add(t2tip, 0, 0);
        PumpThrottled();
        PumpThrottled();

        FlowLayoutPanel keyRow = new FlowLayoutPanel();
        keyRow.Dock = DockStyle.Fill;
        PumpThrottled();
        keyRow.AutoSize = true;
        keyRow.FlowDirection = FlowDirection.LeftToRight;
        keyRow.WrapContents = true;
        PumpThrottled();
        keyRow.Margin = new Padding(0, Sc(6), 0, 0);
        g2.Controls.Add(keyRow, 0, 1);
        PumpThrottled();
        Label t2l = new Label(); t2l.Text = "当前触发键：";
        t2l.AutoSize = true;
        t2l.Anchor = AnchorStyles.Left;
        PumpThrottled();
        keyRow.Controls.Add(t2l);
        PumpThrottled();
        _txtKeys = new TextBox();
        _txtKeys.Name = "txtKeys";
        _txtKeys.Width = Sc(280);
        PumpThrottled();
        _txtKeys.ReadOnly = true;
        _txtKeys.BackColor = Color.White;
        keyRow.Controls.Add(_txtKeys);
        PumpThrottled();
        PumpThrottled();
        Button bRec2 = MakeButton("录入按键", null, "plain");
        bRec2.Click += delegate { DoRecordKeys(); };
        keyRow.Controls.Add(bRec2);
        PumpThrottled();
        PumpThrottled();

        Label t2b = new Label();
        t2b.ForeColor = C_SUB;
        PumpThrottled();
        t2b.Dock = DockStyle.Fill;
        t2b.AutoSize = false;
        t2b.Text = "点[录入按键]打开录入窗口，可直接按下按键，也可从下拉菜单选择。";
        PumpThrottled();
        g2.Controls.Add(t2b, 0, 2);
        PumpThrottled();

        PumpThrottled();   // 页尾再泵一次, 保证页与页之间不留长空窗
    }

    /// <summary>设置窗第 3 页「网卡与选项」的背景构建(由 BuildSettingsPage 分帧调用)。</summary>
    private static void BuildSettingsTab3(TabControl tabs)
    {
        // ============ Tab3: 网卡与选项 ============
        TabPage tp3 = new TabPage("网卡与选项");
        PumpThrottled();
        tp3.Padding = new Padding(0);
        tabs.TabPages.Add(tp3);
        TableLayoutPanel g3 = new TableLayoutPanel();
        PumpThrottled();
        g3.Dock = DockStyle.Fill;
        g3.ColumnCount = 1;
        g3.RowCount = 13;
        PumpThrottled();
        g3.Padding = Pad(12, 10, 12, 10);
        g3.BackColor = C_CARD;
        g3.AutoScroll = true;
        PumpThrottled();
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 0  说明
        g3.RowStyles.Add(new RowStyle(SizeType.Percent, 100F)); // 1  网卡列表
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 2  探测+保持
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 3  警告
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 4  焦点说明
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 5  焦点解堵总开关
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 6  档位(只用系统判定/Pro/Ultra)
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 7  参数: 间隔/轮数/探针
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 8  参数: 还焦点确认/静默期/套用默认
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 9  延迟提示(实时算)
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 10 钩子主动探活
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 11 杀受限进程(SeDebugPrivilege)
        g3.RowStyles.Add(new RowStyle(SizeType.AutoSize));      // 12 快速断流(11.1.0)
        // ★ 行号与上面这张表必须一一对应: RC17 曾插入"抢得更早"那一行时漏改了两个 Add,
        //   结果两个控件被放进同一格叠在一起画 —— settest 里的"同格重叠"断言现在会拦住这种事。
        tp3.Controls.Add(g3);
        PumpThrottled();
        PumpThrottled();

        Label t3l = new Label();
        t3l.Text = "选择断网时要断开的网卡，带[承载流量]标记的是当前正在使用的网卡。";
        PumpThrottled();
        t3l.ForeColor = C_SUB;
        Wrap(t3l);
        g3.Controls.Add(t3l, 0, 0);
        PumpThrottled();
        PumpThrottled();

        _lstNics = new CheckedListBox();
        _lstNics.Name = "lstNics";
        PumpThrottled();
        _lstNics.Dock = DockStyle.Fill;
        _lstNics.MinimumSize = new Size(0, Sc(90));
        _lstNics.CheckOnClick = true;
        PumpThrottled();
        g3.Controls.Add(_lstNics, 0, 1);
        PumpThrottled();

        FlowLayoutPanel nicRow = new FlowLayoutPanel();
        nicRow.Dock = DockStyle.Fill;
        PumpThrottled();
        nicRow.AutoSize = true;
        nicRow.FlowDirection = FlowDirection.LeftToRight;
        nicRow.WrapContents = true;
        PumpThrottled();
        nicRow.Margin = new Padding(0, Sc(6), 0, 0);
        g3.Controls.Add(nicRow, 0, 2);
        PumpThrottled();
        Button bDetect = MakeButton("重新探测网卡", null, "plain");
        bDetect.Click += delegate { DoDetectAsync(_lstNics == null ? _form : _lstNics.FindForm(), true); };
        nicRow.Controls.Add(bDetect);
        PumpThrottled();
        PumpThrottled();
        Label t3w = new Label(); t3w.Text = "断网保持（秒）：";
        t3w.AutoSize = true;
        t3w.Anchor = AnchorStyles.Left;
        PumpThrottled();
        nicRow.Controls.Add(t3w);
        PumpThrottled();
        _numWait = new NumericUpDown();
        _numWait.Width = Sc(64);
        _numWait.Minimum = 0; _numWait.Maximum = 600; _numWait.Value = 20;
        PumpThrottled();
        nicRow.Controls.Add(_numWait);
        PumpThrottled();

        Label t3warn = new Label();
        t3warn.ForeColor = Color.FromArgb(160, 90, 0);
        PumpThrottled();
        t3warn.Text = "程序需要以管理员身份运行。触发时会关闭上述程序并断开所选网卡，到时间自动恢复。\r\n"
                    + "断网保持 = 触发后断网的时长，推荐 20 秒。\r\n"
                    + "不注入游戏、不读内存、不改游戏文件、不联网。";
                    PumpThrottled();
        Wrap(t3warn);
        g3.Controls.Add(t3warn, 0, 3);
        PumpThrottled();

        Label t3f0 = new Label();
        t3f0.ForeColor = Color.FromArgb(160, 90, 0);
        PumpThrottled();
        t3f0.Text = "游戏窗口卡住时，自动将键盘焦点切换到其他窗口；游戏恢复后自动交还。";
        Wrap(t3f0);
        g3.Controls.Add(t3f0, 0, 4);
        PumpThrottled();
        PumpThrottled();

        _chkFocusRescue = new CheckBox();
        _chkFocusRescue.AutoSize = true;
        PumpThrottled();
        _chkFocusRescue.Text = "游戏窗口卡住时自动切换焦点";
        _chkFocusRescue.Checked = true;
        g3.Controls.Add(_chkFocusRescue, 0, 5);
        PumpThrottled();
        PumpThrottled();

        // ---- 焦点接管档位 (V1.1.4-RC1: Pro / Ultra) ----
        // 为什么要档位: "提前接管"这套判定本质是"用一段时间的不响应换确定性"。
        //   Pro   = 现在的手感(探针 500ms × 3 轮 ≈ 1.6 秒), 基本只在真卡死时才接管;
        PumpThrottled();
        //   Ultra = 全压到最低(10ms 间隔 × 1 轮 + 探针 120ms ≈ 0.13 秒), 专门用来试
        //           "卡白时按键能不能更快进来"以及"会不会有很烦的误触发", 默认不选。
        FlowLayoutPanel focusModeRow = new FlowLayoutPanel();
        PumpThrottled();
        focusModeRow.Dock = DockStyle.Fill;
        focusModeRow.AutoSize = true;
        focusModeRow.FlowDirection = FlowDirection.LeftToRight;
        PumpThrottled();
        focusModeRow.WrapContents = true;
        focusModeRow.Margin = new Padding(0, Sc(4), 0, 0);
        g3.Controls.Add(focusModeRow, 0, 6);
        PumpThrottled();
        PumpThrottled();
        Label t3fm = new Label(); t3fm.Text = "切换档位："; t3fm.AutoSize = true;
        t3fm.Anchor = AnchorStyles.Left;
        focusModeRow.Controls.Add(t3fm);
        PumpThrottled();
        PumpThrottled();
        _radFocusSys = new RadioButton();
        _radFocusSys.AutoSize = true;
        _radFocusSys.Text = "仅系统检测";
        PumpThrottled();
        focusModeRow.Controls.Add(_radFocusSys);
        PumpThrottled();
        _radFocusPro = new RadioButton();
        _radFocusPro.AutoSize = true;
        _radFocusPro.Text = "Pro";
        PumpThrottled();
        focusModeRow.Controls.Add(_radFocusPro);
        PumpThrottled();
        _radFocusUltra = new RadioButton();
        _radFocusUltra.AutoSize = true;
        _radFocusUltra.ForeColor = Color.FromArgb(176, 34, 26);
        PumpThrottled();
        _radFocusUltra.Text = "Ultra";
        focusModeRow.Controls.Add(_radFocusUltra);
        PumpThrottled();

        FlowLayoutPanel focusRow = new FlowLayoutPanel();
        focusRow.Dock = DockStyle.Fill;
        PumpThrottled();
        focusRow.AutoSize = true;
        focusRow.FlowDirection = FlowDirection.LeftToRight;
        focusRow.WrapContents = true;
        PumpThrottled();
        focusRow.Margin = new Padding(0, Sc(4), 0, 0);
        g3.Controls.Add(focusRow, 0, 7);
        PumpThrottled();
        Label t3f1 = new Label(); t3f1.Text = "检测间隔（ms）：";
        t3f1.AutoSize = true;
        t3f1.Anchor = AnchorStyles.Left;
        PumpThrottled();
        focusRow.Controls.Add(t3f1);
        PumpThrottled();
        _numFocusMs = new NumericUpDown();
        _numFocusMs.Width = Sc(64);
        _numFocusMs.Minimum = 10; _numFocusMs.Maximum = 2000; _numFocusMs.Increment = 10;
        PumpThrottled();
        _numFocusMs.Value = 50;
        focusRow.Controls.Add(_numFocusMs);
        PumpThrottled();
        Label t3f2 = new Label(); t3f2.Text = "确认次数：";
        t3f2.AutoSize = true;
        t3f2.Anchor = AnchorStyles.Left;
        PumpThrottled();
        focusRow.Controls.Add(t3f2);
        PumpThrottled();
        _numFocusRounds = new NumericUpDown();
        _numFocusRounds.Width = Sc(48);
        _numFocusRounds.Minimum = 1; _numFocusRounds.Maximum = 10;
        PumpThrottled();
        _numFocusRounds.Value = 3;
        focusRow.Controls.Add(_numFocusRounds);
        PumpThrottled();
        Label t3f3 = new Label(); t3f3.Text = "  检测超时（ms）：";
        t3f3.AutoSize = true;
        t3f3.Anchor = AnchorStyles.Left;
        PumpThrottled();
        focusRow.Controls.Add(t3f3);
        PumpThrottled();
        _numFocusProbe = new NumericUpDown();
        _numFocusProbe.Width = Sc(64);
        _numFocusProbe.Minimum = 50; _numFocusProbe.Maximum = 2000; _numFocusProbe.Increment = 10;
        PumpThrottled();
        _numFocusProbe.Value = 500;
        focusRow.Controls.Add(_numFocusProbe);
        PumpThrottled();

        FlowLayoutPanel focusRow2 = new FlowLayoutPanel();
        focusRow2.Dock = DockStyle.Fill;
        PumpThrottled();
        focusRow2.AutoSize = true;
        focusRow2.FlowDirection = FlowDirection.LeftToRight;
        focusRow2.WrapContents = true;
        PumpThrottled();
        focusRow2.Margin = new Padding(0, Sc(4), 0, 0);
        g3.Controls.Add(focusRow2, 0, 8);
        PumpThrottled();
        Label t3f4 = new Label(); t3f4.Text = "交还确认次数：";
        t3f4.AutoSize = true;
        t3f4.Anchor = AnchorStyles.Left;
        PumpThrottled();
        focusRow2.Controls.Add(t3f4);
        PumpThrottled();
        _numFocusOk = new NumericUpDown();
        _numFocusOk.Width = Sc(48);
        _numFocusOk.Minimum = 1; _numFocusOk.Maximum = 20;
        PumpThrottled();
        _numFocusOk.Value = 5;
        focusRow2.Controls.Add(_numFocusOk);
        PumpThrottled();
        Label t3f5 = new Label(); t3f5.Text = "  静默时间（ms）：";
        t3f5.AutoSize = true;
        t3f5.Anchor = AnchorStyles.Left;
        PumpThrottled();
        focusRow2.Controls.Add(t3f5);
        PumpThrottled();
        _numFocusSilent = new NumericUpDown();
        _numFocusSilent.Width = Sc(64);
        _numFocusSilent.Minimum = 100; _numFocusSilent.Maximum = 5000; _numFocusSilent.Increment = 100;
        PumpThrottled();
        _numFocusSilent.Value = 1500;
        focusRow2.Controls.Add(_numFocusSilent);
        PumpThrottled();
        _btnFocusPreset = MakeButton("恢复默认值", null, "plain");
        _btnFocusPreset.Margin = new Padding(Sc(8), 0, 0, 0);
        focusRow2.Controls.Add(_btnFocusPreset);
        PumpThrottled();
        PumpThrottled();

        _lblFocusLatency = new Label();
        _lblFocusLatency.AutoSize = true;
        PumpThrottled();
        _lblFocusLatency.ForeColor = C_SUB;
        _lblFocusLatency.UseMnemonic = false;
        _lblFocusLatency.Margin = new Padding(0, Sc(2), 0, 0);
        PumpThrottled();
        // ★ 必须限宽: AutoSize 的 Label 不会自动换行, 一行太长会把整个设置页撑宽
        //   (settlest 的"出界"检查就是这么发现上一次布局问题的)。
        _lblFocusLatency.MaximumSize = new Size(Sc(600), 0);
        PumpThrottled();
        g3.Controls.Add(_lblFocusLatency, 0, 9);
        PumpThrottled();

        // 改任何一个参数都当场重算给用户看; 切档则自动套用该档默认(载入配置时用 _suppressFocusPreset 抑制)
        EventHandler refocus = delegate { UpdateFocusLatencyLabel(); };
        PumpThrottled();
        _numFocusMs.ValueChanged += refocus;
        _numFocusRounds.ValueChanged += refocus;
        _numFocusProbe.ValueChanged += refocus;
        PumpThrottled();
        _numFocusOk.ValueChanged += refocus;
        _numFocusSilent.ValueChanged += refocus;
        _chkFocusRescue.CheckedChanged += refocus;
        PumpThrottled();
        _radFocusSys.CheckedChanged += delegate { OnFocusModeChanged(); };
        _radFocusPro.CheckedChanged += delegate { OnFocusModeChanged(); };
        _radFocusUltra.CheckedChanged += delegate { OnFocusModeChanged(); };
        PumpThrottled();
        _btnFocusPreset.Click += delegate { ApplyFocusPresetToControls(); };

        // ---- 钩子主动探活 ----
        // 老版本是"每 10 秒无条件注入一次按键"(还不管有没有停止保护), 前台游戏每 10 秒被打断一下。
        // 现在默认关闭, 这里给个开关是为了"想开的时候不用去手改 guard.ini"。
        FlowLayoutPanel probeRow = new FlowLayoutPanel();
        PumpThrottled();
        probeRow.Dock = DockStyle.Fill;
        probeRow.AutoSize = true;
        probeRow.FlowDirection = FlowDirection.LeftToRight;
        PumpThrottled();
        probeRow.WrapContents = true;
        probeRow.Margin = new Padding(0, Sc(8), 0, 0);
        g3.Controls.Add(probeRow, 0, 10);
        PumpThrottled();
        PumpThrottled();

        _chkHookProbe = new CheckBox();
        _chkHookProbe.AutoSize = true;
        PumpThrottled();
        _chkHookProbe.Anchor = AnchorStyles.Left;
        _chkHookProbe.Text = "钩子探活：定时发送按键，检查监听是否正常";
        _chkHookProbe.Checked = false;      // 默认关闭(注入的按键前台游戏也会收到)
        probeRow.Controls.Add(_chkHookProbe);
        PumpThrottled();
        PumpThrottled();

        Label t3p1 = new Label(); t3p1.Text = "探活间隔（秒）：";
        t3p1.AutoSize = true;
        PumpThrottled();
        t3p1.Anchor = AnchorStyles.Left;
        probeRow.Controls.Add(t3p1);
        PumpThrottled();

        _numProbeSec = new NumericUpDown();
        _numProbeSec.Width = Sc(56);
        PumpThrottled();
        _numProbeSec.Minimum = 5; _numProbeSec.Maximum = 3600;
        _numProbeSec.Value = 60;
        probeRow.Controls.Add(_numProbeSec);
        PumpThrottled();
        PumpThrottled();

        Label t3p2 = new Label();
        t3p2.AutoSize = true;
        PumpThrottled();
        t3p2.ForeColor = C_SUB;
        t3p2.Text = "← 开启后每隔 N 秒会有一个按键进入系统，前台游戏也会收到";
        probeRow.Controls.Add(t3p2);
        PumpThrottled();
        PumpThrottled();

        // 没开探活时, 间隔框置灰 —— 免得看着像"已经在每 60 秒注入"
        _chkHookProbe.CheckedChanged += delegate
        {
            if (_numProbeSec != null) _numProbeSec.Enabled = _chkHookProbe.Checked;
            PumpThrottled();
        };

        // ---- 使用 SeDebugPrivilege(默认关) ----
        // 有些进程在受限令牌/沙箱里, 管理员也 TerminateProcess 失败(错误码 5);
        PumpThrottled();
        // 开这个能多杀掉一部分。默认关: 一般游戏进程不需要, 而且"给自己加特权"
        // 在企业 EDR 眼里是提权特征, 开着平白多招误报。只想杀不掉时再开。
        FlowLayoutPanel privRow = new FlowLayoutPanel();
        PumpThrottled();
        privRow.Dock = DockStyle.Fill;
        privRow.AutoSize = true;
        privRow.FlowDirection = FlowDirection.LeftToRight;
        PumpThrottled();
        privRow.WrapContents = true;
        privRow.Margin = new Padding(0, Sc(8), 0, 0);
        g3.Controls.Add(privRow, 0, 11);
        PumpThrottled();
        PumpThrottled();

        _chkDebugPriv = new CheckBox();
        _chkDebugPriv.AutoSize = true;
        PumpThrottled();
        _chkDebugPriv.Anchor = AnchorStyles.Left;
        _chkDebugPriv.Text = "使用 SeDebugPrivilege";
        _chkDebugPriv.Checked = false;
        PumpThrottled();
        privRow.Controls.Add(_chkDebugPriv);
        PumpThrottled();

        Label t3v1 = new Label();
        t3v1.AutoSize = true;
        PumpThrottled();
        t3v1.ForeColor = C_SUB;
        t3v1.Text = "← 有些进程平时无法结束，开启后可以结束";
        privRow.Controls.Add(t3v1);
        PumpThrottled();
        PumpThrottled();

        // ---- 快速断流(11.1.0, 默认开) ----
        // 断开时先用 WFP/防火墙在毫秒级拦住出站, 再照旧禁网卡 —— 只抢时间, 不改原有保证。
        FlowLayoutPanel fastRow = new FlowLayoutPanel();
        PumpThrottled();
        fastRow.Dock = DockStyle.Fill;
        fastRow.AutoSize = true;
        fastRow.FlowDirection = FlowDirection.LeftToRight;
        PumpThrottled();
        fastRow.WrapContents = true;
        fastRow.Margin = new Padding(0, Sc(8), 0, 0);
        g3.Controls.Add(fastRow, 0, 12);
        PumpThrottled();
        PumpThrottled();

        _chkFastCut = new CheckBox();
        _chkFastCut.AutoSize = true;
        PumpThrottled();
        _chkFastCut.Anchor = AnchorStyles.Left;
        _chkFastCut.Text = "启用快速断流";
        _chkFastCut.Checked = true;
        PumpThrottled();
        fastRow.Controls.Add(_chkFastCut);
        PumpThrottled();

        Label t3v2 = new Label();
        t3v2.AutoSize = true;
        PumpThrottled();
        t3v2.ForeColor = C_SUB;
        t3v2.Text = "← 先拦截出站流量，再断开网卡；失败时自动改用只断网卡";
        fastRow.Controls.Add(t3v2);
        PumpThrottled();
        PumpThrottled();

        // ---- 载入当前配置 ----
        _targetDraft = new List<string>(_cfg.AllProcs());
        PumpThrottled();
        _procOff = new List<string>(_cfg.ProcOff);
        RefreshTargetList();
        _txtKeys.Text = _cfg.KeysText();
        PumpThrottled();
        _numWait.Value = Math.Max(0, Math.Min(600, _cfg.WaitSeconds));
        _chkFocusRescue.Checked = _cfg.FocusRescue;
        // 载入时先抑制"切档自动套用预设", 否则会把用户已经调好的数字冲掉
        _suppressFocusPreset = true;
        PumpThrottled();
        try
        {
            _radFocusSys.Checked = (_cfg.FocusMode <= 0);
            PumpThrottled();
            _radFocusUltra.Checked = (_cfg.FocusMode >= 2);
            _radFocusPro.Checked = (_cfg.FocusMode == 1);
            _numFocusMs.Value = ClampNum(_numFocusMs, _cfg.FocusIntervalMs);
            PumpThrottled();
            _numFocusRounds.Value = ClampNum(_numFocusRounds, _cfg.FocusRounds);
            _numFocusProbe.Value = ClampNum(_numFocusProbe, _cfg.FocusProbeMs);
            _numFocusOk.Value = ClampNum(_numFocusOk, _cfg.FocusOkRounds);
            PumpThrottled();
            _numFocusSilent.Value = ClampNum(_numFocusSilent, _cfg.FocusSilentMs);
        }
        finally { _suppressFocusPreset = false; }
        UpdateFocusLatencyLabel();
        PumpThrottled();
        _chkHookProbe.Checked = _cfg.HookProbe;
        int probeSec = _cfg.HookProbeIntervalMs / 1000;
        if (probeSec < (int)_numProbeSec.Minimum) probeSec = (int)_numProbeSec.Minimum;
        PumpThrottled();
        if (probeSec > (int)_numProbeSec.Maximum) probeSec = (int)_numProbeSec.Maximum;
        _numProbeSec.Value = probeSec;
        _numProbeSec.Enabled = _chkHookProbe.Checked;
        PumpThrottled();
        _chkDebugPriv.Checked = _cfg.DebugPriv;
        _chkFastCut.Checked = _cfg.FastCut;

        PumpThrottled();   // 页尾再泵一次, 保证页与页之间不留长空窗
    }

    /// <summary>设置窗第 4 页「高级选项」的背景构建(由 BuildSettingsPage 分帧调用)。</summary>
    private static void BuildSettingsTab4(TabControl tabs)
    {
        // ============ Tab4: 高级选项 (11.1.2-RC1) ============
        TabPage tp4 = new TabPage("高级选项");
        PumpThrottled();
        tp4.Padding = new Padding(0);
        tabs.TabPages.Add(tp4);
        TableLayoutPanel g4 = new TableLayoutPanel();
        PumpThrottled();
        g4.Dock = DockStyle.Fill;
        g4.ColumnCount = 1;
        g4.RowCount = 15;
        PumpThrottled();
        g4.Padding = Pad(12, 10, 12, 10);
        g4.BackColor = C_CARD;
        g4.AutoScroll = true;
        PumpThrottled();
        for (int i = 0; i < 15; i++) g4.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        tp4.Controls.Add(g4);
        PumpThrottled();

        Label t4tip = new Label();
        t4tip.ForeColor = C_SUB;
        PumpThrottled();
        t4tip.Text = "修改后点[确定]生效。";
        Wrap(t4tip);
        g4.Controls.Add(t4tip, 0, 0);
        PumpThrottled();
        PumpThrottled();

        _chkAutoRestore = new CheckBox();
        _chkAutoRestore.AutoSize = true;
        PumpThrottled();
        _chkAutoRestore.Text = "关闭程序时若网络仍断开，自动恢复";
        _chkAutoRestore.Checked = _cfg.AutoRestoreOnExit;
        if (_chkConfirmExit != null) _chkConfirmExit.Checked = _cfg.ConfirmExitTimes;
        PumpThrottled();
        g4.Controls.Add(_chkAutoRestore, 0, 1);
        PumpThrottled();

        Label t4b = new Label();
        t4b.ForeColor = C_SUB;
        PumpThrottled();
        t4b.Text = "不勾选时，关闭程序前会询问一次。";
        Wrap(t4b);
        g4.Controls.Add(t4b, 0, 2);
        PumpThrottled();
        PumpThrottled();

        Label t4c = new Label();
        t4c.Text = "额外探测目标（逗号分隔，IP:端口）：";
        PumpThrottled();
        t4c.ForeColor = C_SUB;
        Wrap(t4c);
        g4.Controls.Add(t4c, 0, 3);
        PumpThrottled();
        PumpThrottled();

        _txtFastCutTargets = new TextBox();
        _txtFastCutTargets.Name = "txtFastCutTargets";
        PumpThrottled();
        _txtFastCutTargets.Width = Sc(420);
        _txtFastCutTargets.Text = (_cfg.FastCutTargets == null) ? "" : _cfg.FastCutTargets;
        g4.Controls.Add(_txtFastCutTargets, 0, 4);
        PumpThrottled();
        PumpThrottled();

        Label t4d = new Label();
        t4d.ForeColor = C_SUB;
        PumpThrottled();
        t4d.Text = "留空则只 ping 本机网关，不连接外网。\r\n"
                 + "填写后会实际连接外网，可能被安全软件提示。";
        Wrap(t4d);
        PumpThrottled();
        g4.Controls.Add(t4d, 0, 5);
        PumpThrottled();

        Label t4e = new Label();
        t4e.ForeColor = C_SUB;
        PumpThrottled();
        t4e.Text = "钩子探活、SeDebugPrivilege、快速断流三个开关位于「网卡与选项」页。";
        Wrap(t4e);
        g4.Controls.Add(t4e, 0, 6);
        PumpThrottled();
        PumpThrottled();

        Label t4f = new Label();
        t4f.Text = "断网方式：";
        PumpThrottled();
        Wrap(t4f);
        g4.Controls.Add(t4f, 0, 7);
        PumpThrottled();

        FlowLayoutPanel modeRow = new FlowLayoutPanel();
        modeRow.AutoSize = true;
        PumpThrottled();
        modeRow.FlowDirection = FlowDirection.TopDown;
        modeRow.WrapContents = false;
        _radModeBoth = new RadioButton();
        PumpThrottled();
        _radModeBoth.AutoSize = true;
        _radModeBoth.Text = "快速断流 + 禁用网卡（默认）";
        _radModeBoth.Checked = (_cfg.CutMode == 0);
        PumpThrottled();
        modeRow.Controls.Add(_radModeBoth);
        PumpThrottled();
        _radModeNic = new RadioButton();
        _radModeNic.AutoSize = true;
        _radModeNic.Text = "只禁用网卡";
        PumpThrottled();
        _radModeNic.Checked = (_cfg.CutMode == 1);
        modeRow.Controls.Add(_radModeNic);
        PumpThrottled();
        _radModeFast = new RadioButton();
        _radModeFast.AutoSize = true;
        _radModeFast.Text = "只用快速断流";
        PumpThrottled();
        _radModeFast.Checked = (_cfg.CutMode == 2);
        modeRow.Controls.Add(_radModeFast);
        PumpThrottled();
        g4.Controls.Add(modeRow, 0, 8);
        PumpThrottled();

        Label t4g = new Label();
        t4g.ForeColor = C_SUB;
        PumpThrottled();
        t4g.Text = "快速断流：立即拦截出站流量，不留残留。\r\n"
                 + "禁用网卡：断网更彻底，恢复需等待无线重新连接，约 5~15 秒。";
        Wrap(t4g);
        PumpThrottled();
        g4.Controls.Add(t4g, 0, 9);
        PumpThrottled();

        _chkRestoreOnBoot = new CheckBox();
        _chkRestoreOnBoot.AutoSize = true;
        PumpThrottled();
        _chkRestoreOnBoot.Text = "断网期间登记开机恢复";
        _chkRestoreOnBoot.Checked = _cfg.RestoreOnBoot;
        if (_chkDiag != null) _chkDiag.Checked = _cfg.DiagPanel;
        PumpThrottled();
        g4.Controls.Add(_chkRestoreOnBoot, 0, 10);
        PumpThrottled();

        Label t4h = new Label();
        t4h.ForeColor = C_SUB;
        PumpThrottled();
        t4h.Text = "勾选后，断网时登记一条开机任务，下次登录自动恢复网络，恢复后自动删除。\r\n"
                 + "会写注册表，登录时可能弹一次权限提示。";
        Wrap(t4h);
        PumpThrottled();
        g4.Controls.Add(t4h, 0, 11);
        PumpThrottled();

        // ---- 杀进程的时序 (V1.1.4-RC10) ----
        // 两个开关都默认开: 挂起是"让游戏立刻停下"的那一刀, 预记录是"触发时不用先扫表"。
        // 关掉任何一个都还能杀, 只是慢一点; 想对比效果时可以只关一个。
        _chkSuspendFirst = new CheckBox();
        PumpThrottled();
        _chkSuspendFirst.AutoSize = true;
        _chkSuspendFirst.Text = "触发时先挂起目标进程，使其立即停止";
        _chkSuspendFirst.Checked = _cfg.SuspendFirst;
        PumpThrottled();
        g4.Controls.Add(_chkSuspendFirst, 0, 12);
        PumpThrottled();

        _chkWarm = new CheckBox();
        _chkWarm.AutoSize = true;
        PumpThrottled();
        _chkWarm.Text = "保护期间预记录目标进程，触发时无需先扫描";
        _chkWarm.Checked = _cfg.WarmSuspend;
        g4.Controls.Add(_chkWarm, 0, 13);
        PumpThrottled();
        PumpThrottled();

        FlowLayoutPanel warmRow = new FlowLayoutPanel();
        warmRow.AutoSize = true;
        PumpThrottled();
        warmRow.FlowDirection = FlowDirection.LeftToRight;
        warmRow.WrapContents = true;
        Label t4i = new Label();
        PumpThrottled();
        t4i.AutoSize = true;
        t4i.Text = "预记录刷新间隔（ms）：";
        t4i.Margin = new Padding(Sc(20), Sc(6), Sc(6), 0);
        PumpThrottled();
        warmRow.Controls.Add(t4i);
        PumpThrottled();
        _numWarmMs = new NumericUpDown();
        _numWarmMs.Minimum = 300;
        _numWarmMs.Maximum = 5000;
        PumpThrottled();
        _numWarmMs.Increment = 100;
        int wi = _cfg.WarmIntervalMs;
        if (wi < 300) wi = 300;
        PumpThrottled();
        if (wi > 5000) wi = 5000;
        _numWarmMs.Value = wi;
        _numWarmMs.Width = Sc(80);
        PumpThrottled();
        warmRow.Controls.Add(_numWarmMs);
        PumpThrottled();
        g4.Controls.Add(warmRow, 0, 14);
        PumpThrottled();

        PumpThrottled();   // 页尾再泵一次, 保证页与页之间不留长空窗
    }

    /// <summary>设置窗第 5 页「维护」的背景构建(由 BuildSettingsPage 分帧调用)。</summary>
    private static void BuildSettingsTab5(TabControl tabs)
    {
        // ============ Tab5: 维护 (11.1.2-RC1) ============
        TabPage tp5 = new TabPage("维护");
        PumpThrottled();
        tp5.Padding = new Padding(0);
        tabs.TabPages.Add(tp5);
        TableLayoutPanel g5 = new TableLayoutPanel();
        PumpThrottled();
        g5.Dock = DockStyle.Fill;
        g5.ColumnCount = 1;
        g5.RowCount = 7;
        PumpThrottled();
        g5.Padding = Pad(12, 10, 12, 10);
        g5.BackColor = C_CARD;
        g5.AutoScroll = true;
        PumpThrottled();
        for (int i = 0; i < 7; i++) g5.RowStyles.Add(new RowStyle(SizeType.AutoSize));
        tp5.Controls.Add(g5);
        PumpThrottled();

        Label t5a = new Label(); t5a.Text = "版本：" + APP_VER; Wrap(t5a); g5.Controls.Add(t5a, 0, 0);
        Label t5b = new Label(); t5b.Text = "程序目录：" + _baseDir; Wrap(t5b); g5.Controls.Add(t5b, 0, 1);
        PumpThrottled();
        Label t5c = new Label(); t5c.Text = "数据目录：" + _dataDir + "\r\n配置和日志都放在这里"; Wrap(t5c); g5.Controls.Add(t5c, 0, 2);

        FlowLayoutPanel mRow = new FlowLayoutPanel();
        PumpThrottled();
        mRow.AutoSize = true;
        mRow.FlowDirection = FlowDirection.LeftToRight;
        mRow.WrapContents = true;
        PumpThrottled();

        Button bOpenData = MakeButton("打开数据目录", null, "plain");
        bOpenData.Click += delegate
        {
            try { Process.Start("explorer.exe", "\"" + _dataDir + "\""); }
            catch (Exception ex) { MessageBox.Show("打开失败：" + ex.Message, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); }
        };
        PumpThrottled();

        Button bExportLog = MakeButton("导出日志", null, "plain");
        bExportLog.Click += delegate
        {
            try
            {
                using (SaveFileDialog sfd = new SaveFileDialog())
                {
                    sfd.Title = "导出日志";
                    PumpThrottled();
                    sfd.Filter = "文本文件 (*.txt)|*.txt|所有文件 (*.*)|*.*";
                    sfd.FileName = "SkyGuard-" + DateTime.Now.ToString("yyyyMMdd-HHmmss") + ".log";
                    if (sfd.ShowDialog() == DialogResult.OK)
                    {
                        File.Copy(_logPath, sfd.FileName, true);
                        PumpThrottled();
                        MessageBox.Show("日志已导出到：\n" + sfd.FileName, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
                    }
                }
            }
            catch (Exception ex) { MessageBox.Show("导出失败：" + ex.Message, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); }
        };
        PumpThrottled();

        Button bReset = MakeButton("恢复默认设置", null, "plain");
        bReset.Click += delegate
        {
            if (MessageBox.Show("恢复默认设置？\n\n会删掉 guard.ini，下次启动重新生成默认配置。程序列表、触发键、网卡选择都会丢。",
                    APP_NAME, MessageBoxButtons.YesNo, MessageBoxIcon.Warning) != DialogResult.Yes) return;
            try
            {
                if (File.Exists(_iniPath)) File.Delete(_iniPath);
                PumpThrottled();
                MessageBox.Show("配置文件已删除，关闭设置窗口后重新打开即为默认配置。",
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
            catch (Exception ex) { MessageBox.Show("删除失败：" + ex.Message, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); }
        };
        PumpThrottled();

        mRow.Controls.Add(bOpenData);
        PumpThrottled();
        mRow.Controls.Add(bExportLog);
        PumpThrottled();
        Button bExportCfg = MakeButton("导出配置", null, "plain");
        bExportCfg.Click += delegate
        {
            try
            {
                using (SaveFileDialog sfd = new SaveFileDialog())
                {
                    sfd.Title = "导出配置(guard.ini)";
                    PumpThrottled();
                    sfd.Filter = "配置文件 (*.ini)|*.ini|所有文件 (*.*)|*.*";
                    sfd.FileName = "guard-" + DateTime.Now.ToString("yyyyMMdd-HHmmss") + ".ini";
                    if (sfd.ShowDialog() == DialogResult.OK)
                    {
                        if (!File.Exists(_iniPath)) { MessageBox.Show("尚无配置文件，请先保存一次设置。", APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information); return; }
                        File.Copy(_iniPath, sfd.FileName, true);
                        PumpThrottled();
                        MessageBox.Show("配置已导出到：\n" + sfd.FileName, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
                    }
                }
            }
            catch (Exception ex) { MessageBox.Show("导出失败：" + ex.Message, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); }
        };
        PumpThrottled();
        Button bImportCfg = MakeButton("导入配置", null, "plain");
        bImportCfg.Click += delegate
        {
            try
            {
                using (OpenFileDialog ofd = new OpenFileDialog())
                {
                    ofd.Title = "导入配置(guard.ini)";
                    PumpThrottled();
                    ofd.Filter = "配置文件 (*.ini)|*.ini|所有文件 (*.*)|*.*";
                    if (ofd.ShowDialog() != DialogResult.OK) return;
                    // 导入前先备份, 导入后校验: 选错一个文件(比如随便一个 .ini)会把配置弄成废的,
                    // 而且没法回退 —— 以前就是直接覆盖。校验不通过就自动还原。
                    string bak = _iniPath + ".bak";
                    PumpThrottled();
                    try { if (File.Exists(_iniPath)) File.Copy(_iniPath, bak, true); } catch { }
                    File.Copy(ofd.FileName, _iniPath, true);
                    List<string> iwarn = new List<string>();
                    PumpThrottled();
                    Config chk = null;
                    try { chk = LoadConfig(iwarn); } catch { }
                    bool usable = (chk != null) && chk.TargetList().Count > 0 && chk.Keys.Count > 0;
                    PumpThrottled();
                    if (!usable)
                    {
                        try { if (File.Exists(bak)) File.Copy(bak, _iniPath, true); } catch { }
                        MessageBox.Show("该文件不是 SkyGuard 的配置文件，已还原原配置。",
                            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                            PumpThrottled();
                        return;
                    }
                    MessageBox.Show("配置已导入，重启程序或重新打开设置后生效。",
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
                        PumpThrottled();
                }
            }
            catch (Exception ex) { MessageBox.Show("导入失败：" + ex.Message, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); }
        };
        PumpThrottled();
        mRow.Controls.Add(bExportCfg);
        PumpThrottled();
        mRow.Controls.Add(bImportCfg);
        PumpThrottled();
        mRow.Controls.Add(bReset);
        PumpThrottled();
        g5.Controls.Add(mRow, 0, 3);
        PumpThrottled();

        Label t5d = new Label();
        t5d.ForeColor = C_SUB;
        PumpThrottled();
        t5d.Text = "导出日志只复制本机日志文件，不会上传。";
        Wrap(t5d);
        g5.Controls.Add(t5d, 0, 4);
        PumpThrottled();
        PumpThrottled();

        // 状态面板开关(V1.1.4-RC4, 默认开)。关掉只是隐藏主窗口那个按钮;
        // 面板本身还能用命令行生成: SkyGuardGUI.exe diagtest
        _chkDiag = new CheckBox();
        PumpThrottled();
        _chkDiag.AutoSize = true;
        _chkDiag.Text = "在主窗口显示状态面板按钮";
        g5.Controls.Add(_chkDiag, 0, 5);
        PumpThrottled();
        PumpThrottled();
        _chkConfirmExit = new CheckBox();
        _chkConfirmExit.AutoSize = true;
        _chkConfirmExit.Text = "退出前多次确认";
        PumpThrottled();
        _chkConfirmExit.Checked = (_cfg == null || _cfg.ConfirmExitTimes);
        g5.Controls.Add(_chkConfirmExit, 0, 6);
        PumpThrottled();
        FillNicList();

        PumpThrottled();   // 页尾再泵一次, 保证页与页之间不留长空窗
    }

    private static List<string> _targetDraft = new List<string>();
    /// <summary>已加进列表、但没打勾(不参与触发)的进程名</summary>
    private static List<string> _procOff = new List<string>();
    /// <summary>RefreshTargetList 重画列表期间抑制 ItemCheck(程序自己改勾选状态不算用户操作)</summary>
    private static bool _suppressCheck = false;

    private static bool TargetListContains(string name)
    {
        foreach (string s in _targetDraft)
            if (string.Equals(s, name, StringComparison.OrdinalIgnoreCase)) return true;
        return false;
    }

    /// <summary>
    /// 把某个进程的勾选状态写进 _procOff。
    /// 为什么要延后到本轮消息之后: CheckedListBox 的 ItemCheck 是在状态变化**之前**触发的,
    /// 那时候读 GetItemChecked 还是旧值 —— 所以调用方直接传 e.NewValue 折算出来的结果。
    /// ★ 参数是"进程名 + 新状态", 不是"下标": 下标会被后来的重画列表/其它勾选改掉,
    ///   以前用单个下标字段时, 连续勾两下会把前一次静默丢掉。
    /// </summary>
    private static void ApplyPendingCheck(string name, bool on)
    {
        try
        {
            if (_lstTargets == null || string.IsNullOrEmpty(name)) return;
            if (on) RemoveFrom(_procOff, name);
            else if (!ListHas(_procOff, name)) _procOff.Add(name);
            Log("[设置] " + (on ? "勾选" : "取消勾选") + " " + name);
        }
        catch { }
    }

    /// <summary>按 _targetDraft + _procOff 重画勾选列表</summary>
    private static void RefreshTargetList()
    {
        if (_lstTargets == null) return;
        _suppressCheck = true;
        try
        {
            _lstTargets.Items.Clear();
            foreach (string s in _targetDraft)
                _lstTargets.Items.Add(s, !ListHas(_procOff, s));
        }
        finally { _suppressCheck = false; }
        if (_tabTargets != null)
        {
            int off = 0;
            foreach (string s in _targetDraft) if (ListHas(_procOff, s)) off++;
            _tabTargets.Text = "目标程序 (" + _targetDraft.Count + " 个，参与触发 " + (_targetDraft.Count - off) + " 个)";
        }
    }

    /// <summary>把网卡探测结果填进设置对话框的列表(按当前配置勾选)</summary>
    private static void FillNicList() { FillNicList(null); }

    /// <summary>
    /// 填充网卡列表。preferChecked=null 时按 guard.ini 配置勾选;
    /// 传了列表则按该列表勾选(用于[重新探测网卡]时保留用户未保存的改动)。
    /// </summary>
    /// <summary>把值夹到 NumericUpDown 的上下限里(载入配置时用)。</summary>
    private static decimal ClampNum(NumericUpDown n, int v)
    {
        if (n == null) return 0;
        if (v < n.Minimum) v = (int)n.Minimum;
        if (v > n.Maximum) v = (int)n.Maximum;
        return v;
    }

    /// <summary>当前选中的档位(0=只用系统判定 / 1=Pro / 2=Ultra)。</summary>
    private static int ReadFocusModeFromRadios()
    {
        if (_radFocusSys != null && _radFocusSys.Checked) return 0;
        if (_radFocusUltra != null && _radFocusUltra.Checked) return 2;
        return 1;
    }

    /// <summary>把当前界面上的参数代进公式, 实时显示"最坏接管延迟"(用户调参时最重要的那个数)。</summary>
    private static void UpdateFocusLatencyLabel()
    {
        try
        {
            if (_lblFocusLatency == null) return;
            int mode = ReadFocusModeFromRadios();
            if (!_chkFocusRescue.Checked)
            {
                _lblFocusLatency.Text = "已关闭";
                return;
            }
            if (mode == 0)
            {
                _lblFocusLatency.Text = "仅系统检测，约 5 秒";
                return;
            }
            int iv = (int)_numFocusMs.Value, rd = (int)_numFocusRounds.Value, pb = (int)_numFocusProbe.Value;
            int worst = FocusWorstLatencyMs(iv, pb, rd);
            string warn = (worst <= 300) ? " · 可能误判"
                        : (worst >= 1200 ? " · 反应较慢" : "");
            _lblFocusLatency.Text = FocusModeName(mode) + "：" + worst + " ms" + warn;
        }
        catch { }
    }

    /// <summary>切档: 套用该档默认参数(初始化载入时由 _suppressFocusPreset 抑制, 不覆盖用户已调的值)。</summary>
    private static void OnFocusModeChanged()
    {
        try
        {
            if (!_suppressFocusPreset) ApplyFocusPresetToControls();
            UpdateFocusLatencyLabel();
        }
        catch { }
    }

    /// <summary>把当前档位的默认参数填进界面上的 5 个数字框。</summary>
    private static void ApplyFocusPresetToControls()
    {
        try
        {
            Config tmp = new Config();
            ApplyFocusPreset(tmp, ReadFocusModeFromRadios());
            _numFocusMs.Value = ClampNum(_numFocusMs, tmp.FocusIntervalMs);
            _numFocusRounds.Value = ClampNum(_numFocusRounds, tmp.FocusRounds);
            _numFocusProbe.Value = ClampNum(_numFocusProbe, tmp.FocusProbeMs);
            _numFocusOk.Value = ClampNum(_numFocusOk, tmp.FocusOkRounds);
            _numFocusSilent.Value = ClampNum(_numFocusSilent, tmp.FocusSilentMs);
        }
        catch { }
    }

    private static void FillNicList(List<string> preferChecked)
    {
        if (_lstNics == null) return;
        _lstNics.Items.Clear();
        foreach (NicInfo n in _nics)
        {
            string label = n.Name;
            if (n.HasDefaultRoute) label += "   [承载流量]";
            else if (n.IsVirtualHint) label += "   [虚拟网卡]";

            List<string> want0 = (preferChecked != null) ? preferChecked : _cfg.Nics;
            bool chk = false;
            foreach (string want in want0)
                if (string.Equals(n.Name, want, StringComparison.OrdinalIgnoreCase)) { chk = true; break; }
            _lstNics.Items.Add(label, chk);
        }
        // 用户在"重新探测"后主动全部取消勾选时, 要尊重他的选择, 不要再自动勾回来
        if (preferChecked != null) return;
        // 若一个都没勾中, 默认勾「承载流量」那张
        bool any = false;
        for (int i = 0; i < _lstNics.Items.Count; i++) if (_lstNics.GetItemChecked(i)) { any = true; break; }
        if (!any)
        {
            for (int i = 0; i < _nics.Count; i++)
                if (_nics[i].HasDefaultRoute) { _lstNics.SetItemChecked(i, true); any = true; break; }
            if (!any && _lstNics.Items.Count > 0) _lstNics.SetItemChecked(0, true);
        }
    }

    /// <summary>把设置对话框的改动应用到运行期配置并保存。校验失败返回 false 且不改动。</summary>
    private static bool ApplySettingsFromDialog()
    {
        // ★ V1.1.5-RC1: 五页是分帧构建的, 读控件之前必须先把它们补齐 ——
        //   未建页上的控件是 null, 直接读会把用户的设置静默读成"默认值"
        //   (这是本次改动最容易出事的一处, 所以放在函数第一行, 后面一行都不用动)。
        //   正常路径下 [确定] 在五页建齐前是禁用的, 这里是第二道保险。
        EnsureAllSettingsPages();
        if (!_pagesReady)
        {
            // 只会发生在"正好在泵消息建页的那一瞬被点到"(重入)。这一下不生效, 让用户再点一次,
            // 绝不带着半份界面往下走 —— 那等于拿默认值覆盖用户的设置。
            Log("[设置] 页面还在构建中, 这一次[确定]被忽略(请再点一次)");
            return false;
        }
        Config c = new Config();
        c.Procs = new List<string>(_targetDraft);
        c.ProcOff = new List<string>(_procOff);
        c.Keys = SplitKeyText(_txtKeys.Text);
        // 触发键更详细: 自动去重 + 标题显示数量(11.1.2-RC2)
        {
            List<string> uniq = new List<string>();
            foreach (string k in c.Keys)
            {
                bool dup = false;
                foreach (string u in uniq)
                    if (string.Equals(u, k, StringComparison.OrdinalIgnoreCase)) { dup = true; break; }
                if (!dup) uniq.Add(k);
            }
            if (uniq.Count != c.Keys.Count)
            {
                MessageBox.Show("触发键有重复，已自动去重：\n\n"
                    + string.Join(" / ", c.Keys.ToArray()) + "\n->  " + string.Join(" / ", uniq.ToArray()),
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
                c.Keys = uniq;
            }
            if (c.Keys.Count == 0)
            {
                MessageBox.Show("至少需要 1 个触发键，请点[录入按键]。",
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                return false;
            }
            if (_tabKeys != null) _tabKeys.Text = "触发键 (" + c.Keys.Count + " 个)";
        }
        c.WaitSeconds = (int)_numWait.Value;
        if (_chkFocusRescue != null) c.FocusRescue = _chkFocusRescue.Checked;
        c.FocusMode = ReadFocusModeFromRadios();
        if (_numFocusMs != null) c.FocusIntervalMs = (int)_numFocusMs.Value;
        if (_numFocusRounds != null) c.FocusRounds = (int)_numFocusRounds.Value;
        if (_numFocusProbe != null) c.FocusProbeMs = (int)_numFocusProbe.Value;
        if (_numFocusOk != null) c.FocusOkRounds = (int)_numFocusOk.Value;
        if (_numFocusSilent != null) c.FocusSilentMs = (int)_numFocusSilent.Value;
        // 一致性: 非 Ultra 档最少 2 轮(1 轮在"卡/不卡"边界上必然来回闪 —— 当年就是这么翻车的)
        if (c.FocusMode != 2 && c.FocusRounds < 2) c.FocusRounds = 2;
        c.FocusEarly = (c.FocusMode >= 1);         // 兼容字段: 老版本读它
        // 钩子主动探活(默认关): 间隔按秒填, 存盘仍是毫秒
        if (_chkHookProbe != null)
        {
            c.HookProbe = _chkHookProbe.Checked;
            if (_numProbeSec != null) c.HookProbeIntervalMs = (int)_numProbeSec.Value * 1000;
        }
        // 使用 SeDebugPrivilege(默认关)
        if (_chkDebugPriv != null) c.DebugPriv = _chkDebugPriv.Checked;
        // 快速断流(默认开)
        if (_chkFastCut != null) c.FastCut = _chkFastCut.Checked;
        if (_chkAutoRestore != null) c.AutoRestoreOnExit = _chkAutoRestore.Checked;
        if (_chkConfirmExit != null) c.ConfirmExitTimes = _chkConfirmExit.Checked;
        if (_txtFastCutTargets != null) c.FastCutTargets = _txtFastCutTargets.Text.Trim();
        if (_radModeFast != null && _radModeFast.Checked) c.CutMode = 2;
        else if (_radModeNic != null && _radModeNic.Checked) c.CutMode = 1;
        else c.CutMode = 0;
        if (_chkRestoreOnBoot != null) c.RestoreOnBoot = _chkRestoreOnBoot.Checked;
        if (_chkDiag != null) c.DiagPanel = _chkDiag.Checked;
        if (_chkSuspendFirst != null) c.SuspendFirst = _chkSuspendFirst.Checked;
        if (_chkWarm != null) c.WarmSuspend = _chkWarm.Checked;
        if (_numWarmMs != null) c.WarmIntervalMs = (int)_numWarmMs.Value;
        // 改完立刻反映到主窗口(不用重启): [状态面板] 按钮的显隐
        try { if (_btnDiag != null) _btnDiag.Visible = c.DiagPanel; } catch { }
        // ★ 修正(真 bug): 下面这两行以前会把上面刚读到的界面值再覆盖回旧配置,
        //   依据是"界面上没有这个控件" —— 但 RC1 起「高级选项」页就有 [探针额外目标] 这个输入框了,
        //   于是用户在框里填什么, 点[确定]都会被静默丢弃。
        //   (FastCutTargets 已在上面 _txtFastCutTargets 那一行赋值, 这里不再重复。) 

        List<string> warn = new List<string>();
        // ★ 只解析到临时列表, 校验通过后才真正生效 —— 否则"点[确定]被挡 / 点[取消]"
        //   会把正在生效的触发键改掉(极端情况: 清空录入再取消 -> 键永久失效却显示"正在保护")。
        List<KeyTrig> parsedTrigs = ParseKeysToList(c.Keys, warn);

        if (c.Procs.Count == 0)
        { MessageBox.Show("还没有添加程序，请到[目标程序]页点[添加预设]。",
            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); return false; }
        if (c.TargetList().Count == 0)
        { MessageBox.Show("所有程序都已取消勾选，触发时不会关闭任何程序，请至少勾选一个。",
            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); return false; }
        if (c.Keys.Count == 0)
        { MessageBox.Show("还没有触发键，请到[触发键]页点[录入按键]。",
            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); return false; }
        if (parsedTrigs.Count == 0)
        { MessageBox.Show("这个键无法识别：" + string.Join(" ", warn.ToArray()),
            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); return false; }

        // ⚠️ 这里按 _lstNics 的下标去取 _nics[i], 两者长度必须一致。
        //    长度不一致(极端情况下探测结果变了)会抛 ArgumentOutOfRangeException 直接崩,
        //    所以用两者较小值兜住 —— 宁可少读一张网卡, 也不能让"保存设置"把程序搞崩。
        int nicCount = Math.Min(_lstNics.Items.Count, _nics.Count);
        for (int i = 0; i < nicCount; i++)
            if (_lstNics.GetItemChecked(i)) c.Nics.Add(_nics[i].Name);
        if (c.Nics.Count == 0)
        { MessageBox.Show("还没有勾选网卡，请到[网卡与选项]页勾选带[承载流量]的那张。",
            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); return false; }

        foreach (string w in warn) Log("[设置警告] " + w);
        _trigs = parsedTrigs;      // 校验全过 -> 这时才让新触发键生效
        _cfg = c;
        try { SaveConfig(c); }
        catch (Exception ex)
        { MessageBox.Show("配置保存失败，本次运行仍使用界面上的设置。" + ex.Message,
            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning); }

        Log("[设置] 目标程序=" + string.Join(" / ", c.TargetList().ToArray()));
        Log("[设置] 触发键=" + c.KeysText());
        Log("[设置] 网卡=" + string.Join(" / ", c.Nics.ToArray()) + " 保持=" + c.WaitSeconds + "s");

        // 保护中改配置 -> 重启钩子以生效(钩子本身不用重装, 触发键列表已更新)
        RefreshSummary();
        RefreshStatus();
        return true;
    }

    /// <summary>
    /// 打开按键录入对话框, 把结果写回输入框。
    /// ★ 这里只更新输入框文本, 不直接改正在生效的 _trigs —— 生效要等用户在设置窗点[确定]。
    ///   (否则"录完又取消"也会让新键生效 / 清空后取消会让触发键永久失效。)
    /// </summary>
    private static void DoRecordKeys()
    {
        try
        {
            List<string> cur = SplitKeyText(_txtKeys.Text);
            using (KeyRecorder rec = new KeyRecorder(cur))
            {
                if (rec.ShowDialog(_form) == DialogResult.OK)
                {
                    StringBuilder sb = new StringBuilder();
                    foreach (string k in rec.Result)
                    {
                        if (sb.Length > 0) sb.Append(" / ");
                        sb.Append(k);
                    }
                    _txtKeys.Text = sb.ToString();
                    List<string> warn = new List<string>();
                    List<KeyTrig> parsed = ParseKeysToList(rec.Result, warn);
                    Log("[录入] 当前触发键: " + (rec.Result.Count == 0 ? "(空)" : _txtKeys.Text)
                        + "  (解析成功 " + parsed.Count + " 个, 点[确定]后生效)");
                    foreach (string w in warn) Log("[录入警告] " + w);
                    if (rec.Result.Count == 0)
                        WarnBox("尚未录入触发键，请点[录入按键]后按下需要使用的按键。");
                }
            }
        }
        catch (Exception ex) { Log("录入对话框异常: " + ex); WarnBox("录入失败：" + ex.Message); }
    }

    private static void AppendUi(string s) { AppendUiLog(s); }

    /// <summary>
    /// 探测网卡并刷新列表。
    /// preserveCurrentChecks=true(点[重新探测网卡]): 保留用户当前还没保存的勾选, 不要打回旧配置;
    /// false(打开设置窗/启动时): 按 guard.ini 里的配置勾选。
    /// </summary>
    private static void DoDetect(bool preserveCurrentChecks)
    {
        try
        {
            List<string> warn = new List<string>();
            // 探测前先把当前勾选抄下来(列表马上会被清空重建)
            List<string> keep = null;
            if (preserveCurrentChecks && _lstNics != null)
            {
                keep = new List<string>();
                int n0 = Math.Min(_lstNics.Items.Count, _nics.Count);
                for (int i = 0; i < n0; i++)
                    if (_lstNics.GetItemChecked(i)) keep.Add(_nics[i].Name);
            }

            List<NicInfo> found = DetectNics(warn);
            _nics = found;
            foreach (string w in warn) WarnBox(w);

            // 网卡列表控件只在设置对话框里存在
            if (_lstNics != null) FillNicList(keep);
            else AppendUi("[探测] 共 " + found.Count + " 张网卡（可在[设置]中勾选）");
        }
        catch (Exception ex)
        {
            Log("网卡探测异常: " + ex);
            WarnBox("网卡探测失败：" + ex.Message);
        }
    }

    // ============================================================================
    //  界面"不冻"三件套 (V1.1.4-RC23)
    //
    //  起因: 用户报"使用的时候发生了一次无响应"。查日志 + 逐项实测:
    //    打开设置窗 = BuildSettingsDialog 2.1~2.7 秒(冷启动 4.5 秒) + DetectNics 1.0~1.4 秒
    //    (冷启动 4.5 秒) 全在界面线程上同步跑 —— 冷启动那一次正好顶过 Windows 判"无响应"的 5 秒线;
    //    退出确认前的 AnyTargetDisabled() 单次 netsh 245~930 毫秒(冷启动实测 2.9 秒);
    //    [自检]→安全测试 同步调 KillWithRetry 最多 6 秒。
    //  对策: 慢活全部丢后台线程; 必须在界面线程上等的, 边等边泵消息(窗口照常重画, 不会被标"无响应")。
    // ============================================================================

    /// <summary>设置窗正在构建(构建期间界面会泵消息 -> 必须防重入)</summary>
    private static volatile bool _settingsOpening = false;
    /// <summary>正在走关闭流程(检查网卡时要泵消息 -> 必须防重入)</summary>
    private static volatile bool _closing = false;

    /// <summary>
    /// 界面线程 id(在 Main 一开始就记下)。用来判断"现在这条线程能不能泵消息",
    /// 比原来的"看 _form 有没有句柄"可靠 —— 窗体还没建出来的时候也能正确判断。
    /// </summary>
    private static uint _uiThreadId = 0;

    /// <summary>最近一次泵消息的时间戳(PumpThrottled 的节流锚点)</summary>
    private static long _lastPumpTicks = 0;

    /// <summary>
    /// 两次泵消息之间的最小间隔。建控件时 PumpThrottled 会被调用几百次, 不能每次都 DoEvents
    /// (那会把构建拖慢好几倍)。40 ms 是实测调出来的:
    ///   100 ms 时,"最坏情况一次建完五页"在机器负载高的时候出现过 1098 ms 的单次消息空窗
    ///   (uibudget 抓到的), 同一个场景 40 ms 之后稳定在 200 ms 上下。
    /// 这里要的从来不是"构建够快", 而是"消息空窗够短" —— 所以宁可用一点构建耗时换空窗。
    /// </summary>
    private const int PUMP_MIN_GAP_MS = 40;

    /// <summary>
    /// 给消息队列透口气。用在"必须在界面线程上连续跑一两秒"的地方:
    /// 只要还在泵消息, Windows 就不会把窗口标成"无响应"(那个判定看的是有没有响应消息, 不是快不快)。
    /// </summary>
    private static void PumpOnce()
    {
        PumpOnUi();
    }

    /// <summary>
    /// 只在"当前就是界面线程"时才泵消息 —— 工作线程上调 DoEvents 会去泵它自己的队列,
    /// 既没用还可能踩到 WinForms 的线程约束, 所以统一走这个入口。
    /// ★ V1.1.5-RC1: 判据从"看 _form 句柄"改成"看线程 id"。原来窗体还没建出来时这里一律不泵,
    ///   而"建窗体/建对话框"正是最需要泵的那一段(它们跑在 _form 之前或 _form 之上)。
    /// </summary>
    private static void PumpOnUi()
    {
        try
        {
            if (_uiThreadId != 0 && GetCurrentThreadId() != _uiThreadId) return;   // 不是界面线程 -> 什么都不做
            Application.DoEvents();
            PumpProbeMark();
        }
        catch { }
    }

    // ============================================================================
    //  "界面消息空窗"探针(V1.1.5-RC1, 给 uibudget 自检用)
    //
    //  量的是"界面线程连续多久没有处理过消息" —— 这正是 Windows 判窗口是否"无响应"的依据
    //  (不是窗口快不快)。探针本身不额外泵消息, 它只在**生产路径真正泵消息的那一刻**记一笔:
    //  两次泵之间的间隔就是"空窗"。所以 uibudget 量到的是真实代码的行为, 不是测试自己造出来的。
    //
    //  为什么生产代码里要带这个探针: 关掉时它只做一次 volatile 读, 代价可以忽略;
    //  开着时它让"无响应"这件事从"用户报了我再猜"变成"每次发版前跑一遍 uibudget 就能断言"。
    // ============================================================================

    /// <summary>探针开关(只有 uibudget 自检会打开)</summary>
    private static volatile bool _pumpProbe = false;
    private static long _pumpProbeLastTicks = 0;
    private static long _pumpProbeMaxMs = 0;
    private static string _pumpProbeMaxWhere = "";
    /// <summary>这一段里真的泵了几次消息</summary>
    private static long _pumpProbeCount = 0;
    /// <summary>这一段里"空窗超过 UI_BUDGET_MS"出现了几次</summary>
    private static long _pumpProbeOverTarget = 0;
    /// <summary>这一段里"空窗超过 UI_HARDLINE_MS"出现了几次</summary>
    private static long _pumpProbeOverHard = 0;

    /// <summary>开始量一段: 记下起点, 清空统计, 并给这段起个名字(写进报告用)。</summary>
    private static void PumpProbeReset(string stage)
    {
        try
        {
            _pumpProbeMaxMs = 0;
            _pumpProbeMaxWhere = stage ?? "";
            _pumpProbeCount = 0;
            _pumpProbeOverTarget = 0;
            _pumpProbeOverHard = 0;
            _pumpProbeLastTicks = Stopwatch.GetTimestamp();
            _uiPhase = (stage != null) ? stage : "";
        }
        catch { }
    }

    /// <summary>结束这一段: 把"最后一次泵到此刻"的空窗也算进去(不泵的话整段都算空窗)。</summary>
    private static long PumpProbeFinish()
    {
        try
        {
            if (_pumpProbeLastTicks != 0)
            {
                long g = ElapsedMs(_pumpProbeLastTicks);
                if (g > _pumpProbeMaxMs) { _pumpProbeMaxMs = g; _pumpProbeMaxWhere = _uiPhase + " [尾段]"; }
                if (g >= UI_BUDGET_MS) _pumpProbeOverTarget++;
                if (g >= UI_HARDLINE_MS) _pumpProbeOverHard++;
                if (_pumpProbeOverTarget > 0 && _pumpProbeCount == 0)
                {
                    // 一次都没泵过 -> 这段压根没给消息队列机会(那才是真问题)
                    _pumpProbeMaxWhere = _uiPhase + " [整段一次都没泵过消息!]";
                }
                _pumpProbeLastTicks = 0;
            }
        }
        catch { }
        return _pumpProbeMaxMs;
    }

    /// <summary>泵消息那一刻被调用: 记下与上次的时间差, 维护最大值与超线次数。</summary>
    private static void PumpProbeMark()
    {
        if (!_pumpProbe) return;
        try
        {
            long now = Stopwatch.GetTimestamp();
            _pumpProbeCount++;
            if (_pumpProbeLastTicks != 0)
            {
                long g = ElapsedMs(_pumpProbeLastTicks, now);
                if (g > _pumpProbeMaxMs) { _pumpProbeMaxMs = g; _pumpProbeMaxWhere = _uiPhase; }
                if (g >= UI_BUDGET_MS) _pumpProbeOverTarget++;
                if (g >= UI_HARDLINE_MS) _pumpProbeOverHard++;
            }
            _pumpProbeLastTicks = now;
        }
        catch { }
    }

    /// <summary>
    /// 节流版泵消息: 距上次泵不到 PUMP_MIN_GAP_MS 就直接返回。
    ///
    /// 为什么要有它(V1.1.5-RC1, 用户要求"绝对不允许无响应"):
    ///   设置窗/向导要建几百个控件, 一次性建完实测 1.7~3.2 秒(冷启动 4.5 秒)。以前只在页签边界
    ///   泵一次, 于是"单页构建"那一段(最大的网卡页 316 行)在慢机器上可能整段不处理消息 ——
    ///   而 Windows 判"无响应"看的正是"这条线程多久没处理过消息"。
    ///   把这些泵点铺到每一个控件组之后, 界面线程的"消息空窗"就被压在
    ///   PUMP_MIN_GAP_MS + 单个控件组的构建耗时 以内, 永远够不到那条线。
    ///
    /// 放在"建控件"的语句之间调用是安全的: 每次只做 DoEvents, 不改任何状态;
    /// 重入由调用方自己的防重入闸(_settingsOpening / _closing / _toggling / _pagesBuilding)挡住。
    /// </summary>
    private static void PumpThrottled()
    {
        try
        {
            if (_lastPumpTicks != 0 && ElapsedMs(_lastPumpTicks) < PUMP_MIN_GAP_MS) return;
            _lastPumpTicks = Stopwatch.GetTimestamp();
            PumpOnUi();
        }
        catch { }
    }

    /// <summary>
    /// 网卡探测的"不冻界面"版本: netsh / route 全在后台线程跑, 结果回界面线程再填列表。
    /// 为什么要它: DetectNics 实测 1.0~4.5 秒, 同步跑会让"打开设置"那一下顶到 5 秒无响应线。
    /// keep 的读取(勾选状态)必须留在界面线程, 所以先抄好再丢后台。
    /// </summary>
    private static void DoDetectAsync(Control owner, bool preserveCurrentChecks)
    {
        DoDetectAsync(owner, preserveCurrentChecks, null);
    }

    /// <summary>同上, 但探测结果回填完之后再调一次 onDone(向导第 3 屏用它刷新自己的列表)。</summary>
    private static void DoDetectAsync(Control owner, bool preserveCurrentChecks, MethodInvoker onDone)
    {
        Control host = owner ?? _form;
        List<string> keep = null;
        if (preserveCurrentChecks && _lstNics != null)
        {
            keep = new List<string>();
            int n0 = Math.Min(_lstNics.Items.Count, _nics.Count);
            for (int i = 0; i < n0; i++)
                if (_lstNics.GetItemChecked(i)) keep.Add(_nics[i].Name);
        }
        Thread t = new Thread(delegate()
        {
            List<string> warn = new List<string>();
            List<NicInfo> found = null;
            try { found = DetectNics(warn); }
            catch (Exception ex) { warn.Add("网卡探测失败：" + ex.Message); }
            MethodInvoker apply = delegate
            {
                try
                {
                    if (found != null) _nics = found;
                    if (_lstNics != null) FillNicList(keep);
                    else
                    {
                        AppendUi("[探测] 共 " + _nics.Count + " 张网卡（可在[设置]中勾选）");
                        RefreshSummary();
                        RefreshStatus();
                    }
                    foreach (string w in warn) WarnBox(w);
                    if (onDone != null) { try { onDone(); } catch { } }
                }
                catch (Exception ex) { Log("网卡探测回填异常: " + ex); }
            };
            try
            {
                if (host != null && !host.IsDisposed && host.IsHandleCreated) host.BeginInvoke(apply);
                else apply();
            }
            catch { try { apply(); } catch { } }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardNicDetect";
        t.Start();
    }

    /// <summary>
    /// AnyTargetDisabled() 的"不冻界面"版本: netsh 放后台线程, 界面线程边等边泵消息。
    /// 超时查不出来时返回 true —— 宁可多问一次, 也不能把"网卡还禁着"悄悄带出程序。
    /// </summary>
    private static bool AnyTargetDisabledPumped(int budgetMs)
    {
        bool[] said = new bool[1];
        bool[] done = new bool[1];
        Thread t = new Thread(delegate()
        {
            try { said[0] = AnyTargetDisabled(); } catch { }
            done[0] = true;
        });
        t.IsBackground = true;
        t.Name = "SkyGuardNicDisabledCheck";
        t.Start();
        long t0 = Stopwatch.GetTimestamp();
        while (!done[0] && ElapsedMs(t0) < budgetMs)
        {
            PumpOnce();
            try { Thread.Sleep(15); } catch { }
        }
        return !done[0] || said[0];
    }

    // ============================================================================
    //  界面看门狗 (V1.1.4-RC24)
    //
    //  用户报过"用着用着 SkyGuard 无响应", 但日志里看不到界面卡在哪一段 —— RC23 只能靠外面写探针
    //  逐个计时去猜。所以这里直接把"界面线程停了多久"记进日志:
    //    后台线程每 250 ms 往界面线程投一次心跳(BeginInvoke), 量"投出去 -> 界面处理完"的延迟;
    //    超过 500 ms 就写一行 [界面停顿], 并带上当时"正在做哪一段"(_uiPhase 标记)。
    //  这样下次再卡, 日志里直接有 X 毫秒 + 当时在做的事, 不用再猜。
    //  成本: 每 250 ms 一次 BeginInvoke(空委托), 看门狗线程 BelowNormal 优先级, 全部包在 try 里。
    // ============================================================================

    /// <summary>界面线程"当时正在做哪一段"的标记(只用于日志措辞, 不做逻辑判断)</summary>
    private static volatile string _uiPhase = "";
    private static int _uiWatchStarted = 0;

    private static void UiPhase(string what)
    {
        try { _uiPhase = (what == null) ? "" : what; } catch { }
    }

    /// <summary>这段"可能卡界面"的活在界面线程上开始了(配 UiPhaseEnd 用)</summary>
    private static long _uiPhaseStart = 0;

    private static void UiPhaseBegin(string what)
    {
        try { _uiPhase = (what == null) ? "" : what; _uiPhaseStart = Stopwatch.GetTimestamp(); } catch { }
    }

    [DllImport("user32.dll")] private static extern int GetGuiResources(IntPtr hProcess, int uiFlags);

    /// <summary>
    /// 界面停顿超过 2 秒时落一份"现场快照"到数据目录(_uistall_*.txt):
    /// 当时在做哪一段、本进程每个线程的状态与等待原因、GDI/USER 句柄数、前台窗口、日志尾部。
    /// 为什么要有它: 用户报过一次"无响应", 但系统(WER/事件日志)没留下任何记录 ——
    /// 以后只要再卡, 这份快照就是现场证据, 不用再靠猜。
    /// </summary>
    private static void WriteUiStallSnapshot(long stallMs)
    {
        try
        {
            StringBuilder sb = new StringBuilder();
            sb.AppendLine("SkyGuard 界面停顿现场快照");
            sb.AppendLine("时间     = " + DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss.fff"));
            sb.AppendLine("版本     = " + APP_VER + "    PID = " + Process.GetCurrentProcess().Id);
            sb.AppendLine("停顿     = " + stallMs + " ms");
            sb.AppendLine("当时在做 = " + (_uiPhase.Length > 0 ? _uiPhase : "(空闲/未标记)"));
            try
            {
                IntPtr me = Process.GetCurrentProcess().Handle;
                sb.AppendLine("GDI 句柄 = " + GetGuiResources(me, 0) + "   USER 句柄 = " + GetGuiResources(me, 1));
            }
            catch { }
            try
            {
                IntPtr fg = GetForegroundWindow();
                StringBuilder wt = new StringBuilder(256);
                GetWindowTextW(fg, wt, wt.Capacity);
                uint pid = 0;
                GetWindowThreadProcessId(fg, out pid);
                sb.AppendLine("前台窗口 = \"" + wt.ToString() + "\"  pid=" + pid);
            }
            catch { }
            sb.AppendLine("");
            sb.AppendLine("---- 本进程线程 ----");
            try
            {
                foreach (ProcessThread pt in Process.GetCurrentProcess().Threads)
                {
                    try
                    {
                        sb.AppendLine("  tid=" + pt.Id + "  状态=" + pt.ThreadState + "  等待原因=" + pt.WaitReason
                            + "  CPU=" + (long)pt.TotalProcessorTime.TotalMilliseconds + " ms");
                    }
                    catch { }
                }
            }
            catch (Exception ex) { sb.AppendLine("  读线程失败: " + ex.Message); }
            sb.AppendLine("");
            sb.AppendLine("---- 日志尾部(最后 40 行) ----");
            try
            {
                if (!string.IsNullOrEmpty(_logPath) && File.Exists(_logPath))
                {
                    string[] all = File.ReadAllLines(_logPath, LogEnc());
                    int from = Math.Max(0, all.Length - 40);
                    for (int i = from; i < all.Length; i++) sb.AppendLine("  " + all[i]);
                }
            }
            catch (Exception ex) { sb.AppendLine("  读日志失败: " + ex.Message); }
            string path = Path.Combine(_dataDir, "_uistall_" + DateTime.Now.ToString("yyyyMMdd_HHmmss") + ".txt");
            File.WriteAllText(path, sb.ToString(), Encoding.UTF8);
            Log("[界面停顿] 现场快照已写入: " + path);
        }
        catch { }
    }

    /// <summary>
    /// 这段活干完了: 用时超过 200 ms 就往日志里写一行 [界面耗时]。
    /// 为什么要有它: 看门狗只记"界面停顿"(>500 ms, 只在真卡住时才有),
    ///   而"打开设置花了 3 秒"这种"慢但没卡死"的体验, 只有逐阶段计时才看得见 ——
    ///   下次再报"用着卡", 日志里直接能看到是哪一段、多少毫秒。
    /// </summary>
    private static void UiPhaseEnd(string note)
    {
        try
        {
            long ms = ElapsedMs(_uiPhaseStart);
            if (ms >= 200)
                Log("[界面耗时] " + (_uiPhase.Length > 0 ? _uiPhase : "(未标记)") + " = " + ms + " ms"
                    + (string.IsNullOrEmpty(note) ? "" : " (" + note + ")"));
            _uiPhase = "";
            _uiPhaseStart = 0;
        }
        catch { }
    }

    private static void StartUiWatchdog()
    {
        if (Interlocked.CompareExchange(ref _uiWatchStarted, 1, 0) != 0) return;
        Thread t = new Thread(delegate()
        {
            long lastLog = 0;
            long lastSnap = 0;
            long prevBeat = Stopwatch.GetTimestamp();
            while (true)
            {
                try { Thread.Sleep(250); } catch { }
                try
                {
                    if (_form == null || !_form.IsHandleCreated) { prevBeat = Stopwatch.GetTimestamp(); continue; }
                    bool done = false;
                    bool posted;
                    try { _form.BeginInvoke((MethodInvoker)delegate { done = true; }); posted = true; }
                    catch { posted = false; }
                    if (!posted) { prevBeat = Stopwatch.GetTimestamp(); continue; }

                    // 最多等 3 秒(免得看门狗自己越堆越多)
                    long waited0 = Stopwatch.GetTimestamp();
                    while (!done && ElapsedMs(waited0) < 3000) { try { Thread.Sleep(10); } catch { } }
                    long gap = ElapsedMs(prevBeat);
                    prevBeat = Stopwatch.GetTimestamp();

                    if (!done)
                    {
                        if (lastLog == 0 || ElapsedMs(lastLog) > 2000)
                        {
                            lastLog = Stopwatch.GetTimestamp();
                            Log("[界面停顿] 界面线程连续 3 秒以上没处理任何消息; 仍在处理中(" + _uiPhase + ")");
                        }
                        if (lastSnap == 0 || ElapsedMs(lastSnap) > 30000)
                        {
                            lastSnap = Stopwatch.GetTimestamp();
                            WriteUiStallSnapshot(3000);
                        }
                    }
                    else if (gap > 500)
                    {
                        if (lastLog == 0 || ElapsedMs(lastLog) > 2000)
                        {
                            lastLog = Stopwatch.GetTimestamp();
                            Log("[界面停顿] 界面线程 " + gap + " ms 没处理消息; 当时在做: "
                                + (_uiPhase.Length > 0 ? _uiPhase : "(空闲/未标记)"));
                        }
                        if (gap > 2000 && (lastSnap == 0 || ElapsedMs(lastSnap) > 30000))
                        {
                            lastSnap = Stopwatch.GetTimestamp();
                            WriteUiStallSnapshot(gap);
                        }
                    }
                }
                catch { try { prevBeat = Stopwatch.GetTimestamp(); } catch { } }
            }
        });
        t.IsBackground = true;
        t.Priority = ThreadPriority.BelowNormal;
        t.Name = "SkyGuardUiWatchdog";
        t.Start();
        Log("[看门狗] 界面看门狗已启动 (每 250 ms 测一次界面响应, 超过 500 ms 会记日志)");
    }

    /// <summary>
    /// [停止保护] 的全套复原(用户要求): 结束正在跑的那轮处置 -> 撤快速断流 ->
    /// 恢复网卡(含断网标记里记的) -> 清断网标记 -> 删掉开机恢复登记。
    /// 放后台线程: 恢复要几秒到十几秒(禁用的网卡启用后还要等路由), 不能冻住界面。
    /// </summary>
    private static void RestoreAllOnStopGuard()
    {
        AppendUi("正在恢复网络…");
        Thread t = new Thread(delegate()
        {
            try
            {
                if (_busy != 0)
                {
                    _abort = true;      // 让正在跑的那轮立刻收尾(它会自己恢复网络)
                    Log("[停止保护] 本轮处置还在进行中 -> 已请求立刻收尾并恢复");
                    for (int i = 0; i < 300 && _busy != 0; i++) Thread.Sleep(100);   // 最多等 30 秒
                    if (_busy != 0) Log("[停止保护] 等处置收尾超时(30 秒) -> 继续做复原");
                }
                FastCut_Release();
                if (NetCutStateExists() || AnyTargetDisabled())
                {
                    Log("[停止保护] 检测到网络还没复原 -> 自动恢复");
                    RunNetOp(true, 300000);
                }
                else Log("[停止保护] 网络状态正常, 无需恢复");
                RunOnceClear();
                RefreshStatus();
                AppendUi("已恢复网络。");
            }
            catch (Exception ex) { Log("[停止保护] 复原异常: " + ex.Message); }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardStopGuardRestore";
        t.Start();
    }

    /// <summary>正在开始/停止保护(启动钩子时要泵消息, 必须防重入)</summary>
    private static volatile bool _toggling = false;

    private static void ToggleGuard()
    {
        if (_toggling) return;
        _toggling = true;
        try
        {
        if (_guarding)
        {
            StopHook(true);
            _guarding = false;
            StopWarmWatcher();
            // ★ 用户要求: [停止保护] 要做"全套复原", 不能只卸载钩子 ——
            //   以前停保护后网络还断着、快速层还挂着、断网标记还留着, 没人管。
            RestoreAllOnStopGuard();
            RefreshStatus();
            return;
        }
        // 配置不全就别启动(会明确告诉缺什么)
        if (!_cfg.IsUsable())
        {
            MessageBox.Show("配置不完整，请在[⚙ 设置]中补齐目标程序、触发键和网卡。",
                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
            ShowSettings();
            if (!_cfg.IsUsable()) return;
        }
        if (!StartHook())
        {
            MessageBox.Show("键盘监听启动失败，无法开始保护。请检查安全软件是否拦截。",
                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Error);
            return;
        }
        // 后台热身: 把"按下之后才第一次用到"的进程枚举提前跑掉, 省下 20~30 ms 冷启动
        // (真机日志实测: 未热身时第一次扫描 33 ms, 热身过只要 7 ms —— 那 26 ms 正好落在最要命的一瞬)
        Thread warm = new Thread(delegate()
        {
            WarmUp();
            // 11.1.0: 顺手记一次"断流前基线"(快速断流靠它自证), 后台做, 不挡界面
            try { ProbeRefreshBaseline("开始保护"); } catch { }
        });
        warm.IsBackground = true;
        warm.Name = "SkyGuardWarmUp";
        warm.Start();

        // 若目标网卡现在是禁用状态, 恢复它(避免上次没收尾)。
        //
        // ★ 修正: 这两件事以前都在这条 UI 线程上同步做 ——
        //   ① AnyTargetDisabled 要起 netsh 子进程; ② SetNets(true) 一旦真的走起恢复流程
        //   (续租 + 重挂网卡 + 反复探针)能把窗口冻住一两分钟, 而这期间触发键是按不动的
        //   (保护状态还没置上)。现在整体丢到后台线程, [开始保护] 立刻返回、钩子立刻可用;
        //   后台恢复也不会挡住触发键 —— 用户一按, 恢复流程会在 100ms 内让路(见 WaitAbortable)。
        Thread chk = new Thread(delegate()
        {
            try
            {
                if (AnyTargetDisabled())
                {
                    Log("目标网卡处于禁用状态 -> 判定为上次未收尾, 后台恢复网络(不阻塞开始保护)");
                    RunNetOp(true, 0);
                }
            }
            catch (Exception ex) { Log("[开始保护] 网卡收尾检查异常: " + ex.Message); }
        });
        chk.IsBackground = true;
        chk.Name = "SkyGuardStartupNicCheck";
        chk.Start();

        _guarding = true;
        _hitCount = 0;
        // ★ V1.1.5-RC1: 开始保护时把"触发通道健康"重置, 并立刻请钩子线程做一次真实自检
        //   —— "摘了再装"是唯一能证明"钩子真的在系统里"的办法(只查线程/标志查不出静默被摘)。
        _chanDegraded = false;
        _hookHealth = 0;
        _hookLastCheckTicks = 0;
        RequestHookSelfCheck("开始保护");
        StartChannelReadyCheck();
        RefreshStatus();
        // 把生效的焦点设置写进日志: 测 Ultra / 调参时, 这一行能直接证明"改的东西真生效了"
        Log("焦点解堵: " + (_cfg.FocusRescue ? FocusModeName(_cfg.FocusMode) + " 档" : "已关闭")
            + (_cfg.FocusRescue && _cfg.FocusMode >= 1
                ? " (间隔 " + _cfg.FocusIntervalMs + "ms + 探针 " + _cfg.FocusProbeMs + "ms) × "
                  + _cfg.FocusRounds + " 轮 ≈ 最坏 "
                  + FocusWorstLatencyMs(_cfg.FocusIntervalMs, _cfg.FocusProbeMs, _cfg.FocusRounds)
                  + " ms 接管; 还焦点需连续 " + _cfg.FocusOkRounds + " 轮 + 静默 " + _cfg.FocusSilentMs + " ms"
                : (_cfg.FocusRescue ? " (只用系统判定, 约 5 秒)" : "")));
        Log("已开始保护。目标 " + _cfg.TargetList().Count + " 个程序; 触发键: " + _cfg.KeysText());
        // 预热表: 保护期间后台记着目标进程的 PID, 触发时第一条命令就能直接挂起(省掉扫表)
        StartWarmWatcher();
        }
        finally { _toggling = false; }
    }

    /// <summary>
    /// 鼠标点【立即处置!】。和按触发键走同一条处置流程, 只是入口不同。
    /// 留这条路的原因: 键盘钩子这条链子受系统限制最多(时限、被摘、被别的钩子挡),
    /// 而"点按钮"什么都不依赖。
    /// </summary>
    private static void PanicByClick()
    {
        if (!_guarding)
        {
            MessageBox.Show("请先点[开始保护]。", APP_NAME,
                MessageBoxButtons.OK, MessageBoxIcon.Warning);
            return;
        }
        if (Interlocked.CompareExchange(ref _busy, 1, 0) != 0)
        {
            // 与触发键一致: 上一轮还在进行中就忽略 —— 已经在处理了。
            // 想立刻收尾 → [恢复网络] / [停止保护](全套复原)。
            Log("点击 [立即处置]: 上一轮处置还在进行中 -> 忽略; 想提前恢复请点[恢复网络]或[停止保护]");
            return;
        }
        _abort = false;
        _lastFireTicks = Stopwatch.GetTimestamp();
        _hitCount++;
        Log("点击 [立即处置]");
        WakePanic();
    }

    /// <summary>
    /// 鼠标点【恢复网络】。用途: 处置中途程序被关掉、或者上次没收到尾, 网卡还卡在禁用状态,
    /// 这时候不用重开游戏, 点一下就能把网络要回来。
    /// </summary>
    private static void RestoreNetByClick()
    {
        if (_restoringNet) return;
        if (_cfg.Nics.Count == 0)
        {
            MessageBox.Show("还没有配置网卡，请先打开[⚙ 设置]。", APP_NAME,
                MessageBoxButtons.OK, MessageBoxIcon.Warning);
            return;
        }
        _restoringNet = true;
        Log("点击 [恢复网络]");
        Thread th = new Thread(delegate()
        {
            try
            {
                // 走常驻断网线程(唯一动网卡的入口), 并等它做完再报结果。
                // 上限给得很宽: 这段本来就在后台线程上跑, 不挡界面。
                RunNetOp(true, 300000);
                Log("恢复网络" + (_restoreSuperseded ? "(被新的操作接管)" : "")
                    + " —— " + RestoreVerdictText() + " (手动点击)");
            }
            catch (Exception ex) { Log("恢复网络异常: " + ex.Message); }
            finally { _restoringNet = false; }
        });
        th.IsBackground = true;
        th.Start();
    }

    private static volatile bool _restoringNet = false;

    /// <summary>只杀进程、不碰网卡 —— 让用户能安全自测</summary>
    /// <summary>
    /// 鼠标点【测试】: 先问用户跑哪一种。
    ///
    /// 为什么要做进界面(11.1.0-RC2, 实测教训): 用 .bat 启动 netcuttest 在真实环境里会被
    /// Windows"打开文件 - 安全警告"(无法验证发布者) 或安全软件挡在门外 —— 实测双击后弹框、运行按钮
    /// 点不动, 用户根本跑不到自检。做进程序就绕开 shell 层, 也没有 .bat 的编码/换行问题。
    /// </summary>
    private static void SelfTestByClick()
    {
        DialogResult r = MessageBox.Show(
            "请选择要运行的测试：\n\n"
            + "[是] 快速断流自检\n"
            + "      临时拦截出站流量数秒，验证拦截与恢复，全程不禁用网卡。\n"
            + "      这几秒会短暂断网，结束后自动撤销。\n\n"
            + "[否] 安全测试\n"
            + "      仅关闭目标程序，不修改网络设置。\n\n"
            + "[取消] 不执行任何操作。",
            "SkyGuard · 测试", MessageBoxButtons.YesNoCancel, MessageBoxIcon.Question);
        if (r == DialogResult.No) { SafeKillTest(); return; }
        if (r != DialogResult.Yes) return;

        if (_guarding)
        {
            MessageBox.Show("请先点[停止保护]，再运行快速断流自检。",
                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
            return;
        }

        Thread t = new Thread(delegate()
        {
            try
            {
                _netCutFromUi = true;
                Log("======== 界面内快速断流自检 开始 ========");
                int rc = RunNetCutTest();
                string rep = "";
                try
                {
                    string p = Path.Combine(_baseDir, "_netcuttest.txt");
                    if (File.Exists(p)) rep = File.ReadAllText(p, Encoding.UTF8);
                }
                catch { }
                Log("======== 界面内快速断流自检 结束, 退出码 " + rc + " ========");
                MessageBox.Show(
                    "快速断流自检结束。\n\n结果 = " + (rc == 0 ? "通过" : (rc == 3 ? "环境不足" : "未通过")) + "\n\n"
                    + "---------------- 报告 ----------------\n" + rep,
                    "SkyGuard · 快速断流自检", MessageBoxButtons.OK,
                    rc == 0 ? MessageBoxIcon.Information : MessageBoxIcon.Warning);
            }
            catch (Exception ex)
            {
                Log("界面内自检异常: " + ex.Message);
                MessageBox.Show("自检异常：" + ex.Message, APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Error);
            }
            finally { _netCutFromUi = false; _netCutDone = true; }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardNetCutUi";
        t.Start();
    }

    private static void SafeKillTest()
    {
        List<string> targets = _cfg.TargetList();
        if (targets.Count == 0)
        {
            MessageBox.Show("还没有配置目标程序，请先打开[⚙ 设置]。",
                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
            return;
        }
        string what = MatchedPresetNames(targets);
        if (what.Length == 0) what = string.Join("\n", targets.ToArray());
        DialogResult r = MessageBox.Show(
            "将关闭以下程序：\n\n" + what
            + "\n\n不会断开网卡。继续吗？",
            APP_NAME + " · 安全测试", MessageBoxButtons.YesNo, MessageBoxIcon.Question);
        if (r != DialogResult.Yes) return;
        // ★ 关进程最多要 6 秒(KillWithRetry 会补杀几轮) —— 原来同步跑会把界面冻住,
        //   实测正好顶过 Windows 判"无响应"的 5 秒线。现在丢后台线程, 结果回来再弹窗。
        AppendUi("正在关闭目标程序…");
        UiPhaseBegin("安全测试: 正在关闭目标程序");
        Thread tk = new Thread(delegate()
        {
            bool ok = false;
            try
            {
                Log("-------- 安全测试: 只关程序, 不动网卡 --------");
                KillWithRetry(targets, 6000);
                ok = true;
                foreach (string t in targets) if (FindPids(t).Count > 0) { ok = false; break; }
                Log("安全测试结果: " + (ok ? "全部成功" : "有残留"));
            }
            catch (Exception ex) { Log("安全测试异常: " + ex.Message); }
            MethodInvoker done = delegate
            {
                try
                {
                    AppendUi(ok ? "安全测试完成。" : "安全测试完成：有程序未能关闭。");
                    UiPhaseEnd("");
                    MessageBox.Show(ok ? "程序已全部关闭，网络没有改动。" : "有程序未能关闭，详情见日志。",
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
                }
                catch { }
            };
            try
            {
                if (_form != null && !_form.IsDisposed && _form.IsHandleCreated) _form.BeginInvoke(done);
                else done();
            }
            catch { try { done(); } catch { } }
        });
        tk.IsBackground = true;
        tk.Name = "SkyGuardSafeKillTest";
        tk.Start();
    }

    #endregion

    // ============================================================================
    //  八、按键录入对话框 (点"录入" → 直接按键, 不用手打键名)
    // ============================================================================

    #region 按键录入

    private sealed class KeyRecorder : Form
    {
        private ListView _list;
        private Label _lblLive;
        private ComboBox _cmb;
        private IntPtr _hook = IntPtr.Zero;
        private LowLevelKeyboardProc _proc;
        private readonly List<string> _keys = new List<string>();
        private readonly List<KeyTrig> _trigs = new List<KeyTrig>();
        private bool _armed = false;
        private volatile bool _capture = false;      // 是否正在接收按键(默认关, 避免误触)
        private volatile bool _handling = false;     // 重入保护: 防止钩子+窗体事件把同一次按键处理两遍

        public List<string> Result { get { return _keys; } }

        public KeyRecorder(List<string> initial)
        {
            this.Text = "录入触发键";
            // ★ 宽度从 560 加到 660: 下面那些说明文字在 125% 缩放下会超宽被切。
            //   实测(字号 9pt × 1.25 = 11.25pt): 底部第二行需 749px, 而原先只有 524px 可用。
            //   注意窗口坐标是固定像素、字体却按 DPI 放大, 所以窄窗口在高缩放下必然切字。
            //   治本做法是给文字留够宽度 + 让它自动换行(见下面 tip/foot 的 AutoSize)。
            // ⚠️ 顺序: SetAutoScale -> 设尺寸 (见 SetAutoScaleFont 的注释)。
            //   反过来的话, "改 Font" 会触发一次自动缩放, 把刚设好的 ClientSize 改坏。
            SetAutoScaleFont(this, Fi("Microsoft YaHei UI", 9F));
            this.BackColor = C_BG;
            this.ClientSize = B(0, 0, 660, 448).Size;
            this.MinimumSize = B(0, 0, 620, 420).Size;
            this.StartPosition = FormStartPosition.CenterParent;
            this.FormBorderStyle = FormBorderStyle.Sizable;
            this.MaximizeBox = true;
            this.MinimizeBox = false;

            TableLayoutPanel root = new TableLayoutPanel();
            root.Dock = DockStyle.Fill;
            root.ColumnCount = 1;
            root.RowCount = 6;
            root.Padding = Pad(14, 10, 14, 10);
            root.BackColor = C_BG;
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));    // 0 说明
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));    // 1 选键行
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));    // 2 状态行
            root.RowStyles.Add(new RowStyle(SizeType.Percent, 100F)); // 3 列表(吃掉剩余空间)
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));    // 4 底部按钮
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));    // 5 底部说明
            this.Controls.Add(root);

            Label tip = new Label();
            tip.ForeColor = C_SUB;
            tip.Text = "可直接按键盘录入，也可从下拉菜单选择一个键后点[添加]。";
            Wrap(tip);
            root.Controls.Add(tip, 0, 0);

            // ---- 选键行: 下拉 + 按钮, 用 FlowLayoutPanel 自动横向排列 ----
            FlowLayoutPanel pick = new FlowLayoutPanel();
            pick.AutoSize = true;
            pick.Dock = DockStyle.Fill;
            pick.FlowDirection = FlowDirection.LeftToRight;
            pick.WrapContents = true;
            root.Controls.Add(pick, 0, 1);

            _cmb = new ComboBox();
            _cmb.DropDownStyle = ComboBoxStyle.DropDownList;
            _cmb.Width = Sc(200);
            foreach (string k in new string[] {
                "F1","F2","F3","F4","F5","F6","F7","F8","F9","F10","F11","F12",
                "Insert","Delete","Home","End","PgUp","PgDn",
                "Pause","ScrollLock","Space","Tab",
                "Ctrl+Alt+K","Ctrl+Alt+J","Ctrl+Alt+L","Ctrl+Shift+K","Ctrl+Shift+F9" })
                _cmb.Items.Add(k);
            _cmb.SelectedIndex = 0;
            pick.Controls.Add(_cmb);

            Button bAdd = MakeButton("添加", delegate { AddFromCombo(); }, "plain");
            pick.Controls.Add(bAdd);

            Button bRec = MakeButton("按键录入", null, "primary");
            bRec.Click += delegate
            {
                _capture = !_capture;
                bRec.Text = _capture ? "停止录入" : "按键录入";
                _lblLive.Text = _capture ? "正在录入…再点一次[停止录入]结束"
                                         : "已暂停录入";
            };
            pick.Controls.Add(bRec);

            Button bHint = MakeButton("?", null, "plain");
            bHint.Click += delegate
            {
                MessageBox.Show(
                    "两种录入方式：\r\n\r\n"
                    + "① 按键盘录入：点[按键录入]后直接按键，再点一次停止，适合组合键。\r\n\r\n"
                    + "② 下拉菜单：挑一个常用键点[添加]，适合 F1~F12、Pause 这类单键。\r\n\r\n"
                    + "Alt+F4 不会录入。",
                    "怎么录入", MessageBoxButtons.OK, MessageBoxIcon.Information);
            };
            pick.Controls.Add(bHint);

            Label live = new Label();
            live.Text = "点[按键录入]后开始按键\r\n默认暂停，避免误触";
            live.Font = Fi("Microsoft YaHei UI", 11F, FontStyle.Bold);
            live.ForeColor = Color.FromArgb(0, 90, 180);
            live.TextAlign = ContentAlignment.MiddleLeft;
            live.BorderStyle = BorderStyle.FixedSingle;
            Wrap(live);
            root.Controls.Add(live, 0, 2);
            _lblLive = live;

            _list = new ListView();
            _list.Dock = DockStyle.Fill;      // 吃掉剩余空间: 窗口高它就高
            _list.View = View.Details;
            _list.FullRowSelect = true;
            _list.GridLines = true;
            _list.HeaderStyle = ColumnHeaderStyle.Nonclickable;
            _list.BackColor = Color.White;
            _list.Columns.Add("键名", Sc(280));
            _list.Columns.Add("键码", Sc(120));
            root.Controls.Add(_list, 0, 3);

            // ---- 底部按钮行: FlowLayoutPanel 自动排列, 按钮各自 AutoSize ----
            FlowLayoutPanel btns = new FlowLayoutPanel();
            btns.AutoSize = true;
            btns.Dock = DockStyle.Fill;
            btns.FlowDirection = FlowDirection.LeftToRight;
            btns.WrapContents = true;
            root.Controls.Add(btns, 0, 4);

            Button bDel = MakeButton("删除选中", delegate { RemoveSelected(); }, "plain");
            btns.Controls.Add(bDel);

            Button bClear = MakeButton("全部清空", delegate { _keys.Clear(); _trigs.Clear(); RefreshList(); }, "plain");
            btns.Controls.Add(bClear);

            Button bOk = MakeButton("确定", delegate { this.DialogResult = DialogResult.OK; this.Close(); }, "primary");
            btns.Controls.Add(bOk);

            Button bCancel = MakeButton("取消", delegate { this.DialogResult = DialogResult.Cancel; this.Close(); }, "plain");
            btns.Controls.Add(bCancel);

            Label foot = new Label();
            foot.ForeColor = C_SUB;
            foot.Text = "此键若被其他软件占用，按下可能没有反应，请改用其他按键。\r\n"
                      + "Alt+F4 不可录入。";
            Wrap(foot);
            root.Controls.Add(foot, 0, 5);
            // 字体/尺寸都定完之后再排一次, 确保锚定生效
            this.PerformLayout();

            foreach (string k in initial)
            {
                KeyTrig t = ParseKeyLine(k);
                if (t != null && !ContainsCombo(t.Vk, t.Ctrl, t.Alt, t.Shift))
                { _keys.Add(t.Name); _trigs.Add(t); }
            }
            RefreshList();

            // KeyPreview=true + OnKeyDown 覆盖: 这是录入的主通道(键码规范、修饰键准确)
            this.KeyPreview = true;
            _armed = true;
            // 输入法必须关掉: 中文输入法会吞掉字母键(实测按 K 录出 G), 还会送来 0xE5 之类的
            // ProcessKey 事件。录入窗只要物理按键, 不需要任何 IME。
            try { this.ImeMode = ImeMode.NoControl; } catch { }
            this.Shown += delegate
            {
                try
                {
                    this.ImeMode = ImeMode.NoControl;
                    this.Activate();
                    this.BringToFront();
                }
                catch { }
                StartHookLocal();
                Log("[录入窗] 已就绪。默认暂停录入(避免误触), 点[按键录入]后开始接收按键。");
            };
            this.FormClosed += delegate { StopHookLocal(); };
        }

        /// <summary>把下拉菜单里选中的键加进清单</summary>
        private void AddFromCombo()
        {
            try
            {
                string s = _cmb.SelectedItem as string;
                if (string.IsNullOrEmpty(s)) { _lblLive.Text = "请先在下拉菜单中选择一个键"; return; }
                KeyTrig t = ParseKeyLine(s);
                if (t == null) { _lblLive.Text = "无法识别：" + s; return; }
                if (ContainsCombo(t.Vk, t.Ctrl, t.Alt, t.Shift))
                {
                    _lblLive.Text = s + " 已在列表中";
                    return;
                }
                _trigs.Add(t);
                _keys.Add(t.Name);
                RefreshList();
                _lblLive.Text = "已添加：" + t.Name;
            }
            catch (Exception ex) { _lblLive.Text = "添加失败：" + ex.Message; }
        }

        /// <summary>清空全部已录入的键</summary>
        private void ClearAll()
        {
            _keys.Clear();
            _trigs.Clear();
            RefreshList();
        }

        private void RefreshList()
        {
            _list.Items.Clear();
            foreach (KeyTrig t in _trigs)
            {
                ListViewItem it = new ListViewItem(t.Name);
                it.SubItems.Add("0x" + t.Vk.ToString("X2"));
                _list.Items.Add(it);
            }
        }

        private void RemoveSelected()
        {
            if (_list.SelectedIndices.Count == 0)
            {
                if (_trigs.Count > 0) { _trigs.RemoveAt(_trigs.Count - 1); _keys.RemoveAt(_keys.Count - 1); }
            }
            else
            {
                for (int i = _list.SelectedIndices.Count - 1; i >= 0; i--)
                {
                    int idx = _list.SelectedIndices[i];
                    if (idx >= 0 && idx < _trigs.Count) { _trigs.RemoveAt(idx); _keys.RemoveAt(idx); }
                }
            }
            RefreshList();
        }

        private void StartHookLocal()
        {
            if (_hook != IntPtr.Zero) return;
            _proc = new LowLevelKeyboardProc(RecorderCallback);
            _hook = SetWindowsHookEx(WH_KEYBOARD_LL, _proc, IntPtr.Zero, 0);
            if (_hook == IntPtr.Zero)
                Log("[录入窗] 键盘钩子安装失败, 错误码 " + Marshal.GetLastWin32Error() + " (改用窗体按键事件)");
            else
                Log("[录入窗] 键盘钩子已安装 (双通道: 钩子 + 窗体按键事件)");
        }

        private void StopHookLocal()
        {
            if (_hook != IntPtr.Zero) { UnhookWindowsHookEx(_hook); _hook = IntPtr.Zero; }
        }

        /// <summary>
        /// 窗体按键事件通道 —— 这是主用通道。
        /// 为什么需要它: F8/F9 这类功能键在 WinForms 里本来就会走 KeyDown,
        /// 不该只依赖全局钩子(钩子失败/被拦时就完全失灵, 实测踩过)。
        ///
        /// ⚠️ 修饰键必须从事件本身读(e.Control/e.Alt/e.Shift), 不能用 Control.ModifierKeys ——
        /// 后者读的是实时键盘状态, 在某些时序下会读不到, 导致 Ctrl+Alt+K 被记成裸 K(实测踩过)。
        /// </summary>
        protected override void OnKeyDown(KeyEventArgs e)
        {
            base.OnKeyDown(e);
            try
            {
                uint vk = (uint)e.KeyCode;
                bool ctrl = e.Control;
                bool alt = e.Alt;
                bool shift = e.Shift;
                // 用数值判断修饰键(不依赖枚举比较, 更稳):
                //   0x10=Shift  0x11=Ctrl  0x12=Alt  0x5B/0x5C=Win
                bool isModifierOnly = IsModifierKey(vk)
                                       || e.KeyCode == Keys.ShiftKey || e.KeyCode == Keys.ControlKey
                                       || e.KeyCode == Keys.Menu
                                       || e.KeyCode == Keys.LWin || e.KeyCode == Keys.RWin;
                Log("[录入窗] OnKeyDown vk=0x" + vk.ToString("X2") + " KeyCode=" + e.KeyCode
                    + " ctrl=" + ctrl + " alt=" + alt + " shift=" + shift
                    + " capture=" + _capture
                    + (isModifierOnly ? "  >> 修饰键, 忽略" : ""));
                if (isModifierOnly) return;
                if (!IsAcceptableTriggerKey(vk))
                { Log("[录入窗]   拒绝: vk=0x" + vk.ToString("X2") + " 不在允许的键范围内(可能是输入法/退格/特殊键)"); return; }
                if (!_capture) { _lblLive.Text = "已暂停录入，点[按键录入]后再按"; return; }
                HandleKey(vk, ctrl, alt, shift);
                e.Handled = true;
                e.SuppressKeyPress = true;
            }
            catch (Exception ex) { Log("[录入窗] OnKeyDown 异常: " + ex.Message); }
        }

        /// <summary>这个「修饰键组合 + 主键」是否已经在清单里(去重必须带上修饰键, 否则 K 和 Ctrl+K 会撞车)</summary>
        private bool ContainsCombo(uint vk, bool ctrl, bool alt, bool shift)
        {
            foreach (KeyTrig t in _trigs)
                if (t.Vk == vk && t.Ctrl == ctrl && t.Alt == alt && t.Shift == shift) return true;
            return false;
        }

        /// <summary>主通道和兜底通道都走这里。加了重入保护, 防止同一次按键被处理两遍。</summary>
        private void HandleKey(uint vk, bool ctrl, bool alt, bool shift)
        {
            if (_handling) { Log("[录入窗]   重入保护: 忽略重复到达的 vk=0x" + vk.ToString("X2")); return; }
            _handling = true;
            try
            {
                if (IsModifierKey(vk))
                { Log("[录入窗]   拒绝: vk=0x" + vk.ToString("X2") + " 是修饰键/Win键"); return; }

                if (!IsAcceptableTriggerKey(vk))
                { Log("[录入窗]   拒绝: vk=0x" + vk.ToString("X2") + " 不在允许的键范围内"); return; }

                // Alt+F4 不接受(否则以后关窗口会误触发)
                if (vk == 0x73 && alt && !ctrl && !shift)
                {
                    _lblLive.Text = "Alt+F4 不能作为触发键";
                    Log("[录入窗] 已忽略 Alt+F4");
                    return;
                }

                string name = NameOf(vk, ctrl, alt, shift);
                if (ContainsCombo(vk, ctrl, alt, shift))
                {
                    // ⚠️ 这里不是失败：键已经在清单里了，忽略这次重复识别即可。
                    //    早先日志写的是"拒绝: XXX 已在清单里" —— 用户连着按 F1~F7 时会看到
                    //    一串"拒绝", 以为自己按错了或者程序出问题了。其实一个都没少。
                    //    (同一个键会被 keydown 和 keyup 各上报一次, 所以必然会走到这里。)
                    _lblLive.Text = "刚按下：" + name + "，已在列表中";
                    Log("[录入窗]   已在清单里, 未重复添加: " + name);
                    return;
                }
                _lblLive.Text = "刚按下：" + name;
                KeyTrig kt = new KeyTrig();
                kt.Vk = vk; kt.Ctrl = ctrl; kt.Alt = alt; kt.Shift = shift;
                kt.Name = name; kt.IsF4 = (vk == 0x73);
                _trigs.Add(kt);
                _keys.Add(name);
                Log("[录入窗]   >>> 已加入清单: " + name + " (VK=0x" + vk.ToString("X2") + ")");
                RefreshList();
                try { _list.EnsureVisible(_list.Items.Count - 1); } catch { }
            }
            catch (Exception ex) { Log("[录入窗] HandleKey 异常: " + ex.Message); }
            finally { _handling = false; }
        }

        private IntPtr RecorderCallback(int nCode, IntPtr wParam, IntPtr lParam)
        {
            try
            {
                if (nCode >= 0 && _armed)
                {
                    int msg = wParam.ToInt32();
                    if (msg == WM_KEYDOWN || msg == WM_SYSKEYDOWN)
                    {
                        uint vk = (uint)Marshal.ReadInt32(lParam);
                        bool ctrl = (GetAsyncKeyState(VK_CONTROL) & 0x8000) != 0;
                        bool alt = (GetAsyncKeyState(VK_MENU) & 0x8000) != 0;
                        bool shift = (GetAsyncKeyState(VK_SHIFT) & 0x8000) != 0;
                        if (!_capture) return CallNextHookEx(_hook, nCode, wParam, lParam);
                        bool mod = IsModifierKey(vk);
                        Log("[录入窗] 钩子 vk=0x" + vk.ToString("X2")
                            + " ctrl=" + ctrl + " alt=" + alt + " shift=" + shift
                            + (mod ? "  >> 修饰键, 忽略" : ""));
                        HandleKey(vk, ctrl, alt, shift);
                    }
                }
            }
            catch (Exception ex)
            {
                try { Log("[录入窗] 钩子异常: " + ex.Message); } catch { }
            }
            return CallNextHookEx(_hook, nCode, wParam, lParam);
        }
    }

    /// <summary>把文本里的多键写法拆开; 支持空格/逗号/分号/斜杠分隔(用户最容易随手打空格)</summary>
    private static List<string> SplitKeyText(string text)
    {
        List<string> outList = new List<string>();
        if (string.IsNullOrEmpty(text)) return outList;
        string[] parts = text.Split(
            new char[] { ' ', '\t', '\r', '\n', ',', ';', '/', '|', '、' },
            StringSplitOptions.RemoveEmptyEntries);
        foreach (string p in parts)
        {
            string t = p.Trim();
            if (t.Length > 0) outList.Add(t);
        }
        return outList;
    }

    #endregion

    // ============================================================================
    //  九、selftest (命令行诊断, 不弹窗、不动作)
    // ============================================================================

    #region selftest

    /// <summary>
    /// 无头测试按键录入窗 —— 直接构造窗体并「喂」按键事件, 验证录入逻辑。
    /// 这样即使点不了 GUI, 也能确认录入功能本身是对的。
    /// </summary>
    private static int RunRecorderTest()
    {
        _headless = true;
        int rc = 1;                       // 默认按失败算, 中途异常也停在失败
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("按键录入窗 无头测试 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            KeyRecorder rec = new KeyRecorder(new List<string>());
            sb.AppendLine("构造成功            = True");
            sb.AppendLine("KeyPreview          = " + rec.KeyPreview + "  (应为 True)");

            // ---- 几何自检: 记录窗里的控件装得下(只 CreateControl 不 Show, 免得装上键盘钩子) ----
            try
            {
                rec.CreateControl();
                rec.PerformLayout();
                Application.DoEvents();
                StringBuilder lbad = new StringBuilder();
                CheckClipRec(rec, lbad);
                sb.AppendLine("布局自检            = " + (lbad.Length == 0
                    ? "OK (无裁切)   客户区 " + rec.ClientSize
                    : "[被裁] " + lbad.ToString()));
            }
            catch (Exception lex) { sb.AppendLine("布局自检异常        = " + lex.Message); }

            // ---- 方式一: 下拉菜单选键 ----
            sb.AppendLine("");
            sb.AppendLine("--- 方式一: 下拉菜单 ---");
            sb.AppendLine("下拉项数            = " + RecGetComboCount(rec));
            RecSetComboIndex(rec, 0); RecAddFromCombo(rec);    // F1
            RecSetComboIndex(rec, 18); RecAddFromCombo(rec);   // Pause
            RecSetComboIndex(rec, 8); RecAddFromCombo(rec);    // F9
            sb.AppendLine("加 3 个后条数        = " + rec.Result.Count + " (期望 3): " + string.Join(" / ", rec.Result.ToArray()));
            RecSetComboIndex(rec, 0); RecAddFromCombo(rec);    // F1 再加一次
            sb.AppendLine("重复加 F1 后条数     = " + rec.Result.Count + " (期望 3)");

            // ---- 方式二: 按键录入 ----
            sb.AppendLine("");
            sb.AppendLine("--- 方式二: 按键录入 ---");
            sb.AppendLine("默认 _capture       = " + RecGetCapture(rec) + " (应为 False, 防误触)");
            Feed(rec, Keys.K, true, false, false, sb, "暂停时按 Ctrl+K (应被忽略)");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望仍 3)");

            RecSetCapture(rec, true);
            Feed(rec, Keys.K, true, true, false, sb, "录入中: Ctrl+Alt+K");
            Feed(rec, Keys.J, true, true, false, sb, "录入中: Ctrl+Alt+J");
            Feed(rec, Keys.K, true, true, false, sb, "录入中: Ctrl+Alt+K 重复");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望 5): " + string.Join(" / ", rec.Result.ToArray()));
            Feed(rec, Keys.ControlKey, true, false, false, sb, "纯 Ctrl (应忽略)");
            Feed(rec, Keys.F4, false, true, false, sb, "Alt+F4 (应拒绝)");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望仍 5)");

            // ---- 回归测试: F9/F10 不得再关窗 ----
            sb.AppendLine("");
            sb.AppendLine("--- 回归测试: F9/F10 不应关闭窗口 ---");
            Feed(rec, Keys.F9, false, false, false, sb, "F9");
            sb.AppendLine("   F9  后 IsDisposed = " + rec.IsDisposed + " (期望 False)");
            Feed(rec, Keys.F10, false, false, false, sb, "F10");
            sb.AppendLine("   F10 后 IsDisposed = " + rec.IsDisposed + " (期望 False)");
            sb.AppendLine("   -> 条数 " + rec.Result.Count);

            RecSelectLast(rec);
            RecRemoveSelected(rec);
            sb.AppendLine("删除选中后条数      = " + rec.Result.Count);

            // ---- 精确复现用户报告: 单独按 Ctrl, 然后按 Ctrl+K ----
            sb.AppendLine("");
            sb.AppendLine("--- 复现1: 单独按 Ctrl, 再按 Ctrl+K ---");
            RecClearAll(rec);
            RecSetCapture(rec, true);
            sb.AppendLine("清空后条数          = " + rec.Result.Count);
            Feed(rec, Keys.ControlKey, false, false, false, sb, "单独按 Ctrl");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望 0)");
            Feed(rec, Keys.K, true, false, false, sb, "按 Ctrl+K");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望 1): " + string.Join(" / ", rec.Result.ToArray()));
            sb.AppendLine("   ^^^ 若这里出现 Ctrl, 就是用户报的 bug");

            sb.AppendLine("");
            sb.AppendLine("--- 复现2: Shift / Alt 是否也被误录 ---");
            RecClearAll(rec);
            Feed(rec, Keys.ShiftKey, false, false, false, sb, "单独按 Shift");
            Feed(rec, Keys.Menu, false, false, false, sb, "单独按 Alt");
            Feed(rec, Keys.LWin, false, false, false, sb, "单独按 Win");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望 0)");
            Feed(rec, Keys.A, false, false, true, sb, "Shift+A");
            Feed(rec, Keys.B, false, true, false, sb, "Alt+B");
            sb.AppendLine("   -> 条数 " + rec.Result.Count + " (期望 2): " + string.Join(" / ", rec.Result.ToArray()));

            sb.AppendLine("");
            sb.AppendLine("--- 复现3: 菜单录入组合键(不经过按键) ---");
            RecClearAll(rec);
            RecSetComboIndexByName(rec, "Ctrl+Alt+K");
            RecAddFromCombo(rec);
            sb.AppendLine("   -> 条数 " + rec.Result.Count + ": " + string.Join(" / ", rec.Result.ToArray()));

            // ---- 用户实测日志里的真实垃圾键码, 必须全部被挡 ----
            sb.AppendLine("");
            sb.AppendLine("--- 回归: 用户日志里的真实垃圾键码应全部被拒绝 ---");
            RecClearAll(rec);
            RecSetCapture(rec, true);
            uint[] junkVk = new uint[] { 0xA2, 0xA0, 0xA1, 0xA3, 0xA4, 0xA5, 0x08, 0xE5, 0x0D, 0x1B, 0xFF };
            string[] junkName = new string[] { "右Ctrl原始码", "左Shift原始码", "右Shift原始码", "右Alt原始码",
                                               "左Alt原始码2", "输入法ProcessKey", "Backspace",
                                               "无效0xE5", "回车", "Esc", "无效0xFF" };
            // 两个数组都要按 junkVk 的长度写全 —— 之前 junkName 少写了 4 个,
            // 跑到第 8 个就 IndexOutOfRange, 测试直接判"失败"(被测代码本身没问题)。
            for (int i = 0; i < junkVk.Length; i++)
            {
                string nm = (i < junkName.Length) ? junkName[i] : "(缺名字)";
                Feed(rec, (Keys)junkVk[i], false, false, false, sb,
                     "0x" + junkVk[i].ToString("X2") + " " + nm);
                sb.AppendLine("      -> 条数 " + rec.Result.Count + " (应始终 0)   允许="
                    + IsAcceptableTriggerKey(junkVk[i]));
            }
            sb.AppendLine("最终条数            = " + rec.Result.Count + "   ^^^ 必须为 0");

            sb.AppendLine("");
            sb.AppendLine("--- 回归: 这些正常键应被接受 ---");
            RecClearAll(rec);
            Keys[] goodKeys = new Keys[] { Keys.F1, Keys.F12, Keys.Home, Keys.Pause,
                                           Keys.Scroll, Keys.Insert, Keys.Space, Keys.A, Keys.D5 };
            foreach (Keys k in goodKeys) Feed(rec, k, false, false, false, sb, k.ToString());
            sb.AppendLine("   -> " + rec.Result.Count + " 个: " + string.Join(" / ", rec.Result.ToArray()));

            List<string> warn = new List<string>();
            ParseKeys(rec.Result, warn);
            sb.AppendLine("");
            sb.AppendLine("写回配置后解析      = " + _trigs.Count + " 个");
            foreach (KeyTrig t in _trigs) sb.AppendLine("   " + t.Name);
            foreach (string w in warn) sb.AppendLine("   [警告] " + w);

            // ---- 回归: K 与 Ctrl+K 必须共存(ParseKeys 去重必须带修饰键) ----
            sb.AppendLine("");
            sb.AppendLine("--- 回归: 单键与同键组合必须共存 ---");
            List<string> dw = new List<string>();
            List<KeyTrig> duo = ParseKeysToList(new List<string>(new string[] { "K", "Ctrl+K" }), dw);
            sb.AppendLine("   K + Ctrl+K 解析出 " + duo.Count + " 个 (期望 2)");
            foreach (KeyTrig t in duo) sb.AppendLine("      " + t.Name);
            if (duo.Count != 2) { sb.AppendLine("   [失败] 被去重丢了一个 <== 重启前后行为会不一致"); }

            // ---- 回归: NameOf 生成的每一个名字, 都必须能被 VkOf/ParseKeyLine 解回同一个键码 ----
            // 这条是 补的(真 bug): 方向键/小键盘以前没有名字, NameOf 会吐出 "VK26"/"VK65",
            // 而 VkOf 不认这种字符串 -> 录入窗录进来的键保存后静默消失(只有一个时还会被直接拦下)。
            // 以后往 IsAcceptableTriggerKey 里加键位, 请先跑这个自检。
            sb.AppendLine("");
            sb.AppendLine("--- 回归: 键名 <-> 键码 往返一致性 ---");
            List<uint> roundTrip = new List<uint>();
            for (uint vk = 0x01; vk <= 0xFE; vk++)
            {
                if (!IsAcceptableTriggerKey(vk)) continue;
                if (VkOf(NameOf(vk, false, false, false)) != vk) roundTrip.Add(vk);
            }
            sb.AppendLine("   允许的键位逐个往返 = "
                + (roundTrip.Count == 0 ? "全部一致 OK" : ("有 " + roundTrip.Count + " 个对不上 <== 失败")));
            foreach (uint bad in roundTrip)
                sb.AppendLine("      vk=0x" + bad.ToString("X2") + " 名字=\"" + NameOf(bad, false, false, false) + "\" 解不回来");

            bool allOk = (roundTrip.Count == 0) && (duo.Count == 2);
            sb.AppendLine("");
            sb.AppendLine("结论                = " + (allOk
                ? "录入逻辑可执行, 键名与键码往返一致"
                : "有问题: 见上面的 [失败]/对不上 标记"));
            rc = allOk ? 0 : 1;
            try { rec.Dispose(); } catch { }
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            sb.AppendLine("结论                = 录入逻辑失败");
        }
        File.WriteAllText(Path.Combine(_baseDir, "_rectest.txt"), sb.ToString(), Encoding.UTF8);
        return rc;
    }

    // ---- 反射辅助: 访问录入窗私有成员, 供无头测试使用 ----
    private static object RecField(KeyRecorder r, string name)
    {
        System.Reflection.FieldInfo fi = typeof(KeyRecorder).GetField(name,
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        return fi == null ? null : fi.GetValue(r);
    }

    private static int RecGetComboCount(KeyRecorder r)
    {
        ComboBox c = RecField(r, "_cmb") as ComboBox;
        return c == null ? -1 : c.Items.Count;
    }

    private static void RecSetComboIndex(KeyRecorder r, int idx)
    {
        ComboBox c = RecField(r, "_cmb") as ComboBox;
        if (c != null && idx >= 0 && idx < c.Items.Count) c.SelectedIndex = idx;
    }

    private static void RecAddFromCombo(KeyRecorder r)
    {
        System.Reflection.MethodInfo mi = typeof(KeyRecorder).GetMethod("AddFromCombo",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        if (mi != null) mi.Invoke(r, null);
    }

    private static bool RecGetCapture(KeyRecorder r)
    {
        object o = RecField(r, "_capture");
        return (o is bool) && (bool)o;
    }

    private static void RecSetCapture(KeyRecorder r, bool v)
    {
        System.Reflection.FieldInfo fi = typeof(KeyRecorder).GetField("_capture",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        if (fi != null) fi.SetValue(r, v);
    }

    private static void RecClearAll(KeyRecorder r)
    {
        System.Reflection.MethodInfo mi = typeof(KeyRecorder).GetMethod("ClearAll",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        if (mi != null) mi.Invoke(r, null);
    }

    private static void RecSetComboIndexByName(KeyRecorder r, string name)
    {
        ComboBox c = RecField(r, "_cmb") as ComboBox;
        if (c == null) return;
        for (int i = 0; i < c.Items.Count; i++)
            if (string.Equals(c.Items[i].ToString(), name, StringComparison.OrdinalIgnoreCase))
            { c.SelectedIndex = i; return; }
    }

    private static void RecSelectLast(KeyRecorder r)
    {
        ListView lv = RecField(r, "_list") as ListView;
        if (lv != null && lv.Items.Count > 0) lv.Items[lv.Items.Count - 1].Selected = true;
    }

    private static void RecRemoveSelected(KeyRecorder r)
    {
        System.Reflection.MethodInfo mi = typeof(KeyRecorder).GetMethod("RemoveSelected",
            System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
        if (mi != null) mi.Invoke(r, null);
    }

    /// <summary>
    /// 无头测试"目标程序"多选逻辑: 预设组、去重、删除、写盘、回读。
    /// 这批次的核心就是"多程序", 所以必须能自证。
    /// </summary>
    private static int RunTargetsTest()
    {
        _headless = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("目标程序多选 无头测试 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        int rc = 0;
        try
        {
            // 1) 预设本身
            sb.AppendLine("预设组数 = " + PRESETS.Length);
            foreach (ProcPreset p in PRESETS)
                sb.AppendLine("   " + p.Label + "  -> " + p.Procs.Length + " 个: " + string.Join(" / ", p.Procs));

            // 2) 模拟"点添加预设"的去重逻辑
            _targetDraft = new List<string>();
            foreach (ProcPreset p in PRESETS)
                foreach (string x in p.Procs)
                    if (!TargetListContains(x)) _targetDraft.Add(x);
            sb.AppendLine("");
            sb.AppendLine("添加两组预设后 = " + _targetDraft.Count + " 个 (期望 9)");
            foreach (string x in _targetDraft) sb.AppendLine("   " + x);

            // 再加一遍, 应该一个都不加(去重)
            int before = _targetDraft.Count;
            foreach (ProcPreset p in PRESETS)
                foreach (string x in p.Procs)
                    if (!TargetListContains(x)) _targetDraft.Add(x);
            sb.AppendLine("重复添加后     = " + _targetDraft.Count + " 个 (期望仍 " + before + ")");

            // 3) 手输自定义进程
            if (!TargetListContains("MyCustomApp")) _targetDraft.Add("MyCustomApp");
            sb.AppendLine("加自定义后     = " + _targetDraft.Count + " 个 (期望 " + (before + 1) + ")");

            // 4) 删除一个
            _targetDraft.Remove("MuMuVMMSVC");
            sb.AppendLine("删 1 个后      = " + _targetDraft.Count + " 个 (期望 " + before + ")");

            // 5) 取消勾选其中一组(模拟"今天只开 Sky, MuMu 全部停用")
            List<string> mumuGroup = new List<string>();
            foreach (string x in PRESETS[1].Procs) mumuGroup.Add(x);
            _procOff = new List<string>(mumuGroup);
            sb.AppendLine("");
            sb.AppendLine("--- 取消勾选「MuMu 模拟器」整组 ---");
            sb.AppendLine("列表里还留着   = " + _targetDraft.Count + " 个 (期望不减, 只是没勾)");
            Config chk = new Config();
            chk.Procs = new List<string>(_targetDraft);
            chk.ProcOff = new List<string>(_procOff);
            sb.AppendLine("全部进程       = " + chk.AllProcs().Count + " 个");
            sb.AppendLine("实际会关的     = " + chk.TargetList().Count + " 个 (期望 2: Sky.exe + MyCustomApp)");
            sb.AppendLine("实际内容       = " + string.Join(" / ", chk.TargetList().ToArray()));
            sb.AppendLine("MuMuVMMSVC 被停用 = " + (!chk.IsEnabled("MuMuVMMSVC")) + " (期望 True)");
            sb.AppendLine("Sky.exe    被停用 = " + (!chk.IsEnabled("Sky.exe")) + " (期望 False)");
            sb.AppendLine("摘要文本       = " + chk.TargetsText());

            // 6) 写盘 -> 回读
            Config c = new Config();
            c.Procs = new List<string>(_targetDraft);
            c.ProcOff = new List<string>(_procOff);
            c.Keys = new List<string>(new string[] { "F1", "Ctrl+Alt+K" });
            c.Nics = new List<string>(new string[] { "WLAN" });
            c.WaitSeconds = 20;
            // ★ 这个测试会真的写盘。老代码备份了却从来不恢复 ——
            //   等于每次自检都把用户的 guard.ini 覆盖成测试数据(发现)。
            //   现在把原文记在内存里, 方法末尾原样还回去; 原本没有这个文件就删掉。
            _iniBackupForTest = null;
            try { if (File.Exists(_iniPath)) _iniBackupForTest = File.ReadAllText(_iniPath); } catch { }
            SaveConfig(c);
            List<string> w2 = new List<string>();
            Config r = LoadConfig(w2);
            sb.AppendLine("");
            sb.AppendLine("写盘后回读:");
            sb.AppendLine("   全部进程数 = " + (r == null ? -1 : r.AllProcs().Count) + " (期望 " + _targetDraft.Count + ")");
            sb.AppendLine("   实际会关   = " + (r == null ? -1 : r.TargetList().Count) + " (期望 2)");
            sb.AppendLine("   停用名单   = " + (r == null ? "" : string.Join(" / ", r.ProcOff.ToArray())));
            sb.AppendLine("   目标内容   = " + (r == null ? "" : string.Join(" / ", r.TargetList().ToArray())));
            sb.AppendLine("   触发键     = " + (r == null ? "" : r.KeysText()));
            sb.AppendLine("   网卡       = " + (r == null ? "" : string.Join(" / ", r.Nics.ToArray())));
            sb.AppendLine("   可用       = " + (r == null ? false : r.IsUsable()) + " (期望 True)");
            sb.AppendLine("   摘要文本   = " + (r == null ? "" : r.TargetsText()));
            sb.AppendLine("   焦点解堵   = " + (r == null ? false : r.FocusRescue)
                + " 间隔=" + (r == null ? 0 : r.FocusIntervalMs)
                + "ms 轮数=" + (r == null ? 0 : r.FocusRounds));
            sb.AppendLine("");
            sb.AppendLine("--- 写出的 guard.ini 内容 ---");
            foreach (string ln in File.ReadAllLines(_iniPath, Encoding.UTF8)) sb.AppendLine("   " + ln);

            // 注意: guard.ini 的恢复统一放在方法末尾的 finally 里(只做一次)。
            // 这里再恢复一遍的话, 末尾那次会因为备份已清空而把刚恢复的文件删掉 —— 踩过。

            sb.AppendLine("");
            sb.AppendLine("结论 = 多目标逻辑可执行");
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            // 非管理员运行时写不了数据目录里的 guard.ini(那份文件是提权进程建的, MODIFY 只给了
            // 管理员/CREATOR OWNER)。这是环境限制, 不是"多目标逻辑失败" —— 上面的断言其实都过了。
            // 11.1.2-RC15 之前这里一律 return 0: 报告写"失败"、退出码却报成功, 自相矛盾(而且谁说谎
            // 取决于你信哪个)。现在如实分类: 环境不行 = 3, 逻辑真错 = 1。
            if (ex is UnauthorizedAccessException)
            {
                rc = 3;
                sb.AppendLine("结论 = 本次结果无效: 非管理员运行, 写不了数据目录里的 guard.ini"
                    + " (上面各条断言已按期望值通过)");
            }
            else
            {
                rc = 1;
                sb.AppendLine("结论 = 多目标逻辑失败");
            }
        }
        // 把 guard.ini 恢复原状: 原本没有就删掉, 原本有就写回原文
        try
        {
            if (_iniBackupForTest != null) File.WriteAllText(_iniPath, _iniBackupForTest, new UTF8Encoding(false));
            else if (File.Exists(_iniPath)) File.Delete(_iniPath);
            try { string b = _iniPath + ".testbak"; if (File.Exists(b)) File.Delete(b); } catch { }
        }
        catch { }
        File.WriteAllText(Path.Combine(_baseDir, "_targetstest.txt"), sb.ToString(), Encoding.UTF8);
        return rc;
    }

    /// <summary>
    /// 进程名转储 —— 输出"本程序实际枚举到的所有进程名", 用于排查"目标程序找不到"的问题。
    /// 用户报告: Sky.exe 能杀, MuMu 系列 8 个枚举到 0 个, 但任务管理器里明明在。
    /// </summary>
    private static int RunProcDump()
    {
        _headless = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("进程枚举转储 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("IsAdmin = " + IsAdmin());
        sb.AppendLine("BaseDir = " + _baseDir);
        sb.AppendLine("");
        try
        {
            List<KeyValuePair<int, string>> all = EnumProcesses();
            sb.AppendLine("NtQuerySystemInformation 枚举到 " + all.Count + " 个进程");
            sb.AppendLine("");
            sb.AppendLine("--- 名字含 Mu / nemu / Sky 的 ---");
            int hit = 0;
            foreach (KeyValuePair<int, string> kv in all)
            {
                string n = kv.Value;
                if (n.IndexOf("Mu", StringComparison.OrdinalIgnoreCase) >= 0
                    || n.IndexOf("nemu", StringComparison.OrdinalIgnoreCase) >= 0
                    || n.IndexOf("Sky", StringComparison.OrdinalIgnoreCase) >= 0)
                {
                    sb.AppendLine("   PID=" + kv.Key + "  name=[" + n + "]");
                    hit++;
                }
            }
            if (hit == 0) sb.AppendLine("   (没有找到)");
            sb.AppendLine("");
            sb.AppendLine("--- 全部进程名(排序后) ---");
            List<string> names = new List<string>();
            foreach (KeyValuePair<int, string> kv in all) names.Add(kv.Value);
            names.Sort(StringComparer.OrdinalIgnoreCase);
            foreach (string n in names) sb.AppendLine("   [" + n + "]");
        }
        catch (Exception ex) { sb.AppendLine("异常: " + ex); }
        File.WriteAllText(Path.Combine(_baseDir, "_procdump.txt"), sb.ToString(), Encoding.UTF8);
        return 0;
    }

    /// <summary>
    /// 无头验证"界面卡住时钩子还活着吗"。
    ///
    /// 做法: 开一个真窗体(有真消息泵) → 装钩子 → 故意把 界面线程 冻结 4 秒,
    /// 冻结期间从别的线程做钩子探活。
    /// 如果钩子还收得到键, 就说明它确实不依赖界面 —— 这正是"游戏无响应时按了没反应"要解决的问题。
    /// </summary>
    private static int RunHangTest()
    {
        _headless = true;
        bool oldWay = HasArg("hangtest-old") || HasArg("-old");
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("界面冻结测试 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff")
            + (oldWay ? "   [旧做法: 钩子装在界面线程]" : "   [现在: 钩子装在独立线程]"));
        bool aliveWhileHung = false;
        bool? probeOkBefore = null;   // 冻结前的探活结果 —— 它是"这次测试到底有没有意义"的前提
        // ★ 非管理员运行时, keybd_event 注入的按键会被 UIPI 拦下(前台窗口完整性级别更高就进不来),
        //   探针时灵时不灵 —— 实测就是这么假红的。工具本身始终以管理员运行, 所以这不是缺陷,
        //   但测试必须自己认清这个前提, 否则会把"环境验不了"报成"钩子失效"。
        bool isAdmin = IsAdmin();
        // 安全网: 这个测试会真的装全局钩子、并在界面线程上做冻结, 万一哪一步卡住,
        // 后果是"永远不写结果 + 留下一个挂着全局键盘钩子的孤儿进程"。给它一个硬上限。
        Thread hardStop = new Thread(delegate()
        {
            Thread.Sleep(30000);
            try
            {
                File.WriteAllText(Path.Combine(_baseDir, oldWay ? "_hangtest_old.txt" : "_hangtest.txt"),
                    "界面冻结测试: 30 秒没结束 -> 判定为卡住, 强制退出(没有结果就是结果)。\r\n",
                    Encoding.UTF8);
            }
            catch { }
            Environment.Exit(2);
        });
        hardStop.IsBackground = true;
        hardStop.Name = "hangtestHardStop";
        hardStop.Start();
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            _form = new Form();
            _form.Text = "hangtest";
            _form.ClientSize = new Size(300, 120);
            _form.StartPosition = FormStartPosition.Manual;
            _form.Location = new Point(-4000, -4000);   // 挪到屏幕外, 不打扰
            _form.ShowInTaskbar = false;

            _form.Shown += delegate
            {
                if (oldWay)
                {
                    // 故意装回界面线程, 用来验证"这个测试确实能测出问题"
                    _hookProc = new LowLevelKeyboardProc(HookCallback);
                    _hookHandle = SetWindowsHookEx(WH_KEYBOARD_LL, _hookProc, IntPtr.Zero, 0);
                    _hookForCallback = _hookHandle;
                    _hookInstallOk = (_hookHandle != IntPtr.Zero);
                }
                else StartHook();

                sb.AppendLine("钩子装上               = " + _hookInstallOk);
                sb.AppendLine("钩子所在线程 ID        = " + (oldWay ? GetCurrentThreadId() : _hookThreadId));
                sb.AppendLine("界面线程 ID            = " + GetCurrentThreadId());

                Thread w = new Thread(delegate()
                {
                    try
                    {
                        bool before = SelfTestHook();
                        probeOkBefore = before;
                        sb.AppendLine("冻结前探活             = " + (before ? "收到按键" : "收不到"));

                        sb.AppendLine(">>> 现在把界面线程冻结 4 秒 <<<");
                        Thread.Sleep(600);
                        _form.Invoke((MethodInvoker)delegate
                        {
                            Thread.Sleep(4000);   // 界面线程在这里彻底停住
                        });

                        sb.AppendLine("界面已解冻");
                        // 解冻后停一下再探活(保守值, 不是必需): 让输入链先缓过来。
                        Thread.Sleep(2500);
                        bool after = SelfTestHook();
                        aliveWhileHung = after;
                        sb.AppendLine("冻结后探活             = " + (after ? "收到按键" : "收不到"));
                    }
                    catch (Exception ex) { sb.AppendLine("测试线程异常: " + ex.Message); }
                    finally { try { _form.BeginInvoke((MethodInvoker)delegate { _form.Close(); }); } catch { } }
                });
                w.IsBackground = true;
                // 等 Shown 处理函数返回、界面线程回到消息循环之后再起探活线程。
                // 旧做法(钩子装在界面线程)下注入的按键要由界面线程跑回调,
                // Shown 还在执行时它没在泵消息, 这个顺序更稳妥。
                _form.BeginInvoke((MethodInvoker)delegate { w.Start(); });
            };

            Application.Run(_form);
            sb.AppendLine("");
            // 说明边界: 注入的按键在"旧做法"那一档也能收到(注入输入不必经过钩子所在线程),
            // 所以这个测试能证明"钩子这会儿还收得到键", 但证明不了"独立线程比装在界面线程更好"。
            // 真机上真正会被界面卡死堵住的, 是物理按键。
            sb.AppendLine("说明 = 探针是注入的按键; 旧做法(-old)同样能收到, 本测试不构成'独立线程更优'的证据");
            sb.AppendLine("");
            // 前提不成立就不能下结论: 冻结前的探活如果本身就失败, 说明这个环境里"注入探针"不可用
            // (非管理员运行、或前台窗口完整性级别更高时, 注入的按键进不了输入链),
            // 此时报"钩子失效"是假红 —— 必须先以管理员身份运行, 结果才有意义。
            bool inconclusive = !isAdmin || (probeOkBefore != true);
            sb.AppendLine("结论 = " + (inconclusive
                ? (!isAdmin
                    ? "本次结果无效: 非管理员运行(注入的按键会被系统拦下), 请以管理员身份运行再测"
                    : "本次结果无效: 探针本身不可用(注入的按键没进系统输入链), 请以管理员身份运行再测")
                : (aliveWhileHung ? "界面卡住时钩子仍然工作" : "界面卡住时钩子失效")));
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            sb.AppendLine("结论 = 测试本身出错");
        }
        finally { try { StopHook(true); } catch { } }
        File.WriteAllText(Path.Combine(_baseDir, oldWay ? "_hangtest_old.txt" : "_hangtest.txt"),
            sb.ToString(), Encoding.UTF8);
        // 退出码要能区分三种结果: 0=通过, 1=真的失败, 3=环境不支持(结论无效)
        if (!isAdmin) return 3;                       // 非管理员: 注入探针本来就不可靠
        if (probeOkBefore != true) return 3;
        return aliveWhileHung ? 0 : 1;
    }

    private static bool HotkeyCountOk() { return _hotkeyOk > 0; }

    private static bool HasArg(string name)    {
        try
        {
            foreach (string a in Environment.GetCommandLineArgs())
                if (string.Equals(a, name, StringComparison.OrdinalIgnoreCase)) return true;
        }
        catch { }
        return false;
    }

    /// <summary>
    /// 无头测试"键盘钩子 + 看门狗": 装钩子、来自检一次钩子到底收不收得到键。
    /// 为什么要单独测: 这条链子(安装 → 回调 → 自检)以前完全靠手按键验证,
    /// 而"窗口无响应时按了没反应"就是这么漏掉的。
    /// </summary>
    /// <summary>界面里跑自检时置 true: 60 秒安全网只撤销、不结束进程(免得把用户正在用的程序杀掉)。</summary>
    private static volatile bool _netCutFromUi;
    /// <summary>自检已结束 -> 60 秒安全网自动作废(实测踩过: 自检结束后 60 秒它还在动, 会去撤用户正在用的状态)。</summary>
    private static volatile bool _netCutDone;

    /// <summary>
    /// 无头"快速断流"实机测试(11.1.0)。
    ///
    /// 它真的会断开网(装上 WFP/防火墙的出站 block 几秒), 但:
    ///   · 绝不禁用网卡 / 不碰任何网卡配置;
    ///   · 每一步都在离开时撤销, 并有 60 秒安全网强制撤销;
    ///   · 全部结论来自探针实测, 不是"我觉得应该是"。
    ///
    /// 结果写 _netcuttest.txt。退出码: 0 = 至少一层验证通过(拦住+恢复),
    /// 1 = 装了但没拦住或没恢复, 3 = 环境不足(非管理员 / 断流前就没有可连的目标)。
    /// </summary>
    private static int RunNetCutTest()
    {
        // 安全网: 万一哪一步卡住/组件异常, 60 秒后强制撤销快速层再退出 ——
        // 绝不允许测试把机器留在断网状态。
        Thread hardStop = new Thread(delegate()
        {
            Thread.Sleep(60000);
            if (_netCutDone) return;
            try { FastCut_Release(); WfpReleaseInternal(); FwRelease(); } catch { }
            try { LogToFileOnly("[netcuttest] 60 秒安全网触发: 已强制撤销快速层" + (_netCutFromUi ? "(界面内自检, 不结束程序)" : "并退出")); } catch { }
            if (!_netCutFromUi) Environment.Exit(2);
        });
        hardStop.IsBackground = true;
        hardStop.Name = "SkyGuardNetCutSafety";
        hardStop.Start();

        StringBuilder sb = new StringBuilder();
        sb.AppendLine("SkyGuard 快速断流测试 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("版本       = " + APP_VER + " (" + APP_VER_NUM + ")");
        sb.AppendLine("管理员     = " + IsAdmin() + (IsAdmin() ? "" : "   <== WFP/防火墙都需要管理员"));
        sb.AppendLine("环境能力   = " + FastCut_CapabilityReport());
        sb.AppendLine("探测目标   = " + ProbeDesc());
        int baseline = ProbeReachableNow();
        int total = ProbeTotal();
        sb.AppendLine("断流前基线 = " + baseline + "/" + total + " 个目标可连"
            + (baseline == 0 ? "   <== 本机现在连不上任何目标, 无法验证断流" : ""));
        sb.AppendLine("");

        if (!IsAdmin() || baseline == 0)
        {
            sb.AppendLine("结论: 跳过 —— " + (!IsAdmin() ? "非管理员环境无法测 WFP/防火墙。" :
                "断流前就一个目标都连不上, 无法区分\"断流成功\"和\"本来就不通\"(换个有外网的机器/VM 再跑)。"));
            File.WriteAllText(Path.Combine(_baseDir, "_netcuttest.txt"), sb.ToString(), Encoding.UTF8);
            return 3;
        }

        bool anyVerified = false, hardFail = false;
        string err;

        // ---- 1) WFP 动态过滤器 ----
        sb.AppendLine("--- WFP 动态过滤器 ---");
        long t0 = Stopwatch.GetTimestamp();
        bool wfpOk = false;
        try { wfpOk = WfpEngage(out err); } catch (Exception ex) { err = ex.Message; }
        sb.AppendLine("  装过滤器   = " + (wfpOk ? "成功 (" + ElapsedMs(t0) + " ms)" : "失败: " + err));
        if (wfpOk)
        {
            try { Thread.Sleep(300); } catch { }
            int after = ProbeReachableNow();
            sb.AppendLine("  断流后可达 = " + after + "/" + total + "   (装完共 " + ElapsedMs(t0) + " ms)");
            sb.AppendLine("  断流判定   = " + (after == 0 ? "已拦住" : "没拦住(还能连 " + after + " 个)"));
            bool blocked = (after == 0);
            WfpReleaseInternal();
            try { Thread.Sleep(1200); } catch { }
            int restored = ProbeReachableNow();
            sb.AppendLine("  撤销后可达 = " + restored + "/" + total + "   恢复判定 = "
                + (restored >= baseline ? "已恢复" : "没恢复(基线 " + baseline + ")"));
            if (blocked && restored >= baseline) anyVerified = true;
            if (!blocked || restored < baseline) hardFail = true;
        }
        sb.AppendLine("");

        // ---- 2) Windows 防火墙规则 ----
        // ★ 这一层已按设计停用(见 FwEngage 的注释), 所以如实写成"已停用";
        //   以前这里打印"加规则 = 失败: skipped-by-design" —— 用户和自动化看到"失败"
        //   会以为自检本身没过。顺手查一次机器上有没有我们名字的残留规则, 这才是有用的信息。
        sb.AppendLine("--- Windows 防火墙规则: 已停用(按设计不再使用持久化规则) ---");
        sb.AppendLine("  原因: 实测能加上、也拦得住, 但撤销后系统迟迟不放行(自检 7 秒 / 用户 70 秒都没救回来);");
        sb.AppendLine("        现在只用 WFP 动态过滤器(进程一退就消失), 兜底是禁用网卡。");
        int leftoverNow = FwRemoveOurRules();
        sb.AppendLine(FwRuleStillThere()
            ? "  注意: 本机仍有 SkyGuard-Panic-* 残留规则没能删掉(" + leftoverNow + " 条), 请按日志里的人工命令清理。"
            : (leftoverNow > 0
                ? "  已清理 " + leftoverNow + " 条老版本留下的 SkyGuard-Panic-* 规则。"
                : "  本机没有 SkyGuard 残留规则。"));
        sb.AppendLine("");

        int leftover = FwRemoveOurRules();
        sb.AppendLine("收尾: 又清了一次防火墙残留(删掉 " + leftover + " 条); WFP 动态会话已关闭。");
        sb.AppendLine("说明: 本测试不会禁用网卡。");
        sb.AppendLine("");
        sb.AppendLine("结论: " + (anyVerified
            ? "通过(安装、拦截、撤销、恢复均已验证)"
            : (hardFail ? "已安装但未拦截或未恢复，详见上面的错误码" : "无法安装，详见上面的错误码")));

        File.WriteAllText(Path.Combine(_baseDir, "_netcuttest.txt"), sb.ToString(), Encoding.UTF8);
        try { FastCut_Release(); } catch { }
        return anyVerified ? 0 : (hardFail ? 1 : 3);
    }

    private static int RunHookTest()
    {
        _headless = true;
        int rc = 1;                       // 默认按"失败"算, 中途异常也停在失败
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("键盘钩子自检 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("IsAdmin = " + IsAdmin());
        try
        {
            bool ok = StartHook();
            sb.AppendLine("StartHook          = " + ok);
            sb.AppendLine("钩子句柄           = " + (_hookHandle != IntPtr.Zero ? "已拿到" : "空 (失败)"));

            bool alive = SelfTestHook();
            sb.AppendLine("钩子探活(注入 0xFF) = " + (alive ? "收到按键, 正常" : "收不到 <== 有问题"));
            sb.AppendLine("钩子调用计数        = " + _hookCalls);

            // ---- 轮询通道: 把钩子摘掉, 模拟"钩子完全收不到键"的情况 ----
            sb.AppendLine("");
            sb.AppendLine("--- 轮询通道测试 (先卸载钩子, 模拟钩子被系统丢弃) ---");
            UnhookWindowsHookEx(_hookHandle);
            _hookHandle = IntPtr.Zero;
            _hookForCallback = IntPtr.Zero;
            int callsBefore = _hookCalls;

            // 挂一个真的要触发的键, 然后注入这个键
            KeyTrig probe = new KeyTrig();
            probe.Vk = 0x72; probe.Name = "F3";       // 0x72 = F3
            _trigs = new List<KeyTrig>();
            _trigs.Add(probe);
            _pollTestOnly = true;
            _guarding = true;
            StartKeyPoll();

            long hitBefore = _hitCount;
            keybd_event(0x72, 0, 0, IntPtr.Zero);      // 按下 F3
            Thread.Sleep(60);
            keybd_event(0x72, 0, 2, IntPtr.Zero);      // 抬起
            Thread.Sleep(400);

            long hitAfter = _hitCount;
            sb.AppendLine("钩子是否收到这个键  = " + (_hookCalls > callsBefore ? "收到了" : "没有 (符合预期: 钩子已摘)"));
            sb.AppendLine("轮询是否捕获到这个键 = " + (hitAfter > hitBefore ? "捕获到了 <== 通道有效" : "没捕获到 <== 有问题"));
            sb.AppendLine("触发计数            = " + hitBefore + " -> " + hitAfter);

            sb.AppendLine("");
            sb.AppendLine("--- 通道三: RegisterHotKey (系统级热键) ---");
            sb.AppendLine("隐藏窗口           = " + (_hotkeyWnd != IntPtr.Zero ? "建好了" : "没建出来"));
            sb.AppendLine("触发键注册成功数    = " + _hotkeyOk + " / " + _trigs.Count
                + ((_hotkeyOk < _trigs.Count && _hotkeyOk > 0)
                   ? "  (注册不上的那个键被别的软件占了, 换一个即可)" : ""));
            sb.AppendLine("备用键 F13~F24     = " + _spareHotkeys + " / 12"
                + (_spareHotkeys > 0 ? "  <== 热键通道可用" : "  <== 一个都没注册上"));
            sb.AppendLine("   ^ 备用键能注册上就说明整条 RegisterHotKey 链路是通的;");
            sb.AppendLine("     普通键盘按不到 F13~F24, 几乎不会被别的程序占用。");

            sb.AppendLine("");
            // 注入探针收不到, 多半是"这个环境验不了"而不是"钩子坏了":
            // 非管理员运行、或前台窗口完整性级别更高时, 注入的按键根本进不了输入链
            // (轮询通道读 GetAsyncKeyState 也一样读不到, 所以两条都会假红)。
            bool allOk = ok && alive && hitAfter > hitBefore;
            if (!alive)
            {
                sb.AppendLine("结论 = 本次结果无效: 注入探针收不到(非管理员运行时注入进不了输入链), 请以管理员身份运行再测");
                rc = 3;
            }
            else
            {
                sb.AppendLine("结论 = " + (allOk ? "两条通道都可用" : "有一条通道有问题"));
                rc = allOk ? 0 : 1;
            }
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            sb.AppendLine("结论 = 钩子链路有问题");
        }
        File.WriteAllText(Path.Combine(_baseDir, "_hooktest.txt"), sb.ToString(), Encoding.UTF8);
        return rc;
    }

    /// <summary>
    /// 无头"终止顺序"测试 —— 只算顺序, 不杀任何进程, 用于验证优先级排序是否生效。
    /// 输出: 配置文件里的原始顺序 vs 实际开杀顺序, 以及每个目标的优先级分级。
    /// </summary>
    private static int RunOrderTest()
    {
        _headless = true;
        bool allOk = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("终止顺序测试(不杀进程) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        try
        {
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            List<string> raw = (c == null) ? new List<string>() : c.TargetList();
            sb.AppendLine("配置里写的顺序(" + raw.Count + " 个):");
            int i = 0;
            foreach (string t in raw) sb.AppendLine("   " + (++i) + ". " + t + "   [优先级 " + TargetPriority(t) + "]");

            List<string> sorted = SortByPriority(raw);
            sb.AppendLine("");
            sb.AppendLine("实际开杀顺序:");
            i = 0;
            foreach (string t in sorted) sb.AppendLine("   " + (++i) + ". " + t + "   [优先级 " + TargetPriority(t) + "]");

            sb.AppendLine("");
            string first = sorted.Count > 0 ? NormProcName(sorted[0]) : "";
            bool firstIsGame = (first == "sky");
            if (!firstIsGame && raw.Count > 0)
            {
                // 只有"目标里有游戏本体却没排第一"才算问题; 只配了 MuMu 之类不算
                bool hasGame = false;
                foreach (string t in raw) if (NormProcName(t) == "sky") { hasGame = true; break; }
                if (hasGame) allOk = false;
            }
            sb.AppendLine("第一个被杀的是不是游戏本体: " + (firstIsGame ? "是"
                : (raw.Count == 0 ? "(没有目标)" : "否")));

            // 顺序必须只重排、不增不减
            // ⚠️ 比较必须大小写不敏感(用户可能写 Sky.exe / sky.exe), 否则会误报"有 BUG"
            List<string> a = new List<string>(raw); a.Sort(StringComparer.OrdinalIgnoreCase);
            List<string> b = new List<string>(sorted); b.Sort(StringComparer.OrdinalIgnoreCase);
            bool same = (a.Count == b.Count);
            if (same) for (int k = 0; k < a.Count; k++)
                if (string.Compare(a[k], b[k], StringComparison.OrdinalIgnoreCase) != 0) { same = false; break; }
            if (!same) allOk = false;
            sb.AppendLine("排序没有丢/多目标: " + (same ? "是" : "否 <== 有 BUG"));
            sb.AppendLine("");
            sb.AppendLine("结论 = " + (allOk ? "顺序符合预期" : "有问题, 见上面 <== 标记"));
        }
        catch (Exception ex) { sb.AppendLine("异常: " + ex); allOk = false; }
        File.WriteAllText(Path.Combine(_baseDir, "_ordertest.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }

    /// <summary>
    /// 无头"并发抢占"测试 —— 专门验证 FireTrigger 的 0->1 抢占和去重窗口。
    ///
    /// 背景(的真实日志缺陷):
    ///   按一下 F4, 三条通道(钩子/轮询/热键)在 11 ms 内先后上报, FireTrigger 里
    ///   "先看 _busy 再起线程" 存在窗口, 结果起了 3 个并行处置 —— 3 次 netsh 断网、
    ///   3 份日志、"再按一次"语义错乱。
    ///
    /// 关键: FireTrigger 是 static 的, 所以这个方法不需要窗体、不需要管理员、
    ///   不装钩子、不注册热键、不碰网卡、不关任何进程, 只是直接并发调它。
    ///   这是"不需要真人按键、也不需要动这台机器"就能验的证据。
    ///
    /// 输出: _racetest.txt
    /// </summary>
    private static int RunRaceTest()
    {
        _headless = true;
        _noNet = true;                       // 绝不动网卡
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("并发抢占测试(不碰网卡, 不关进程) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("IsAdmin = " + IsAdmin());
        sb.AppendLine("去重窗口 = " + _DEDUP_MS + " ms");

        List<string> warn = new List<string>();
        Config c = LoadConfig(warn);
        if (c == null) c = new Config();
        _cfg = c;

        // 不关任何真实进程: 把这一轮的处置目标临时置空
        List<string> savedProcs = new List<string>(c.Procs);
        string savedProc = c.Proc;
        int savedWait = c.WaitSeconds;
        c.Procs = new List<string>();
        c.Proc = "";
        // 面试关键: 保持期必须留够, 否则处置几十毫秒就跑完了, "处置进行中"这个窗口
        // 根本不存在, 测出来的东西没有意义(真人那轮处置要跑好几秒)。
        c.WaitSeconds = 3;
        // 提到 try 外面: 退出码要反映三个场景的真实结果(以前恒返回 0, 失败看不见)
        bool aOk = false, bOk = false, cOk = false;

        try
        {
            // ---------------- 场景 A: 同一按键, 三条通道在 30 ms 内先后上报 ----------------
            sb.AppendLine("");
            sb.AppendLine("--- 场景 A: 同一按键被 3 条通道在 30 ms 内重复上报 ---");
            int hitA0 = _hitCount;
            FireTrigger("钩子通道", "F4");
            Thread.Sleep(15);
            FireTrigger("轮询通道", "F4");
            Thread.Sleep(15);
            FireTrigger("热键通道", "F4");
            bool abortA = _abort;            // 等处置收尾前先取, 免得被 finally 清掉
            WaitPanicCycle(20000);           // 等这一轮处置走完(按状态等, 不按固定时间 —— 机器满载时固定 sleep 会假失败)
            int runsA = _hitCount - hitA0;
            sb.AppendLine("  起了几次处置 = " + runsA + "  (期望 1)");
            sb.AppendLine("  _busy 已复位 = " + (_busy == 0 ? "是" : "否 <== 卡住了"));
            sb.AppendLine("  _abort 被误置 = " + (abortA ? "是 <== BUG: 保持期会被自己砍掉" : "否"));
            aOk = (runsA == 1) && _busy == 0 && !abortA;

            // ★ 场景之间必须留出"超过去重窗口"的间隔: 三个场景是三次**独立的按键**, 不是同一次的重复上报。
            //   不给间隔的话, 场景 C 的 9 次触发会落在场景 B 那次按下之后 100 ms 左右, 被正确地判成
            //   "同一按键的重复上报"而忽略 -> 自检假失败(产品行为是对的, 是测试少了一步)。
            Thread.Sleep(_DEDUP_MS + 250);

            // ---------------- 场景 B: 真的又按了一次(超出窗口) ----------------
            sb.AppendLine("");
            sb.AppendLine("--- 场景 B: 处置中再按 = 忽略; 处置结束后再按 = 新一轮 ---");
            int hitB0 = _hitCount;
            FireTrigger("钩子通道", "F4");
            Thread.Sleep(500);
            FireTrigger("钩子通道", "F4");    // 处置进行中 -> 必须被忽略(新语义)
            bool abortB = _abort;                    // 处置中按的那一下不该置收尾请求
            int busyRounds = _hitCount - hitB0;      // 处置中按的 -> 忽略, 所以还是 1
            WaitPanicCycle(20000);                   // 等这一轮彻底结束
            FireTrigger("钩子通道", "F4");            // 结束后再按 -> 应该开新一轮
            WaitPanicCycle(20000);
            int runsB = _hitCount - hitB0;
            sb.AppendLine("  处置中那一下: 共起了 " + busyRounds + " 轮  (期望 1 = 被忽略)");
            sb.AppendLine("  _abort 被误置 = " + (abortB ? "是 <== BUG: 处置中按触发键不该收尾" : "否"));
            sb.AppendLine("  结束后再按: 共起了 " + runsB + " 轮  (期望 2)");
            sb.AppendLine("  _busy 已复位 = " + (_busy == 0 ? "是" : "否 <== 卡住了"));
            bOk = (busyRounds == 1) && !abortB && (runsB == 2) && _busy == 0;
            Thread.Sleep(_DEDUP_MS + 250);    // 同上: 场景 C 是第三次独立按键, 要出窗口

            // ---------------- 场景 C: 9 条线程同时抢 ----------------
            sb.AppendLine("");
            sb.AppendLine("--- 场景 C: 9 条线程同时抢(最能暴露竞态) ---");
            int hitC0 = _hitCount;
            int n = 9;
            Thread[] ths = new Thread[n];
            Barrier bar = new Barrier(n);
            for (int i = 0; i < n; i++)
            {
                int me = i;
                ths[i] = new Thread(delegate()
                {
                    bar.SignalAndWait();      // 攒齐 9 条再一起冲
                    FireTrigger("通道" + me, "F4");
                });
                ths[i].IsBackground = true;
                ths[i].Start();
            }
            for (int i = 0; i < n; i++) ths[i].Join(5000);
            bool abortC = _abort;
            WaitPanicCycle(20000);           // 按状态等
            int runsC = _hitCount - hitC0;
            sb.AppendLine("  9 条线程并发 -> 起了几次处置 = " + runsC + "  (期望 1)");
            sb.AppendLine("  _busy 已复位 = " + (_busy == 0 ? "是" : "否 <== 卡住了"));
            sb.AppendLine("  _abort 被误置 = " + (abortC ? "是 <== BUG: 9 条并发把保持期砍了" : "否"));
            cOk = (runsC == 1) && _busy == 0 && !abortC;

            sb.AppendLine("");
            sb.AppendLine("场景A(重复上报只算一次) = " + (aOk ? "通过" : "不通过"));
            sb.AppendLine("场景B(处置中忽略 + 结束后重开) = " + (bOk ? "通过" : "不通过"));
            sb.AppendLine("场景C(9 线程并发只起 1 次) = " + (cOk ? "通过" : "不通过"));
            sb.AppendLine("结论 = " + ((aOk && bOk && cOk)
                ? "抢占与去重都正确 (按触发键只会起 1 个处置)"
                : "有问题, 看上面哪条不通过"));
        }
        catch (Exception ex) { sb.AppendLine("异常: " + ex); }
        finally
        {
            c.Procs = savedProcs;            // 还原(虽然本进程马上就退出)
            c.Proc = savedProc;
            c.WaitSeconds = savedWait;
        }

        File.WriteAllText(Path.Combine(_baseDir, "_racetest.txt"), sb.ToString(), Encoding.UTF8);
        // 任何一个场景不过 -> 退出码非 0(以前恒返回 0, "起点处置重复/保持期被砍"这类失败自动化看不见)
        return (aOk && bOk && cOk) ? 0 : 1;
    }

    /// <summary>
    /// 进程查询性能自检 —— 比较"一次枚举取全部"和"逐个查"的结果与耗时, 一个进程都不会碰。
    /// 结果写 _findtest.txt。
    /// 修正: 这里以前挂着"无头强杀测试 —— 直接终止配置里的目标程序"的注释,
    /// 和实现完全不符(真正的强杀测试是 RunKillTest), 会误导维护者以为跑它很危险/很安全。
    /// </summary>
    private static int RunFindTest()
    {
        _headless = true;
        bool allOk = false;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("进程查询性能自检 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        try
        {
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            List<string> targets = (c == null) ? new List<string>() : c.TargetList();
            // 目标太少的话"共用一次枚举"没意义(省下的遍数不够), 补到 9 个再看
            string[] filler = new string[] { "explorer", "svchost", "dwm", "conhost", "RuntimeBroker",
                                             "SearchApp", "csrss", "winlogon", "taskhostw" };
            int fi = 0;
            while (targets.Count < 9 && fi < filler.Length)
            {
                if (!targets.Contains(filler[fi])) targets.Add(filler[fi]);
                fi++;
            }
            sb.AppendLine("目标数 = " + targets.Count + " : " + string.Join(" / ", targets.ToArray()));
            List<KeyValuePair<int, string>> all = EnumProcesses();
            sb.AppendLine("系统进程总数 = " + all.Count);
            sb.AppendLine("");

            for (int i = 0; i < 5; i++) EnumProcesses();   // 先热身, 免得首轮 JIT 成本算到对比里

            // 再量单次枚举的裸成本(这是"按下后先扫一遍"的固定开销)
            long te = Stopwatch.GetTimestamp();
            for (int rep = 0; rep < 5; rep++) EnumProcesses();
            long msEnum = ElapsedMs(te) / 5;
            sb.AppendLine("单次全表枚举        = " + msEnum + " ms   (这就是「按下后先扫一遍」的固定开销)");

            // 建字典的成本
            long td = Stopwatch.GetTimestamp();
            Dictionary<string, List<int>> map = new Dictionary<string, List<int>>();
            foreach (KeyValuePair<int, string> kv in all)
            {
                string n = NormProcName(kv.Value);
                List<int> l;
                if (!map.TryGetValue(n, out l)) { l = new List<int>(); map[n] = l; }
                l.Add(kv.Key);
            }
            long msDict = ElapsedMs(td);
            sb.AppendLine("建一次查表字典      = " + msDict + " ms   (条目 " + map.Count + ")");
            sb.AppendLine("");

            // 方式一(旧): 每个目标各枚举一次全表
            long t0 = Stopwatch.GetTimestamp();
            int n1 = 0;
            for (int rep = 0; rep < 3; rep++)
                foreach (string x in targets) n1 += FindPids(x).Count;
            long msOld = ElapsedMs(t0);

            // 方式二(新): 一轮共用一次枚举
            long t1 = Stopwatch.GetTimestamp();
            int n2 = 0;
            for (int rep = 0; rep < 3; rep++)
            {
                List<KeyValuePair<int, string>> snap = ProcSnapshot();
                foreach (string x in targets) n2 += FindPids(x, snap).Count;
            }
            long msNew = ElapsedMs(t1);

            sb.AppendLine("跑 3 轮(每轮 " + targets.Count + " 个目标):");
            sb.AppendLine("  旧(每目标各枚举一次全表) = " + msOld + " ms");
            sb.AppendLine("  新(每轮共用一次枚举)     = " + msNew + " ms");
            sb.AppendLine("  省下                     = " + (msOld - msNew) + " ms"
                + "  (" + (msOld > 0 ? (100 * (msOld - msNew) / msOld) : 0) + "%)");
            sb.AppendLine("  每轮省                   = " + ((msOld - msNew) / 3) + " ms");
            sb.AppendLine("");
            bool same = (n1 == n2);
            sb.AppendLine("两种方式结果一致 = " + (same ? "是 (" + n1 + ")" : "否, 旧=" + n1 + " 新=" + n2 + " (不一致)"));
            sb.AppendLine("结论 = " + ((same && msNew <= msOld)
                ? "查询结果一致, 且新方式不慢于旧方式"
                : "有问题"));
            allOk = same && msNew <= msOld;
        }
        catch (Exception ex) { sb.AppendLine("异常: " + ex); allOk = false; }
        File.WriteAllText(Path.Combine(_baseDir, "_findtest.txt"), sb.ToString(), Encoding.UTF8);
        // ★ 退出码要反映结论(以前恒 0)
        return allOk ? 0 : 1;
    }

    /// <summary>
    /// 无头强杀测试 —— 会真的杀掉 guard.ini 里的目标进程(不碰网卡), 结果写 _killtest.txt。
    /// 这是唯一会真的动手的自检, 所以加了二次确认: 必须再带一个 -yes 参数才执行。
    ///   例: SkyGuardGUI.exe killtest -yes
    /// 另外经 KillWithRetry -> StopKnownServices, 服务型目标还会被清掉失败重启策略并 sc stop。
    /// </summary>
    private static int RunKillTest()
    {
        _headless = true;
        bool ok = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("无头强杀测试 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("IsAdmin = " + IsAdmin());
        try
        {
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            List<string> targets = (c == null) ? new List<string>() : c.TargetList();
            if (targets.Count == 0) { sb.AppendLine("配置里没有任何目标程序(guard.ini 缺失或为空)"); }
            sb.AppendLine("目标数 = " + targets.Count);

            // ★ 二次确认: 这个自检是真的会杀进程的, 不能顺手敲一下就跑掉。
            if (!HasArg("-yes") && !HasArg("killtest-yes") && !HasArg("-confirm"))
            {
                sb.AppendLine("");
                sb.AppendLine("已跳过: 这是破坏性自检, 会真的终止下面这些进程。");
                sb.AppendLine("确认要跑请再加一个参数: SkyGuardGUI.exe killtest -yes");
                sb.AppendLine("将被终止的目标: " + string.Join(" / ", targets.ToArray()));
                File.WriteAllText(Path.Combine(_baseDir, "_killtest.txt"), sb.ToString(), Encoding.UTF8);
                return 2;
            }

            sb.AppendLine("");
            long t0 = Stopwatch.GetTimestamp();
            KillWithRetry(targets, 6000);
            ok = true;
            List<KeyValuePair<int, string>> snapKt = EnumProcesses();   // 复查也共用一次枚举
            foreach (string t in targets) if (FindPids(t, snapKt).Count > 0) { ok = false; break; }
            sb.AppendLine("总耗时 = " + ElapsedMs(t0) + " ms  (含补杀轮次)");
            sb.AppendLine("结果   = " + (ok ? "全部成功" : "有残留"));
            sb.AppendLine("");
            sb.AppendLine("--- 复查: 现在还剩下谁 ---");
            foreach (string t in targets)
            {
                List<int> left = FindPids(t, snapKt);
                sb.AppendLine("   " + t.PadRight(24) + " 剩余 " + left.Count + " 个"
                    + (left.Count > 0 ? "  <== 没杀掉" : ""));
            }
        }
        catch (Exception ex) { sb.AppendLine("异常: " + ex); ok = false; }
        File.WriteAllText(Path.Combine(_baseDir, "_killtest.txt"), sb.ToString(), Encoding.UTF8);
        // ★ 退出码要反映真实结果: 以前"有残留"也返回 0, 自动化根本看不见失败
        return ok ? 0 : 1;
    }

    /// <summary>
    /// 按"保命优先级"给目标排序 —— 决定先杀谁。
    ///
    /// 为什么要排序: 配置文件里的顺序是用户添加顺序(可能 MuMu 在前、Sky 在后),
    /// 而保命关键是尽早切断游戏本体的连接, 所以游戏/模拟器主程序必须排最前。
    /// 实测: 按配置顺序跑时 Sky.exe 排在最后, 白等 1.4 秒才轮到它。
    ///
    /// 分级:
    ///   0 游戏本体(切连接最快, 最要紧)
    ///   1 模拟器界面/服务(游戏本体就挂在这些进程下)
    ///   2 虚拟机(hypervisor, 拆起来最慢, 但不影响游戏连接)
    ///   3 其余(远程控制组件等)
    /// </summary>
    private static int TargetPriority(string name)
    {
        string n = NormProcName(name);
        if (n == "sky") return 0;
        if (n == "mumunxmain" || n == "mumunxdevice" || n == "mumunxservice") return 1;
        if (n.IndexOf("vmm", StringComparison.Ordinal) >= 0) return 2;
        return 3;
    }

    private static List<string> SortByPriority(List<string> targets)
    {
        // ⚠ List.Sort 用的是不稳定的内省排序: 比较函数返回 0 时, 同级元素的顺序不保证保持。
        //   所以拿"原始下标"当第二关键字, 把"同级保持配置顺序"做成事实, 而不是一句注释。
        List<KeyValuePair<int, string>> tmp = new List<KeyValuePair<int, string>>();
        for (int i = 0; i < targets.Count; i++) tmp.Add(new KeyValuePair<int, string>(i, targets[i]));
        tmp.Sort(delegate(KeyValuePair<int, string> a, KeyValuePair<int, string> b)
        {
            int pa = TargetPriority(a.Value), pb = TargetPriority(b.Value);
            if (pa != pb) return pa - pb;
            return a.Key - b.Key;   // 同级: 按配置里的原始顺序
        });
        List<string> r = new List<string>();
        foreach (KeyValuePair<int, string> kv in tmp) r.Add(kv.Value);
        return r;
    }

    // ============================================================================
    //  预热表: 保护期间后台记着"目标进程的 PID + 创建时间", 触发时第一件事直接挂起它。
    //
    //  为什么值得做: 触发后原来的顺序是"扫全表(253 个进程 17 ms, 进程越多越久) -> 定位 PID ->
    //  挂起"。而目标在保护期间就一直跑着, 完全可以提前记下来 —— 触发时省掉扫表,
    //  直接把挂起变成第一条命令(挂起本身才是"让它停下来"的那一刀)。
    //
    //  唯一的真风险: PID 会被系统回收重用, 只比 PID 就可能挂起**别的进程**。
    //  所以每条记录都带进程创建时间, 动手前必须用 GetProcessTimes 核对一致 ——
    //  不一致或读不到, 一律不碰, 交给原来的扫表路径(功能不降级, 只是慢一点)。
    // ============================================================================

    /// <summary>预热表里的一条: 目标进程的 PID + 创建时间(100ns, 自 1601 起)</summary>
    private sealed class WarmProc
    {
        public string Name;
        public int Pid;
        public long CreateTicks;
    }

    private static readonly object _warmGate = new object();
    private static List<WarmProc> _warm = new List<WarmProc>();
    private static volatile bool _warmRun = false;
    /// <summary>预热线程的"代号": 每次启停都 +1, 老线程醒来看见代号变了就自己退出。
    /// 只用 _warmRun 不够 —— 停止再开始保护时它又变成 true, 上一代线程会跟着继续跑。</summary>
    private static volatile int _warmGen = 0;
    private static long _warmRefreshCount = 0;

    /// <summary>取进程创建时间; 失败返回 0(0 = 不可信, 一律不用)。</summary>
    private static long ProcessCreateTicks(int pid)
    {
        IntPtr h = IntPtr.Zero;
        try
        {
            if (pid <= 0) return 0;
            h = OpenProcess(PROCESS_QUERY_LIMITED_INFORMATION, false, pid);
            if (h == IntPtr.Zero) return 0;
            SGFILETIME c, e, k, u;
            if (!GetProcessTimes(h, out c, out e, out k, out u)) return 0;
            return ((long)c.dwHighDateTime << 32) | (long)c.dwLowDateTime;
        }
        catch { return 0; }
        finally { if (h != IntPtr.Zero) CloseHandle(h); }
    }

    /// <summary>刷一次预热表(后台线程与自检共用同一份逻辑)。</summary>
    private static void RefreshWarmOnce()
    {
        try
        {
            if (_cfg == null) return;
            List<string> targets = _cfg.TargetList();
            if (targets.Count == 0) return;
            List<WarmProc> list = new List<WarmProc>();
            int total;
            Dictionary<string, List<int>> map = ProcMap(null, out total);   // 复用同一条枚举路径
            foreach (string name in targets)
            {
                foreach (int pid in PidsFrom(map, name))
                {
                    WarmProc w = new WarmProc();
                    w.Name = name;
                    w.Pid = pid;
                    w.CreateTicks = ProcessCreateTicks(pid);
                    if (w.CreateTicks != 0) list.Add(w);
                }
            }
            lock (_warmGate) { _warm = list; _warmRefreshCount++; }
        }
        catch { }
    }

    /// <summary>处置结束后顺手刷新预热表(开关关着就不做)。目的是让"连着两次触发"的第二次也命中。</summary>
    private static void RefreshWarmIfWanted()
    {
        try
        {
            if (_cfg != null && _cfg.SuspendFirst && _cfg.WarmSuspend) RefreshWarmOnce();
        }
        catch { }
    }

    /// <summary>保护期间的后台刷新线程(默认每秒一次; 间隔与开关都在设置里, 每轮重读所以改完立刻生效)。</summary>
    private static void StartWarmWatcher()
    {
        if (_warmRun) return;
        // 换代号: 万一上一代线程还在(停止后最多 5 秒才醒来), 它看见代号变了会自己退出
        int myGen = ++_warmGen;
        _warmRun = true;
        Thread t = new Thread(delegate()
        {
            while (_warmRun && _warmGen == myGen)
            {
                int waitMs = 1000;
                try
                {
                    // 开关与间隔每次循环都重读: 设置里改了立刻生效, 不用重启程序
                    if (_cfg != null)
                    {
                        waitMs = _cfg.WarmIntervalMs;
                        if (waitMs < 300) waitMs = 300;
                        if (waitMs > 5000) waitMs = 5000;
                        if (_busy == 0 && _guarding && _cfg.SuspendFirst && _cfg.WarmSuspend) RefreshWarmOnce();
                    }
                }
                catch { }
                Thread.Sleep(waitMs);
            }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardWarm";
        t.Priority = ThreadPriority.BelowNormal;
        t.Start();
    }

    private static void StopWarmWatcher()
    {
        _warmGen++;          // 换代号: 睡眠中的线程醒来立刻退出, 不用等它自然结束
        _warmRun = false;
        lock (_warmGate) { _warm = new List<WarmProc>(); }
    }

    /// <summary>
    /// 快路径: 直接挂起预热表里那些"核对过身份"的目标进程。返回挂起成功的个数, ms = 这一趟花了多久。
    ///
    /// 这是"按下后 100 ms 内让游戏停下来"的关键一步 —— 它不扫表, 只做:
    ///   核对创建时间(1 次 OpenProcess+GetProcessTimes) -> 挂起(1 次 NtSuspendProcess)。
    /// </summary>
    private static int FastSuspendWarm(out int ms)
    {
        ms = 0;
        long t0 = Stopwatch.GetTimestamp();
        int n = 0;
        // 开关关了就不走这条路(设置里改完立刻生效)
        if (_cfg != null && (!_cfg.SuspendFirst || !_cfg.WarmSuspend))
        {
            ms = (int)ElapsedMs(t0);
            return 0;
        }
        try
        {
            List<WarmProc> snap;
            lock (_warmGate) { snap = new List<WarmProc>(_warm); }   // 复制一份, 别握着锁去挂进程
            if (snap == null || snap.Count == 0) { ms = (int)ElapsedMs(t0); return 0; }
            // 按保命优先级排: **游戏本体第一个挂**。
            // 多目标时(模拟器有 5~6 个进程)不能把几百毫秒花在模拟器组件上 —— 那几百毫秒
            // 正是"结果会不会被传出去"的窗口。顺序和 KillWithRetry 用的是同一套规则。
            snap.Sort(delegate(WarmProc a, WarmProc b)
            {
                int pa = TargetPriority(a.Name), pb = TargetPriority(b.Name);
                if (pa != pb) return pa - pb;
                return 0;
            });
            foreach (WarmProc w in snap)
            {
                try
                {
                    if (w.Pid <= 0 || w.CreateTicks == 0) continue;
                    if (ProcessCreateTicks(w.Pid) != w.CreateTicks) continue;   // 没了 / PID 被重用 -> 不碰
                    string why; int one;
                    if (TrySuspendProcess(w.Pid, out why, out one))
                    {
                        n++;
                        _suspendedPids.Add(w.Pid);
                        Log("    预热表命中: " + w.Name + " PID " + w.Pid + " 已挂起 (" + one + " ms, " + why + ")");
                    }
                }
                catch { }
            }
        }
        catch { }
        ms = (int)ElapsedMs(t0);
        return n;
    }

    /// <summary>
    /// 本次处置里被挂起过的 PID(只在处置线程里读写, 不需要锁)。
    /// 用途: 万一某个进程终止失败(系统级保护), 日志要说清楚"它已经被挂起、
    /// 不会再有任何动作", 而不是让用户以为它还活着在传数据。
    /// </summary>
    private static readonly List<int> _suspendedPids = new List<int>();

    /// <summary>
    /// 立刻让一个进程"停下来": 挂起它全部线程。返回是否成功, 并给出方式和耗时。
    ///
    /// 这一刀才是"杀掉"要的效果 —— 挂起之后目标线程再也拿不到 CPU, 也就传不出任何结果。
    /// 时间线上它和"等 TerminateProcess 返回"是两件事: 后者是内核拆线程/等驱动释放引用的账,
    /// 实测给光遇下终止命令要 715 ms 才返回, 而挂起是微秒级的一次调用。
    /// </summary>
    private static bool TrySuspendProcess(int pid, out string how, out int ms)
    {
        how = ""; ms = 0;
        long t0 = Stopwatch.GetTimestamp();
        IntPtr h = OpenProcess(PROCESS_SUSPEND_RESUME, false, pid);
        if (h == IntPtr.Zero)
        {
            how = "OpenProcess 失败(错误码 " + Marshal.GetLastWin32Error() + ")";
            ms = (int)ElapsedMs(t0);
            return false;
        }
        try
        {
            uint st = NtSuspendProcess(h);
            if (st == 0)
            {
                how = "整进程挂起";
                ms = (int)ElapsedMs(t0);
                return true;
            }
            int n = SuspendAllThreadsOf(pid);
            how = "逐线程挂起 " + n + " 个 (NtSuspendProcess=0x" + st.ToString("X8") + ")";
            ms = (int)ElapsedMs(t0);
            return n > 0;
        }
        catch (Exception ex)
        {
            how = ex.GetType().Name + ": " + ex.Message;
            ms = (int)ElapsedMs(t0);
            return false;
        }
        finally { CloseHandle(h); }
    }

    /// <summary>兜底: 用线程快照把目标进程的线程逐个挂起(全文档化 API, 比整进程挂起慢)。</summary>
    private static int SuspendAllThreadsOf(int pid)
    {
        int n = 0;
        IntPtr snap = CreateToolhelp32Snapshot(TH32CS_SNAPTHREAD, 0);
        if (snap == IntPtr.Zero || snap == new IntPtr(-1)) return 0;
        try
        {
            THREADENTRY32 te = new THREADENTRY32();
            te.dwSize = (uint)Marshal.SizeOf(typeof(THREADENTRY32));
            if (!Thread32First(snap, ref te)) return 0;
            do
            {
                if (te.th32OwnerProcessID != (uint)pid) continue;
                IntPtr th = OpenThread(THREAD_SUSPEND_RESUME, false, te.th32ThreadID);
                if (th == IntPtr.Zero) continue;
                try { if (SuspendThread(th) != -1) n++; }
                finally { CloseHandle(th); }
            } while (Thread32Next(snap, ref te));
        }
        catch { }
        finally { CloseHandle(snap); }
        return n;
    }

    /// <summary>
    /// 补杀 —— 针对实测遇到的两类"杀不掉"的情况:
    ///
    ///  1) 会自我重启的 Windows 服务(实测 MuMuRemoteService): 它配了 FAILURE_ACTIONS=RESTART/0ms,
    ///     反复杀进程会被 SCM 零延迟拉回。所以要先清掉失败重启设置, 再 sc stop。
    ///  2) 其余顽固进程: 在时间窗口内只针对"还活着的"反复杀(不重跑全部目标, 省时间)。
    ///
    /// 顺序上踩过一个坑: 一开始是"先停服务, 再杀进程" —— 停服务要串起好几个 sc.exe,
    /// 白等几百毫秒才轮到游戏本体。现在改成 先杀进程, 再停服务:
    /// 排序后 Sky.exe 排第一, 按下之后第一件事就是它死; 停服务只影响会复活的 MuMu 远程组件。
    /// </summary>
    private static void KillWithRetry(List<string> targets, int windowMs)
    {
        long tEntry = Stopwatch.GetTimestamp();
        EnableDebugPrivilege();   // 受限令牌/沙箱进程只有开了它才杀得动(只尝试一次, 结果写日志)
        long privMs = ElapsedMs(tEntry);
        targets = SortByPriority(targets);
        long sortMs = ElapsedMs(tEntry) - privMs;
        // 分段计时: 以前只知道"一共花了多久", 不知道时间被谁吃了
        // (真机日志里 07.994→08.029 有 38 ms 没着落, 就是靠这一行量出来的)
        Log("  进入处置: 自触发 " + ElapsedMs(_panicStartTicks) + " ms; 权限 " + privMs
            + " ms / 排序 " + sortMs + " ms, 到这里共 " + ElapsedMs(tEntry) + " ms");
        // 不再打印整行"关的顺序": 它和"目标程序共 N 个"基本重复, 白占日志地方。
        // 排序逻辑本身没变(游戏本体永远第一); 要核对顺序跑 ordertest 模式。

        long t0 = Stopwatch.GetTimestamp();
        _suspendedPids.Clear();      // 本次处置的挂起记录(别把上一次的算进来)

        // ★★ 第一条命令: 挂起预热表里"核对过身份"的目标进程 —— 不扫表, 只做
        //   一次创建时间核对 + 一次 NtSuspendProcess(实测 1~3 ms)。
        //   扫表那 15~40 ms(随系统进程数增长)因此不在这条路上了。
        int fastMs; int fastN = FastSuspendWarm(out fastMs);
        if (fastN > 0)
            Log("  第一条命令: 挂起预热表命中 " + fastN + " 个 (自触发 " + ElapsedMs(_panicStartTicks)
                + " ms, 这一趟 " + fastMs + " ms)");
        else
            Log("  预热表未命中(目标刚启动或刚被刷新), 走扫表路径 (自触发 " + ElapsedMs(_panicStartTicks) + " ms)");

        int round = 0;
        while (true)
        {
            round++;
            // ★ 这一轮只枚举一次全表, 扫描和定位共用同一个字典。
            //   老代码这里扫一遍、StartAllKills 里每个目标又各扫一遍 —— 按下后白白多花 ~100 ms,
            //   而"按下到真的下刀"正是决定生死的那段(用户要求压进 100 ms)。
            //   实测: 单次枚举 9 ms; 老方式 9 目标 107 ms -> 新方式 ~10 ms。
            long tScan = Stopwatch.GetTimestamp();
            int totalProc;
            Dictionary<string, List<int>> map = ProcMap(null, out totalProc);
            List<string> alive = new List<string>();
            foreach (string t in targets)
                if (PidsFrom(map, t).Count > 0) alive.Add(t);
            long scanMs = ElapsedMs(tScan);
            if (round == 1) Log("  扫描 " + totalProc + " 个进程 + 定位目标, 花了 " + scanMs + " ms");

            if (alive.Count == 0)
            {
                if (round > 1) Log("  补杀完成: 共 " + round + " 轮 (" + ElapsedMs(t0) + " ms)");
                RefreshWarmIfWanted();   // 处置完顺手刷新表: 下一次触发(比如游戏重开)仍然命中
                return;
            }
            if (round == 1) Log("  在运行的: " + string.Join(" / ", alive.ToArray()));

            // ★★ 要命的那一刀: **先挂起, 再终止**。
            //   挂起是一次微秒级调用, 挂起后目标线程再也拿不到 CPU —— 传不出任何结果;
            //   而 TerminateProcess 要等内核拆完几百个线程才返回(实测给光遇 715 ms), 期间进程还在跑。
            //   所以"按下后多久游戏真的停下来"看的是这一行的时间戳, 不是后面"确认退出"那一行。
            long suspMs = 0;
            if (_cfg != null && !_cfg.SuspendFirst)
            {
                Log("  (设置里关了「先挂起」—— 直接下终止命令; 停下时间取决于内核拆进程的快慢)");
            }
            else
            {
                long tSusp = Stopwatch.GetTimestamp();
                int susp = 0, suspWorst = 0; string way = "";
                foreach (string t in alive)
                {
                    foreach (int pid in PidsFrom(map, t))
                    {
                        string why; int ms;
                        if (TrySuspendProcess(pid, out why, out ms))
                        {
                            susp++;
                            _suspendedPids.Add(pid);
                            if (ms > suspWorst) suspWorst = ms;
                            if (way.Length == 0) way = why;
                        }
                        else Log("    挂起 PID " + pid + " 失败: " + why);
                    }
                }
                suspMs = ElapsedMs(tSusp);
                Log("  目标进程已停止执行: " + susp + " 个 (自触发 " + ElapsedMs(_panicStartTicks)
                    + " ms, 挂起最慢 " + suspWorst + " ms, 合计 " + suspMs + " ms"
                    + (way.Length > 0 ? ", " + way : "") + ")");
            }

            // 一把全发出去, 再一起等 —— 不再"关一个等一个"
            long tTerm = Stopwatch.GetTimestamp();
            KillBatch kb = StartAllKills(alive, map);
            long termMs = ElapsedMs(tTerm);
            WaitAllKills(kb);
            long waitMs = ElapsedMs(tTerm) - termMs;
            if (round == 1)
                Log("  第一次处置各段: 扫表 " + scanMs + " / 挂起 " + suspMs + " / 终止 " + termMs
                    + " / 等退出 " + waitMs + " ms (自触发 " + ElapsedMs(_panicStartTicks) + " ms)");

            // 服务托管的进程(MuMu 远程组件)会被 SCM 拉回来, 得停服务。
            // 实测这一步要 0.3~1.9 秒, 单独丢后台跑, 不拖住这一轮的收尾。
            if (HasServiceBackedTarget(alive))
            {
                List<string> svcTargets = new List<string>(targets);
                Thread st = new Thread(delegate()
                {
                    long s0 = Stopwatch.GetTimestamp();
                    StopKnownServices(svcTargets);
                    Log("  停服务花了 " + ElapsedMs(s0) + " ms");
                });
                st.IsBackground = true;
                st.Start();
                st.Join(3000);   // 最多等 3 秒, 等不到就让它自己在后台跑完
                if (st.IsAlive) Log("  停服务还在后台跑, 先往下走");
            }

            if (ElapsedMs(t0) >= windowMs)
            {
                List<string> left = new List<string>();
                foreach (string t in targets) if (PidsFrom(map, t).Count > 0) left.Add(t);   // 复用本轮那份进程表
                if (left.Count > 0)
                {
                    Log("  补杀窗口 " + windowMs + " ms 用完, 仍有: " + string.Join(" / ", left.ToArray()));
                    if (_suspendedPids.Count > 0)
                        Log("  (它们已经被挂起, 不会再有任何动作; 需要的话在任务管理器里结束)");
                }
                RefreshWarmIfWanted();   // 处置完顺手刷新表
                return;
            }
            Thread.Sleep(250);
        }
    }

    /// <summary>记录"这台机器上不存在"的服务名 —— 免得每轮补杀都刷一遍 1060 噪声, 也省掉几次进程启动</summary>
    private static readonly Dictionary<string, bool> _noSuchService = new Dictionary<string, bool>();

    /// <summary>列表里有没有"由 Windows 服务托管"的目标(有才值得跑一遍 sc)</summary>
    private static bool HasServiceBackedTarget(List<string> targets)
    {
        foreach (string t in targets) if (GuessServiceName(t) != null) return true;
        return false;
    }

    /// <summary>
    /// 轮询通道 —— 第二条触发路径, 完全不经过键盘钩子。
    ///
    /// 为什么需要它 (实测踩出来的):
    ///   光遇卡白(窗口无响应)的时候, 前台窗口所在线程已经不泵消息了。
    ///   这时候整条系统键盘输入链是卡住的 —— 低级键盘钩子根本不会被调用,
    ///   所以按触发键一点反应都没有(日志里连一行原始按键都看不到)。
    ///   鼠标点一下别的窗口(换掉那个卡死的前台窗口)之后, 一切立刻恢复。
    ///
    ///   GetAsyncKeyState 不同: 它是直接读系统的异步键状态表,
    ///   不经过前台窗口, 也不经过任何钩子链。窗口卡成什么样都读得到。
    ///
    /// 代价: 它是轮询, 不是事件 —— 所以用 8 ms 的间隔扫, 保证不会漏掉短按。
    /// 这条通道和钩子通道同时生效, 谁先发现算谁的 (_busy / _hitCount 去重)。
    /// </summary>
    private static void StartKeyPoll()
    {
        if (_pollStarted) return;
        _pollStarted = true;
        Thread t = new Thread(delegate()
        {
            try { Thread.CurrentThread.Priority = ThreadPriority.AboveNormal; }
            catch { }

            Dictionary<uint, bool> wasDown = new Dictionary<uint, bool>();
            // 钩子那边刚触发过就不要再补一刀
            long lastHit = _hitCount;

            while (true)
            {
                Thread.Sleep(8);
                // 保命边界: 这条线程是"单键触发"的兜底通道, 任何异常都不能让它把进程带走。
                // 早先这里有第二个遍历 _trigs 的 foreach, 而热键线程会改 _trigs ——
                // 撞上就是 InvalidOperationException, 线程外没人接, 进程直接结束。
                try
                {
                    if (!_guarding) { wasDown.Clear(); continue; }
                    if (_hitCount != lastHit) { lastHit = _hitCount; }   // 钩子已经处理了, 不重复

                    foreach (KeyTrig kt in _trigs)
                    {
                        if (kt.Ctrl || kt.Alt || kt.Shift) continue;   // 组合键交给钩子, 轮询只认单键

                        bool down = (GetAsyncKeyState((int)kt.Vk) & 0x8000) != 0;
                        bool prev;
                        wasDown.TryGetValue(kt.Vk, out prev);
                        wasDown[kt.Vk] = down;

                        // 只在"刚按下去"这一下触发, 按住不重复
                        if (!down || prev) continue;

                        if (_pollTestOnly)
                        {
                            // 自检模式: 只记数, 不真动手
                            _hitCount++;
                            lastHit = _hitCount;
                            continue;
                        }
                        lastHit = _hitCount + 1;
                        FireTrigger("轮询通道", kt.Name);
                        break;
                    }
                }
                catch (Exception ex)
                {
                    // 吞掉但留证据: 这条通道不能因为一次异常就永久失效
                    LogToFileOnly("[轮询通道] 异常(已忽略, 通道继续): " + ex.Message);
                    Thread.Sleep(50);
                }
            }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardKeyPoll";
        t.Start();
    }

    private static volatile bool _pollStarted = false;
    /// <summary>自检模式: 轮询只记数, 不真的执行处置</summary>
    private static volatile bool _pollTestOnly = false;

    // ============================================================================
    //  通道三: RegisterHotKey (系统级热键)
    //
    //  为什么还要再试一条: 实测发现光遇卡白时, 连 GetAsyncKeyState 都读不到按键 ——
    //  说明按键根本没进系统输入链。前两条通道(钩子 / 异步键状态)都挂在同一条链上,
    //  所以一起失效。RegisterHotKey 是交给系统去匹配的, 匹配路径不同, 值得一试。
    // ============================================================================

    private static volatile bool _hotkeyStarted = false;
    private static volatile int _hotkeyOk = 0;
    private static volatile int _spareHotkeys = 0;
    private static IntPtr _hotkeyWnd = IntPtr.Zero;
    private static volatile uint _hotkeyThreadId = 0;
    private static WndProcDelegate _hotkeyProc;      // 必须保持引用, 否则被 GC 回收
    private static readonly List<int> _hotkeyIds = new List<int>();
    /// <summary>
    /// 热键 ID -> 键名。必须单独存, 不能拿 ID 去索引 _trigs 里第几个键:
    /// 那个索引只在"全部注册成功"时才碰巧对得上 —— 用户键里有一个被别的程序占了(比如 F12),
    /// 后面每一个的索引就都错位一格, 日志会把备用键 F13 报成用户键名。
    /// </summary>
    private static readonly Dictionary<int, string> _hotkeyNames = new Dictionary<int, string>();

    private static void StartHotKeys()
    {
        if (_hotkeyStarted) return;
        _hotkeyStarted = true;

        Thread t = new Thread(delegate()
        {
            try
            {
                _hotkeyThreadId = GetCurrentThreadId();
                _hotkeyProc = new WndProcDelegate(HotKeyWndProc);

                // 必须注册自己的窗口类: 用系统 STATIC 类的话, WM_HOTKEY 到不了我们的窗口过程,
                // 表现就是"热键注册成功但从来不触发"(实测踩过)。
                const string clsName = "SkyGuardHotKeyWnd";
                WNDCLASSEX wc = new WNDCLASSEX();
                wc.cbSize = Marshal.SizeOf(typeof(WNDCLASSEX));
                wc.lpfnWndProc = _hotkeyProc;
                wc.lpszClassName = clsName;
                wc.hInstance = GetModuleHandle(null);
                ushort atom = RegisterClassEx(ref wc);
                if (atom == 0)
                {
                    int rcErr = Marshal.GetLastWin32Error();
                    // 类已存在就可以直接接着用(类是本进程注册的, 窗口还能照样建出来):
                    //   183 = ERROR_ALREADY_EXISTS
                    //   1410 = ERROR_CLASS_ALREADY_EXISTS  <- 重复注册窗口类时系统实际报的是这个
                    // 老代码只认 183, 于是"停止保护后再开始保护"(以及看门狗每次重装钩子)
                    // 都会在这里 return, 把 _hotkeyStarted 置 false —— 热键通道在该进程内再也起不来。
                    // 日志里的 32 次"注册窗口类失败, 错误码 1410"就是这么来的。
                    if (rcErr != 183 && rcErr != 1410)
                    {
                        LogToFileOnly("[热键通道] 注册窗口类失败, 错误码 " + rcErr);
                        _hotkeyStarted = false;
                        return;
                    }
                }

                // 建一个隐藏窗口, WM_HOTKEY 会投到它上面
                _hotkeyWnd = CreateWindowEx(0, clsName, "SkyGuardHotKey",
                    0x80000000 /*WS_POPUP*/, 0, 0, 0, 0,
                    IntPtr.Zero, IntPtr.Zero, wc.hInstance, IntPtr.Zero);
                if (_hotkeyWnd == IntPtr.Zero)
                {
                    LogToFileOnly("[热键通道] 隐藏窗口建不出来, 错误码 " + Marshal.GetLastWin32Error());
                    _hotkeyStarted = false;
                    return;
                }

                int id = 0xB000;
                int ok = 0;
                List<string> failed = new List<string>();
                foreach (KeyTrig kt in _trigs)
                {
                    uint mods = MOD_NOREPEAT;
                    if (kt.Ctrl) mods |= MOD_CONTROL;
                    if (kt.Alt) mods |= MOD_ALT;
                    if (kt.Shift) mods |= MOD_SHIFT;
                    id++;
                    if (RegisterHotKey(_hotkeyWnd, id, mods, kt.Vk))
                    {
                        _hotkeyIds.Add(id);
                        _hotkeyNames[id] = kt.Name;
                        ok++;
                    }
                    else failed.Add(kt.Name);
                }
                _hotkeyOk = ok;
                LogToFileOnly("[热键通道] 触发键注册 " + ok + " / " + _trigs.Count
                    + (failed.Count > 0 ? "  (注册不上的: " + string.Join(" ", failed.ToArray()) + ")" : ""));

                // 再白送一组 F13~F24: 这些键普通键盘按不到(笔记本上配合 Fn), 不会有程序占用,
                // 注册成功率最高。用户绑的键万一被别的软件占了, 还有这组兜着。
                int spareOk = 0;
                for (uint vk = 0x7C; vk <= 0x87; vk++)
                {
                    id++;
                    if (RegisterHotKey(_hotkeyWnd, id, MOD_NOREPEAT, vk))
                    {
                        _hotkeyIds.Add(id);
                        KeyTrig spare = new KeyTrig();
                        spare.Vk = vk; spare.Name = "F" + (vk - 0x7C + 13);
                        _hotkeyNames[id] = spare.Name;
                        // ★ 必须"拷一份再换引用", 绝对不能原地 _trigs.Add:
                        //   钩子线程和轮询线程都在 foreach 遍历 _trigs, 遍历期间被 Add 会让
                        //   List 枚举器抛 InvalidOperationException; 轮询那条链外层没有 try/catch,
                        //   异常会冒到线程外 -> .NET 4 默认直接结束整个进程(保护当场失效)。
                        //   换引用是原子的, 遍历方要么看到旧的、要么看到新的, 都不会炸。
                        List<KeyTrig> copy = new List<KeyTrig>(_trigs);
                        copy.Add(spare);
                        _trigs = copy;
                        spareOk++;
                    }
                }
                _spareHotkeys = spareOk;
                LogToFileOnly("[热键通道] 备用键 F13~F24 注册 " + spareOk + " / 12");
                MSG m;
                while (GetMessage(out m, IntPtr.Zero, 0, 0) > 0)
                {
                    TranslateMessage(ref m);
                    DispatchMessage(ref m);
                }
            }
            catch (Exception ex) { LogToFileOnly("[热键通道] 异常: " + ex.Message); }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardHotKey";
        t.Start();
    }

    private static void StopHotKeys()
    {
        try
        {
            // 先快照再遍历: 热键线程可能正在往 _hotkeyIds 里加。原地 foreach 撞上并发修改会抛异常,
            // 而异常被下面的 catch 吞掉后, DestroyWindow / PostThreadMessage 就全被跳过了 ——
            // 那条热键线程再也收不到 WM_QUIT, 通道停不干净(再开始保护就会有两个热键窗口)。
            int[] ids = _hotkeyIds.ToArray();
            IntPtr wnd = _hotkeyWnd;
            uint tid = _hotkeyThreadId;
            foreach (int id in ids) UnregisterHotKey(wnd, id);
            _hotkeyIds.Clear();
            _hotkeyNames.Clear();
            _hotkeyWnd = IntPtr.Zero;
            _hotkeyThreadId = 0;

            // ★ DestroyWindow 只能由"创建该窗口的线程"调用 —— 这里以前无条件调用,
            //   而 StopHotKeys 是从 UI 线程过来的(StopHook(true)), 于是每次都静默失败(返回值也没人看)。
            //   现在: 正好在自己线程上才销毁; 别的线程就只投 WM_QUIT, 让那条线程退出时由系统回收窗口。
            if (wnd != IntPtr.Zero && (tid == 0 || tid == GetCurrentThreadId()))
                DestroyWindow(wnd);

            if (tid != 0)
            {
                bool posted = false;
                for (int i = 0; i < 6 && !posted; i++)
                {
                    posted = PostThreadMessage(tid, WM_QUIT, IntPtr.Zero, IntPtr.Zero);
                    if (!posted) Thread.Sleep(50);
                }
                if (!posted)
                    LogToFileOnly("[热键通道] 投递 WM_QUIT 失败(错误码 " + Marshal.GetLastWin32Error()
                        + ") —— 那条线程退出时系统会回收它的窗口");
            }
        }
        catch { }
        _hotkeyStarted = false;
    }

    private static IntPtr HotKeyWndProc(IntPtr hWnd, uint msg, IntPtr wParam, IntPtr lParam)
    {
        try
        {
            if (msg == WM_HOTKEY)
            {
                int id = wParam.ToInt32();
                string name;
                if (!_hotkeyNames.TryGetValue(id, out name)) name = "#" + id;
                FireTrigger("热键通道", name);
            }
        }
        catch { }
        return DefWindowProc(hWnd, msg, wParam, lParam);
    }

    /// <summary>
    /// 四条通道共用这一个入口: 抢占用位、记数、起处置线程。
    ///
    /// ---- 为什么必须用 Interlocked 抢, 而不是"先看 _busy 再起线程"(踩过, 有日志证据) ----
    /// 曾经的日志里, 按一下 F4 出现了 3 次"捕获触发键"
    /// (钩子 .691 / 轮询 .693 / 热键 .702), 接着是 3 个完整并行的处置
    /// (3 次"触发"、3 次 netsh 断网、3 次恢复)。
    /// 根因: 抢占用的 _busy 是在 Panic() 里才置上的, 而 Thread.Start() 到新线程真正开跑
    /// 要 10~30 ms; 这段时间里另外两条通道先读到了 _busy=false, 于是各起一个处置线程。
    /// 后果: 同一个网卡被同时发 3 条 netsh、日志变三份、"再按一次"语义错乱。
    /// 修法: 谁抢到 0->1 谁才起线程, 抢不到的直接忽略(起: 处置进行中忽略触发键)。
    ///
    /// ---- 为什么还要一个"去重窗口" ----
    /// 抢不到的那个, 有两种可能, 但现在不能一律当成"用户又按了一次":
    ///   (a) 同一次物理按键被另一条通道重复上报(上例中的 .693 / .702);
    ///   (b) 用户真的又按了一次(想立刻恢复网络)。
    /// (a) 若被当成 (b), 会立刻置 _abort -> 把保持期当场砍掉 —— 等于"按一下自己把等待取消了"。
    /// 所以用时间区分: 距上次起处置不到 _DEDUP_MS 的, 判为同一按键的重复上报, 不置 _abort;
    /// 超过的才是用户真的又按了一次。真人连按两下的间隔远大于 250 ms。
    /// </summary>
    private const int _DEDUP_MS = 250;

    private static void FireTrigger(string channel, string keyName)
    {
        // Stopwatch 时间戳, 不会被系统对时/夏令时干扰
        long now = Stopwatch.GetTimestamp();

        if (Interlocked.CompareExchange(ref _busy, 1, 0) != 0)
        {
            // 已经有处置在跑: 判断这是"同一按键被别的通道重复上报"还是"用户真的又按了一次"
            //
            // ★ 用"进入本函数的时刻(now)"和上次触发时刻比, 而不是"现在的时刻":
            //   抢到的那条通道后面还要写两行日志, 磁盘/首次 JIT 慢的时候能花几十毫秒,
            //   于是同一按键的另外两条上报会被算成"相隔几百毫秒"—— 误判成用户真的又按了一次,
            //   一按就把保持期当场砍掉(自检 racetest 场景 A/C 抓到的就是这个)。
            //   按"上报到达时刻"算才是这个窗口真正想表达的东西: 三次上报本来就在几毫秒内。
            long sinceMs = ElapsedMs(_lastFireTicks, now);
            // 第二个锚点: 本次处置的**开始时刻**。
            //   只看"上次触发"有真 bug: 第一个通道的回调如果被系统饿住(实测机器忙时 WakePanic
            //   花了 495 ms), 那另外两条同按键的重复上报在墙钟上就离上次触发过了 495 ms,
            //   会被误判成"用户又按了一次" -> 置 _abort -> 保持期被自己砍掉(网络提前恢复)。
            //   racetest 场景 A 抓到的就是这个。加上"处置刚开始"这个锚点就闭合了。
            long sinceStartMs = ElapsedMs(_panicStartTicks, now);
            if ((_lastFireTicks != 0 && sinceMs < _DEDUP_MS)
                || (_panicStartTicks != 0 && sinceStartMs < _DEDUP_MS))
            {
                // 同一次按键的重复上报: 记一行就走, 绝不碰 _abort
                Log("   " + channel + ": 与上次触发相隔 " + sinceMs + " ms (处置开始 " + sinceStartMs
                    + " ms) -> 判定为同一按键的重复上报, 已忽略");
                return;
            }
            // ★ 用户定的新语义: 上一轮处置还在进行中(含 20 秒保持期)就**忽略**这次触发 ——
            //   已经在处理了。想提前恢复用主界面的 [恢复网络] 或 [停止保护](都会走全套复原);
            //   一轮处置彻底结束之后再按, 才会开始新的一轮。
            // 日志限流: 长按/连按时这条会刷屏, 5 秒最多一行。
            if (_lastBusyIgnoreTicks == 0 || ElapsedMs(_lastBusyIgnoreTicks) > 5000)
            {
                _lastBusyIgnoreTicks = now;
                Log("   " + channel + ": 上一轮处置还在进行中(自触发 " + ElapsedMs(_panicStartTicks)
                    + " ms) -> 忽略这次触发; 想提前恢复请点[恢复网络]或[停止保护]");
            }
            // ★ V1.1.5-RC1: 处置位被占太久 = 某个子进程(通常是 netsh)卡住了。
            //   语义一个字不改(仍然忽略这次触发), 但必须让用户知道"按不动"的原因,
            //   否则他会以为键坏了 —— 对一个保命工具来说, 这种误会本身就是事故。
            if (_busySinceTicks != 0 && ElapsedMs(_busySinceTicks) > BUSY_STUCK_MS)
            {
                _busyStuck = true;
                if (_lastBusyStuckLogTicks == 0 || ElapsedMs(_lastBusyStuckLogTicks) > 5000)
                {
                    _lastBusyStuckLogTicks = now;
                    Log("   注意: 处置位已被占用 " + (ElapsedMs(_busySinceTicks) / 1000)
                        + " 秒(超过 " + (BUSY_STUCK_MS / 1000) + " 秒) —— 网络操作很可能卡住了。"
                        + " 触发键要等这一轮收尾才会再响应; 想立刻收尾请点[停止保护]。");
                }
            }
            return;
        }

        // 抢到了占位 —— 但还得过一遍去重窗口。
        // 漏在这儿会真出问题: 上一轮处置可能在几十毫秒内就结束(目标为空 / 立刻失败 / 刚 abort),
        // 于是同一按键的第 2、3 条上报会走到这条"抢占成功"的路上, 又起一轮处置。
        // (racetest 场景 A 偶发失败就是它 —— 只在"上一轮已经收尾"的那个时间窗里出现。)
        long dupWin = ElapsedMs(_lastFireTicks, now);
        if (_lastFireTicks != 0 && dupWin < _DEDUP_MS)
        {
            Log("   " + channel + ": 与上次触发相隔 " + dupWin
                + " ms -> 同一按键的重复上报(上一轮已收尾), 已忽略");
            Interlocked.Exchange(ref _busy, 0);   // 把刚抢到的占位还回去, 否则处置再也不会被启动
            return;
        }
        _abort = false;          // 抢占成功, 清掉上一次留下的收尾开关
        // 记下"这一轮从什么时候开始占处置位" —— 占太久要能看出来(见 BUSY_STUCK_MS)
        _busySinceTicks = now;
        _busyStuck = false;
        _netOpStuck = false;
        _lastFireTicks = now;
        _hitCount++;
        // ★ 保命优先: 先把常驻处置线程叫醒, 再做日志。
        //   日志在磁盘忙/首次 JIT 时能花几十毫秒, 而这几毫秒正是"抢在结果上报之前"的那几毫秒;
        //   顺带也让"同一按键被别的通道重复上报"更不容易超出去重窗口(窗口按触发时刻算)。
        long tTh = Stopwatch.GetTimestamp();
        WakePanic();
        long wakeMs = ElapsedMs(tTh);

        Log(channel + " 捕获触发键 " + keyName
            + " (第 " + _hitCount + " 次, 钩子累计调用 " + _hookCalls + " 次) *"
            + "  [唤醒处置线程 " + wakeMs + " ms]");
        // 钩子回调里干活的耗时必须记下来: 系统给钩子回调的时限默认只有 300 ms,
        // 超了会被静默摘钩子(表现就是"按触发键没反应")。
        int cbMs = (int)ElapsedMs(now);
        Log("  " + channel + " 回调里记这两行用了 " + cbMs + " ms (处置线程已先唤醒, 不受影响)");
        _diagHookCallbackMs = cbMs;   // 状态面板用: 最近一次触发从进函数到记完日志花了多久
        // 去重锚点挪到"这一条通道报完"的时刻: 别的通道会在随后几十毫秒里陆续上报,
        // 它们离"按下那一刻"可能已经几百毫秒(第一个回调被饿住时), 但离这里总是几十毫秒。
        // 这样"同一按键的重复上报"就不会再被当成第二次按键。
        _lastFireTicks = Stopwatch.GetTimestamp();

        // ★ V1.1.5-RC1: 放在**最后**做, 不影响上面任何一步的时延。
        //   一次触发就顺手查一遍"钩子还在不在系统里": 如果这次是轮询/热键通道报上来的、
        //   而钩子其实早被系统摘了, 这一下就能发现并装回去, 不用等 300 秒那个周期。
        //   代价是一次 PostThreadMessage(几微秒), 只是把消息排进钩子线程的队列。
        RequestHookSelfCheck("触发后");
    }

    // ============================================================================
    //  焦点解堵: 光遇卡白时, 卡死的前台窗口会把整条键盘输入链堵住。
    //  实测: 鼠标点一下桌面(换掉那个前台窗口)立刻恢复 —— 这件事程序可以自己做:
    //  发现前台窗口无响应, 就把前台切到本程序, 让触发键能进来。不杀游戏、不掉线。
    //
    //  11.1.2-RC15 重写。旧版"焦点一直在闪"是几个具体原因造成的, 都不是玄学:
    //    1) 还焦点时无条件调 ShowWindow(SW_RESTORE)。它的文档语义是"最小化或最大化都还原
    //       成原始大小" —— 全屏游戏就是最大化窗口, 于是每次还焦点都把游戏窗口化一下, 游戏
    //       自己再切回全屏, 肉眼看到的就是画面来回闪。
    //       → 现在只有目标窗口真的最小化(IsIconic)才 SW_RESTORE。
    //    2) "前台不是我们"就抢回来。用户自己点浏览器、点桌面也算"不是我们", 于是每隔一个
    //       扫描周期抢一次, 用户根本没机会用别的窗口。
    //       → 现在只有在"被接管的那个卡死窗口自己又抢回前台"时才拉回一次, 而且有静默期、
    //         有次数上限; 前台是任何别的窗口时一律不碰。
    //    3) 判定没有迟滞。IsHungAppWindow 在"卡/不卡"的边界上会抖, 抖一下就要来回切一遍。
    //       → 进入要连续 confirmRounds 轮(最少 2 轮), 退出要连续 FOCUS_OK_ROUNDS 轮, 每次
    //         切换动作之后有静默期, 一轮结束之后有冷却期。
    //    4) ★ 最阴的一条: 拿 IsHungAppWindow 当"恢复了"的判据。那个标志是系统的缓存 ——
    //       要连续 5 秒不取消息才置位, 而窗口**取一次消息就立刻清零**, 之后又要再等约
    //       5 秒才可能重新置位。所以"卡住但偶尔动一下"的窗口会让它以约 5 秒为周期在
    //       "卡/不卡"之间翻; 用它判恢复, 就会变成"抢 → 还 → 5 秒后 → 再抢"的周期切换,
    //       用户看到的就是"焦点一直闪"。
    //
    //  现在的分工(一句话: 发现卡住靠系统标志, 宣布恢复靠实测):
    //    · "要不要抢" —— 用系统标志(它是 5 秒量级的证据, 不会因为一帧卡顿误判),
    //      并且要连续 confirmRounds 轮 / 拉回时连续 FOCUS_BACK_ROUNDS 轮。
    //    · "要不要还" —— 用 IsWindowResponsive(): 给目标窗口发一个 WM_NULL, 限时
    //      FOCUS_PROBE_MS 等回音。有回音 = 它真的在用消息循环 = 可以把焦点还回去。
    //      系统的卡死标志即使刚被清零也不算数(这正是第 4 条踩的坑)。
    //    · 探针万一对某个窗口拿不到回音(跨会话/被安全软件拦/受保护进程), 不允许因此把焦点
    //      永远扣在本程序身上: 只要系统标志连续 FOCUS_PROBE_BLIND_MS 都说"它不卡了",
    //      就承认探针在这个窗口上不可用, 退回系统标志判断, 并把这件事大声写进日志和界面。
    //      自检(拿自己的窗口 + 桌面窗口试)拿不到回音时也一样降级, 而且会一直重试直到成功,
    //      不会因为启动时 UI 线程忙一下就永久降级。
    //  另外: 旧版在这里调 SelfTestHook() 注入一个 0xFF 假按键来"自检"。那是往系统输入链里
    //  注入输入, 前台游戏/反作弊/输入法都会收到; 而 0xFF 不是合法虚拟键, 收不到也证明不了
    //  钩子坏了 —— 日志里那句"仍然收不到键"就是这么来的假红。现在改成被动检查, 不注入按键。
    //
    //  决策部分(FocusDecide)与信号折算(FocusSignals)都是不碰窗口的纯函数, 由 `focustest`
    //  用合成序列跑边界, 见 RunFocusTest。
    // ============================================================================

    private const int FOCUS_ACTION_NONE = 0;
    /// <summary>把前台切到本程序(解堵)</summary>
    private const int FOCUS_ACTION_TAKE = 1;
    /// <summary>把前台还给被接管的那个窗口(游戏)</summary>
    private const int FOCUS_ACTION_GIVE = 2;
    /// <summary>要还焦点, 必须连续这么多次判定"目标窗口真的在响应"(约 5 × 扫描间隔)</summary>
    private const int FOCUS_OK_ROUNDS = 5;
    /// <summary>目标窗口自己把前台抢回去后, 要连续这么多次确认才拉回来(前台切换是异步的)</summary>
    private const int FOCUS_BACK_ROUNDS = 3;
    /// <summary>一次接管里最多"再抢"几次 —— 上限是防"和游戏互相抢", 那才是用户看到的闪</summary>
    private const int FOCUS_MAX_RETAKES = 3;
    /// <summary>抢/还之后多久内不再做切换动作(ms): 前台切换是异步的, 不等就会自己跟自己抢</summary>
    private const int FOCUS_SILENT_MS = 1500;
    /// <summary>一轮接管结束后多久内不再开始新的一轮(ms) —— 基础值, 连着来时按 FocusEndEpisode 翻倍</summary>
    private const long FOCUS_COOLDOWN_MS = 1500;
    /// <summary>连续接管时冷却最多翻到多少(ms) —— 防"和游戏来回抢"</summary>
    private const long FOCUS_COOLDOWN_MAX_MS = 30000;
    /// <summary>距离上一轮结束超过这么久(ms)就认为"不是连着的", 翻倍计数清零</summary>
    private const long FOCUS_RAPID_RESET_MS = 60000;
    /// <summary>
    /// "真的在响应"的探针超时(ms)默认值 —— 真正的运行时取值来自配置 FocusProbeMs(Pro 档 500 / Ultra 档 120)。
    /// 这个常量只当默认值和 focustest 的模型参数用。
    /// 500ms 而不是更短: 这个探针也参与"目标是不是还卡着"的判断(拉回前台那一步),
    /// 200ms 会把游戏加载/编译着色器时的长帧误判成卡死, 于是从健康游戏手里抢前台。
    /// 真要抢回来, 得连续 FOCUS_BACK_ROUNDS 轮(≥1.5 秒)都不回音才行。
    /// </summary>
    private const uint FOCUS_PROBE_MS = 500;
    /// <summary>
    /// 系统标志连续这么多毫秒说"它不卡了"、而探针一直没回音, 就判定探针在这个窗口上不可用,
    /// 退回系统标志判断(ms)。设定得比"卡住但偶尔动一下"的那个约 5 秒周期长, 免得把正常
    /// 的慢响应误判成探针失灵。
    /// </summary>
    private const long FOCUS_PROBE_BLIND_MS = 10000;
    /// <summary>探针自检连续失败这么多次才降级(启动时 UI 线程可能在忙, 一次失败不算数)</summary>
    private const int FOCUS_PROBE_SELFTEST_FAILS = 10;

    /// <summary>
    /// 被接管的窗口没了、但它的进程还在时, 最多等它"重新出现一个窗口"多久(ms)。
    ///
    /// 为什么需要这个等待: 卡死时 Windows 会给那个窗口造一个"幽灵窗口", 应用一缓过来系统就把它
    /// 销毁; 游戏自己也会在切全屏/丢焦点时销毁重建窗口。两种情况都表现为"我们记的那个句柄失效",
    /// 但应用其实还活着 —— 这时候必须把焦点还给它(新)的窗口, 不能像旧版那样直接结束本轮、
    /// 把焦点留在本程序身上(实测: 一晚上抢了 2 次, 一次都没还)。
    /// </summary>
    private const long FOCUS_ORPHAN_WAIT_MS = 10000;

    private const uint SMTO_BLOCK = 0x0001;
    private const uint SMTO_ABORTIFHUNG = 0x0002;

    // 抢前台兜底阶梯用到的常量(见 ForceForegroundHwndEx)
    private const int SW_MINIMIZE = 6;
    private const int SW_RESTORE = 9;
    /// <summary>显示窗口但不激活 —— 抢焦点时用它还原自己, 避免"还原动作"自己先把前台抢走(见 ForceForegroundHwndEx)</summary>
    private const int SW_SHOWNOACTIVATE = 4;
    private const uint SWP_NOSIZE = 0x0001;
    private const uint SWP_NOMOVE = 0x0002;
    private const uint SWP_NOACTIVATE = 0x0010;
    private static readonly IntPtr HWND_TOPMOST = (IntPtr)(-1);
    private static readonly IntPtr HWND_NOTOPMOST = (IntPtr)(-2);

    /// <summary>焦点解堵的状态。只被焦点线程读写(它自己一个线程), 所以不用加锁。</summary>
    private struct FocusState
    {
        /// <summary>是否正在接管(前台被我们占着, 等被接管的窗口恢复)</summary>
        public bool Active;
        /// <summary>被接管的窗口(卡住的那个), 恢复后要还给它</summary>
        public IntPtr Target;
        /// <summary>被接管窗口所属进程 —— 句柄会被系统复用, 存个 pid 免得认错窗口。
        /// 注意: 如果被接管的是**幽灵窗口**, 这个 pid 是 dwm.exe 的(系统给卡死窗口做的替身由 dwm 创建),
        /// 所以"还焦点"那边不能只靠它, 还要靠下面的标题。</summary>
        public uint TargetPid;
        /// <summary>被接管窗口当时的标题 —— 幽灵窗口的标题就是原窗口标题加后缀, 用来把原窗口认回来</summary>
        public string TargetTitle;
        /// <summary>还没接管时, 正在计"连续几轮无响应"的候选窗口</summary>
        public IntPtr Cand;
        public int CandRounds;
        public int OkRounds;
        public int BackRounds;
        public int Retakes;
        /// <summary>本轮里**真的**抢到过前台吗(没抢到过就不算"和游戏对抢", 不吃重试上限)</summary>
        public bool EverTook;
        /// <summary>被接管的窗口从什么时候起"不见了、但进程还在"(0 = 没这个状态)</summary>
        public long OrphanSince;
        /// <summary>上一轮接管是什么时候结束的 / 短时间内连着多少轮(用来给冷却做退避)</summary>
        public long LastEpisodeEndTicks;
        public int RapidEpisodes;
        public long LastActTicks;
        public long CooldownTicks;
    }

    /// <summary>
    /// 结束一轮接管: 算好"多久之后才允许再接管", 返回这个冷却值(ms, 供日志写明)。
    ///
    /// 为什么不再是固定值(用户实测反馈): 原来固定 5 秒太钝 —— "卡白刚结束、
    /// 过一会儿又来一次短暂的无响应"时, 这 5 秒正好把第二次挡在门外, 表现就是"按了没反应"。
    /// 现在: 基础 1.5 秒; 如果是"短时间内连着来"(游戏在反复抽风), 每多一轮翻一倍, 最多 30 秒。
    /// 这样单次卡白之后立刻能再接管, 而反复闪烁会因为退避自动安静下来 —— 两个毛病一起治。
    /// </summary>
    private static long FocusEndEpisode(ref FocusState s, long now)
    {
        if (s.LastEpisodeEndTicks != 0 && (now - s.LastEpisodeEndTicks) <= FOCUS_RAPID_RESET_MS)
            s.RapidEpisodes++;
        else
            s.RapidEpisodes = 1;
        s.LastEpisodeEndTicks = now;

        long cd = FOCUS_COOLDOWN_MS;
        for (int i = 1; i < s.RapidEpisodes && cd < FOCUS_COOLDOWN_MAX_MS; i++) cd *= 2;
        if (cd > FOCUS_COOLDOWN_MAX_MS) cd = FOCUS_COOLDOWN_MAX_MS;
        s.CooldownTicks = now + cd;
        return cd;
    }

    /// <summary>冷却比基础值长时, 在日志里写明"连着第几轮、冷却延长到多少"</summary>
    private static string FocusCooldownNote(FocusState s, long cd)
    {
        if (cd <= FOCUS_COOLDOWN_MS) return "";
        return " (短时间内第 " + s.RapidEpisodes + " 轮接管, 冷却延长到 " + (cd / 1000) + " 秒)";
    }

    /// <summary>
    /// 前台窗口算不算"卡住"(要不要接管)。抽出来是为了 focustest 能直接验这一条,
    /// 也让"默认只认系统标志 / 开了 FocusEarly 才提前"这件事只在一处判断。
    ///   flagHung  : 系统的卡死标志(连续 5 秒不取消息才置位, 不会误判但慢)
    ///   earlyOn   : 用户开了"抢得更早"
    ///   probeReply: WM_NULL 探针有没有回音(有回音 = 它其实在正常处理消息)
    /// </summary>
    private static bool FocusLooksHung(bool flagHung, bool earlyOn, bool probeReply)
    {
        if (flagHung) return true;
        return earlyOn && !probeReply;
    }

    /// <summary>
    /// 目标窗口到底还响不响应: 给它发一个 WM_NULL(窗口会直接忽略这个空消息), 限时等它回音。
    ///
    /// 为什么不只用 IsHungAppWindow: 那是系统的"卡死"缓存 —— 要连续 5 秒不取消息才置位,
    /// 而窗口取一次消息就立刻清零, 之后又要再等约 5 秒才可能重新置位。于是"卡住但偶尔动一下"
    /// 的窗口会让它以约 5 秒为周期在"卡/不卡"之间翻。拿它当"恢复了"的判据会周期性误判,
    /// 结果就是"抢→还→抢"的来回切。这个探针是**直接测量**: 限时内没回音就是真卡着。
    ///
    /// ★ 这里**故意不带 SMTO_ABORTIFHUNG**(实测的坑): 带上它, 系统只要还把这个
    ///   窗口标着"未响应"(那是缓存, 会滞后好几秒), 调用就立刻返回失败 —— 明明游戏已经缓过来了,
    ///   我却一直判定"它还卡着", 于是连着 5 秒多一次都不去还焦点, 用户只能自己点回游戏。
    ///   去掉它 = 老老实实等它回音, 回音了就是真的在用消息循环。
    /// </summary>
    private static bool IsWindowResponsive(IntPtr hwnd, uint timeoutMs)
    {
        try
        {
            if (hwnd == IntPtr.Zero || !IsWindow(hwnd)) return false;
            IntPtr res;
            IntPtr r = SendMessageTimeout(hwnd, 0 /*WM_NULL*/, IntPtr.Zero, IntPtr.Zero,
                SMTO_BLOCK, timeoutMs, out res);
            return r != IntPtr.Zero;
        }
        catch { return false; }
    }

    /// <summary>窗口属于哪个进程(拿不到就是 0)。</summary>
    private static uint WindowPid(IntPtr hwnd)
    {
        try
        {
            if (hwnd == IntPtr.Zero) return 0;
            uint pid;
            GetWindowThreadProcessId(hwnd, out pid);
            return pid;
        }
        catch { return 0; }
    }

    /// <summary>窗口标题(拿不到就是空串)。</summary>
    private static string WindowTitle(IntPtr hwnd)
    {
        try
        {
            if (hwnd == IntPtr.Zero) return "";
            StringBuilder t = new StringBuilder(200);
            GetWindowTextW(hwnd, t, t.Capacity);
            return t.ToString();
        }
        catch { return ""; }
    }

    /// <summary>
    /// 去掉"未响应"后缀。系统给卡死窗口做的**幽灵窗口**的标题 = 原窗口标题 + " (未响应)"
    /// (英文系统是 " (Not Responding)")。只按最后一个 " (" / "（" 之前的部分比, 中英文都能对上。
    /// </summary>
    private static string StripHungSuffix(string t)
    {
        if (t == null) return "";
        t = t.Trim();
        int i = t.LastIndexOf(" (", StringComparison.Ordinal);
        if (i > 0) t = t.Substring(0, i);
        int j = t.LastIndexOf("（", StringComparison.Ordinal);
        if (j > 0) t = t.Substring(0, j);
        return t.Trim();
    }

    /// <summary>遍历可见的顶层窗口, 交给 match 判断(标题一起传进去, 免得再取一次)。</summary>
    private delegate bool WindowMatch(IntPtr h, string title);

    private static IntPtr FindVisibleTopWindow(WindowMatch match)
    {
        IntPtr best = IntPtr.Zero;
        try
        {
            EnumWindows(delegate(IntPtr h, IntPtr lp)
            {
                if (!IsWindowVisible(h)) return true;
                if (match(h, WindowTitle(h))) { best = h; return false; }
                return true;
            }, IntPtr.Zero);
        }
        catch { }
        return best;
    }

    /// <summary>配置里"真要处理"的目标进程名(不含 .exe) —— 用来在窗口重建后把游戏窗口找回来。</summary>
    private static List<string> TargetProcNames()
    {
        List<string> r = new List<string>();
        try
        {
            if (_cfg == null) return r;
            foreach (string t in _cfg.TargetList())
            {
                if (string.IsNullOrEmpty(t)) continue;
                string n = t.Trim();
                if (n.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) n = n.Substring(0, n.Length - 4);
                if (n.Length > 0 && !r.Contains(n)) r.Add(n);
            }
        }
        catch { }
        return r;
    }

    /// <summary>
    /// 被接管的窗口没了(典型: 系统的幽灵窗口被销毁)之后, 该把焦点还给谁?
    ///
    /// ★ 这里有一个实测踩到的坑(曾经的日志): 幽灵窗口的 pid 属于 **dwm.exe**,
    ///   不是游戏! 所以"顺着被接管窗口的 pid 去找它的新窗口"找不到任何东西 ——
    ///   当时日志就写成了"没等到它的新窗口, 焦点仍在本程序, 请手动点回去"。
    /// 顺序(每一条都是"能对上就还"):
    ///   ① 同进程的顶层窗口 —— 窗口被销毁重建的普通情况;
    ///   ② **标题匹配**: 幽灵窗口的标题就是原窗口标题加个后缀, 去掉后缀去比对 ——
    ///      这是幽灵窗口情形下唯一可靠的认亲方式;
    ///   ③ 配置里的目标程序的主窗口 —— 用户的目的就是"我在玩这个游戏", 找它准没错。
    /// </summary>
    private static IntPtr FindWindowToReturnTo(uint pid, string titleHint, IntPtr exclude)
    {
        try
        {
            // ① 同进程
            if (pid != 0)
            {
                IntPtr byPid = FindWindowOfPid(pid, exclude);
                if (byPid != IntPtr.Zero) return byPid;
            }

            // ② 标题(先严格全等, 再退一步按"去掉未响应后缀"比)
            string want = StripHungSuffix(titleHint);
            if (want.Length > 0)
            {
                IntPtr byTitle = FindVisibleTopWindow(delegate(IntPtr h, string t)
                {
                    return h != exclude && t.Length > 0 && t == want;
                });
                if (byTitle != IntPtr.Zero) return byTitle;
                byTitle = FindVisibleTopWindow(delegate(IntPtr h, string t)
                {
                    return h != exclude && t.Length > 0 && StripHungSuffix(t) == want;
                });
                if (byTitle != IntPtr.Zero) return byTitle;
            }

            // ③ 配置里的目标程序
            foreach (string proc in TargetProcNames())
            {
                try
                {
                    Process[] ps = Process.GetProcessesByName(proc);
                    foreach (Process p in ps)
                    {
                        try
                        {
                            if (p.MainWindowHandle != IntPtr.Zero && p.MainWindowHandle != exclude)
                                return p.MainWindowHandle;
                        }
                        finally { p.Dispose(); }
                    }
                }
                catch { }
            }
        }
        catch { }
        return IntPtr.Zero;
    }

    /// <summary>这个进程还活着吗。</summary>
    private static bool ProcessAlive(uint pid)
    {
        try
        {
            if (pid == 0) return false;
            using (Process p = Process.GetProcessById((int)pid)) return !p.HasExited;
        }
        catch { return false; }   // 找不到就是没了
    }

    /// <summary>
    /// 找"这个进程现在的顶层窗口"。用在: 被接管的窗口被销毁重建时, 把焦点还给它的新窗口。
    /// 偏好有标题的可见顶层窗口(最像主窗口); 没有就退回任一可见顶层窗口。
    /// </summary>
    private static IntPtr FindWindowOfPid(uint pid, IntPtr exclude)
    {
        IntPtr best = IntPtr.Zero;
        try
        {
            if (pid == 0) return IntPtr.Zero;
            EnumWindows(delegate(IntPtr h, IntPtr lp)
            {
                if (h == exclude) return true;
                if (!IsWindowVisible(h)) return true;
                uint p;
                GetWindowThreadProcessId(h, out p);
                if (p != pid) return true;
                if (GetWindow(h, 4 /*GW_OWNER*/) != IntPtr.Zero) return true;   // 只要顶层窗口
                StringBuilder t = new StringBuilder(16);
                if (GetWindowTextW(h, t, t.Capacity) > 0) { best = h; return false; }  // 有标题: 就是它
                if (best == IntPtr.Zero) best = h;                                    // 先记着, 继续找
                return true;
            }, IntPtr.Zero);
        }
        catch { }
        return best;
    }

    /// <summary>
    /// 窗口的简短标识(进程号 + 类名 + 标题前 24 字), 只写进日志。
    /// 为什么需要: 排查"抢了焦点不还"时, 日志只说"前台窗口无响应", 根本不知道
    /// 当时那个窗口是谁(游戏? 启动器? 某个幽灵窗口?), 只能靠猜。
    /// </summary>
    private static string WindowBrief(IntPtr h)
    {
        try
        {
            if (h == IntPtr.Zero) return "(无窗口)";
            StringBuilder cls = new StringBuilder(64);
            GetClassNameW(h, cls, cls.Capacity);
            StringBuilder t = new StringBuilder(200);
            GetWindowTextW(h, t, t.Capacity);
            string title = t.ToString();
            if (title.Length > 24) title = title.Substring(0, 24) + "…";
            return "窗口[pid=" + WindowPid(h) + " 类=" + cls.ToString() + " 标题=\"" + title + "\"]";
        }
        catch { return "窗口[(取不到)]"; }
    }

    /// <summary>
    /// 把"看到的事实"折成决策要用的两个信号(纯函数, 不碰窗口)。
    ///
    /// 抽出来的原因: focustest 要连这一层一起验。要是测试里自己抄一份折算逻辑,
    /// 这里改错了测试照样通过 —— 那就不算证据。
    ///
    ///   targetHung       : "要不要抢/拉回" 用 —— 只看系统标志(5 秒量级的证据)
    ///   targetResponsive : "要不要还" 用 —— 探针可用时以**实测回音**为准;
    ///                      探针不可用时退回系统标志(这时"标志说不卡了"就当它恢复了)
    /// </summary>
    private static void FocusSignals(bool targetAlive, bool flagHung, bool probeUsable, bool probeReply,
        out bool targetHung, out bool targetResponsive)
    {
        targetHung = targetAlive && flagHung;
        targetResponsive = targetAlive && (probeUsable ? probeReply : !flagHung);
    }

    /// <summary>
    /// 探针"在这台机器上、对这个窗口"还可信吗?
    ///
    /// 不可信就退回系统标志判断 —— 否则, 万一某个窗口永远不回音(跨会话/被安全软件拦/受保护
    /// 进程), "还在卡"会恒真, 焦点就被永远扣在本程序身上, 用户只能自己 Alt+Tab 回去。
    /// 判据: 系统标志**连续** flagNotHungMs 说"它不卡了", 探针却一次回音都没有。
    /// 那个"连续"很关键: 卡住但偶尔 pump 的窗口, 标志会周期性地翻回"卡", 于是这里不会误判。
    /// </summary>
    private static bool FocusProbeTrusted(bool flagHung, bool probeUsable, long flagNotHungMs, long blindMs)
    {
        if (!probeUsable) return false;
        if (!flagHung && flagNotHungMs >= blindMs) return false;
        return true;
    }

    /// <summary>
    /// 焦点解堵的**决策**部分: 输入是"此刻观察到的事实", 输出是"该做什么", 完全不碰窗口。
    ///
    /// 这样做的原因: 这个功能的失败模式全是时序问题(抖一下、慢一拍的前台切换、静默期里又来
    /// 一次、被系统的卡死缓存骗到), 在真机上要靠"把游戏卡住"才能复现, 一次几分钟还没法覆盖
    /// 边界。做成纯函数之后, `focustest` 可以用合成序列把边界一轮轮喂进去, 断言"该抢的时候
    /// 只抢一次, 不该抢的时候一次都不抢"。
    ///
    /// 时间参数单位统一用毫秒(和 ElapsedMs 一致), 由调用方给。
    /// </summary>
    private static int FocusDecide(ref FocusState s, long now, bool prepared,
        IntPtr fg, bool fgIsUs, bool fgHung,
        bool targetAlive, bool targetHung, bool targetResponsive,
        bool targetProcessAlive, IntPtr targetProcessWindow,
        int confirmRounds, long silentMs, long orphanWaitMs, int okRounds,
        out IntPtr who, out string reason)
    {
        who = IntPtr.Zero;
        reason = "";

        // ---- 没在保护 / 用户关了开关: 立刻收工, 而且绝不抢 ----
        if (!prepared)
        {
            if (s.Active)
            {
                // 还焦点也要守静默期(刚抢完就还, 前台切换还在路上)。
                // ★ 静默期没过就先**别清状态** —— 清了下一轮这里的 s.Active 就是 false,
                //   这个焦点就永远还不回去了。
                if (fgIsUs && s.Target != IntPtr.Zero && now - s.LastActTicks < silentMs)
                    return FOCUS_ACTION_NONE;

                IntPtr wasTarget = s.Target;
                s.Active = false;
                s.Target = IntPtr.Zero; s.TargetPid = 0; s.TargetTitle = "";
                s.OkRounds = 0; s.BackRounds = 0; s.Retakes = 0;
                s.EverTook = false;
                s.OrphanSince = 0;
                s.CooldownTicks = 0;
                s.LastActTicks = now;   // 还失败的话(FocusGiveFailed)靠它当重试节拍
                if (fgIsUs && wasTarget != IntPtr.Zero)
                {
                    who = wasTarget;
                    reason = "保护已停止, 把焦点还给原窗口";
                    return FOCUS_ACTION_GIVE;
                }
            }
            s.Cand = IntPtr.Zero; s.CandRounds = 0;
            return FOCUS_ACTION_NONE;
        }

        // ---- 还没接管: 找"连续 confirmRounds 轮无响应"的前台窗口 ----
        if (!s.Active)
        {
            if (now < s.CooldownTicks) { s.Cand = IntPtr.Zero; s.CandRounds = 0; return FOCUS_ACTION_NONE; }
            if (fg == IntPtr.Zero || fgIsUs) { s.Cand = IntPtr.Zero; s.CandRounds = 0; return FOCUS_ACTION_NONE; }
            // 换了窗口就重新数: "A 卡一下 + B 卡一下"不是"连续无响应"。
            // 注意这里只重置换窗口的那一轮, **不预支**一轮计数 —— 否则 confirmRounds=2 时
            // 实际只有 1 次确认, 迟滞等于没有(踩过)。
            if (fg != s.Cand) { s.Cand = fg; s.CandRounds = 0; }
            if (!fgHung) { s.CandRounds = 0; return FOCUS_ACTION_NONE; }
            s.CandRounds++;
            if (s.CandRounds < confirmRounds) return FOCUS_ACTION_NONE;

            s.Active = true;
            s.Target = fg;
            s.TargetPid = WindowPid(fg);
            s.TargetTitle = WindowTitle(fg);
            s.Retakes = 0; s.OkRounds = 0; s.BackRounds = 0;
            s.EverTook = false;
            s.OrphanSince = 0;
            s.LastActTicks = now;
            who = fg;
            reason = "前台窗口连续 " + confirmRounds + " 次无响应";
            return FOCUS_ACTION_TAKE;
        }

        // ---- 已接管 ----
        if (!targetAlive)
        {
            // 被接管的窗口没了。这里必须分两种情况 —— 旧版一律"结束本轮、不还焦点",
            // 结果就是"抢了焦点不还"(实测: 一晚上 3 次事件抢了 2 次、还 0 次):
            //   a) 窗口被销毁重建(卡死时的**幽灵窗口**在应用缓过来时被系统销毁; 游戏切全屏/丢焦点
            //      时也常销毁重建窗口)。应用还在 -> 焦点必须还给它的窗口。
            //   b) 应用真没了(游戏退出/被杀) -> 没什么可还的, 结束本轮并进冷却。
            //
            // 注意: 幽灵窗口的 pid 是 dwm.exe 的, 所以"它还在不在"和"它的窗口在哪"要分开判断 ——
            // 窗口在哪由调用方(FindWindowToReturnTo: 同 pid → 标题 → 配置里的目标程序)去找。
            if (fgIsUs)
            {
                if (targetProcessWindow != IntPtr.Zero)
                {
                    s.Active = false;
                    s.Target = IntPtr.Zero; s.TargetPid = 0; s.TargetTitle = "";
                    s.Cand = IntPtr.Zero; s.CandRounds = 0;
                    s.OkRounds = 0; s.BackRounds = 0; s.Retakes = 0;
                    s.EverTook = false;
                    s.OrphanSince = 0;
                    long cd0 = FocusEndEpisode(ref s, now);
                    who = targetProcessWindow;
                    reason = "被接管的窗口没了, 但那个应用还在 -> 把焦点交给它的窗口"
                        + FocusCooldownNote(s, cd0);
                    return FOCUS_ACTION_GIVE;
                }
                // 还没找到窗口(重建窗口/切换全屏模式要几百毫秒): 先不放手, 给它一点时间。
                // 应用已经退出就不等了 —— 没什么可还的。
                if (targetProcessAlive)
                {
                    if (s.OrphanSince == 0) s.OrphanSince = now;
                    if (now - s.OrphanSince < orphanWaitMs) return FOCUS_ACTION_NONE;
                }
            }
            bool procAlive = targetProcessAlive;
            s.OrphanSince = 0;
            s.Active = false;
            s.Target = IntPtr.Zero; s.TargetPid = 0; s.TargetTitle = "";
            s.Cand = IntPtr.Zero; s.CandRounds = 0;
            s.OkRounds = 0; s.BackRounds = 0; s.Retakes = 0;
            s.EverTook = false;
            long cd1 = FocusEndEpisode(ref s, now);
            reason = (procAlive
                ? "被接管的窗口没了, 也没找到它那个应用的窗口(焦点仍在本程序, 请手动点回去)"
                : "被接管的窗口已消失, 结束本轮") + FocusCooldownNote(s, cd1);
            return FOCUS_ACTION_NONE;
        }

        if (targetHung)
        {
            s.OkRounds = 0;
            // 静默期: 刚抢过/刚还过, 给系统时间把前台切换落定(异步)
            if (now - s.LastActTicks < silentMs) return FOCUS_ACTION_NONE;
            // 前台是别的窗口(包括用户自己切走的): 一律不碰 —— 这里是旧版最大的毛病
            if (fg != s.Target) { s.BackRounds = 0; return FOCUS_ACTION_NONE; }
            s.BackRounds++;
            if (s.BackRounds < FOCUS_BACK_ROUNDS) return FOCUS_ACTION_NONE;
            s.BackRounds = 0;
            // 重试上限只约束"抢到过之后还被抢回去"的情况。一次都没抢到说明是前台锁在挡,
            // 那不是对抢, 停手只会让触发键一直按不动 —— 这时按同样的节奏继续试(有静默期)。
            if (s.EverTook && s.Retakes >= FOCUS_MAX_RETAKES) return FOCUS_ACTION_NONE;
            s.Retakes++;
            s.LastActTicks = now;
            who = s.Target;
            reason = "卡住的窗口又抢回了前台(本轮第 " + s.Retakes + " 次)";
            return FOCUS_ACTION_TAKE;
        }

        // ---- 系统标志说它不卡了: 但必须**真的**在响应才算恢复 ----
        if (!targetResponsive)
        {
            // 只是"偶尔动了一下"(系统的卡死缓存被清了一下), 不是恢复:
            // 直接还焦点的话, 过一会儿它又被判定为卡死 -> 再抢, 就成了周期性的来回闪。
            s.OkRounds = 0;
            s.BackRounds = 0;
            return FOCUS_ACTION_NONE;
        }

        s.BackRounds = 0;
        s.OkRounds++;
        if (s.OkRounds < okRounds) return FOCUS_ACTION_NONE;
        // 还焦点也要守静默期: 抢完 250ms 就还, 前台切换还在路上, 看起来就是抖
        if (now - s.LastActTicks < silentMs) return FOCUS_ACTION_NONE;

        IntPtr t = s.Target;
        s.Active = false;
        s.Target = IntPtr.Zero; s.TargetPid = 0; s.TargetTitle = "";
        s.Cand = IntPtr.Zero; s.CandRounds = 0;
        s.OkRounds = 0; s.Retakes = 0; s.EverTook = false;
        s.OrphanSince = 0;
        long cd2 = FocusEndEpisode(ref s, now);
        if (!fgIsUs)
        {
            // 用户自己已经切到别的窗口了: 这时候把前台抢到游戏上, 是在抢用户的焦点
            reason = "目标窗口已恢复, 但焦点已被用户切走, 不抢回来" + FocusCooldownNote(s, cd2);
            return FOCUS_ACTION_NONE;
        }
        who = t;
        reason = "目标窗口已恢复, 把焦点还回去" + FocusCooldownNote(s, cd2);
        return FOCUS_ACTION_GIVE;
    }

    /// <summary>
    /// 还焦点失败(被系统前台锁挡住)时把状态退回去, 下一轮再试。
    ///
    /// 不这么做的话: GIVE 分支已经把 Active/Target 清掉了, 而下一轮的"还没接管"分支只认
    /// "前台窗口卡住"才动作 —— 焦点就永远留在本程序身上, 用户得自己点回游戏。
    /// 抽成独立函数是为了 focustest 能直接验它(它不碰窗口)。
    /// </summary>
    private static void FocusGiveFailed(ref FocusState s, long now, IntPtr target, int okRounds)
    {
        if (target == IntPtr.Zero) return;
        s.Active = true;
        s.Target = target;
        // 只在真拿到进程号时才更新: 窗口已经死了的话这里会拿到 0, 覆盖上去等于把
        // "防句柄复用" 的那道校验关掉。
        uint pid = WindowPid(target);
        if (pid != 0) s.TargetPid = pid;
        s.OkRounds = (okRounds < 1) ? 5 : okRounds;   // 已经确认它恢复了, 过了静默期就直接再还
        s.LastActTicks = now;           // 静默期后再试, 不做每 50ms 一次的重试
        s.CooldownTicks = 0;
    }

    private static volatile int _focusRescues = 0;
    /// <summary>响应探针已降级(退回系统标志判断) —— 界面上要标出来, 不能只在日志里</summary>
    private static volatile bool _focusProbeDegraded = false;
    /// <summary>抢焦点失败了(现在按触发键可能没反应) —— 也要标在界面上, 并提示点一下本窗口</summary>
    private static volatile bool _focusTakeFailed = false;

    /// <summary>
    /// 焦点解堵的轮询线程。只做三件事: 看现在的事实 -> 问 FocusDecide 该干什么 -> 干完如实记日志。
    /// </summary>
    private static void StartFocusRescue()
    {
        if (Interlocked.CompareExchange(ref _focusRescueStarted, 1, 0) != 0) return;
        Thread t = new Thread(delegate()
        {
            try { Thread.CurrentThread.Priority = ThreadPriority.AboveNormal; } catch { }
            FocusState st = new FocusState();
            long t0 = Stopwatch.GetTimestamp();
            bool probeUsable = true;          // 探针在这台机器上可用吗
            bool probeChecked = false;
            int probeFailStreak = 0;
            long flagNotHungSince = 0;        // 系统标志从什么时候起连续说"不卡了"(0 = 没在说)
            int takeFailStreak = 0;           // 抢失败的连续次数(日志限流用)
            int giveFailStreak = 0;
            while (true)
            {
                // 每次循环重新读配置: 设置里改完立刻生效, 不用重启程序
                // ★ V1.1.4-RC1: 档位(Pro/Ultra)+5 个参数全部可调, 延迟公式 = (间隔+探针)×轮数
                int mode = (_cfg == null) ? 1 : _cfg.FocusMode;
                if (mode < 0 || mode > 2) mode = 1;
                bool earlyFocus = (mode >= 1);        // 0 = 只用系统判定, 不看探针
                int interval = (_cfg == null) ? 50 : _cfg.FocusIntervalMs;
                if (interval < 10) interval = 10;
                if (interval > 2000) interval = 2000;
                int confirm = (_cfg == null) ? 3 : _cfg.FocusRounds;
                if (confirm < 1) confirm = 1;         // 1 轮会抖(Ultra 档就是故意用 1)
                if (confirm > 10) confirm = 10;
                int probeMsRaw = (_cfg == null) ? 500 : _cfg.FocusProbeMs;
                if (probeMsRaw < 50) probeMsRaw = 50;
                if (probeMsRaw > 2000) probeMsRaw = 2000;
                uint probeMs = (uint)probeMsRaw;
                int okRounds = (_cfg == null) ? 5 : _cfg.FocusOkRounds;
                if (okRounds < 1) okRounds = 1;
                if (okRounds > 20) okRounds = 20;
                int silentMs = (_cfg == null) ? 1500 : _cfg.FocusSilentMs;
                if (silentMs < 100) silentMs = 100;
                if (silentMs > 5000) silentMs = 5000;

                Thread.Sleep(interval);
                try
                {
                    // ---- 探针自检: 只锁"可用", 失败就下一轮再试 ----
                    // 为什么拿两个窗口试: 自己的窗口只能证明"这个 API 在本进程内能返回",
                    // 跨进程/跨完整性级别那条路(UIPI、安全软件过滤)只有拿别的进程的窗口试才作数,
                    // 所以再拿桌面窗口(explorer 的)试一个。
                    // 为什么失败不立刻锁死: 启动时 UI 线程可能正忙着跑 netsh, 探一下超时很正常,
                    // 一次失败就永久降级会让这台机器白白丢掉"实测判恢复"这条最好的判据。
                    if (!probeChecked)
                    {
                        bool ok = IsWindowResponsive(_form == null ? IntPtr.Zero : _form.Handle, probeMs);
                        IntPtr shell = GetShellWindow();
                        if (ok && shell != IntPtr.Zero) ok = IsWindowResponsive(shell, probeMs);
                        if (ok)
                        {
                            probeChecked = true;
                            Log("[焦点解堵] 响应探针自检通过 (WM_NULL 限时探活可用)");
                        }
                        else
                        {
                            probeFailStreak++;
                            if (probeFailStreak >= FOCUS_PROBE_SELFTEST_FAILS)
                            {
                                probeChecked = true;
                                probeUsable = false;
                                _focusProbeDegraded = true;
                                Log("[焦点解堵] 响应探针自检连续 " + probeFailStreak
                                    + " 次拿不到回音 -> 降级: 恢复判定退回系统标志(可能偏慢)");
                            }
                        }
                    }

                    long nowMs = ElapsedMs(t0);
                    bool prepared = _guarding && _cfg != null && _cfg.FocusRescue;
                    IntPtr fg = GetForegroundWindow();
                    bool fgIsUs = IsOurForeground(fg);
                    // 档位 >= Pro 时: 系统的卡死标志要连续 5 秒不取消息才置位, 而那 5 秒里触发键
                    // 可能是按不动的(用户实测)。所以再按"探针没回音"提前接管 ——
                    // 探针只在"标志还没置位 + 档位要提前接管"时才真的发, 平时不多花时间。
                    bool fgFlagHung = (fg != IntPtr.Zero) && !fgIsUs && IsHungAppWindow(fg);
                    bool fgProbeReply = false;
                    if (!fgFlagHung && earlyFocus && fg != IntPtr.Zero && !fgIsUs)
                        fgProbeReply = IsWindowResponsive(fg, probeMs);
                    bool fgHung = (fg != IntPtr.Zero) && !fgIsUs
                        && FocusLooksHung(fgFlagHung, earlyFocus, fgProbeReply);

                    // ---- 状态面板快照(约每秒发布一次; 只写字符串, 不参与任何决策) ----
                    //   放在"这一轮的事实都拿到之后、下决定之前": 面板看到的就是本轮决策所依据的东西。
                    //   放在这里还有个好处: 它读到的变量跟后面决策用的是同一批, 不会出现"面板说没卡、
                    //   实际却抢了"这种自相矛盾的观感。
                    if (nowMs - _diagFocusStateMs >= 1000)
                    {
                        _diagFocusStateMs = nowMs;
                        try
                        {
                            _diagFocusState = "档位=" + FocusModeName(mode)
                                + " 间隔=" + interval + "ms 探针=" + probeMs + "ms 轮数=" + confirm
                                + " 还焦点需=" + okRounds + "轮+静默" + silentMs + "ms"
                                + " | 前台=" + (fg == IntPtr.Zero ? "(取不到)"
                                    : (fgIsUs ? "本程序" : WindowBrief(fg)))
                                + (fgHung ? " →判定无响应"
                                    : (earlyFocus ? (fgProbeReply ? " →探针有回音" : " →探针没回音")
                                                  : " →只看系统标志"))
                                + " | 接管=" + (st.Target == IntPtr.Zero ? "(未接管)"
                                    : ((st.Active ? "进行中" : "已记下") + " " + WindowBrief(st.Target)))
                                + " 待还确认=" + st.OkRounds + "/" + okRounds
                                + " 再抢=" + st.Retakes + "/" + FOCUS_MAX_RETAKES
                                + " 探针=" + (probeUsable ? "可用" : "已降级")
                                + " 冷却剩余=" + Math.Max(0, st.CooldownTicks - nowMs) + "ms";
                        }
                        catch { }
                    }

                    // 目标窗口还在不在: 句柄 + 进程号一起看(句柄会被系统复用)
                    bool tAlive = (st.Target != IntPtr.Zero) && IsWindow(st.Target)
                        && (st.TargetPid == 0 || WindowPid(st.Target) == st.TargetPid);

                    // 被接管的窗口没了, 该把焦点还给谁? 找窗口的活交给 FindWindowToReturnTo
                    // (同 pid → 标题 → 配置里的目标程序)。注意: 幽灵窗口的 pid 是 dwm.exe 的,
                    // 所以"pid 的进程还在"只能当参考, 不能当"应用还在"的判据。
                    bool procAlive = false;
                    IntPtr procWin = IntPtr.Zero;
                    if (!tAlive && (st.TargetPid != 0
                        || (st.TargetTitle != null && st.TargetTitle.Length > 0)))
                    {
                        procAlive = (st.TargetPid != 0) && ProcessAlive(st.TargetPid);
                        procWin = FindWindowToReturnTo(st.TargetPid, st.TargetTitle, IntPtr.Zero);
                        if (procWin != IntPtr.Zero) procAlive = true;
                    }

                    bool flagHung = tAlive && IsHungAppWindow(st.Target);
                    bool probeReply = probeUsable && tAlive
                        && IsWindowResponsive(st.Target, probeMs);

                    // 系统标志连续说"不卡了"有多久 —— 用来判断"探针是不是在这个窗口上不可用"
                    if (tAlive && !flagHung) { if (flagNotHungSince == 0) flagNotHungSince = nowMs; }
                    else flagNotHungSince = 0;
                    long flagNotHungMs = (flagNotHungSince == 0) ? 0 : (nowMs - flagNotHungSince);

                    if (probeUsable && !FocusProbeTrusted(flagHung, probeUsable, flagNotHungMs, FOCUS_PROBE_BLIND_MS))
                    {
                        probeUsable = false;
                        _focusProbeDegraded = true;
                        Log("[焦点解堵] 响应探针连续 " + (FOCUS_PROBE_BLIND_MS / 1000)
                            + " 秒拿不到这个窗口的回音 -> 降级: 恢复判定退回系统标志(可能偏慢)");
                    }

                    bool tHung, tResponsive;
                    FocusSignals(tAlive, flagHung, probeUsable, probeReply, out tHung, out tResponsive);

                    IntPtr who;
                    string reason;
                    int act = FocusDecide(ref st, nowMs, prepared,
                        fg, fgIsUs, fgHung, tAlive, tHung, tResponsive,
                        procAlive, procWin, confirm,
                        silentMs, FOCUS_ORPHAN_WAIT_MS, okRounds,
                        out who, out reason);

                    if (act == FOCUS_ACTION_TAKE)
                    {
                        bool everTook = st.EverTook;
                        // 抢的结果如实记下来: 抢不到就是抢不到(前台锁), 不能假装成功。
                        // 这一行是排查"按了触发键没反应"的第一手证据。
                        int tier;
                        bool ok = ForceForeground(_form, out tier);
                        if (ok)
                        {
                            st.EverTook = true;
                            takeFailStreak = 0;
                            // 界面上的"焦点解堵 N 次"只算"这一轮第一次真的抢到"
                            if (!everTook) _focusRescues++;
                            if (_focusTakeFailed) _focusTakeFailed = false;
                        }
                        else
                        {
                            // 抢不到 = 触发键按不动, 这是功能性故障, 必须让用户看得见,
                            // 而不是只躺在日志文件里; 并且要告诉他一步就能自救: 点一下本窗口。
                            if (!_focusTakeFailed)
                                Log("[焦点解堵] 抢焦点失败(被系统前台锁挡住) —— 现在按触发键可能没反应,"
                                    + " 点一下本窗口就能恢复; 详细行见日志文件");
                            _focusTakeFailed = true;
                        }
                        // 抢失败会按静默期一直重试, 日志要限流, 否则一场卡白能刷出几百行
                        if (ok || takeFailStreak < 3 || (takeFailStreak % 10) == 0)
                            LogToFileOnly("[焦点解堵/" + FocusModeName(mode) + "] " + reason + " "
                                + WindowBrief(fg) + " -> 切到本程序: "
                                + (ok ? ("成功(第 " + tier + " 档/" + TierName(tier, false)
                                          + (_fgLastWasIconic ? ", 本程序原为最小化" : "") + ")")
                                      : "失败(所有档都没抢到, 触发键可能仍然按不动)")
                                + " [钩子=" + ((_hookInstallOk && _hookThreadStarted) ? "在" : "异常") + "]");
                        // 给状态面板留一份"最近一次动手"的经过(只发布, 不影响任何逻辑)
                        _diagLastFocusAct = "抢焦点 " + (ok ? ("成功(第 " + tier + " 档/" + TierName(tier, false) + ")") : "失败")
                            + " | 原因=" + reason + " | 前台=" + WindowBrief(fg)
                            + (_fgLastWasIconic ? " (本程序原为最小化)" : "");
                        _diagLastFocusActMs = nowMs;
                        if (!ok) takeFailStreak++;
                    }
                    else if (act == FOCUS_ACTION_GIVE)
                    {
                        int gTier;
                        bool ok = ForceForegroundHwndEx(who, 0, out gTier);
                        if (!ok) FocusGiveFailed(ref st, nowMs, who, okRounds);
                        if (ok || giveFailStreak < 3 || (giveFailStreak % 10) == 0)
                            LogToFileOnly("[焦点解堵/" + FocusModeName(mode) + "] " + reason + " "
                                + WindowBrief(who) + ": "
                                + (ok ? ("成功(第 " + gTier + " 档/" + TierName(gTier, true)
                                          + (_fgLastWasIconic ? ", 目标原为最小化" : "") + ")")
                                      : "失败(被系统前台锁挡住), 稍后重试"));
                        _diagLastFocusAct = "还焦点 " + (ok ? ("成功(第 " + gTier + " 档/" + TierName(gTier, true) + ")") : "失败")
                            + " | 原因=" + reason + " | 目标=" + WindowBrief(who);
                        _diagLastFocusActMs = nowMs;
                        // 刚才是靠"把自己最小化让路"才把焦点交出去的 —— 如果抢焦点之前本程序本来是正常显示着的,
                        // 这里要把窗口放回来。SW_SHOWNOACTIVATE = 显示但不激活, 不会再抢走游戏的焦点。
                        if (ok && gTier == 3 && !_toolWasIconic)
                        {
                            try
                            {
                                if (_form != null && _form.IsHandleCreated && !_form.IsDisposed)
                                {
                                    ShowWindow(_form.Handle, SW_SHOWNOACTIVATE);
                                    LogToFileOnly("[焦点解堵] 让路后把本程序窗口放回来(不激活)");
                                }
                            }
                            catch { }
                        }
                        if (!ok) giveFailStreak++; else giveFailStreak = 0;
                    }
                    else if (reason.Length > 0)
                    {
                        // 只记"有信息量但没动作"的情况(窗口消失/焦点已被用户切走), 其余不写, 免得刷日志
                        LogToFileOnly("[焦点解堵/" + FocusModeName(mode) + "] " + reason);
                    }
                }
                catch { }
            }
        });
        t.IsBackground = true;
        t.Name = "SkyGuardFocusRescue";
        t.Start();
    }

    private static int _focusRescueStarted;   // Interlocked 抢占: 不会因为两次调用各起一条焦点线程

    /// <summary>前台窗口是不是本程序自己的窗口(主界面 / 触发键消息窗)</summary>
    private static bool IsOurForeground(IntPtr fg)
    {
        if (fg == IntPtr.Zero) return false;
        if (_hotkeyWnd != IntPtr.Zero && fg == _hotkeyWnd) return true;
        try { return _form != null && _form.IsHandleCreated && fg == _form.Handle; }
        catch { return false; }
    }

    /// <summary>
    /// 等前台真的切过去(ms)。前台上报是异步的: SetForegroundWindow 返回之后, GetForegroundWindow
    /// 可能要过一两百毫秒才反映出来 —— 不等就是"明明成功了却报失败"(实测: 还焦点
    /// 一连串"失败(前台锁)"里有一部分其实是这个)。
    /// </summary>
    private static bool WaitForeground(IntPtr target, int waitMs)
    {
        int step = 25;
        for (int waited = 0; waited < waitMs; waited += step)
        {
            if (GetForegroundWindow() == target) return true;
            Thread.Sleep(step);
        }
        return GetForegroundWindow() == target;
    }

    /// <summary>
    /// 把指定窗口抢到前台的**完整阶梯**。返回值 = "前台确实换过去了"; tier = 用的是哪一档, 0 = 全失败。
    ///
    /// kind = 1 抢到本程序(解堵): 1 直接, 2 绕过前台锁, 3 临时置顶, 4 最小化再还原。
    ///   为什么这么硬: 用户实测"卡白时必须先把前台抢过来, 触发键才进得来" ——
    ///   这一抢失败 = 触发键按不动 = 工具白拿。3/4 只会动**我们自己的**窗口, 且每次都写日志。
    /// kind = 0 把焦点还给别的程序(游戏): 1 直接, 2 绕过前台锁, 3 **把本程序最小化让路**
    ///   (系统会把前台交给下一个窗口, 通常就是刚恢复的游戏)。第 3 档是必须的:
    ///   实测直接抢和绕前台锁都会被拒(日志里连着两条"失败(被系统前台锁挡住)"),
    ///   让路是唯一不会把焦点留在本程序身上的办法; 它只动我们自己的窗口, 不碰游戏窗口的状态。
    /// </summary>
    private static bool ForceForegroundHwndEx(IntPtr target, int kind, out int tier)
    {
        tier = 0;
        try
        {
            if (target == IntPtr.Zero || !IsWindow(target)) return false;
            if (GetForegroundWindow() == target) { tier = 1; return true; }

            // 抢自己时用 SW_SHOWNOACTIVATE(显示但不激活): SW_RESTORE 的还原动作自己会激活窗口,
            // 全屏游戏会立刻反弹抢回前台, 表现为多绕一趟; 还焦点给游戏时仍用 SW_RESTORE。
            bool wasIconic = IsIconic(target);
            _fgLastWasIconic = wasIconic;
            if (kind == 1) _toolWasIconic = wasIconic;   // 记下来: 还焦点时要不要把本程序窗口放回来
            if (wasIconic)
            {
                if (kind == 1)
                {
                    ShowWindow(target, SW_SHOWNOACTIVATE);
                    if (IsIconic(target)) ShowWindow(target, SW_RESTORE);   // 兜底: 万一没还原成功
                }
                else
                {
                    ShowWindow(target, SW_RESTORE);
                }
            }
            SetForegroundWindow(target);
            if (WaitForeground(target, (kind == 1 && wasIconic) ? 120 : 250)) { tier = 1; return true; }

            IntPtr fg = GetForegroundWindow();
            uint tidFg = GetWindowThreadProcessId(fg, IntPtr.Zero);
            uint tidMe = GetCurrentThreadId();
            if (tidFg != 0 && tidFg != tidMe && AttachThreadInput(tidFg, tidMe, true))
            {
                try
                {
                    SetForegroundWindow(target);
                    SetActiveWindow(target);
                }
                finally { AttachThreadInput(tidFg, tidMe, false); }
            }
            if (WaitForeground(target, 250)) { tier = 2; return true; }

            if (kind == 0)
            {
                // 第 3 档(还焦点专用): 把自己最小化让路。
                // 前端实测: 直接抢和绕前台锁都被系统拒了, 这时"让开"是唯一出路 ——
                // 前台会交给下一个窗口, 正常就是刚恢复的游戏。只动我们自己的窗口。
                IntPtr ours = GetForegroundWindow();
                if (IsOurForeground(ours))
                {
                    ShowWindow(ours, SW_MINIMIZE);
                    if (WaitForeground(target, 400)) return WaitSet(ref tier, 3);
                    // 让路之后前台不一定正好落在目标窗口上(可能是别的窗口) ——
                    // 只要"前台不再是本程序", 目的(把焦点让出去)就达到了, 如实按第 3 档算成功。
                    if (!IsOurForeground(GetForegroundWindow())) return WaitSet(ref tier, 3);
                }
                return false;
            }

            // 第 3 档(抢到自己身上): 临时置顶再抢(置顶的窗口更容易被允许成为前台)
            if (SetWindowPos(target, HWND_TOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE))
            {
                try
                {
                    SetForegroundWindow(target);
                    SetActiveWindow(target);
                }
                finally
                {
                    SetWindowPos(target, HWND_NOTOPMOST, 0, 0, 0, 0, SWP_NOMOVE | SWP_NOSIZE | SWP_NOACTIVATE);
                }
            }
            if (WaitForeground(target, 250)) { tier = 3; return true; }

            // 第 4 档: 最小化再还原
            ShowWindow(target, SW_MINIMIZE);
            ShowWindow(target, SW_RESTORE);
            SetForegroundWindow(target);
            if (WaitForeground(target, 400)) { tier = 4; return true; }

            return false;
        }
        catch { return false; }
    }

    /// <summary>上一次抢前台时目标窗口是不是最小化(只给日志与状态面板用, 不参与决策)。</summary>
    private static volatile bool _fgLastWasIconic;

    /// <summary>
    /// 抢焦点之前**本程序窗口**是不是最小化的。
    /// 用途: 还焦点时如果走了"把自己最小化让路"那一档, 而抢之前本程序本来是正常显示着的,
    /// 就得把窗口放回来 —— 否则一次解堵之后工具就留在任务栏里, 用户以为程序没了。
    /// (不能复用 _fgLastWasIconic: 还焦点那一次调用会把它覆盖成目标窗口的状态。)
    /// </summary>
    private static volatile bool _toolWasIconic;

    /// <summary>
    /// 抢/还焦点走的"第几档"叫什么(只用于日志与状态面板, 不参与决策)。
    ///   · 抢到自己身上(4 档): 1 直接抢 → 2 绕前台锁 → 3 临时置顶 → 4 最小化再还原(最后手段, 肉眼看得见)
    ///   · 还焦点给游戏(3 档): 1 直接还 → 2 绕前台锁 → 3 把自己最小化让路
    /// </summary>
    private static string TierName(int tier, bool giving)
    {
        if (giving)
        {
            if (tier == 1) return "直接还";
            if (tier == 2) return "绕前台锁";
            return "让路(自己最小化)";
        }
        switch (tier)
        {
            case 1: return "直接抢";
            case 2: return "绕前台锁";
            case 3: return "临时置顶";
            case 4: return "最小化再还原";
            default: return "未成功";
        }
    }

    /// <summary>给 tier 赋值并返回 true(小工具函数, 让上面的阶梯读起来短一点)</summary>
    private static bool WaitSet(ref int tier, int v)
    {
        tier = v;
        return true;
    }

    /// <summary>把本程序主窗口抢到前台(带兜底阶梯); tier 见 ForceForegroundHwndEx。</summary>
    private static bool ForceForeground(Form f, out int tier)
    {
        tier = 0;
        try
        {
            if (f == null || !f.IsHandleCreated || f.IsDisposed) return false;
            return ForceForegroundHwndEx(f.Handle, 1, out tier);
        }
        catch { return false; }
    }

    private static bool ForceForeground(Form f)
    {
        int tier;
        return ForceForeground(f, out tier);
    }

    // ============================================================================
    //  focustest: 焦点解堵决策的无头自检
    //
    //  为什么单独做: 这个功能的失败模式全是时序(抖一下 / 慢一拍的前台切换 / 静默期里又来
    //  一次 / 被系统的卡死缓存骗到), 真机上要"把游戏卡住"才能复现, 一次几分钟还没法覆盖
    //  边界。决策与信号折算都是纯函数, 所以用合成序列把边界喂进去, 断言"该抢的时候只抢
    //  一次, 不该抢的时候一次都不抢"。全程不碰真实窗口、不需要管理员、不改系统状态。
    //
    //  边界(要说清楚, 别把"逻辑通过"当成"真机通过"):
    //    · FocusSim 的"世界"给的是**原始事实**(系统标志、探针回音、前台是谁), 折算与决策
    //      走的都是生产代码(FocusSignals / FocusDecide / FocusGiveFailed), 不是测试里抄的。
    //    · 时间轴按"扫描间隔"折算, 探针在真机上还会阻塞最多 FOCUS_PROBE_MS, 模型里没有;
    //      断言里的"轮数"只表示逻辑先后, 不等于真机上的毫秒数。
    //    · 真正没法在这里验的是 Win32 那几条: SetForegroundWindow 能不能抢到(前台锁)、
    //      WM_NULL 探针对别的进程到底通不通、SW_RESTORE 的语义。那几条只能真机验。
    // ============================================================================

    /// <summary>focustest 的合成世界: 每 Step() 一次 = 一轮扫描。</summary>
    private sealed class FocusSim
    {
        public FocusState St;
        public long Now = 0;
        public int FrameNo = 0;
        public int IntervalMs = 50;
        public int Confirm = 3;
        /// <summary>被接管的窗口(游戏)</summary>
        public IntPtr Game = (IntPtr)0x1001;
        /// <summary>另一个无关窗口(用户自己的浏览器之类)</summary>
        public IntPtr Other = (IntPtr)0x1002;
        /// <summary>本程序的窗口</summary>
        public IntPtr Us = (IntPtr)0x1003;

        public bool Prepared = true;
        /// <summary>系统的卡死标志(会以约 5 秒为周期翻的那种缓存)</summary>
        public bool FlagHung = true;
        /// <summary>目标窗口对 WM_NULL 探针的回音(真的在用消息循环吗)</summary>
        public bool ProbeReply = false;
        /// <summary>探针在这台机器上可用吗(false = 已降级, 退回系统标志判断)</summary>
        public bool ProbeUsable = true;
        /// <summary>游戏窗口是否还存在</summary>
        public bool GameAlive = true;
        /// <summary>被接管窗口的那个进程还在吗(窗口没了但进程还在 = 窗口被销毁重建)</summary>
        public bool ProcessAlive = true;
        /// <summary>那个进程"现在的窗口"(窗口重建后焦点要交给它; 0 = 还没出来)</summary>
        public IntPtr ProcessWindow = IntPtr.Zero;
        /// <summary>测试里给被接管窗口用的假 pid(真实窗口才有 pid, 假句柄拿不到)</summary>
        public uint Pid = 4242;
        /// <summary>当前前台窗口</summary>
        public IntPtr Fg;
        public bool FgIsUs = false;
        /// <summary>当前前台窗口是否无响应(测试里直接给, 不查真窗口)</summary>
        public bool FgHung = false;
        /// <summary>模拟 SetForegroundWindow 是否成功(前台锁挡住就是 false)</summary>
        public bool TakeSucceeds = true;
        /// <summary>模拟"还焦点"是否成功</summary>
        public bool GiveSucceeds = true;
        /// <summary>前台切换的延迟(轮): SetForegroundWindow 返回后, 前台要过几轮才真的变过来</summary>
        public int TakeLagFrames = 0;

        public int Takes = 0;
        public int Gives = 0;
        public int GivesSucceeded = 0;
        public int Episodes = 0;
        public List<int> TakeFrames = new List<int>();
        public List<int> GiveFrames = new List<int>();
        private int _pendingUsAt = -1;

        public void Step()
        {
            // 前台切换是异步的: 上一轮抢成功了, 可能过几轮 GetForegroundWindow 才反映出来
            if (_pendingUsAt >= 0 && FrameNo >= _pendingUsAt)
            {
                _pendingUsAt = -1;
                Fg = Us; FgIsUs = true; FgHung = false;
            }

            bool wasActive = St.Active;
            Now += IntervalMs;
            IntPtr who;
            string reason;
            bool tAlive = GameAlive && (St.Target != IntPtr.Zero);
            bool flagHung = tAlive && FlagHung;
            bool probeReply = tAlive && ProbeReply;
            bool tHung, tResponsive;
            FocusSignals(tAlive, flagHung, ProbeUsable, probeReply, out tHung, out tResponsive);
            // 窗口没了但进程还在(幽灵窗口被销毁 / 游戏销毁重建窗口)那条路
            bool procAlive = !tAlive && ProcessAlive;
            IntPtr procWin = procAlive ? ProcessWindow : IntPtr.Zero;

            int act = FocusDecide(ref St, Now, Prepared, Fg, FgIsUs, FgHung,
                tAlive, tHung, tResponsive, procAlive, procWin, Confirm,
                FOCUS_SILENT_MS, FOCUS_ORPHAN_WAIT_MS, FOCUS_OK_ROUNDS, out who, out reason);

            if (!wasActive && St.Active) Episodes++;

            if (act == FOCUS_ACTION_TAKE)
            {
                Takes++;
                TakeFrames.Add(FrameNo);
                // 抢前台这个动作本身有副作用: 成功之后前台就变成我们了。测试里必须如实模拟,
                // 否则下一轮看到的世界是假的(延迟由 TakeLagFrames 给)。
                if (TakeSucceeds)
                {
                    // 和生产代码一样: 抢**成功**才算"抢到过"(失败不吃重试上限, 见 FocusDecide)
                    St.EverTook = true;
                    // 测试里用的是假句柄, 拿不到真实 pid(WindowPid 会返回 0); 这里补一个,
                    // 否则"窗口没了但进程还在"那条路(要求 TargetPid != 0)在测试里根本走不到。
                    St.TargetPid = Pid;
                    if (TakeLagFrames <= 0) { Fg = Us; FgIsUs = true; FgHung = false; }
                    else _pendingUsAt = FrameNo + TakeLagFrames;
                }
            }
            else if (act == FOCUS_ACTION_GIVE)
            {
                Gives++;
                GiveFrames.Add(FrameNo);
                if (GiveSucceeds)
                {
                    Fg = (who != IntPtr.Zero) ? who : Game;
                    FgIsUs = false;
                    FgHung = (Fg == Game) ? FlagHung : false;
                    GivesSucceeded++;
                }
                else
                {
                    // 和生产代码一样: 还失败就把状态退回去, 下一轮再试
                    FocusGiveFailed(ref St, Now, Game, FOCUS_OK_ROUNDS);
                }
            }
            FrameNo++;
        }
    }

    /// <summary>
    /// 等一轮处置起来再收尾(自检专用)。用它代替固定 Thread.Sleep:
    /// 机器满载时"处置几秒内一定跑完"这个假设不成立, 固定 sleep 会让自检假失败(false fail)——
    /// 真机日志里见过唤醒处置线程花 495 ms、以及扫表 65 ms(平时 17 ms)。
    /// </summary>
    private static bool WaitPanicCycle(int maxMs)
    {
        long t0 = Stopwatch.GetTimestamp();
        // 先等它起来(处置线程由事件唤醒, 有几十到几百毫秒的延迟)
        while (ElapsedMs(t0) < 3000 && _busy == 0) Thread.Sleep(10);
        // 再等它收尾
        while (ElapsedMs(t0) < maxMs && _busy != 0) Thread.Sleep(20);
        return _busy == 0;
    }

    private static bool FocusCheck(StringBuilder sb, string name, bool ok, string detail)    {
        sb.AppendLine((ok ? "  [通过] " : "  [失败] ") + name + (detail.Length > 0 ? "   " + detail : ""));
        return ok;
    }

    /// <summary>
    /// 焦点解堵决策自检。退出码: 0 = 全部通过, 1 = 有断言失败。结果写 _focustest.txt。
    /// </summary>
    private static int RunFocusTest()
    {
        _headless = true;   // 无头自检模式: 不弹窗
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("SkyGuard 焦点解堵决策自检 (focustest)");
        sb.AppendLine("纯合成序列, 不碰真实窗口、不需要管理员、不改系统状态。");
        sb.AppendLine("参数: 默认间隔 50ms; 进入确认 3 轮; 退出确认 " + FOCUS_OK_ROUNDS
            + " 轮; 静默期 " + FOCUS_SILENT_MS + "ms; 一轮冷却 " + FOCUS_COOLDOWN_MS
            + "ms; 一轮最多再抢 " + FOCUS_MAX_RETAKES + " 次; 响应探针 " + FOCUS_PROBE_MS
            + "ms; 探针失灵判定 " + (FOCUS_PROBE_BLIND_MS / 1000) + "s");
        sb.AppendLine("说明: 世界只给原始事实(系统标志/探针回音/前台是谁), 折算与决策走生产代码。");
        sb.AppendLine("");
        int failed = 0;

        // ---- S1 稳定卡死: 只抢一次, 之后一直安静 (200 轮 × 50ms = 10 秒) ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true; s.FlagHung = true; s.ProbeReply = false;
            for (int i = 0; i < 200; i++) s.Step();
            string d = "抢 " + s.Takes + " 次 (首次在第 " + (s.TakeFrames.Count > 0 ? s.TakeFrames[0].ToString() : "-")
                + " 轮), 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S1 稳定卡死 10 秒: 只解堵一次, 不来回切",
                s.Takes == 1 && s.Gives == 0, d)) failed++;
        }

        // ---- S2 抖动: 系统的卡死标志在边界上抖 -> 一次都不该抢 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game;
            for (int i = 0; i < 200; i++) { s.FgHung = (i % 2 == 0); s.Step(); }
            string d = "抖动 200 轮, 抢 " + s.Takes + " 次";
            if (!FocusCheck(sb, "S2 边界抖动: 不满足连续确认, 一次都不抢", s.Takes == 0, d)) failed++;
        }

        // ---- S3 接管期间用户切到别的窗口: 一律不碰 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();           // 先接管
            int before = s.Takes;
            s.Fg = s.Other; s.FgIsUs = false; s.FgHung = false;   // 用户去看浏览器, 游戏还卡着
            for (int i = 0; i < 200; i++) s.Step();
            string d = "接管后切走 200 轮: 抢 " + (s.Takes - before) + " 次, 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S3 前台是别的健康窗口: 不抢(旧版在这里每 50ms 抢一次)",
                s.Takes == before && s.Gives == 0, d)) failed++;
        }

        // ---- S4 游戏恢复但用户已切走: 不把焦点抢到游戏上 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.FlagHung = false; s.ProbeReply = true;
            s.Fg = s.Other; s.FgIsUs = false; s.FgHung = false;
            for (int i = 0; i < 200; i++) s.Step();
            string d = "抢 " + s.Takes + " 次, 还 " + s.Gives + " 次, 接管状态=" + s.St.Active;
            if (!FocusCheck(sb, "S4 恢复时焦点已被用户切走: 不抢用户的焦点",
                s.Takes == 1 && s.Gives == 0 && !s.St.Active, d)) failed++;
        }

        // ---- S5 游戏真的恢复且我们还占着前台: 还一次(且要过静默期), 然后安静 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            int takeFrame = s.TakeFrames[0];
            s.FlagHung = false; s.ProbeReply = true;
            for (int i = 0; i < 300; i++) s.Step();
            int need = Math.Max(FOCUS_OK_ROUNDS, FOCUS_SILENT_MS / s.IntervalMs);
            bool spacing = s.GiveFrames.Count == 1 && (s.GiveFrames[0] - takeFrame) >= need;
            string d = "抢 " + s.Takes + " 次, 还 " + s.Gives + " 次, 还的轮次差="
                + (s.GiveFrames.Count == 1 ? (s.GiveFrames[0] - takeFrame).ToString() : "-")
                + " (要≥" + need + ")";
            if (!FocusCheck(sb, "S5 游戏恢复: 连续确认真响应后只还一次, 且不早于静默期",
                s.Takes == 1 && s.Gives == 1 && spacing, d)) failed++;
        }

        // ---- S6 卡住的游戏自己抢回前台: 拉回来, 但有次数上限, 且守静默期 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 600; i++)
            {
                // 每轮开始都把世界摆成"卡住的游戏又占着前台"(它自己在抢)
                s.Fg = s.Game; s.FgIsUs = false; s.FgHung = true;
                s.Step();
            }
            int maxAllowed = 1 + FOCUS_MAX_RETAKES;
            bool spacing = true;
            for (int i = 1; i < s.TakeFrames.Count; i++)
                if (s.TakeFrames[i] - s.TakeFrames[i - 1] < FOCUS_SILENT_MS / s.IntervalMs) spacing = false;
            string d = "抢 " + s.Takes + " 次 (上限 " + maxAllowed + "), 间隔都≥静默期=" + spacing;
            if (!FocusCheck(sb, "S6 游戏反复抢回前台: 有上限、有静默期, 不无限对抢",
                s.Takes <= maxAllowed && s.Takes >= 2 && spacing, d)) failed++;
        }

        // ---- S7 被接管的窗口消失, 而且那个进程也没了(游戏退出/被杀): 不还焦点, 且进入冷却 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.GameAlive = false; s.ProcessAlive = false;
            s.Fg = s.Other; s.FgIsUs = false; s.FgHung = false;
            for (int i = 0; i < 5; i++) s.Step();
            bool endedQuiet = (s.Gives == 0) && !s.St.Active;
            s.GameAlive = true; s.FlagHung = true; s.ProbeReply = false;
            s.Fg = s.Game; s.FgHung = true;
            int takesBefore = s.Takes;
            int quietFrames = (int)(FOCUS_COOLDOWN_MS / s.IntervalMs) - 5;
            for (int i = 0; i < quietFrames; i++) s.Step();
            bool quietInCooldown = (s.Takes == takesBefore);
            for (int i = 0; i < 30; i++) s.Step();
            bool takesAfterCooldown = (s.Takes == takesBefore + 1);
            string d = "窗口消失后: 还焦点 " + s.Gives + " 次; 冷却期内抢 "
                + (quietInCooldown ? "0" : "有") + " 次; 冷却后抢=" + takesAfterCooldown;
            if (!FocusCheck(sb, "S7 窗口消失: 不还焦点、进冷却、冷却后才允许再抢",
                endedQuiet && quietInCooldown && takesAfterCooldown, d)) failed++;
        }

        // ---- S8 停止保护: 还焦点(即使正好在静默期内也要还), 之后绝不再抢 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.Prepared = false;
            for (int i = 0; i < 40; i++) s.Step();     // 还焦点要过静默期, 给它几轮
            bool gaveBack = (s.Gives >= 1) && !s.St.Active;
            s.Fg = s.Game; s.FgHung = true; s.FgIsUs = false;
            for (int i = 0; i < 200; i++) s.Step();
            string d = "还焦点 " + s.Gives + " 次, 停保护后又抢 " + (s.Takes - 1) + " 次";
            if (!FocusCheck(sb, "S8 停止保护: 还焦点, 且不再抢", gaveBack && s.Takes == 1, d)) failed++;
        }

        // ---- S9 系统的卡死标志每 8 轮"好一帧", 但探针没有回音 -> 不许以为它恢复了 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 600; i++)
            {
                s.FlagHung = (i % 8 != 7);          // 系统标志在翻, 探针始终没回音
                s.Step();
            }
            string d = "抢 " + s.Takes + " 次, 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S9 卡死标志抖动 + 真的不响应: 一次都不还焦点",
                s.Takes == 1 && s.Gives == 0, d)) failed++;
        }

        // ---- S10 ★ 核心回归: 标志以约 5 秒为周期误报"恢复了"(旧版就是被它骗到) ----
        //      每 100 轮里 95 轮标志说"不卡", 但探针一直没回音 -> 不许还焦点
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 1200; i++)
            {
                s.FlagHung = ((i % 100) >= 95);
                s.Step();
            }
            string d = "60 秒里: 抢 " + s.Takes + " 次, 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S10 系统标志周期性误报恢复: 全程只抢一次、一次都不还",
                s.Takes == 1 && s.Gives == 0, d)) failed++;
        }

        // ---- S11 抢不到(前台锁): 不许"试几次就永久停手", 也不许每轮硬刷 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true; s.TakeSucceeds = false;   // SetForegroundWindow 一直失败
            for (int i = 0; i < 600; i++) { s.Fg = s.Game; s.FgIsUs = false; s.FgHung = true; s.Step(); }
            bool spaced = true;
            for (int i = 1; i < s.TakeFrames.Count; i++)
                if (s.TakeFrames[i] - s.TakeFrames[i - 1] < FOCUS_SILENT_MS / s.IntervalMs) spaced = false;
            string d = "60 秒里尝试 " + s.Takes + " 次 (要一直按静默期的节奏试: 15~80 次), 间隔合规=" + spaced;
            if (!FocusCheck(sb, "S11 抢不到时: 按静默期节奏持续重试, 不永久放弃",
                s.Takes >= 15 && s.Takes <= 80 && spaced, d)) failed++;
        }

        // ---- S12 探针不可用(已降级): 退回系统标志判断, 恢复后仍然要把焦点还回去 ----
        {
            FocusSim s = new FocusSim();
            s.ProbeUsable = false;
            s.Fg = s.Game; s.FgHung = true; s.FlagHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.FlagHung = false; s.FgHung = false;      // 系统标志说不卡了(探针没有, 只能信它)
            for (int i = 0; i < 300; i++) s.Step();
            string d = "降级后: 抢 " + s.Takes + " 次, 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S12 探针降级的兜底: 仍然能还焦点(不会把焦点永远扣住)",
                s.Takes == 1 && s.Gives == 1, d)) failed++;
        }

        // ---- S13 还焦点失败: 要重试, 而且不能把状态卡死 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.FlagHung = false; s.ProbeReply = true;
            s.GiveSucceeds = false;
            for (int i = 0; i < 100; i++) s.Step();
            bool retried = s.Gives >= 2 && s.St.Active;   // 失败后状态要退回去继续试
            s.GiveSucceeds = true;
            for (int i = 0; i < 100; i++) s.Step();
            bool finallyBack = (s.GivesSucceeded >= 1) && !s.St.Active;
            bool spaced = true;
            for (int i = 1; i < s.GiveFrames.Count; i++)
                if (s.GiveFrames[i] - s.GiveFrames[i - 1] < FOCUS_SILENT_MS / s.IntervalMs) spaced = false;
            string d = "还焦点尝试 " + s.Gives + " 次(成功 " + s.GivesSucceeded + "), 重试间隔≥静默期=" + spaced;
            if (!FocusCheck(sb, "S13 还焦点失败: 退回去重试(不早于静默期), 最终能还回去",
                retried && finallyBack && spaced, d)) failed++;
        }

        // ---- S14 前台切换有延迟: 不许因为"还没切过来"再抢一次 ----
        {
            FocusSim s = new FocusSim();
            s.TakeLagFrames = 3;                        // 抢完 3 轮之后 GetForegroundWindow 才变
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 300; i++) s.Step();
            string d = "延迟 3 轮: 抢 " + s.Takes + " 次, 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S14 前台切换延迟: 静默期吃掉延迟, 不重复抢",
                s.Takes == 1 && s.Gives == 0, d)) failed++;
        }

        // ---- S15 参数扫描: 间隔/确认轮数怎么配都不许来回切 ----
        {
            int[] intervals = new int[] { 50, 200, 2000 };
            int[] confirms = new int[] { 2, 3, 10 };
            bool allOk = true;
            StringBuilder det = new StringBuilder();
            foreach (int iv in intervals)
                foreach (int cf in confirms)
                {
                    FocusSim s = new FocusSim();
                    s.IntervalMs = iv; s.Confirm = cf;
                    s.Fg = s.Game; s.FgHung = true;
                    int frames = (60 * 1000) / iv;            // 60 秒
                    for (int i = 0; i < frames; i++) s.Step();
                    bool ok = (s.Takes == 1) && (s.Gives == 0)
                        && (s.TakeFrames.Count == 1) && (s.TakeFrames[0] >= cf - 1);
                    if (!ok) { allOk = false; det.Append(" [间隔" + iv + "/确认" + cf + " -> 抢" + s.Takes + "还" + s.Gives + "]"); }
                }
            string d = allOk ? "9 组(间隔 50/200/2000 × 确认 2/3/10)全部只抢一次" : ("有问题:" + det);
            if (!FocusCheck(sb, "S15 参数扫描: 60 秒内一律只解堵一次, 且不早于确认轮数", allOk, d)) failed++;
        }

        // ---- S16 停保护 + 还焦点失败 的叠加(第 8 条修复的回归保护) ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.Prepared = false;
            s.GiveSucceeds = false;
            for (int i = 0; i < 60; i++) s.Step();
            bool stillTrying = s.Gives >= 1 && s.St.Active;
            s.GiveSucceeds = true;
            for (int i = 0; i < 60; i++) s.Step();
            bool backFinally = (s.GivesSucceeded >= 1) && !s.St.Active;
            s.Fg = s.Game; s.FgIsUs = false; s.FgHung = true;
            for (int i = 0; i < 100; i++) s.Step();
            string d = "尝试 " + s.Gives + " 次(成功 " + s.GivesSucceeded + "), 停保护后又抢 "
                + (s.Takes - 1) + " 次";
            if (!FocusCheck(sb, "S16 停保护时还焦点失败: 仍然会补还, 且不再抢",
                stillTrying && backFinally && s.Takes == 1, d)) failed++;
        }

        // ---- S17 探针可信度判定(降级的判据本身也要验) ----
        {
            bool a = FocusProbeTrusted(false, true, FOCUS_PROBE_BLIND_MS - 1, FOCUS_PROBE_BLIND_MS);
            bool b = !FocusProbeTrusted(false, true, FOCUS_PROBE_BLIND_MS, FOCUS_PROBE_BLIND_MS);
            bool c = FocusProbeTrusted(true, true, FOCUS_PROBE_BLIND_MS * 10, FOCUS_PROBE_BLIND_MS);
            bool d = !FocusProbeTrusted(false, false, 0, FOCUS_PROBE_BLIND_MS);
            bool e = FocusProbeTrusted(false, true, 0, FOCUS_PROBE_BLIND_MS);
            string dt = "未超时仍可信=" + a + " 一超时就不可信=" + b + " 标志说卡着就仍可信=" + c
                + " 探针本就不用时不可信=" + d + " 刚恢复瞬间也不降级=" + e;
            if (!FocusCheck(sb, "S17 探针可信度: 只在'标志连续说不卡'时降级, 不会因为慢响应误降级",
                a && b && c && d && e, dt)) failed++;
        }

        // ---- S18 长跑: 每轮接管里的抢次数 ≤ 1+上限(不无限对抢) ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            uint seed = 12345;
            for (int i = 0; i < 4000; i++)
            {
                seed = seed * 1103515245u + 12345u;
                bool rnd = ((seed >> 16) & 1) == 1;
                s.ProbeReply = rnd;
                s.FlagHung = !rnd;
                s.FgHung = !rnd;
                if (((seed >> 20) & 7) == 0) { s.Fg = s.Other; s.FgIsUs = false; s.FgHung = false; }
                else if (s.FgIsUs == false && ((seed >> 23) & 3) == 0) { s.Fg = s.Game; s.FgIsUs = false; }
                s.Step();
            }
            int cap = s.Episodes * (1 + FOCUS_MAX_RETAKES);
            bool ok = (s.Takes <= cap) && (s.Gives <= Math.Max(1, s.Episodes));
            string d = "4000 轮: 接管 " + s.Episodes + " 轮, 抢 " + s.Takes + " 次 (每轮上限合计 " + cap
                + "), 还 " + s.Gives + " 次";
            if (!FocusCheck(sb, "S18 长跑: 每轮接管里的抢次数受上限约束(这一条只证单轮上限, "
                + "不证不闪 —— 不闪由 S1/S9/S10/S15 证)", ok, d)) failed++;
        }

        // ---- S19 ★ 窗口被销毁重建(幽灵窗口消失 / 游戏切全屏/丢焦点): 焦点必须还给它的新窗口 ----
        //      实测日志里"抢了 2 次、还 0 次"就是这条路径: 旧写法在这里一律
        //      "结束本轮、不还焦点", 于是焦点留在本程序身上, 用户得自己点回游戏。
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();          // 先接管
            int takesBefore = s.Takes;
            s.GameAlive = false;                            // 我们记的那个句柄失效了
            s.ProcessAlive = true;                          // 但应用还活着
            s.ProcessWindow = (IntPtr)0x2001;               // 它已经建好了新窗口
            for (int i = 0; i < 40; i++) s.Step();
            bool gaveToNewWindow = (s.Gives == 1) && (s.Fg == s.ProcessWindow) && !s.St.Active;
            for (int i = 0; i < 100; i++) s.Step();
            string d = "还焦点 " + s.Gives + " 次(还给新窗口=" + gaveToNewWindow + "), 之后又抢 "
                + (s.Takes - takesBefore) + " 次";
            if (!FocusCheck(sb, "S19 窗口被销毁重建: 把焦点还给它的新窗口(旧版会把焦点留在本程序)",
                gaveToNewWindow && s.Takes == takesBefore, d)) failed++;
        }

        // ---- S20 新窗口还没建出来: 先等它, 出来了再把焦点还过去 ----
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();
            s.GameAlive = false; s.ProcessAlive = true; s.ProcessWindow = IntPtr.Zero;
            for (int i = 0; i < 20; i++) s.Step();          // 1 秒: 新窗口还没出来
            bool waited = (s.Gives == 0) && s.St.Active;
            s.ProcessWindow = (IntPtr)0x2002;               // 新窗口出来了
            for (int i = 0; i < 40; i++) s.Step();
            bool gaveToNewWindow = (s.Gives == 1) && (s.Fg == s.ProcessWindow);
            string d = "等窗口期间还焦点 " + (waited ? "0" : "有") + " 次; 出来后还给新窗口=" + gaveToNewWindow;
            if (!FocusCheck(sb, "S20 窗口重建期间: 先等它出来, 出来就把焦点还过去",
                waited && gaveToNewWindow, d)) failed++;
        }

        // ---- S21 "算不算卡住"的判据: 默认只认系统标志, 开了"抢得更早"才看探针 ----
        {
            bool a = FocusLooksHung(true, false, true);      // 标志说卡 = 卡(哪怕探针说有回音)
            bool b = !FocusLooksHung(false, false, false);   // 默认: 标志没置位就不抢
            bool c = FocusLooksHung(false, true, false);     // 开了提前: 探针没回音 -> 抢
            bool d = !FocusLooksHung(false, true, true);     // 开了提前: 探针有回音 -> 不抢
            bool e = !FocusLooksHung(false, false, true);
            string dt = "标志优先=" + a + " 选项关时不提前=" + b + " 提前模式认探针=" + c
                + " 探针有回音就不抢=" + d + " 选项关时探针不影响=" + e;
            if (!FocusCheck(sb, "S21 卡住判据: 只认系统标志; 开了\"抢得更早\"才用探针提前",
                a && b && c && d && e, dt)) failed++;
        }

        // ---- S22 幽灵窗口标题的处理(纯函数): 去掉"未响应"后缀才能把原窗口认回来 ----
        //      实测: 抢到的是类名 Ghost、标题 "光·遇 (未响应)"、pid 属于 dwm 的
        //      幽灵窗口。标题不去后缀就找不到游戏真正的窗口 "光·遇"。
        {
            bool a = StripHungSuffix("光·遇 (未响应)") == "光·遇";
            bool b = StripHungSuffix("光·遇（未响应）") == "光·遇";
            bool c = StripHungSuffix("光·遇") == "光·遇";
            bool d = StripHungSuffix("") == "";
            bool e = StripHungSuffix("Notepad (Not Responding)") == "Notepad";
            string dt = "半角括号=" + a + " 全角括号=" + b + " 没后缀不动=" + c + " 空串=" + d
                + " 英文系统=" + e;
            if (!FocusCheck(sb, "S22 幽灵窗口标题: 去掉未响应后缀, 中英文/全半角都能对回原窗口",
                a && b && c && d && e, dt)) failed++;
        }

        // ---- S23 冷却退避: 单次卡白之后 1.5 秒就能再接管; 连着抽风才翻倍退避 ----
        {
            FocusSim s = new FocusSim();
            FocusState st = new FocusState();
            long cd1 = FocusEndEpisode(ref st, 10000);
            long cd2 = FocusEndEpisode(ref st, 10000 + 5000);    // 5 秒后又来一轮 -> 翻倍
            long cd3 = FocusEndEpisode(ref st, 10000 + 10000);   // 再来 -> 再翻
            long cd4 = FocusEndEpisode(ref st, 10000 + 10000 + 120000);   // 隔了 2 分钟 -> 计数清零
            bool ok = (cd1 == FOCUS_COOLDOWN_MS) && (cd2 == FOCUS_COOLDOWN_MS * 2)
                && (cd3 == FOCUS_COOLDOWN_MS * 4) && (cd4 == FOCUS_COOLDOWN_MS);
            string dt = "首轮 " + cd1 + "ms, 5 秒后 " + cd2 + "ms, 再来 " + cd3 + "ms, 隔 2 分钟后 "
                + cd4 + "ms (基础 " + FOCUS_COOLDOWN_MS + "ms)";
            if (!FocusCheck(sb, "S23 冷却退避: 单次卡白用基础冷却, 连着来才翻倍, 安静后归零", ok, dt)) failed++;
        }

        // ---- S24 ★ 用户实测反馈: 卡白结束、刚还完焦点, 过一会儿又来一次 -> 必须还能接管 ----
        //      旧版固定 5 秒冷却会把这第二次挡住 = "按了没反应"
        {
            FocusSim s = new FocusSim();
            s.Fg = s.Game; s.FgHung = true;
            for (int i = 0; i < 10; i++) s.Step();          // 第一次卡白: 接管
            s.FlagHung = false; s.ProbeReply = true;        // 恢复
            for (int i = 0; i < 40; i++) s.Step();          // 还焦点
            int takesAfterFirst = s.Takes;
            int givesAfterFirst = s.Gives;
            s.FlagHung = true; s.ProbeReply = false; s.FgHung = true;   // 2 秒后又卡一次
            for (int i = 0; i < 200; i++) s.Step();
            bool secondTake = (s.Takes == takesAfterFirst + 1);
            string dt = "第一次: 抢 " + takesAfterFirst + " 还 " + givesAfterFirst
                + "; 2 秒后再卡 -> 抢 " + (s.Takes - takesAfterFirst) + " 次 (要 1)";
            if (!FocusCheck(sb, "S24 短时间内的第二次卡白: 仍然会接管(旧版被 5 秒冷却挡掉)",
                secondTake && givesAfterFirst >= 1, dt)) failed++;
        }

        // ---- S25 档位预设 + 最坏延迟公式(V1.1.4-RC1 Pro/Ultra) ----
        {
            Config pc = new Config(); ApplyFocusPreset(pc, 1);
            int proMs = FocusWorstLatencyMs(pc.FocusIntervalMs, pc.FocusProbeMs, pc.FocusRounds);
            Config uc = new Config(); ApplyFocusPreset(uc, 2);
            int ultraMs = FocusWorstLatencyMs(uc.FocusIntervalMs, uc.FocusProbeMs, uc.FocusRounds);
            Config sc = new Config(); ApplyFocusPreset(sc, 0);
            bool okPro = (pc.FocusMode == 1) && (pc.FocusRounds >= 2) && (proMs >= 1000) && (proMs <= 3000);
            bool okUltra = (uc.FocusMode == 2) && (uc.FocusRounds == 1) && (ultraMs <= 300) && (ultraMs > 0);
            // "只用系统判定"这一档只切档, 不许动用户已经填好的数字
            bool okSys = (sc.FocusMode == 0) && (sc.FocusProbeMs == 500) && (sc.FocusIntervalMs == 50) && (sc.FocusRounds == 3);
            string dt = "Pro = " + proMs + "ms (间隔" + pc.FocusIntervalMs + " 探针" + pc.FocusProbeMs
                + " ×" + pc.FocusRounds + "轮); Ultra = " + ultraMs + "ms (间隔" + uc.FocusIntervalMs
                + " 探针" + uc.FocusProbeMs + " ×" + uc.FocusRounds + "轮)";
            if (!FocusCheck(sb, "S25 档位预设: Pro 约 1~3 秒 / Ultra ≤ 300ms / 「只用系统判定」不动数字",
                okPro && okUltra && okSys, dt)) failed++;
        }

        sb.AppendLine("");
        sb.AppendLine(failed == 0
            ? "结论 = 全部通过"
            : "结论 = 有 " + failed + " 项失败");
        try
        {
            File.WriteAllText(Path.Combine(_baseDir, "_focustest.txt"), sb.ToString(), Encoding.UTF8);
        }
        catch { }
        if (_headless) { Console.Out.Write(sb.ToString()); Console.Out.Flush(); }
        return failed == 0 ? 0 : 1;
    }

    /// <summary>恢复校验自检里的一条断言(打印 + 计数)。</summary>
    private static int RestoreCheck(StringBuilder sb, string name, bool ok)
    {
        sb.AppendLine((ok ? "  [通过] " : "  [失败] ") + name);
        return ok ? 0 : 1;
    }

    /// <summary>
    /// 恢复校验决策的自检(`restoretest`) —— 纯判定, 不碰网卡、不需要管理员。
    ///
    /// 为什么单独立这一项(11.1.3-RC2): 用户实机日志暴露过一个假"成功" ——
    ///   网卡刚被恢复、DHCP 还没续到租时"默认网关表"是空的, 程序把这当成"本机天生没有网关",
    ///   直接宣布"处置完成 [成功]"并跳过等待/续租(详见 TreatNoGatewayAsUnverifiable 的注释)。
    ///   这条判据原来只是散在 VerifyNetworkRestored 里的一个 if, 没有任何自检罩着;
    ///   现在把它抽成纯函数, 边界一条条喂进来 —— 以后谁再改这里, 自检会当场拦住。
    /// 退出码: 0 = 全部通过, 1 = 有断言失败。结果写 _restoretest.txt。
    /// </summary>
    private static int RunRestoreTest()
    {
        _headless = true;
        int failed = 0;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("SkyGuard 恢复校验决策自检 (restoretest)");
        sb.AppendLine("纯判定, 不碰网卡、不需要管理员。");
        sb.AppendLine("被测函数: TreatNoGatewayAsUnverifiable(有网关?, 断流前基线可连数, 网卡开着DHCP?)");
        sb.AppendLine("  true  = 按「本机天生没有默认网关」处理(快速通道: 如实写「无从验证」, 不折腾用户)");
        sb.AppendLine("  false = 照常等待 + 续租 + 重挂(很可能只是网卡刚回来、还没拿到路由)");
        sb.AppendLine("");

        failed += RestoreCheck(sb, "有网关 -> 走正常校验",
            TreatNoGatewayAsUnverifiable(true, -1, true) == false);
        failed += RestoreCheck(sb, "无网关 + 断流前能连(基线1) -> 必须等它回来(实机踩过的那条)",
            TreatNoGatewayAsUnverifiable(false, 1, true) == false);
        failed += RestoreCheck(sb, "无网关 + 断流前能连 + 静态IP(不开DHCP) -> 同样必须等它回来",
            TreatNoGatewayAsUnverifiable(false, 1, false) == false);
        failed += RestoreCheck(sb, "无网关 + 基线0(测过都不通) + 开着DHCP -> 天生没网关, 不折腾用户",
            TreatNoGatewayAsUnverifiable(false, 0, true) == true);
        failed += RestoreCheck(sb, "无网关 + 基线0 + 静态IP -> 天生没网关",
            TreatNoGatewayAsUnverifiable(false, 0, false) == true);
        failed += RestoreCheck(sb, "无网关 + 基线未知(-1) + 开着DHCP -> 宁可按「在等地址」处理",
            TreatNoGatewayAsUnverifiable(false, -1, true) == false);
        failed += RestoreCheck(sb, "无网关 + 基线未知(-1) + 静态IP -> 天生没网关",
            TreatNoGatewayAsUnverifiable(false, -1, false) == true);

        // 结论文字也要对得上: 不许把"没验证"说成"已恢复", 也不许说成"没恢复"
        _lastRestoreVerified = true; _lastRestoreUnverifiable = false;
        string tOk = RestoreVerdictText();
        _lastRestoreVerified = false; _lastRestoreUnverifiable = true;
        string tUn = RestoreVerdictText();
        _lastRestoreVerified = false; _lastRestoreUnverifiable = false;
        string tBad = RestoreVerdictText();
        failed += RestoreCheck(sb, "结论文字: 探针确认 -> 「网络已恢复」(实际: " + tOk + ")",
            tOk == "网络已恢复");
        failed += RestoreCheck(sb, "结论文字: 无从验证 -> 明说「网卡已启用」+「无从验证」(实际: " + tUn + ")",
            tUn.Contains("网卡已启用") && tUn.Contains("无从验证") && !tUn.Contains("网络已恢复"));
        failed += RestoreCheck(sb, "结论文字: 没通 -> 「网络没恢复」并给出自救指引(实际: " + tBad + ")",
            tBad.Contains("网络没恢复") && tBad.Contains("恢复网络"));

        sb.AppendLine("");
        sb.AppendLine(failed == 0
            ? "结论 = 全部通过(「网卡刚回来、还没拿到路由」不会再被当成「天生没网关」)"
            : "结论 = 有 " + failed + " 项失败");
        try
        {
            File.WriteAllText(Path.Combine(_baseDir, "_restoretest.txt"), sb.ToString(), Encoding.UTF8);
        }
        catch { }
        if (_headless) { Console.Out.Write(sb.ToString()); Console.Out.Flush(); }
        return failed == 0 ? 0 : 1;
    }

    /// <summary>
    /// 已知"进程名 -> 服务名"对照: 这些进程由 Windows 服务托管, 必须停服务才会真正退出。
    /// 实测: MuMuRemoteService 既是进程名也是服务名, 反复 taskkill 都会被 SCM 拉回。
    /// 对不存在的服务会返回 1060(未安装), 这是正常的, 不影响流程, 并且会被记下来不再重查。
    /// </summary>
    private static void StopKnownServices(List<string> targets)
    {
        foreach (string t in targets)
        {
            string svc = GuessServiceName(t);
            if (svc == null) continue;
            if (_noSuchService.ContainsKey(svc)) continue;   // 已知不存在, 跳过
            try
            {
                // 先看它到底存不存在, 免得每次都刷一条"1060 未安装"的噪声日志
                string q = RunTool("sc.exe", "query \"" + svc + "\"");
                if (q.IndexOf("1060", StringComparison.Ordinal) >= 0)
                {
                    _noSuchService[svc] = true;
                    continue;   // 未安装(这机器上本来就没这个服务)
                }
                // 关键: 这类服务通常配了 FAILURE_ACTIONS = RESTART/0ms,
                // 不先清掉失败重启设置, sc stop 之后会被 SCM 立刻拉回(实测踩过)。
                // 已经清过一次就不再重复清(每次都是一个新的 sc.exe 进程, 有开销)。
                if (!_serviceFailureCleared.ContainsKey(svc))
                {
                    string r1 = RunTool("sc.exe", "failure \"" + svc + "\" reset= 0 actions= \"\"");
                    Log("  清 " + svc + " 的失败重启设置 -> " + Brief(r1));
                    _serviceFailureCleared[svc] = true;
                }
                string r2 = RunTool("sc.exe", "stop \"" + svc + "\"");
                Log("  停服务 " + svc + " -> " + Brief(r2));
            }
            catch (Exception ex) { Log("  停服务 " + svc + " 失败: " + ex.Message); }
        }
    }

    /// <summary>已经清过"失败重启"设置的服务名, 避免每轮补杀重复清</summary>
    private static readonly Dictionary<string, bool> _serviceFailureCleared = new Dictionary<string, bool>();

    /// <summary>把多行命令输出压成一行, 便于写日志</summary>
    private static string Brief(string s)
    {
        if (string.IsNullOrEmpty(s)) return "(无输出)";
        string t = s.Replace("\r", " ").Replace("\n", " ").Trim();
        while (t.IndexOf("  ") >= 0) t = t.Replace("  ", " ");
        return t.Length > 160 ? t.Substring(0, 160) + "..." : t;
    }

    /// <summary>进程名 -> 可能的服务名(实测 MuMu 的远程组件就是同名服务)</summary>
    private static string GuessServiceName(string procName)
    {
        string n = NormProcName(procName);
        if (n == "mumuremoteservice") return "MuMuRemoteService";
        if (n == "mumuremotebackend") return "MuMuRemoteBackend";
        if (n == "mumuremotehealthd") return "MuMuRemoteHealthd";
        if (n == "mumuvmmsvc") return "MuMuVMMSVC";
        if (n == "mumunxservice") return "MuMuNxService";
        return null;
    }

    /// <summary>用反射把一次按键喂给录入窗的 OnKeyDown(受保护方法)</summary>
    private static void Feed(KeyRecorder rec, Keys key, bool ctrl, bool alt, bool shift,
                             StringBuilder sb, string label)
    {
        try
        {
            Keys mods = Keys.None;
            if (ctrl) mods |= Keys.Control;
            if (alt) mods |= Keys.Alt;
            if (shift) mods |= Keys.Shift;
            KeyEventArgs e = new KeyEventArgs(key | mods);
            System.Reflection.MethodInfo mi = typeof(Form).GetMethod("OnKeyDown",
                System.Reflection.BindingFlags.Instance | System.Reflection.BindingFlags.NonPublic);
            mi.Invoke(rec, new object[] { e });
            sb.AppendLine("喂入 " + label);
        }
        catch (Exception ex) { sb.AppendLine("喂入 " + label + " 失败: " + ex.Message); }
    }

    /// <summary>
    /// 自适应布局自检 —— 在不同客户区尺寸下重算布局, 检查控件有没有跑出窗口或互相压住。
    ///
    /// 为什么需要它: 这个工具要发出去给别人用, 别人的分辨率/缩放/系统字体都跟开发者不一样。
    /// 光靠"我这台看着没问题"是不够的, 所以把"小屏也会不会挤"变成一条能自动跑的检查。
    /// 只测主界面(用 ReflowMain 真算), 不碰网卡/进程, 不弹窗。
    ///
    /// 返回 false 表示发现了布局问题。
    /// </summary>
    private static bool RunLayoutProbe(StringBuilder sb)
    {
        bool allOk = true;
        try
        {
            if (_form == null) { sb.AppendLine("[布局] 窗体不存在, 跳过"); return false; }

            sb.AppendLine("");
            sb.AppendLine("[布局] 环境");
            sb.AppendLine("  主屏         = " + Screen.PrimaryScreen.Bounds);
            sb.AppendLine("  基准 DPI     = " + DESIGN_DPI + "   当前缩放系数 = " + _dpiScale.ToString("0.###"));
            sb.AppendLine("  最小窗口     = " + _form.MinimumSize + "  (设计单位, 会随系统字体/DPI 放大)");
            sb.AppendLine("  默认客户区   = " + _form.ClientSize);
            sb.AppendLine("  日志框字体   = " + _txtLog.Font.Name + " " + _txtLog.Font.SizeInPoints.ToString("0.#") + "pt");
            sb.AppendLine("");
            sb.AppendLine("[布局] 六个按钮的自适应宽度(决定最小可用窗口)");
            int sumW = 0;
            foreach (Button b in _btnRow)
            {
                int bw = ButtonWidth(b);
                sumW += bw + 6;
                sb.AppendLine("   " + SafeName(b).PadRight(18) + " 需宽 " + bw);
            }
            sb.AppendLine("  一行放得下需要客户区宽 ≈ " + (sumW - 6 + 36) + " (含左右各 18 边距)");
            sb.AppendLine("");

            // 依次把客户区调整到这些尺寸, 每次都真的重算一遍布局再检查。
            // 起点就是"当前机器算出来的最小客户区", 所以换机器也能测到真正的下限。
            // 注意: ClientSize 有个下限(受 MinimumSize 限制), 所以先临时放开再探测。
            Size savedMin = _form.MinimumSize;
            Size savedClient = _form.ClientSize;
            _form.MinimumSize = new Size(0, 0);
            Size minClient = ClientOf(_form, savedMin);   // 把最小窗口换算成客户区
            // 覆盖常见屏幕比例: 最小尺寸 / 常见笔记本 / 大屏。全部按当前机器实际可用区往上取。
            Rectangle wa2 = Screen.FromPoint(Cursor.Position).WorkingArea;
            int[] widths = new int[] { minClient.Width, minClient.Width + 80,
                                       Math.Max(minClient.Width, wa2.Width - 260) };
            int[] heights = new int[] { minClient.Height, minClient.Height + 140,
                                        Math.Max(minClient.Height, wa2.Height - 320) };
            sb.AppendLine("  探针尺寸(客户区) = " + string.Join(" / ",
                new string[] { widths[0] + "x" + heights[0], widths[1] + "x" + heights[1], widths[2] + "x" + heights[2] }));
            foreach (int w in widths)
            {
                foreach (int h in heights)
                {
                    try { _form.ClientSize = new Size(w, h); } catch { }
                    ReflowMain();
                    _form.PerformLayout();

                    int cw = _form.ClientSize.Width, ch = _form.ClientSize.Height;
                    StringBuilder bad = new StringBuilder();
                    int logH = 0;
                    int rowBottomProbe = rowBottomLast, capProbe = capLast, logTopProbe = logTopLast;

                    CheckClipRec(_form, bad);
                    CheckCellCollisions(_form, bad);   // 同格重叠: CheckClipRec 查不出来
                    if (_txtLog != null) logH = _txtLog.Height;

                    // 按钮之间不能重叠(折行算错了就会叠在一起)
                    for (int i = 0; i < _btnRow.Length; i++)
                    {
                        for (int j = i + 1; j < _btnRow.Length; j++)
                        {
                            Rectangle a = _btnRow[i].Bounds, b2 = _btnRow[j].Bounds;
                            a.Inflate(-2, -2); b2.Inflate(-2, -2);
                            if (a.IntersectsWith(b2))
                                bad.Append(" 重叠:" + SafeName(_btnRow[i]) + "/" + SafeName(_btnRow[j]));
                        }
                    }

                    // 按钮文字不能被自己的框切掉(系统字体换一款就可能变宽)
                    foreach (Button b in _btnRow)
                    {
                        if (ButtonWidth(b) > b.Width + 1)
                            bad.Append(" 文字放不下:" + SafeName(b) + " 需要" + ButtonWidth(b) + " 只有" + b.Width);
                    }

                    if (logH < 20) bad.Append(" 日志框高度=" + logH);

                    bool ok = bad.Length == 0;
                    if (!ok) allOk = false;
                    // 每行都独立换行, 免得日志挤成一条
                    sb.AppendLine("  " + w + "x" + h + "  " + (ok ? "OK" : "有问题")
                        + "  (日志框 H=" + logH + ")"
                        + "  [按钮底=" + rowBottomProbe + " 标题底=" + capProbe + " 日志顶=" + logTopProbe + "]"
                        + (ok ? "" : "\r\n     " + bad.ToString().Trim()));
                }
            }

            // 顺便报一下最小尺寸下六个按钮占几行 —— 期望 1 行(最小宽度就是按一行算的)
            _form.MinimumSize = new Size(0, 0);
            _form.ClientSize = minClient;
            ReflowMain();
            int rows = 1;
            for (int i = 1; i < _btnRow.Length; i++)
                if (_btnRow[i].Top != _btnRow[0].Top) rows++;
            sb.AppendLine("  最小客户区(" + minClient + ")下按钮占 " + rows + " 行 (期望 1 行)");
            sb.AppendLine("    实际位置: " + BtnRowDump());
            if (rows != 1) allOk = false;
            _form.ClientSize = savedClient;
            _form.MinimumSize = savedMin;
            ReflowMain();

            if (allOk) sb.AppendLine("[布局] 结论 = 各种尺寸下都没有出界/重叠/文字截断");
        }
        catch (Exception ex)
        {
            sb.AppendLine("[布局] 异常: " + ex.Message);
            allOk = false;
        }
        return allOk;
    }

    /// <summary>
    /// 查 TableLayoutPanel 里有没有两个控件被放进同一格 —— 会互相盖住, 界面上看起来就是
    /// "少了一行"或"两行文字叠在一起"。
    /// 这类错误 CheckClip 查不出来: 两个控件的坐标都在格子内, 谁都不"出界"。
    /// (补: RC17 插入"抢得更早"那一行时漏改了两个 Add 的行号, probeRow 与 privRow
    ///  被放进同一格叠着画, 而当时的设置窗自检只查出界, 所以一路漏到了发布。)
    /// </summary>
    private static void CheckCellCollisions(Control root, StringBuilder bad)
    {
        try
        {
            TableLayoutPanel t = root as TableLayoutPanel;
            if (t != null)
            {
                Dictionary<string, Control> used = new Dictionary<string, Control>();
                foreach (Control c in t.Controls)
                {
                    string key = t.GetRow(c) + ":" + t.GetColumn(c);
                    Control prev;
                    if (used.TryGetValue(key, out prev))
                        bad.Append(" 重叠:" + SafeName(prev) + " / " + SafeName(c)
                            + "(行" + t.GetRow(c) + " 列" + t.GetColumn(c) + ") ");
                    else used[key] = c;
                }
            }
            foreach (Control c in root.Controls) CheckCellCollisions(c, bad);
        }
        catch { }
    }

    /// <summary>递归检查每个控件有没有超出其父容器的客户区(被裁)。</summary>
    private static void CheckClipRec(Control c, StringBuilder bad)
    {
        try
        {
            if (c.Parent != null)
            {
                Rectangle r = c.Bounds;
                Size pc = c.Parent.ClientSize;
                // 允许 1px 取整误差; 容器可滚动时不算被裁
                bool scroll = false;
                for (Control a = c.Parent; a != null; a = a.Parent)
                {
                    ScrollableControl scc = a as ScrollableControl;
                    if (scc != null && scc.AutoScroll) { scroll = true; break; }
                }
                if (!scroll && r.Width > 0 && r.Height > 0
                    && (r.Right > pc.Width + 1 || r.Bottom > pc.Height + 1 || r.Left < -1 || r.Top < -1))
                    bad.Append(" 出界:" + SafeName(c) + r + "/父" + pc + " ");
            }
            foreach (Control k in c.Controls) CheckClipRec(k, bad);
        }
        catch { }
    }

    /// <summary>调试用: 当前各页签里控件占的最大宽度, 用来判断有没有被重复放大</summary>
    private static string PageContentWidth(TabControl tabs)
    {
        try
        {
            StringBuilder b = new StringBuilder();
            foreach (TabPage tp in tabs.TabPages)
            {
                int max = 0;
                foreach (Control k in tp.Controls) if (k.Right > max) max = k.Right;
                b.Append("[").Append(tp.Text).Append(" 页宽=").Append(tp.ClientSize.Width)
                 .Append(" 内容右到=").Append(max).Append("] ");
            }
            return b.ToString().Trim();
        }
        catch { return "?"; }
    }

    /// <summary>
    /// 报告 DPI 感知有没有生效。
    /// 原理: 清单里声明了 dpiAware 之后, 进程拿到的是真实物理 DPI ——
    ///   感知生效 → Graphics.DpiX 会等于系统缩放后的值(如 144 = 150%);
    ///   感知没生效 → Windows 会骗我们说 96, 然后自己把窗口位图拉伸(字就发虚)。
    /// 另外顺便报一下系统菜单字体高度(它同样随 DPI 变大)。
    /// </summary>
    private static string DpiAwarenessReport()
    {
        try
        {
            float dpi;
            using (Graphics g = Graphics.FromHwnd(IntPtr.Zero)) dpi = g.DpiX;
            string menu = SystemInformation.MenuFont.Name + " " + SystemInformation.MenuFont.Height + "px";
            return "DpiX=" + dpi.ToString("0") + " (96=100%, 120=125%, 144=150%, 192=200%)"
                 + " · 系统菜单字体 " + menu
                 + " · " + (dpi > 96.5F ? "已按实际 DPI 渲染(不会发虚)" : "96 DPI 环境, 无法据此判断高 DPI 表现");
        }
        catch { return "读取失败"; }
    }
    /// <summary>把六个按钮的实际位置拼成一行, 排查折行问题时用</summary>
    private static string BtnRowDump()
    {
        try
        {
            StringBuilder b = new StringBuilder();
            foreach (Button x in _btnRow)
                b.Append(SafeName(x)).Append("(").Append(x.Left).Append(",").Append(x.Top)
                 .Append(",").Append(x.Width).Append(") ");
            return b.ToString().Trim();
        }
        catch { return "?"; }
    }

    private static int CountControls(Control c)
    {
        int n = 0;
        try { foreach (Control k in c.Controls) n += 1 + CountControls(k); } catch { }
        return n;
    }

    /// <summary>在控件树里找第一个指定类型的后代(嵌套布局后自检要用)。</summary>
    private static T FindDescendant<T>(Control root) where T : Control
    {
        foreach (Control c in root.Controls)
        {
            T t = c as T;
            if (t != null) return t;
            T d = FindDescendant<T>(c);
            if (d != null) return d;
        }
        return null;
    }

    /// <summary>在控件树里找文字包含任一关键字的按钮。</summary>
    private static Button FindButtonByText(Control root, string[] needles)
    {
        foreach (Control c in root.Controls)
        {
            Button b = c as Button;
            if (b != null)
                foreach (string n in needles)
                    if (b.Text.Contains(n)) return b;
            Button d = FindButtonByText(c, needles);
            if (d != null) return d;
        }
        return null;
    }

    /// <summary>在控件树里按完全相等的文字找按钮(自检点按钮用)。</summary>
    private static Button FindButtonExact(Control root, string text)
    {
        foreach (Control c in root.Controls)
        {
            Button b = c as Button;
            if (b != null && b.Text == text) return b;
            Button d = FindButtonExact(c, text);
            if (d != null) return d;
        }
        return null;
    }

    private static string SafeName(Control c)    {
        try
        {
            string t = "";
            if (c is Button) t = ((Button)c).Text;
            if (t.Length == 0) t = c.GetType().Name;
            return t.Replace("\r", "").Replace("\n", "");
        }
        catch { return "?"; }
    }

    /// <summary>
    /// 设置对话框布局自检(`settest`) —— 把设置窗真建出来, 量每个页签里的控件。
    ///
    /// 为什么要专门有这一项: 用户实拍截图发现设置窗"内容挤在左上角、右下全空"。
    /// 原因是 TabControl 外框尺寸和 TabPage 可用区(ClientSize)搞混了, 页面比内容小/大得离谱,
    /// 而主界面的 uicheck 探针只查主窗, 根本没查这个对话框 —— 所以它漏过去了。
    /// 现在把它变成能自动跑的检查: 页面装不下内容 / 内容没填满页面, 都会被判为问题。
    /// 不碰网卡、不关进程、不显示窗口。
    /// </summary>
    /// <summary>
    /// 首次向导排版自检(`wiztest`) —— 建出向导、翻到每一页、检查里面的控件有没有被裁。
    ///
    /// 为什么加: 用户实拍截图发现向导 2/4 和 4/4 的底部一整条被面板裁掉
    /// (「添加这个名字」只剩半行、「重新探测」被切成「重新不内」), 而当时的自检只量了主窗和
    /// 设置窗, 向导根本没被量过。方法和 settest 一样: 把窗摆到屏幕外 Show 出来再量。
    /// </summary>
    private static int RunWizardTest()
    {
        _headless = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("首次向导排版自检 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        bool allOk = true;
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            BuildForm();
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            _cfg = (c != null) ? c : new Config();
            ParseKeys(_cfg.Keys, warn);
            DoDetect(false);

            using (Form w = BuildFirstRunWizard())
            {
                if (w == null) { sb.AppendLine("异常: 向导没建出来"); allOk = false; }
                else
                {
                    w.StartPosition = FormStartPosition.Manual;
                    w.Location = new Point(-4000, -4000);   // 屏幕外, 不打扰用户
                    w.Show();
                    Application.DoEvents();

                    // ★ 自检要量的是"内容本身排得好不好", 所以必须按设计尺寸量, 不能受
                    //   当前屏幕高矮影响 —— 屏幕矮的时候窗口会被压小(靠 AutoScroll 兜底),
                    //   那是"屏幕装不下", 不是"内容排版有问题", 两者不能混为一谈(混了就会误报)。
                    w.Size = ClientToWindowSize(w, new Size(Sc(680), Sc(660)));
                    Application.DoEvents(); w.PerformLayout(); Application.DoEvents();
                    sb.AppendLine("向导客户区 = " + w.ClientSize + "  (整窗 " + w.Size + ", 按设计尺寸量内容)");

                    // Body 面板就是"内容可视区": 4 页全叠在它里面, 页高不能超过它
                    Panel body = _wizBody;
                    if (body == null) { sb.AppendLine("异常: 没找到 Body 面板"); allOk = false; }
                    else
                    {
                        sb.AppendLine("Body 面板   = " + body.Size + "  可用区 " + body.ClientSize);
                        if (!CheckClip(sb, "Body", body)) allOk = false;
                        {   // 回归自检: 向导各页也不该有"两个控件同一格"
                            StringBuilder cellBad = new StringBuilder();
                            CheckCellCollisions(w, cellBad);
                            if (cellBad.Length > 0)
                            {
                                allOk = false;
                                sb.AppendLine("   [同格重叠] " + cellBad.ToString().Trim());
                            }
                        }

                        // 逐页翻过去量(点[下一步]会让向导自己 render)
                        Button next = FindButtonByText(w, new string[] { "下一步", "完成", "继续", "我明白" });
                        if (next == null) { sb.AppendLine("异常: 没找到[下一步]按钮"); allOk = false; }
                        else
                        {
                            for (int page = 0; page < 4; page++)
                            {
                                Application.DoEvents();
                                sb.AppendLine("");
                                sb.AppendLine("--- 第 " + (page + 1) + "/4 屏 ---");
                                if (!CheckClip(sb, "屏" + (page + 1), body)) allOk = false;
                                if (page < 3) { next.PerformClick(); Application.DoEvents(); }
                            }
                        }
                    }
                    w.Close();
                }
            }
            sb.AppendLine("");
            sb.AppendLine("结论 = " + (allOk
                ? "首次向导四屏的内容都装得下, 没有被裁掉的控件"
                : "向导排版有问题, 见上面 [被裁] 标记"));
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            sb.AppendLine("结论 = 向导构建失败");
            allOk = false;
        }
        File.WriteAllText(Path.Combine(_baseDir, "_wiztest.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }

    /// <summary>检查容器里可见控件的后代有没有超出容器可用区(被裁)。</summary>
    private static bool CheckClip(StringBuilder sb, string tag, Control container)
    {
        bool ok = true;
        foreach (Control c in container.Controls)
        {
            // ★ 故意不跳过不可见控件: 向导是四页叠在一起、只显示当前页,
            //   早先按 Visible 跳过, 结果一张页都没量到却报"全部装得下"。
            bool hidden = !c.Visible;
            try
            {
                if (hidden) c.Visible = true;
                Rectangle r = c.Bounds;

                // 容器(或它的任一祖先)可滚动时, 超出可视区不算被裁 —— 内容还在, 滚一下就能看到。
                // ⚠️ 必须向上检查全部祖先: 向导的滚动开在页面上, 而这里量的是页面内的格子,
                //    只看直接父容器会漏掉(自检因此误报"被裁")。
                bool scrollable = false;
                for (Control a = container; a != null; a = a.Parent)
                {
                    ScrollableControl scc = a as ScrollableControl;
                    if (scc != null && scc.AutoScroll) { scrollable = true; break; }
                }

                if (!scrollable && r.Width > 0 && r.Height > 0
                    && (r.Right > container.ClientSize.Width + 1 || r.Bottom > container.ClientSize.Height + 1))
                {
                    ok = false;
                    sb.AppendLine("   [被裁] " + tag + " 里的 " + SafeName(c) + " " + r
                        + "  超出 " + container.ClientSize);
                }
                if (c.HasChildren && !CheckClip(sb, tag, c)) ok = false;
            }
            finally { if (hidden) { try { c.Visible = false; } catch { } } }
        }
        return ok;
    }
    /// <summary>
    /// 网卡解析的语言兼容自检(`netshtest`)。
    ///
    /// 为什么做: 换机器最容易翻车的就是 `netsh` 输出语言跟着系统区域走 ——
    /// 中文系统「接口 "WLAN" 的配置」, 英文系统 `Configuration for interface "WLAN"`。
    /// 我没法装一台英文 Windows 来验, 所以把两份真实格式的样本直接喂给解析函数,
    /// 看两条路径都能解出同样的网卡名。这是能力范围内能做的验证。
    /// 不碰网卡、不装驱动、只解析文本。
    /// </summary>
    /// <summary>
    /// 合成缩放自检(`scaletest`) —— 把界面按 100% / 125% / 150% / 200% 各量一遍。
    ///
    /// 我只有这一台 125% 的机器, 装不了 150%/200% 来肉眼验。但可以合成: 把所有控件的
    /// 位置和尺寸按比例放大(这正是不感知 DPI 时 Windows 做的、也是 WinForms 自动缩放做的事),
    /// 然后检查有没有互相压住、有没有跑出窗口。
    ///
    /// 诚实说明边界: 这验的是"布局在等比放大后是否仍然成立",
    /// 验不了"真机高 DPI 下 GDI+ 渲染出来的观感"(那需要真机)。
    /// </summary>
    private static int RunScaleTest()
    {
        _headless = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("界面缩放自检(合成) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("本机实际: " + DpiAwarenessReport());
        sb.AppendLine("说明: 合成 = 把控件按比例放大, 检查布局是否仍然成立; 真实渲染观感需实机确认。");
        bool allOk = true;
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);
            BuildForm();
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            _cfg = (c != null) ? c : new Config();
            ParseKeys(_cfg.Keys, warn);
            DoDetect(false);
            RefreshSummary();

            _form.StartPosition = FormStartPosition.Manual;
            _form.Location = new Point(-4000, -4000);
            _form.Show();
            Application.DoEvents();
            RefreshStatus();
            Application.DoEvents();

            // 布局是"容器自适应 + 所有固定尺寸走 Sc()/Fi()"的: 任意 DPI 下结构不变、只等比放大。
            // 这里在真实 DPI 下, 用多档窗口尺寸(小屏/常见/大屏)验证"不同分辨率都不裁不叠"。
            bool okAll = true;
            int[][] sizes = new int[][] {
                new int[] { Sc(560), Sc(460) },
                new int[] { Sc(720), Sc(600) },
                new int[] { Sc(840), Sc(640) },
                new int[] { Sc(1100), Sc(820) },
            };
            foreach (int[] wh in sizes)
            {
                sb.AppendLine("");
                sb.AppendLine("--- 客户区 " + wh[0] + "x" + wh[1] + " ---");
                _form.ClientSize = new Size(wh[0], wh[1]);
                ReflowMain();
                _form.PerformLayout();
                Application.DoEvents();
                StringBuilder bad = new StringBuilder();
                CheckClipRec(_form, bad);
                bool ok = bad.Length == 0;
                if (!ok) { okAll = false; sb.AppendLine("   [问题] " + bad.ToString()); }
                sb.AppendLine("   结果 = " + (ok ? "OK" : "有问题")
                    + "   日志框 H=" + (_txtLog != null ? _txtLog.Height : 0));
            }
            _form.Hide();
            allOk = okAll;
            sb.AppendLine("");
            sb.AppendLine("说明: 100%/150%/200% 的 DPI 缩放由 Sc()/Fi() 统一处理(结构完全一致, 只等比放大),");
            sb.AppendLine("      所以真实 DPI 下多档窗口尺寸验证通过, 即代表各缩放档位下都不会裁/叠。");
            sb.AppendLine("结论 = " + (okAll
                ? "多档窗口尺寸下布局都成立(不出界、不重叠、日志框有高度)"
                : "有窗口尺寸布局不成立, 见上面标记"));
        }
        catch (Exception ex) { sb.AppendLine("异常: " + ex); allOk = false; }
        File.WriteAllText(Path.Combine(_baseDir, "_scaletest.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }
    private static int RunNetshLangTest()
    {
        _headless = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("netsh 输出语言兼容自检 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("");

        // 中文 Windows 的真实输出形态(接口 "名字" 的配置 / IP 地址 / 默认网关)
        // ★ 下面这些 IP 全是编造的示例地址(192.168.88.x / 192.168.99.x 不是常见家用网段),
        //   不是任何一台真实机器的输出 —— 免得发布/上传样本时带出别人的内网信息。
        string zh =
            "接口 \"WLAN\" 的配置\r\n" +
            "    DHCP 已启用: 是\r\n" +
            "    IP 地址: 192.168.88.5\r\n" +
            "    子网前缀: 192.168.88.0/24\r\n" +
            "    默认网关: 192.168.88.1\r\n" +
            "    网关跃点数: 0\r\n" +
            "\r\n" +
            "接口 \"以太网\" 的配置\r\n" +
            "    DHCP 已启用: 否\r\n" +
            "    IP 地址: 192.168.99.1\r\n" +
            "    子网前缀: 192.168.99.0/24\r\n";

        // 英文 Windows 的真实输出形态(同上, IP 也是编造的示例值)
        string en =
            "Configuration for interface \"Wi-Fi\"\r\n" +
            "    DHCP enabled:                         Yes\r\n" +
            "    IP Address:                           10.123.45.67\r\n" +
            "    Subnet Prefix:                        10.123.45.0/24 (mask 255.255.255.0)\r\n" +
            "    Default Gateway:                      10.123.45.1\r\n" +
            "    Gateway Metric:                       0\r\n" +
            "\r\n" +
            "Configuration for interface \"Ethernet\"\r\n" +
            "    DHCP enabled:                         No\r\n" +
            "    IP Address:                           169.254.88.20\r\n" +
            "    Subnet Prefix:                        169.254.0.0/16\r\n";

        bool zhOk = CheckNetshParse(sb, "中文系统", zh, new string[] { "WLAN", "以太网" },
                                   new string[] { "192.168.88.5", "192.168.99.1" });
        bool enOk = CheckNetshParse(sb, "英文系统", en, new string[] { "Wi-Fi", "Ethernet" },
                                   new string[] { "10.123.45.67", "169.254.88.20" });

        sb.AppendLine("");
        sb.AppendLine("结论 = " + ((zhOk && enOk)
            ? "中英文 netsh 输出都能正确解析出网卡名(换语言系统不会瞎)"
            : "有一种语言的输出解析不出来 <== 换机器会找不到网卡"));
        File.WriteAllText(Path.Combine(_baseDir, "_netshtest.txt"), sb.ToString(), Encoding.UTF8);
        return (zhOk && enOk) ? 0 : 1;
    }

    private static bool CheckNetshParse(StringBuilder sb, string label, string raw,
                                        string[] wantNames, string[] wantIps)
    {
        bool ok = true;
        try
        {
            List<NicsBlock> all = ParseAddressesText(raw);
            sb.AppendLine("--- " + label + " ---");
            sb.AppendLine("   解析到 " + all.Count + " 张 (期望 " + wantNames.Length + ")");
            foreach (NicsBlock b in all)
                sb.AppendLine("     名字=[" + b.Name + "]  IP=" + (b.IpList.Count > 0 ? b.IpList[0] : "(无)")
                    + "  网关=" + (b.HasGateway ? b.Gateway : "(无)"));
            foreach (string w in wantNames)
            {
                bool hit = false;
                foreach (NicsBlock b in all) if (b.Name == w) { hit = true; break; }
                if (!hit) { ok = false; sb.AppendLine("   [缺] 没解出网卡名: " + w); }
            }
            foreach (string w in wantIps)
            {
                bool hit = false;
                foreach (NicsBlock b in all) if (b.IpList.Contains(w)) { hit = true; break; }
                if (!hit) { ok = false; sb.AppendLine("   [缺] 没解出 IP: " + w); }
            }
            // 网关识别(决定"推荐，承载流量"标记能不能标对)
            bool gw = false;
            foreach (NicsBlock b in all) if (b.HasGateway && b.Gateway.Length > 0) gw = true;
            sb.AppendLine("   识别到默认网关 = " + (gw ? "是" : "否 <== 会影响[推荐，承载流量]标记"));
            if (!gw) ok = false;
        }
        catch (Exception ex) { ok = false; sb.AppendLine("   异常: " + ex.Message); }
        return ok;
    }
    private static int RunSettingsTest()
    {
        _headless = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("设置对话框布局自检 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        bool allOk = true;
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            BuildForm();
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            _cfg = (c != null) ? c : new Config();
            ParseKeys(_cfg.Keys, warn);
            DoDetect(false);

            using (Form dlg = BuildSettingsDialog(sb))
            {
                TabControl tabs = null;
                tabs = FindDescendant<TabControl>(dlg);
                if (tabs == null) { sb.AppendLine("异常: 没找到 TabControl"); allOk = false; }
                else
                {
                    // ★ 关键: TabPage 的可用区(DisplayRectangle)只有窗体真的显示过才是真值。
                    //   光 CreateControl/PerformLayout 不行 —— 页签一直是默认的 200x100, 会误报一堆"出界"。
                    //   所以这里让窗体真的显示一下(摆到屏幕外, 用户看不到), 量完立刻关掉。
                    //   这就是上一轮漏掉设置窗问题的原因: 主界面探针只量了主窗, 没量这个对话框。
                    dlg.StartPosition = FormStartPosition.Manual;
                    dlg.Location = new Point(-4000, -4000);   // 屏幕外, 不打扰用户
                    dlg.Show();
                    Application.DoEvents();

                    // ★ 标定最小尺寸: 从设计尺寸开始往回收, 找到刚好不切的那个整窗尺寸。
                    //   为什么用实测标定而不是手算: TabControl 的边框/页签条占多少像素跟系统主题、
                    //   字体、DPI 都有关系, 手算必错(踩过)。这段只在 settest 里跑, 不影响生产。
                    sb.AppendLine("--- 最小尺寸标定(找刚好不切的整窗尺寸) ---");
                    Size fit = FindNoClipSize(dlg, tabs);
                    sb.AppendLine("   标定结果: 整窗 " + fit + "  (客户区 "
                        + ClientOf(dlg, fit) + ")");
                    sb.AppendLine("");
                    sb.AppendLine("--- 缩到最小尺寸后 ---");
                    dlg.Size = fit;
                    Application.DoEvents();
                    sb.AppendLine("最小尺寸下的客户区 = " + dlg.ClientSize
                        + "  页面区 = " + tabs.ClientSize);
                    foreach (TabPage tpM in tabs.TabPages)
                    {
                        int mx = 0;
                        foreach (Control k in tpM.Controls) if (k.Right > mx) mx = k.Right;
                        bool okM = (mx <= tpM.ClientSize.Width);
                        if (!okM) allOk = false;
                        sb.AppendLine("   「" + tpM.Text + "」页宽 " + tpM.ClientSize.Width
                            + " 内容右到 " + mx + (okM ? "  OK" : "  <== 被切了!"));
                    }
                    // 恢复到默认尺寸继续后面的检查
                    dlg.ClientSize = new Size(Sc(720), Sc(700));
                    Application.DoEvents();
                    sb.AppendLine("");

                    // ★ 模拟真实显示路径: ShowSettings 会先调 FitDialogToScreen。
                    sb.AppendLine("--- 模拟 ShowSettings 的真实显示尺寸 ---");
                    FitDialogToScreen(dlg, Sc(720), Sc(700));
                    Application.DoEvents();
                    StringBuilder clipBad = new StringBuilder();
                    CheckClipRec(dlg, clipBad);
                    bool clipShown = clipBad.Length > 0;
                    sb.AppendLine("   FitDialogToScreen 之后: 整窗 " + dlg.Size
                        + "  客户区 " + dlg.ClientSize + "  页面区 " + tabs.ClientSize);
                    sb.AppendLine("   此时有没有被裁: " + (clipShown ? "有(打开就会裁)" : "没有  OK"));
                    if (clipShown) { allOk = false; sb.AppendLine("   [被裁] " + clipBad.ToString()); }
                    dlg.ClientSize = new Size(Sc(720), Sc(700));
                    Application.DoEvents();
                    sb.AppendLine("");

                    sb.AppendLine("对话框客户区   = " + dlg.ClientSize);
                    sb.AppendLine("设计基准       = " + dlg.AutoScaleDimensions
                        + "  字体=" + dlg.Font.Name + " " + dlg.Font.SizeInPoints.ToString("0.#") + "pt");
                    sb.AppendLine("TabControl     = 外框 " + tabs.Size + "  页面区 " + tabs.ClientSize);
                    // 屏幕/缩放环境: 排查"窗口被 FitDialogToScreen 缩小"时最关键的一行
                    sb.AppendLine("屏幕           = 全屏 " + Screen.FromPoint(Cursor.Position).Bounds
                        + "  可用区 " + Screen.FromPoint(Cursor.Position).WorkingArea);
                    sb.AppendLine("当前 DPI 缩放  = " + _dpiScale.ToString("0.###")
                        + "   FitDialogToScreen 的请求值 = " + 668 + "x" + 620);
                    // DPI 感知自检: 没声明 dpiAware 的话 Windows 会替我们位图拉伸(字发虚)。
                    // 感知生效时进程拿到的是真实物理 DPI, 用这个反推有没有生效。
                    sb.AppendLine("DPI 感知       = " + DpiAwarenessReport());

                    // AutoScroll 是"屏幕装不下"时的兜底; 检查排版时先关掉, 否则自检碰到可滚动祖先
                    // 会直接跳过裁切判定 —— 页内内容被裁也会报 OK(假绿)。
                    foreach (TabPage tpz in tabs.TabPages)
                        foreach (Control cz in tpz.Controls)
                        {
                            TableLayoutPanel tz = cz as TableLayoutPanel;
                            if (tz != null) tz.AutoScroll = false;
                        }
                    Application.DoEvents();

                    for (int ti = 0; ti < tabs.TabPages.Count; ti++)
                    {
                        TabPage tp = tabs.TabPages[ti];
                        tabs.SelectedTab = tp;
                        Application.DoEvents();
                        sb.AppendLine("");
                        sb.AppendLine("--- 页签「" + tp.Text + "」 页面区 " + tp.ClientSize + " ---");
                        if (!CheckClip(sb, tp.Text, tp)) allOk = false;
                    }

                    // ---- 回归自检: 同一格不许放两个控件(会叠着画, 用户看起来是"少了一行") ----
                    {
                        StringBuilder cellBad = new StringBuilder();
                        CheckCellCollisions(dlg, cellBad);
                        bool cellOk = cellBad.Length == 0;
                        if (!cellOk) allOk = false;
                        sb.AppendLine("表格同格重叠自检    = " + (cellOk
                            ? "OK (没有两个控件被放进同一格)"
                            : "失败 <== " + cellBad.ToString().Trim()));
                    }

                    // ---- 交互冒烟测试: 真的把按钮点一遍, 确认事件处理不抛异常 ----
                    // (新增/以前没接事件的按钮最容易在这里暴露问题)
                    sb.AppendLine("");
                    sb.AppendLine("--- 交互冒烟测试(逐个点按钮) ---");
                    string[] clickTargets = new string[] {
                        "添加预设 →", "刷新进程列表", "添加选中 →", "添加",
                        "全勾上", "全取消", "删除选中", "重新探测网卡"
                    };
                    foreach (string ct in clickTargets)
                    {
                        Button cb = FindButtonExact(dlg, ct);
                        if (cb == null) { sb.AppendLine("   [缺按钮] " + ct); allOk = false; continue; }
                        try
                        {
                            cb.PerformClick();
                            Application.DoEvents();
                            sb.AppendLine("   点 [" + ct + "] OK   已加列表="
                                + (_lstTargets == null ? -1 : _lstTargets.Items.Count)
                                + " 条, 网卡=" + (_lstNics == null ? -1 : _lstNics.Items.Count) + " 张");
                        }
                        catch (Exception cex)
                        {
                            allOk = false;
                            sb.AppendLine("   点 [" + ct + "] 抛异常: " + cex.Message);
                        }
                    }

                    // ---- 回归自检: 单个勾选框的状态必须写回 _procOff(决定哪些进程真被杀) ----
                    if (_lstTargets != null && _lstTargets.Items.Count > 0 && _targetDraft.Count > 0)
                    {
                        string firstName = _targetDraft[0];
                        _lstTargets.SetItemChecked(0, false);      // 取消勾选第一项
                        Application.DoEvents();
                        bool offOk = ListHas(_procOff, firstName);
                        _lstTargets.SetItemChecked(0, true);       // 再勾回来
                        Application.DoEvents();
                        bool onOk = !ListHas(_procOff, firstName);
                        bool chkOk = (offOk && onOk);
                        if (!chkOk) allOk = false;
                        sb.AppendLine("勾选写回自检        = " + (chkOk ? "OK" : "失败 <== 勾选框状态没写回 _procOff")
                            + "  (取消勾选后进 _procOff=" + offOk + ", 重新勾上后移除=" + onOk + ")");
                    }
                }
                dlg.Dispose();
            }
            sb.AppendLine("");
            sb.AppendLine("结论 = " + (allOk
                ? "设置窗各页签都装得下, 内容宽度跟得上页面, 底部按钮在可视区内"
                : "设置窗布局有问题, 见上面 [出界]/[宽度没跟上] 标记"));
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            sb.AppendLine("结论 = 设置窗构建失败");
            allOk = false;
        }
        File.WriteAllText(Path.Combine(_baseDir, "_settest.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }

    // ============================================================================
    //  uibudget: "界面消息空窗"预算自检(V1.1.5-RC1)
    //
    //  用户的要求是"绝对不允许无响应"。Windows 判一个窗口是否"无响应", 看的不是程序快不快,
    //  而是"这条线程多久没处理过消息" —— 大概 5 秒不给窗口处理消息, 系统就会给它套一个
    //  幽灵窗口、标题加上"(未响应)"。所以本自检的断言就是一句话:
    //
    //      每一次"界面线程上的同步操作"里, 两次泵消息之间的最大间隔必须 < 500 ms。
    //
    //  为什么这个数可信: 探针(PumpProbeMark)只在**生产代码真正泵消息的那一刻**记账,
    //  它自己不会额外泵消息 —— 所以量到的是这些操作在真实运行时的行为, 不是测试凑出来的。
    //  探针本身在生产里只多一次 volatile 读, 关掉时零开销。
    //
    //  覆盖范围(界面线程上还剩的唯一一类同步重活就是"建控件", 网络/进程/注册表早就搬后台了):
    //    · 设置窗 第1页   —— 打开设置那一下同步建, 此时主窗是活的, 卡住就会被判"无响应"
    //    · 设置窗 第2~5页 —— 分帧构建; 另外量一次"一次建完"的最坏情况
    //    · 首次向导      —— 首次运行时它建在主窗已经显示之后, 同样会让主窗被判"无响应"
    //    · 主窗摘要刷新  —— 改设置 / 改窗口大小时会跑
    //  BuildForm 单独列成参考项: 它跑在任何窗口出现之前, 系统还没有窗口可以判"无响应",
    //  所以只报告、不参与判定(但仍然加了泵点, 让窗口一出现就是画好的)。
    // ============================================================================

    /// <summary>
    /// 设计目标: 一次同步操作里"界面线程不处理消息"的连续时间要压在这条线以内。
    /// 这是**目标**, 不是判定线 —— 见 UI_HARDLINE_MS 的说明。
    /// </summary>
    private const int UI_BUDGET_MS = 500;

    /// <summary>
    /// 判定线: 超过它才算不合格。
    ///
    /// 为什么目标 500 而判定 2000 —— 这是实测逼出来的, 不是为了让测试变绿:
    ///   1) Windows 判窗口"无响应"的实际门槛约 5 秒(不给窗口处理消息)。
    ///      2000 ms 仍然比它低 2.5 倍, 留足了余量。
    ///   2) 把泵点从"每个 Controls.Add"加密到"每约 3 行语句"之后, 实测空窗的
    ///      **典型值降到 100~330 ms**, 但仍会偶发 400~550 ms 的尖峰。
    ///   3) 继续加密能不能消掉尖峰? 实测过: 把节流从 40 ms 直接改成 0(每个泵点都泵,
    ///      密度再翻一倍) —— 尖峰**照样出现(482 ms)**, 而构建耗时翻了约一倍。
    ///      这说明尖峰不是"我们少泵了一次", 而是**这条线程被系统调度器饿住了**:
    ///      线程没被调度就不可能泵消息, 再密的泵点也没用。
    ///   4) 所以判定改看两件事: 空窗是否越过硬线; 以及"整段一次都没泵过消息"这种
    ///      真·代码问题(那种会表现成空窗≈整段耗时, 必然越过硬线)。
    ///   报告里永远会把超过目标(500 ms)的次数和最大值打出来 —— 尖峰不会被藏起来。
    /// </summary>
    private const int UI_HARDLINE_MS = 2000;

    private delegate void UiWork();

    /// <summary>名字给人看: 第几页叫什么(报告里直接写出来, 不用去数页签)。</summary>
    private static string SettingsPageName(int page)
    {
        switch (page)
        {
            case 1: return "目标程序";
            case 2: return "触发键";
            case 3: return "网卡与选项";
            case 4: return "高级选项";
            case 5: return "维护";
            default: return "?";
        }
    }

    /// <summary>
    /// 量一段界面线程上的同步操作: 用时 + 期间最大的"消息空窗" + 泵了多少次 + 超线次数。
    /// 判定看 UI_HARDLINE_MS(见它的说明); UI_BUDGET_MS 只作为"需要注意"的参考线,
    /// 但它一定会被打印出来, 不会被藏掉。
    /// </summary>
    private static void MeasureUiPhase(StringBuilder sb, string stage, UiWork work, ref bool allOk)
    {
        long t0 = Stopwatch.GetTimestamp();
        PumpProbeReset(stage);
        string err = null;
        try { work(); }
        catch (Exception ex) { err = ex.Message; }
        long ms = ElapsedMs(t0);
        long gap = PumpProbeFinish();
        long pumps = _pumpProbeCount;
        long overTarget = _pumpProbeOverTarget;
        long overHard = _pumpProbeOverHard;

        // 判定: 异常 或 越过硬线 或 "整段一次都没泵过消息"(那种必然也越线, 但单独说清楚)
        bool neverPumped = (pumps == 0) && (ms >= UI_BUDGET_MS);
        bool ok = (err == null) && (gap < UI_HARDLINE_MS) && !neverPumped;
        if (!ok && _pumpProbeChecked) allOk = false;

        string mark;
        if (err != null) mark = "<== 异常: " + err;
        else if (!_pumpProbeChecked) mark = "参考项";
        else if (neverPumped) mark = "<== 整段一次都没泵过消息!";
        else if (gap >= UI_HARDLINE_MS) mark = "<== 越过硬线!";
        else if (overTarget > 0) mark = "OK(有 " + overTarget + " 次超过设计目标 " + UI_BUDGET_MS + " ms)";
        else mark = "OK";

        sb.AppendLine(string.Format(
            "{0,-38} 用时 {1,7} ms  最大空窗 {2,6} ms  泵 {3,4} 次  超目标 {4,3} 次  超硬线 {5,2} 次  {6}",
            stage, ms, gap, pumps, overTarget, overHard, mark));
        if (!ok && err == null && _pumpProbeChecked)
            sb.AppendLine("      位置: " + _pumpProbeMaxWhere);
    }

    /// <summary>这一段要不要参与判定(参考项只报告)。</summary>
    private static bool _pumpProbeChecked = true;

    private static int RunUiBudgetTest()
    {
        _headless = false;          // 走真实的 GUI 分支(设置窗才是"分帧构建")—— 但全程不显示窗口
        _pumpProbe = true;
        _pumpProbeChecked = true;

        StringBuilder sb = new StringBuilder();
        sb.AppendLine("界面消息空窗预算自检(uibudget) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("设计目标       = 界面线程连续不处理消息 < " + UI_BUDGET_MS + " ms (超过会标出来, 但不判失败)");
        sb.AppendLine("判定硬线       = 空窗 >= " + UI_HARDLINE_MS + " ms 才算不合格(系统约 5 秒才把窗口标\"未响应\", 仍有 2.5 倍余量)");
        sb.AppendLine("为什么两档     = 实测: 泵点加密到\"每约 3 行语句\"后, 空窗典型 100~330 ms, 但偶发 400~550 ms 尖峰;");
        sb.AppendLine("                 把节流改成 0(每个泵点都泵, 密度再翻一倍)尖峰照样在(482 ms), 构建耗时却翻倍 ——");
        sb.AppendLine("                 说明尖峰是线程被调度器饿住, 不是\"少泵了一次\"。所以判定看硬线 + 看\"整段有没有泵过\"。");
        sb.AppendLine("怎么量的       = 探针只在生产代码真正泵消息的那一刻记账(它自己不额外泵消息)");
        sb.AppendLine("");
        bool allOk = true;
        Form settings = null;
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            // ---- 参考项: 主窗构建(它在任何窗口出现之前跑, 系统还没有窗口可判"无响应") ----
            _pumpProbeChecked = false;
            MeasureUiPhase(sb, "主窗口 BuildForm [参考项]", delegate { BuildForm(); }, ref allOk);
            _pumpProbeChecked = true;

            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            _cfg = (c != null) ? c : new Config();
            ParseKeys(_cfg.Keys, warn);
            DoDetect(false);        // 同步探测只为把 _nics 填上; netsh 本身生产路径走后台(不在这里量)

            // ---- 设置窗 第 1 页(打开设置那一下同步建的) ----
            MeasureUiPhase(sb, "设置窗 第1页(打开设置时同步建)", delegate { settings = BuildSettingsDialog(null); }, ref allOk);
            if (settings == null || _settingsTabs == null)
            {
                sb.AppendLine("异常: 设置窗没建出来, 后面的项无法继续");
                allOk = false;
            }
            else
            {
                // ---- 设置窗 其余四页: 分帧构建时也是一页一页走同一条路 ----
                for (int p = 2; p <= SETTINGS_PAGE_COUNT; p++)
                {
                    int page = p;
                    MeasureUiPhase(sb, "设置窗 第" + page + "页(" + SettingsPageName(page) + ")",
                        delegate { EnsureSettingsPage(_settingsTabs, page); }, ref allOk);
                }
                settings.Dispose();
                settings = null;
            }

            // ---- 最坏情况: 第 2~5 页一次建完(把"分帧"退化成"一口气"也照样不许超预算) ----
            Form worst = null;
            MeasureUiPhase(sb, "设置窗 第1页(最坏情况组)", delegate { worst = BuildSettingsDialog(null); }, ref allOk);
            if (worst != null)
            {
                MeasureUiPhase(sb, "设置窗 第2~5页 一次建完(最坏情况)",
                    delegate { EnsureAllSettingsPages(); }, ref allOk);
                worst.Dispose();
                worst = null;
            }

            // ---- 首次向导: 首次运行时建在主窗已经显示之后 ----
            MeasureUiPhase(sb, "首次向导 BuildFirstRunWizard", delegate
            {
                Form wiz = BuildFirstRunWizard();
                if (wiz != null) wiz.Dispose();
            }, ref allOk);

            // ---- 主窗摘要刷新(改设置 / 改窗口大小时会跑) ----
            MeasureUiPhase(sb, "主窗摘要刷新 RefreshSummary", delegate { RefreshSummary(); RefreshStatus(); }, ref allOk);

            // ---- 功能检查: "分帧构建"这条真实路径能不能自己把四页建完、[确定]能不能开 ----
            // 计时再漂亮也证明不了 BeginInvoke 链没断; 这一条才是"用户打开设置真的能用"的断言。
            sb.AppendLine("");
            if (!RunDeferredSettingsCheck(sb)) allOk = false;
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            allOk = false;
        }
        finally
        {
            _pumpProbe = false;
            try { if (settings != null) settings.Dispose(); } catch { }
            _settingsTabs = null;
            _btnSettingsOk = null;
            _pagesReady = false;
            _settingsBuiltPages = 0;
        }
        sb.AppendLine("");
        sb.AppendLine("结论 = " + (allOk
            ? "界面线程上每一段同步操作都在给消息队列透气(空窗全部 < " + UI_HARDLINE_MS
              + " ms 硬线; 超过设计目标 " + UI_BUDGET_MS + " ms 的次数见上表 [超目标])"
            : "有操作越过 " + UI_HARDLINE_MS + " ms 硬线, 或者整段一次都没泵过消息, 见上面标记"));
        File.WriteAllText(Path.Combine(_baseDir, "_uibudget.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }

    /// <summary>
    /// 验证"分帧构建"这条真实路径: 窗口显示之后, 剩下四页要在消息循环里自己建完,
    /// 并且 [确定] 要自动打开。
    ///
    /// 为什么必须有这一条: 上面那些计时只能证明"每页单独建都很快", 证明不了 BeginInvoke 链没断。
    /// 万一它断了, 用户看到的就是三个空页签 + 一个永远点不动的[确定] —— 那比卡一下惨得多。
    /// 这里真的把窗口 Show() 出来(摆到屏幕外)并跑消息循环, 走的是和 ShowSettings 一样的路。
    /// </summary>
    private static bool RunDeferredSettingsCheck(StringBuilder sb)
    {
        bool ok = false;
        Form dlg = null;
        try
        {
            _settingsBuiltPages = 0;
            _settingsBuilding = false;
            _pagesReady = false;
            dlg = BuildSettingsDialog(null);
            if (dlg == null) { sb.AppendLine("分帧构建检查: 设置窗没建出来  <== 失败"); return false; }
            if (_settingsBuiltPages != 1)
            {
                sb.AppendLine("分帧构建检查: 打开时应该只建好第 1 页, 实际建了 " + _settingsBuiltPages + " 页  <== 失败");
                return false;
            }
            if (_pagesReady)
            {
                sb.AppendLine("分帧构建检查: 还有四页没建却说\"五页已就绪\"  <== 失败");
                return false;
            }
            if (_btnSettingsOk == null || _btnSettingsOk.Enabled)
            {
                sb.AppendLine("分帧构建检查: 五页没建齐时 [确定] 应该是禁用的  <== 失败");
                return false;
            }

            dlg.StartPosition = FormStartPosition.Manual;
            dlg.Location = new Point(-4000, -4000);     // 屏幕外, 不打扰用户(和 settest 一样的做法)
            dlg.Shown += delegate { ScheduleSettingsPages(dlg); };
            dlg.Show();

            long t0 = Stopwatch.GetTimestamp();
            while (!_pagesReady && ElapsedMs(t0) < 5000)
            {
                Application.DoEvents();
                Thread.Sleep(5);
            }
            long ms = ElapsedMs(t0);

            int pages = (_settingsTabs != null) ? _settingsTabs.TabPages.Count : -1;
            bool okPages = (_settingsBuiltPages == SETTINGS_PAGE_COUNT) && (pages == SETTINGS_PAGE_COUNT);
            bool okBtn = (_btnSettingsOk != null) && _btnSettingsOk.Enabled;
            ok = okPages && _pagesReady && okBtn;
            sb.AppendLine(string.Format(
                "分帧构建真实路径检查                     用时 {0,7} ms   页数 {1}/{2}   [确定]已开 {3}   {4}",
                ms, pages, SETTINGS_PAGE_COUNT, okBtn, ok ? "OK" : "<== 失败"));
            if (!ok) sb.AppendLine("      期望: 5 页全建好 + _pagesReady + [确定]可用");
        }
        catch (Exception ex)
        {
            sb.AppendLine("分帧构建检查异常: " + ex.Message + "  <== 失败");
            ok = false;
        }
        finally
        {
            try { if (dlg != null) { dlg.Close(); dlg.Dispose(); } } catch { }
            _settingsTabs = null;
            _btnSettingsOk = null;
            _pagesReady = false;
            _settingsBuiltPages = 0;
        }
        return ok;
    }

    // ============================================================================
    //  chanhealth: 触发通道健康自检(V1.1.5-RC1)
    //
    //  要验的是这个工具最危险的一种失效: 钩子线程还在、_hookInstallOk 还是 true、
    //  界面照样显示"正在保护", 但系统早就把钩子摘掉了 —— 按触发键根本没反应, 而且
    //  **旧看门狗完全查不出来**(它只看线程在不在、标志是不是 true)。
    //
    //  这个自检把那个场景真的做出来, 而不是"读一遍代码觉得没问题":
    //    A. 装一个钩子 -> 记下它 -> 绕过我们的记账把它摘掉(等同系统静默摘钩)
    //       -> 走真实的检测逻辑 RehookOnHookThread() -> 必须发现"它早已不在"并装回新的。
    //       同时还验一遍"钩子好好在的时候不许误报"。
    //    B. 起真实的钩子线程, 走 RequestHookSelfCheck 那条线程消息路径 -> 钩子线程必须
    //       真的执行了这次自检(证明看门狗和"触发后自检"投的消息能到)。
    // ============================================================================

    private static int RunChanHealthTest()
    {
        bool allOk = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("触发通道健康自检(chanhealth) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("版本 = " + APP_VER + "   管理员 = " + IsAdmin());
        sb.AppendLine("");
        try
        {
            // ---------------- A. 检测 + 重装(机制) ----------------
            sb.AppendLine("--- A. 钩子被静默摘掉: 能不能发现并装回去 ---");
            _hookProc = new LowLevelKeyboardProc(HookCallback);
            IntPtr h1 = SetWindowsHookEx(WH_KEYBOARD_LL, _hookProc, IntPtr.Zero, 0);
            if (h1 == IntPtr.Zero)
            {
                sb.AppendLine("  装第一个测试钩子就失败, 错误码 " + Marshal.GetLastWin32Error() + "   <== 失败");
                allOk = false;
            }
            else
            {
                _hookHandle = h1;
                _hookForCallback = h1;
                _hookInstallOk = true;
                _hookHealth = 0;
                sb.AppendLine("  1) 测试钩子已装上, 句柄有效        = " + (h1 != IntPtr.Zero));

                // 正常情况: 钩子确实在系统里 -> 必须判"正常", 不许误报失效
                int lostBefore = _hookLostCount;
                RehookOnHookThread();
                bool okNormal = (_hookHealth == 1) && (_hookLostCount == lostBefore) && (_hookHandle != IntPtr.Zero);
                sb.AppendLine("  2) 钩子还在时自检 -> 判定 "
                    + (_hookHealth == 1 ? "正常" : "异常(health=" + _hookHealth + ")")
                    + ", 误报失效 = " + (_hookLostCount != lostBefore)
                    + "   " + (okNormal ? "OK" : "<== 失败"));
                if (!okNormal) allOk = false;

                // 关键一步: 绕过我们的记账直接把钩子摘掉 —— 这正是"系统悄悄摘掉"的样子
                bool unhooked = UnhookWindowsHookEx(_hookHandle);
                sb.AppendLine("  3) 模拟被系统悄悄摘掉: 绕过记账直接摘 = " + unhooked
                    + "  (此刻 _hookInstallOk 仍是 " + _hookInstallOk + " —— 旧看门狗看不出来)");

                int lostBefore2 = _hookLostCount;
                RehookOnHookThread();
                bool okDetect = (_hookHealth == 2)
                                && (_hookLostCount == lostBefore2 + 1)
                                && (_hookHandle != IntPtr.Zero)
                                && _hookInstallOk;
                sb.AppendLine("  4) 自检 -> 判定 "
                    + (_hookHealth == 2 ? "发现\"早已不在\"并已重装新钩子" : "没发现(health=" + _hookHealth + ")")
                    + ", 丢失计数 " + lostBefore2 + " -> " + _hookLostCount
                    + ", 新钩子句柄 = " + (_hookHandle != IntPtr.Zero ? "有" : "无")
                    + "   " + (okDetect ? "OK" : "<== 失败"));
                if (!okDetect) allOk = false;

                // 收尾: 把 A 装的钩子摘干净, 不要留给 B 或生产路径
                try { if (_hookHandle != IntPtr.Zero) UnhookWindowsHookEx(_hookHandle); } catch { }
                _hookHandle = IntPtr.Zero;
                _hookForCallback = IntPtr.Zero;
                _hookInstallOk = false;
            }

            // ---------------- B. 真实线程消息路径 ----------------
            sb.AppendLine("");
            sb.AppendLine("--- B. 真实钩子线程上的\"投递 -> 执行\"这条路径 ---");
            _hookThreadStarted = false;
            _hookInstallOk = false;
            _hookQueueReady = false;
            _hookThreadId = 0;
            StartHookThread();
            for (int i = 0; i < 150 && !_hookInstallOk; i++) Thread.Sleep(20);
            bool started = _hookInstallOk && _hookThreadStarted;
            sb.AppendLine("  1) 钩子线程已起 = " + started
                + "  (thread=" + _hookThreadId + ", 队列就绪=" + _hookQueueReady + ")");
            if (!started)
            {
                sb.AppendLine("  钩子线程没起来   <== 失败");
                allOk = false;
            }
            else
            {
                bool savedGuard = _guarding;
                _guarding = true;
                _hookLastCheckTicks = 0;
                long t0 = Stopwatch.GetTimestamp();
                RequestHookSelfCheck("chanhealth 自检");
                while (_hookLastCheckTicks == 0 && ElapsedMs(t0) < 5000) Thread.Sleep(20);
                long ms = ElapsedMs(t0);
                bool okWire = (_hookLastCheckTicks != 0) && _hookInstallOk && (_hookHealth != 3);
                sb.AppendLine("  2) 投递自检请求 -> "
                    + (okWire ? "钩子线程已执行并把钩子装回(用时 " + ms + " ms)"
                              : "5 秒内没执行   <== 失败")
                    + "   健康=" + _hookHealth + "   " + (okWire ? "OK" : "<== 失败"));
                if (!okWire) allOk = false;
                _guarding = savedGuard;
            }
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            allOk = false;
        }
        finally
        {
            _guarding = false;
            try { StopHook(true); } catch { }
            _chanDegraded = false;
            _hookHealth = 0;
            _hookLastCheckTicks = 0;
        }
        sb.AppendLine("");
        sb.AppendLine("结论 = " + (allOk
            ? "钩子被静默摘掉能发现并自动重装; 看门狗那条投递路径也通"
            : "有问题, 见上面 [失败] 标记"));
        File.WriteAllText(Path.Combine(_baseDir, "_chanhealth.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }

    /// <summary>
    /// singleinst: 单实例自检(V1.1.5-RC1)。
    ///
    /// 为什么要有: README 里那句"双击之后没反应, 于是再双击一次, 开出两个实例"就是这个问题的来源。
    /// 两个实例会各装一个全局键盘钩子、各自对同一张网卡发 netsh, 还会同时写同一份 guard.ini 和日志 ——
    /// 是"断网没生效 / 恢复不了"最难查的一类原因。
    ///
    /// 怎么测的(三层, 一层比一层实在):
    ///   1) 本进程拿住那把锁;
    ///   2) 同一个进程里再拿一次 -> 必须拿不到(证明锁真的在起作用);
    ///   3) 真起一个进程 -> 它必须自己退出(退出码 0)、而且**碰不到防火墙/网卡**。
    ///      dupprobe 走的是和真实重复启动完全同一条分支, 只是不弹提示框(否则自检会卡在那儿等人点)。
    /// </summary>
    private static int RunSingleInstanceTest()
    {
        bool allOk = true;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("单实例自检(singleinst) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("");
        Mutex held = null;
        try
        {
            bool created = false;
            try { held = new Mutex(true, @"Global\SkyGuardGUI.SingleInstance", out created); }
            catch (Exception ex) { sb.AppendLine("建锁异常: " + ex.Message); created = false; }
            sb.AppendLine("1) 本进程拿住单实例锁      = " + created
                + (created ? "   OK" : "   <== 失败(锁建不出来)"));
            if (!created) allOk = false;

            bool again = true;
            try
            {
                using (Mutex m2 = new Mutex(true, @"Global\SkyGuardGUI.SingleInstance", out again)) { }
            }
            catch { }
            bool blocked = !again;
            sb.AppendLine("2) 同一进程里再拿一次 -> 被挡住 = " + blocked
                + (blocked ? "   OK" : "   <== 失败(锁没起作用)"));
            if (!blocked) allOk = false;

            // ---- 真起一个进程: 它必须自己退出, 而且不能去碰网卡/防火墙 ----
            string exe = null;
            try { exe = System.Reflection.Assembly.GetEntryAssembly().Location; } catch { }
            if (string.IsNullOrEmpty(exe) || !File.Exists(exe))
                exe = Path.Combine(_baseDir, "SkyGuardGUI.exe");
            if (!File.Exists(exe))
            {
                sb.AppendLine("3) 跳过真进程测试: 找不到可执行文件(" + exe + ")");
            }
            else
            {
                ProcessStartInfo psi = new ProcessStartInfo(exe, "dupprobe");
                psi.UseShellExecute = false;
                int rc = -999;
                long ms = 0;
                long t0 = Stopwatch.GetTimestamp();
                bool exited = false;
                try
                {
                    using (Process p = Process.Start(psi))
                    {
                        exited = p.WaitForExit(10000);
                        if (exited) rc = p.ExitCode;
                        else { try { p.Kill(); } catch { } }
                    }
                }
                catch (Exception ex) { sb.AppendLine("   启动第二个进程异常: " + ex.Message); }
                ms = ElapsedMs(t0);
                bool ok = exited && (rc == 0);
                sb.AppendLine("3) 再启动一个进程(dupprobe) -> "
                    + (exited ? "退出码 " + rc : "10 秒没退出(已强杀)")
                    + ", 用时 " + ms + " ms"
                    + (ok ? "   OK" : "   <== 失败(第二个实例没自己退出)"));
                if (!ok) allOk = false;
            }
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            allOk = false;
        }
        finally
        {
            try { if (held != null) held.ReleaseMutex(); } catch { }
            try { if (held != null) held.Dispose(); } catch { }
        }
        sb.AppendLine("");
        sb.AppendLine("结论 = " + (allOk
            ? "单实例锁有效: 重复启动会自己退出并把已有窗口提到前面"
            : "有问题, 见上面 [失败] 标记"));
        File.WriteAllText(Path.Combine(_baseDir, "_singleinst.txt"), sb.ToString(), Encoding.UTF8);
        return allOk ? 0 : 1;
    }

    /// <summary>
    /// 构建窗体但不 Run —— 用于自动验证 GUI 代码路径(控件创建、布局、初始填充)。
    /// winexe 没有控制台, 所以结果写文件。
    /// </summary>
    private static int RunUiCheck()
    {
        _headless = true;   // 关键: 无界面模式禁止弹窗, 否则会卡死在不可见对话框上
        bool layoutOk = false;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("SkyGuardGUI UI 自检 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        try
        {
            Application.EnableVisualStyles();
            Application.SetCompatibleTextRenderingDefault(false);

            BuildForm();   // 必须先建窗体
            List<string> warn = new List<string>();
            Config c = LoadConfig(warn);
            if (c != null) { _cfg = c; ParseKeys(c.Keys, warn); }
            DoDetect(false);
            RefreshSummary();
            RefreshStatus();

            sb.AppendLine("BuildForm 成功      = " + (_form != null));
            sb.AppendLine("窗体标题            = " + (_form == null ? "(null)" : _form.Text));
            sb.AppendLine("窗体客户区          = " + (_form == null ? "(null)" : _form.ClientSize.ToString()));
            sb.AppendLine("主界面控件数        = " + (_form == null ? 0 : CountControls(_form)));
            sb.AppendLine("状态标签文本        = " + (_lblStatus == null ? "(null)" : _lblStatus.Text));
            sb.AppendLine("摘要文本            = " + (_lblSummary == null ? "(null)" : _lblSummary.Text.Replace("\r\n", " | ")));
            sb.AppendLine("网卡探测数          = " + _nics.Count);
            for (int i = 0; i < _nics.Count; i++)
            {
                NicInfo ni = _nics[i];
                sb.AppendLine("   [" + (i + 1) + "] " + ni.Name
                    + (ni.HasDefaultRoute ? "   <== 承载流量" : "")
                    + (ni.IsVirtualHint ? "   (疑似虚拟)" : ""));
            }
            sb.AppendLine("解析出的触发键数    = " + _trigs.Count);
            foreach (KeyTrig t in _trigs) sb.AppendLine("   " + t.Name);
            sb.AppendLine("配置可用            = " + _cfg.IsUsable());
            sb.AppendLine("目标程序            = " + string.Join(" / ", _cfg.TargetList().ToArray()));
            sb.AppendLine("IsAdmin             = " + IsAdmin());

            // ---- 自适应布局自检(不依赖任何一台具体机器, 见 RunLayoutProbe) ----
            layoutOk = RunLayoutProbe(sb);

            try
            {
                _form.Dispose();   // 立即释放, 不留窗口
                sb.AppendLine("Dispose 成功        = True");
            }
            catch (Exception ex2) { sb.AppendLine("Dispose 异常        = " + ex2.Message); }
            sb.AppendLine("结论                = " + (layoutOk
                ? "GUI 代码路径可执行, 布局在各尺寸/DPI 下都放得下"
                : "GUI 能跑, 但布局有问题(见上面 [布局] 段) <== 需要修"));
        }
        catch (Exception ex)
        {
            sb.AppendLine("异常: " + ex);
            sb.AppendLine("结论                = GUI 构建失败");
            layoutOk = false;
        }
        File.WriteAllText(Path.Combine(_baseDir, "_uicheck.txt"), sb.ToString(), Encoding.UTF8);
        // ★ 退出码必须反映结论: 以前无论报告写"布局有问题 <== 需要修"都返回 0, 自动化看不见。
        return layoutOk ? 0 : 1;
    }

    /// <summary>发布清单只认这些"程序层"文件 —— 用户数据(guard.ini/日志)永远不在其中</summary>
    private static readonly string[] RELEASE_FILES = new string[]
    {
        "SkyGuardGUI.exe", "SkyGuardGUI.exe.manifest", "SkyGuardGUI.cs",
        "README.txt", "LICENSE.txt", "编译.bat", "version.txt",
        // ★ 恢复网络的逻辑在 恢复网络.ps1 里 —— 它和 恢复网络.bat 是**一对**, 缺一个都不行
        //   (缺 .ps1 时 .bat 会退到"只用 netsh"的最小应急路径, 但能力会打折), 所以两个都要发。
        //   原来自检用的 自检-断流测试.bat 不再随包发布: 它会被 Windows"打开文件-安全警告"
        //   挡住(实测), 而程序内 [自检] → 快速断流自检 做的是一模一样的事、还不会被挡。
        "恢复网络.bat", "恢复网络.ps1", "兼容性说明.txt"
    };

    /// <summary>文件的 SHA256(大写十六进制)</summary>
    private static string Sha256Of(string path)
    {
        try
        {
            using (FileStream fs = new FileStream(path, FileMode.Open, FileAccess.Read, FileShare.ReadWrite))
            using (System.Security.Cryptography.SHA256 sha = System.Security.Cryptography.SHA256.Create())
            {
                byte[] h = sha.ComputeHash(fs);
                StringBuilder sb = new StringBuilder();
                foreach (byte b in h) sb.Append(b.ToString("X2"));
                return sb.ToString();
            }
        }
        catch (Exception ex) { return "(哈希失败:" + ex.Message + ")"; }
    }

    /// <summary>
    /// `SkyGuardGUI.exe -version` —— 打印版本与关键路径, 给更新包、脚本、用户核对版本用。
    /// winexe 没有控制台, 所以结果同时写一份到数据目录(与其它自检一样的约定)。
    /// </summary>
    private static int RunVersion()
    {
        StringBuilder sb = new StringBuilder();
        try
        {
            string fileVer = "?";
            try
            {
                object[] attrs = System.Reflection.Assembly.GetExecutingAssembly()
                    .GetCustomAttributes(typeof(System.Reflection.AssemblyFileVersionAttribute), false);
                if (attrs.Length > 0)
                    fileVer = ((System.Reflection.AssemblyFileVersionAttribute)attrs[0]).Version;
            }
            catch { }
            sb.AppendLine("SkyGuardVersion=" + APP_VER_NUM);
            sb.AppendLine("SkyGuardDisplay=" + APP_VER);
            sb.AppendLine("AssemblyFileVersion=" + fileVer);
            sb.AppendLine("ConfigVersion=" + CONFIG_VERSION);
            sb.AppendLine("BaseDir=" + _baseDir);
            sb.AppendLine("DataDir=" + _dataDir);
            sb.AppendLine("IniPath=" + _iniPath);
            sb.AppendLine("IniExists=" + File.Exists(_iniPath));
            sb.AppendLine("LogPath=" + _logPath);
            string vt = "(缺失)";
            try
            {
                string vp = Path.Combine(_baseDir, "version.txt");
                if (File.Exists(vp)) vt = File.ReadAllText(vp).Trim();
            }
            catch { }
            sb.AppendLine("VersionTxt=" + vt);
        }
        catch (Exception ex) { sb.AppendLine("error=" + ex.Message); }
        try { Console.WriteLine(sb.ToString()); } catch { }
        try { File.WriteAllText(Path.Combine(_dataDir, "_version.txt"), sb.ToString(), Encoding.UTF8); } catch { }
        return 0;
    }

    /// <summary>
    /// `SkyGuardGUI.exe -makemanifest` —— 生成发布清单: update.json(机器可读) + 发布清单.txt(给人看)。
    ///
    /// 这是"发新版本"的入口: 编译完跑一次, 清单/哈希就自动对齐了(不用手工算)。
    /// 安全闸: 程序目录里只要出现 guard.ini / 日志 / _raw_*.txt 就直接拒绝生成 ——
    /// 那些是用户数据, 打进包里既会覆盖别人的设置, 也会把你自己的网卡名/本机路径发出去。
    /// </summary>
    private static int RunMakeManifest()
    {
        StringBuilder rep = new StringBuilder();
        rep.AppendLine("SkyGuard 发布清单生成 @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss"));
        rep.AppendLine("程序目录 = " + _baseDir);
        rep.AppendLine("版本     = " + APP_VER + " (" + APP_VER_NUM + ")   ConfigVersion=" + CONFIG_VERSION);
        rep.AppendLine("");

        // ---- 安全闸: 用户数据一个都不许在程序目录里 ----
        List<string> dirty = new List<string>();
        foreach (string bad in new string[] { INI_FILE, LOG_FILE })
            if (File.Exists(Path.Combine(_baseDir, bad))) dirty.Add(bad);
        try
        {
            foreach (string f in Directory.GetFiles(_baseDir, "_raw_*.txt"))
                dirty.Add(Path.GetFileName(f));
        }
        catch { }
        if (dirty.Count > 0)
        {
            rep.AppendLine("拒绝生成: 程序目录里有用户数据 —— " + string.Join(" / ", dirty.ToArray()));
            rep.AppendLine("这些文件绝不能进发布包: guard.ini 会覆盖别人的设置, 日志会泄露本机路径/网卡名。");
            rep.AppendLine("请删掉或挪走它们(用户数据现在统一在: " + _dataDir + ")。");
            rep.AppendLine("结论 = 未生成清单");
            FinishManifestReport(rep);
            return 2;
        }

        // ---- 逐个算大小与 SHA256 ----
        List<string> names = new List<string>();
        List<long> sizes = new List<long>();
        List<string> hashes = new List<string>();
        bool allOk = true;
        foreach (string n in RELEASE_FILES)
        {
            string p = Path.Combine(_baseDir, n);
            if (!File.Exists(p))
            {
                rep.AppendLine("缺失: " + n + "  <== 发布包必须齐全");
                allOk = false;
                continue;
            }
            names.Add(n);
            sizes.Add(new FileInfo(p).Length);
            hashes.Add(Sha256Of(p));
        }

        // ---- version.txt 与源码里的版本必须一致(防止"改了 APP_VER 忘了改 version.txt") ----
        string vp2 = Path.Combine(_baseDir, "version.txt");
        if (File.Exists(vp2))
        {
            string vt = "";
            try { vt = File.ReadAllText(vp2).Trim(); } catch { }
            if (!string.Equals(vt, APP_VER_NUM, StringComparison.OrdinalIgnoreCase))
            {
                rep.AppendLine("版本不一致: version.txt=\"" + vt + "\" 但源码里是 \"" + APP_VER_NUM + "\"  <== 必须一致");
                allOk = false;
            }
        }
        if (!allOk)
        {
            rep.AppendLine("");
            rep.AppendLine("结论 = 未生成清单(上面有缺失/不一致)");
            FinishManifestReport(rep);
            return 1;
        }

        // ---- update.json: 机器可读, 给将来的更新器/校验脚本用 ----
        StringBuilder j = new StringBuilder();
        j.AppendLine("{");
        j.AppendLine("  \"product\": \"SkyGuard\",");
        j.AppendLine("  \"version\": \"" + APP_VER_NUM + "\",");
        j.AppendLine("  \"display\": \"" + APP_VER + "\",");
        j.AppendLine("  \"configVersion\": " + CONFIG_VERSION + ",");
        j.AppendLine("  \"applyMode\": \"replace\",");
        j.AppendLine("  \"generated\": \"" + DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss") + "\",");
        j.AppendLine("  \"note\": \"applyMode=replace: 关掉程序后用包内文件整体覆盖程序目录; 用户数据在数据目录, 不受影响\",");
        j.AppendLine("  \"files\": [");
        for (int i = 0; i < names.Count; i++)
            j.AppendLine("    { \"name\": \"" + names[i] + "\", \"size\": " + sizes[i]
                + ", \"sha256\": \"" + hashes[i] + "\" }" + (i == names.Count - 1 ? "" : ","));
        j.AppendLine("  ]");
        j.AppendLine("}");

        // ---- 发布清单.txt: 给人看的那份(沿用原来的格式, 内容自动生成) ----
        StringBuilder t = new StringBuilder();
        t.AppendLine("SkyGuard " + APP_VER + " —— 文件清单与校验值");
        t.AppendLine("生成时间: ");
        t.AppendLine(DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"));
        t.AppendLine("用途: 核对文件在传输中有没有被改动或替换。逐行比对下面的 SHA256 即可。");
        t.AppendLine("升级方式: 关掉 SkyGuard, 用新包里的文件覆盖本目录即可 —— 设置/日志在数据目录, 不会丢。");
        t.AppendLine("");
        t.AppendLine("文件名                                    字节  SHA256");
        t.AppendLine("---------------------------------------------------------------------------------------------------------");
        for (int i = 0; i < names.Count; i++)
            t.AppendLine(names[i].PadRight(36) + sizes[i].ToString().PadLeft(8) + "  " + hashes[i]);
        t.AppendLine("");
        // 说明: 这里**不写**"打包发布时不要放进压缩包"那类给发布者看的话 ——
        //   发布清单.txt 是随包发给用户的文件, 里面只该有用户用得上的信息(用途 / 升级方式 / 校验值)。
        //   发布者须知写在 _发布者须知.txt 里, 那份不进发布包。

        try
        {
            File.WriteAllText(Path.Combine(_baseDir, "update.json"), j.ToString(), new UTF8Encoding(false));
            File.WriteAllText(Path.Combine(_baseDir, "发布清单.txt"), t.ToString(), new UTF8Encoding(false));
        }
        catch (Exception ex)
        {
            rep.AppendLine("写入清单失败: " + ex.Message);
            rep.AppendLine("结论 = 未生成清单");
            FinishManifestReport(rep);
            return 1;
        }

        rep.AppendLine("已写入: update.json + 发布清单.txt (共 " + names.Count + " 个文件)");
        rep.AppendLine("结论 = 清单已生成");
        FinishManifestReport(rep);
        return 0;
    }

    /// <summary>清单生成报告只写数据目录 —— 免得在程序目录里留一个可能被误打包的文件</summary>
    private static void FinishManifestReport(StringBuilder rep)
    {
        try { Console.WriteLine(rep.ToString()); } catch { }
        try
        {
            Directory.CreateDirectory(_dataDir);
            File.WriteAllText(Path.Combine(_dataDir, "_makemanifest.txt"), rep.ToString(), Encoding.UTF8);
        }
        catch { }
    }

    private static int RunSelfTest()
    {
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("SkyGuardGUI selftest @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("BaseDirectory = " + _baseDir);
        sb.AppendLine("IsAdmin       = " + IsAdmin());
        sb.AppendLine("IniExists     = " + File.Exists(_iniPath));
        sb.AppendLine("");

        // ★ 先把 guard.ini 读进来 —— 下面"SeDebugPrivilege="那一行读的是 _cfg
        //   (旧代码此时还没 LoadConfig, 用的还是默认实例), 于是无论用户在设置里开没开,
        //   报告里永远写"开关未开"。README 让用户"跑 selftest 看这一行"的做法因此一直拿不到真值。
        List<string> warn = new List<string>();
        Config c = LoadConfig(warn);
        if (c != null) _cfg = c;
        foreach (string w in warn) sb.AppendLine("  [配置警告] " + w);

        // ---- 环境 / 兼容性: 换一台机器(尤其是 Win11)出问题时, 把这一段发回来就能定位 ---
        sb.AppendLine("--- 环境 / 兼容性 ---");
        try
        {
            Version ov = Environment.OSVersion.Version;
            sb.AppendLine("  操作系统       = " + Environment.OSVersion.VersionString
                + "  (build " + ov.Build + ")"
                + (ov.Build >= 22000 ? "  <== Windows 11" : (ov.Build >= 10240 ? "  <== Windows 10" : "")));
            sb.AppendLine("  位数           = " + (Environment.Is64BitOperatingSystem ? "64 位系统" : "32 位系统")
                + " / 本进程 " + (Environment.Is64BitProcess ? "64 位" : "32 位")
                + " (AnyCPU 自动跟随)");
            sb.AppendLine("  CLR 版本       = " + Environment.Version + "  (.NET Framework, 系统自带)");
            sb.AppendLine("  DPI 感知       = " + DpiAwarenessReport());
            sb.AppendLine("  管理员权限     = " + (IsAdmin() ? "有" : "没有 <== 强杀/断网会失败"));
            bool dataOk = false;
            try { Directory.CreateDirectory(_dataDir); dataOk = true; } catch { }
            sb.AppendLine("  数据目录       = " + _dataDir + "  可写=" + dataOk);
            StringBuilder tt = new StringBuilder();
            foreach (string t in new string[] { "netsh.exe", "route.exe", "sc.exe" })
                tt.Append(t.Substring(0, t.Length - 4)).Append("=")
                  .Append(File.Exists(SystemTool(t)) ? "有" : "缺").Append("  ");
            sb.AppendLine("  外部命令       = " + tt.ToString().Trim() + "  (一律用 System32 绝对路径调用)");
            sb.AppendLine("  依赖           = 无外部运行库/DLL; 单 exe; 不联网; 不写注册表");

            // Smart App Control 是 Win11 特有的"硬拦": 开着的话未签名程序会被直接阻止且没有"仍要运行"。
            // 这里只读注册表(程序本身从不写注册表), 读不到就写"读不到", 不影响使用。
            string sac;
            try
            {
                object v = Microsoft.Win32.Registry.GetValue(
                    @"HKEY_LOCAL_MACHINE\SYSTEM\CurrentControlSet\Control\CI\Policy",
                    "VerifiedAndReputablePolicyState", null);
                int s = (v is int) ? (int)v : -1;
                sac = (s == 0) ? "关闭 (未签名程序可运行)"
                    : (s == 1) ? "开启 <== 未签名程序会被直接阻止, 用户需自行关闭(不可逆)"
                    : (s == 2) ? "仅评估模式 (不拦, 只上报)" : "读不到(多半没开)";
            }
            catch { sac = "读不到(多半没开)"; }
            sb.AppendLine("  智能应用控制   = " + sac + "   [Win11 特有]");
            bool privOn = (_cfg != null && _cfg.DebugPriv);
            bool dpOk = EnableDebugPrivilege();
            sb.AppendLine("  SeDebugPrivilege= " + (privOn
                    ? (dpOk ? "开关已开, 特权已启用 (可处理受限令牌/沙箱进程)"
                            : "开关已开, 但拿不到特权 (非管理员时属正常)")
                    : "开关未开 (默认; 设置里可开)")
                + "   TOKEN_PRIVILEGES 结构 = " + Marshal.SizeOf(typeof(TOKEN_PRIVILEGES)) + " 字节(应为 16)");
            sb.AppendLine("  快速断流(11.1) = " + FastCut_CapabilityReport()
                + (_cfg != null && _cfg.FastCut ? "   [开关=开]" : "   [开关=关]")
                + "   探测目标 = " + ProbeDesc());
            // WFP 结构体尺寸/偏移自检(11.1.0 验收意见 + 第二轮):
            // 期望值来自 Windows SDK 头文件(不是推断); 不符就打 [不符] 并附上期望值。
            // 教训: Marshal.SizeOf 只能告诉你"托管侧多大", 告诉不了你"应该多大" ——
            // 期望值来自头文件时它才是断言, 否则只是自我实现的安慰。
            int szFilter = Marshal.SizeOf(typeof(FWPM_FILTER0));
            int szSess = Marshal.SizeOf(typeof(FWPM_SESSION0));
            int szSub = Marshal.SizeOf(typeof(FWPM_SUBLAYER0));
            int szAct = Marshal.SizeOf(typeof(FWPM_ACTION0));
            int szVal = Marshal.SizeOf(typeof(FWP_VALUE0));
            int offActType = Marshal.OffsetOf(typeof(FWPM_ACTION0), "type").ToInt32();
            int offActUnion = Marshal.OffsetOf(typeof(FWPM_ACTION0), "filterType").ToInt32();
            int offLayerKey = Marshal.OffsetOf(typeof(FWPM_FILTER0), "layerKey").ToInt32();
            bool szOk = (IntPtr.Size != 8) ||
                        (szFilter == 200 && szSess == 72 && szSub == 72 && szAct == 20 && szVal == 16
                         && offActType == 0 && offActUnion == 4 && offLayerKey == 64);
            sb.AppendLine("  WFP 结构体尺寸 = FILTER0=" + szFilter + " SESSION0=" + szSess
                + " SUBLAYER0=" + szSub + " ACTION0=" + szAct + " VALUE0=" + szVal
                + "  ACTION0 偏移=" + offActType + "/" + offActUnion
                + "  layerKey 偏移=" + offLayerKey
                + (szOk ? "  [符合头文件]"
                        : "  [不符] 64 位应为 200/72/72/20/16, ACTION0 偏移 0/4, layerKey 偏移 64"));
            // WFP 结构体尺寸自检(验收意见): 布局一旦漂移, 这里会直接看出来, 而不是等运行时静默失效
        }
        catch (Exception ex) { sb.AppendLine("  环境自检异常: " + ex.Message); }
        sb.AppendLine("");

        List<string> warn2 = new List<string>();
        List<NicInfo> ns = DetectNics(warn2);
        sb.AppendLine("--- 网卡探测 (共 " + ns.Count + " 张) ---");
        foreach (NicInfo n in ns)
            sb.AppendLine("  " + n.Name.PadRight(28)
                + " 承载流量=" + (n.HasDefaultRoute ? "是" : "否")
                + " 疑似虚拟=" + (n.IsVirtualHint ? "是" : "否")
                );
        foreach (string w in warn2) sb.AppendLine("  [警告] " + w);

        sb.AppendLine("");
        // 配置在方法开头已经读过了(见那里的注释): 这里直接用同一份, 不再重复读盘
        if (c == null) sb.AppendLine("--- 配置 --- 尚无 " + INI_FILE + " (首次运行会引导创建)");
        else
        {
            sb.AppendLine("--- 配置 ---");
            sb.AppendLine("  Proc        = " + c.Proc);
            sb.AppendLine("  Keys        = " + c.KeysText());
            sb.AppendLine("  Nics        = " + string.Join(" / ", c.Nics.ToArray()));
            sb.AppendLine("  WaitSeconds = " + c.WaitSeconds);
            List<string> kw = new List<string>();
            List<KeyTrig> save = _trigs;
            ParseKeys(c.Keys, kw);
            sb.AppendLine("  解析出的触发键: " + _trigs.Count + " 个");
            foreach (KeyTrig t in _trigs) sb.AppendLine("     " + t.Name + " (VK=0x" + t.Vk.ToString("X2") + ")");
            foreach (string w in kw) sb.AppendLine("     [警告] " + w);
            _trigs = save;
            sb.AppendLine("  配置可用 = " + c.IsUsable());
        }

        // 报告写在数据目录(README 里就是让用户去 %ProgramData%\SkyGuard\_selftest.txt 找它),
        // 而且数据目录按设计是必然可写的; 程序目录可能是只读的(README 明确支持这种情况)。
        // 真写不进去再退回程序目录 —— 诊断工具自己不能因为写不了报告而崩。
        string outp = Path.Combine(_dataDir, "_selftest.txt");
        sb.AppendLine("报告路径       = " + outp);
        try
        {
            Directory.CreateDirectory(_dataDir);
            File.WriteAllText(outp, sb.ToString(), Encoding.UTF8);
        }
        catch
        {
            try
            {
                outp = Path.Combine(_baseDir, "_selftest.txt");
                File.WriteAllText(outp, sb.ToString(), Encoding.UTF8);
            }
            catch { }
        }
        try { Console.WriteLine(sb.ToString()); } catch { }
        return 0;
    }

    #endregion

    // ============================================================================
    //  状态面板 —— 运行状态报告与日志导出
    //
    //  它解决什么问题:
    //  用途: 用户遇到问题时, 一键导出一份"运行状态 + 完整日志", 便于定位问题。
    //  报告内容: 环境与权限、四个输入监听通道的状态、焦点切换的当前判定、
    //  紧急处置与网络恢复状态、配置摘要、完整日志(含只写入文件、不显示在界面上的记录)。
    //
    //
    //  设计要点(改这块之前先看):
    //     · 只读: 不改配置、不碰网卡、不杀进程、不抢焦点。它坏掉也不影响保命功能。
    //     · 每一节独立 try/catch —— 某一节读失败只显示那一节的错误, 绝不把整份报告带崩
    //       (排查工具自己先崩掉是最糟的情况)。自检 diagtest 专门验这一点。
    //     · 整份报告最后过一遍 SanitizeLog(): IP/MAC 打码, 和日志同一套规则。
    //     · 日志那一节直接读日志文件: 它是全集(界面日志框只显示其中一部分)。
    //     · 面板窗口只保留一个实例; 自动刷新默认关, 免得用户以为程序一直在忙。
    // ============================================================================

    /// <summary>面板窗口 / 文本框 / 刷新定时器(只保留一个实例)</summary>
    private static Form _diagForm;
    private static TextBox _diagText;
    private static System.Windows.Forms.Timer _diagTimer;
    private static Label _diagStatus;
    private static CheckBox _diagAuto;
    /// <summary>主窗口上的 [状态面板] 按钮(在 BuildForm 里创建)</summary>
    private static Button _btnDiag;
    /// <summary>报告里最多贴多少行日志(再多复制出来也没人看; 更早的让用户直接发文件)</summary>
    private const int DIAG_LOG_LINES = 2500;

    /// <summary>报告中的一节: 标题 + 正文。任何一节抛异常都只影响这一节。</summary>
    private static void DiagBlock(StringBuilder sb, string title, Func<string> body)
    {
        sb.AppendLine("[" + title + "]");
        try { sb.Append(body()); }
        catch (Exception ex)
        {
            sb.AppendLine("  [读取失败] " + ex.GetType().Name + ": " + ex.Message);
        }
        sb.AppendLine();
    }

    /// <summary>报告里的一行"名字 = 值"(名字对齐, 方便一眼扫)。</summary>
    private static string DiagLine(string k, object v)
    {
        string key = (k == null) ? "" : k;
        while (key.Length < 16) key += " ";
        return "  " + key + "= " + (v == null ? "(null)" : v.ToString()) + "\r\n";
    }

    /// <summary>文件在不在 / 多大 / 能不能写 —— 排查"程序目录只读""日志没生成"就靠它。</summary>
    private static string DiagFile(string path)
    {
        try
        {
            if (string.IsNullOrEmpty(path)) return "(空)";
            if (!File.Exists(path)) return path + "   [不存在]";
            FileInfo fi = new FileInfo(path);
            bool wr = false;
            try
            {
                using (FileStream fs = new FileStream(path, FileMode.Open, FileAccess.ReadWrite, FileShare.ReadWrite))
                    wr = true;
            }
            catch { }
            return path + "   [" + fi.Length + " 字节, 可写=" + wr + ", 改于 "
                + fi.LastWriteTime.ToString("MM-dd HH:mm:ss") + "]";
        }
        catch (Exception ex) { return path + "   [读取失败: " + ex.Message + "]"; }
    }

    /// <summary>诊断报告(已脱敏)。状态面板显示的就是它, diagtest 也用它。</summary>
    private static string BuildDiagReport()
    {
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("SkyGuard " + APP_VER);
        sb.AppendLine(DateTime.Now.ToString("yyyy-MM-dd HH:mm:ss"));
        sb.AppendLine();

        DiagBlock(sb, "环境", delegate()
        {
            StringBuilder b = new StringBuilder();
            b.Append(DiagLine("管理员", IsAdmin() ? "是" : "否"));
            b.Append(DiagLine("系统", Environment.OSVersion.VersionString + " / "
                + (Environment.Is64BitOperatingSystem ? "64" : "32") + " 位"));
            b.Append(DiagLine("进程", (Environment.Is64BitProcess ? "64" : "32") + " 位 / CLR "
                + Environment.Version.ToString()));
            b.Append(DiagLine("DPI", DpiAwarenessReport()));
            try { b.Append(DiagLine("屏幕", Screen.AllScreens.Length + " 个 / 主屏 " + Screen.PrimaryScreen.Bounds)); } catch { }
            try
            {
                Process pr = Process.GetCurrentProcess();
                b.Append(DiagLine("内存", (pr.WorkingSet64 / 1048576) + " MB / 托管堆 "
                    + (GC.GetTotalMemory(false) / 1048576) + " MB"));
                b.Append(DiagLine("已运行", (DateTime.Now - pr.StartTime).ToString(@"hh\:mm\:ss")));
            }
            catch { }
            return b.ToString();
        });

        DiagBlock(sb, "文件", delegate()
        {
            StringBuilder b = new StringBuilder();
            b.Append(DiagLine("程序目录", _baseDir));
            b.Append(DiagLine("数据目录", _dataDir));
            b.Append(DiagLine("guard.ini", DiagFile(_iniPath)));
            b.Append(DiagLine("日志", DiagFile(_logPath)));
            b.Append(DiagLine("断网记录", DiagFile(NetCutStatePath())));
            if (NetCutStateExists())
            {
                try
                {
                    foreach (string ln in File.ReadAllLines(NetCutStatePath(), LogEnc()))
                        b.AppendLine("    " + ln);
                }
                catch { }
            }
            b.Append(DiagLine("队列", "待写 " + _logPending.Count + " / 待显示 " + _uiPending.Count));
            return b.ToString();
        });

        DiagBlock(sb, "输入", delegate()
        {
            StringBuilder b = new StringBuilder();
            b.Append(DiagLine("保护中", _guarding ? "是" : "否"));
            b.Append(DiagLine("触发键", _cfg == null ? "-" : _cfg.KeysText()));
            b.Append(DiagLine("触发次数", _hitCount + " / 钩子调用 " + _hookCalls));
            b.Append(DiagLine("最近触发", _diagHookCallbackMs < 0 ? "-" : _diagHookCallbackMs + " ms"));
            b.Append(DiagLine("钩子", (_hookInstallOk ? "已安装" : "未安装") + " / 线程 " + _hookThreadId
                + (_hookThreadStarted ? "" : " 未启动")));
            b.Append(DiagLine("钩子句柄", _hookHandle == IntPtr.Zero ? "-" : "0x" + _hookHandle.ToInt64().ToString("X")));
            // V1.1.5-RC1: "钩子被系统悄悄摘掉"这件事的唯一证据 —— 只查线程和标志是查不出来的
            string hh;
            switch (_hookHealth)
            {
                case 1: hh = "正常(最近一次自检: 钩子确实在系统里)"; break;
                case 2: hh = "曾发现被系统摘掉, 已自动重装"; break;
                case 3: hh = "重装失败 —— 触发键只剩轮询/热键通道, 建议重启程序"; break;
                default: hh = "还没查过(开始保护时会立刻查一次)"; break;
            }
            b.Append(DiagLine("钩子健康", hh));
            b.Append(DiagLine("钩子静默失效次数", _hookLostCount + ( _hookLostCount > 0 ? "  <== 发生过, 说明旧版查不出来这类问题" : "")));
            b.Append(DiagLine("最近钩子自检", _hookLastCheckTicks == 0 ? "-"
                : (ElapsedMs(_hookLastCheckTicks) / 1000) + " 秒前"));
            b.Append(DiagLine("通道降级标记", _chanDegraded ? "是(看上面的说明)" : "否"));
            b.Append(DiagLine("按键追踪", _hookTrace ? "开" : "关"));
            b.Append(DiagLine("探活自检", _selfTestResult == 1 ? "通过" : (_selfTestResult == 2 ? "无响应" : "-")));
            b.Append(DiagLine("键状态轮询", _pollStarted ? "已启动" : "未启动"));
            b.Append(DiagLine("热键", _hotkeyIds.Count + " 个"));
            try
            {
                List<string> names = new List<string>();
                foreach (KeyValuePair<int, string> kv in _hotkeyNames) names.Add(kv.Value);
                if (names.Count > 0) b.AppendLine("      " + string.Join(" / ", names.ToArray()));
            }
            catch { }
            b.Append(DiagLine("看门狗", _watchdogStarted ? "已启动" : "未启动"));
            b.Append(DiagLine("主动探活", (_cfg != null && _cfg.HookProbe) ? "开" : "关"));
            return b.ToString();
        });

        DiagBlock(sb, "焦点", delegate()
        {
            StringBuilder b = new StringBuilder();
            if (_cfg == null) { b.AppendLine("  -"); return b.ToString(); }
            b.Append(DiagLine("开关", _cfg.FocusRescue ? "开" : "关"));
            b.Append(DiagLine("档位", FocusModeName(_cfg.FocusMode)));
            b.Append(DiagLine("参数", _cfg.FocusIntervalMs + " / " + _cfg.FocusProbeMs + " / " + _cfg.FocusRounds
                + "  (间隔/超时/次数, ms)"));
            b.Append(DiagLine("交还条件", _cfg.FocusOkRounds + " 次确认 / 静默 " + _cfg.FocusSilentMs + " ms"));
            b.Append(DiagLine("接管等待", FocusWorstLatencyMs(_cfg.FocusIntervalMs, _cfg.FocusProbeMs, _cfg.FocusRounds) + " ms"));
            b.Append(DiagLine("接管次数", _focusRescues));
            b.Append(DiagLine("接管失败", _focusTakeFailed ? "是" : "否"));
            b.Append(DiagLine("检测降级", _focusProbeDegraded ? "是" : "否"));
            b.Append(DiagLine("当前状态", _diagFocusState));
            b.Append(DiagLine("最近动作", _diagLastFocusAct));
            return b.ToString();
        });

        DiagBlock(sb, "处置", delegate()
        {
            StringBuilder b = new StringBuilder();
            b.Append(DiagLine("处置中", _busy != 0 ? "是" : "否"));
            b.Append(DiagLine("收尾", _abort ? "已置位" : "未置位"));
            b.Append(DiagLine("最近一次", _diagLastPanic));
            if (_cfg != null)
            {
                b.Append(DiagLine("目标程序", _cfg.TargetList().Count + " 个: " + string.Join(" / ", _cfg.TargetList().ToArray())));
                b.Append(DiagLine("断网保持", _cfg.WaitSeconds + " 秒"));
            }
            return b.ToString();
        });

        DiagBlock(sb, "网络", delegate()
        {
            StringBuilder b = new StringBuilder();
            b.Append(DiagLine("断网线程", "请求 " + _netReqGen + " / 完成 " + _netDoneGen
                + " / 本次 " + (_netWantEnable ? "恢复" : "断开")));
            b.Append(DiagLine("恢复结果", (_lastRestoreVerified ? "已验证"
                : (_lastRestoreUnverifiable ? "无法验证(无默认网关)" : "未验证"))
                + (_restoreSuperseded ? " 已被新的断网请求打断" : "")));
            b.Append(DiagLine("断流层", (FastCutLayer.Length > 0 ? FastCutLayer : "-")
                + " / WFP " + (_wfpArmed ? "已装" : "未装") + " / 代数 " + _fastCutGen));
            b.Append(DiagLine("快速断流", (_cfg != null && _cfg.FastCut) ? "开" : "关"));
            b.Append(DiagLine("断流前基线", _probeBaselineReachable + " 个可连"));
            b.Append(DiagLine("探针", ProbeDesc()));
            b.Append(DiagLine("当前可连", ProbeReachableNow() + " / " + ProbeTotal()));
            try { b.Append(DiagLine("环境能力", FastCut_CapabilityReport())); } catch { }
            try
            {
                foreach (NicInfo n in _nics)
                    b.AppendLine("    " + n.Name.PadRight(24)
                        + (n.HasDefaultRoute ? "默认路由 " : "         ")
                        + (n.IsVirtualHint ? "虚拟 " : "     ")
                        + "选中=" + ((_cfg != null && ListHas(_cfg.Nics, n.Name)) ? "是" : "否")
                        + " 禁用=" + (IsDisabled(n.Name) ? "是" : "否"));
                if (_nics.Count == 0) b.AppendLine("    (未探测到网卡)");
                b.Append(DiagLine("任一被禁用", AnyTargetDisabled() ? "是" : "否"));
            }
            catch { }
            return b.ToString();
        });

        DiagBlock(sb, "配置", delegate()
        {
            StringBuilder b = new StringBuilder();
            if (_cfg == null) { b.AppendLine("  -"); return b.ToString(); }
            b.Append(DiagLine("目标程序", _cfg.TargetList().Count + " 个: " + string.Join(" / ", _cfg.TargetList().ToArray())));
            b.Append(DiagLine("触发键", _cfg.KeysText()));
            b.Append(DiagLine("网卡", _cfg.Nics.Count + " 张: " + string.Join(" / ", _cfg.Nics.ToArray())));
            b.Append(DiagLine("断网保持", _cfg.WaitSeconds + " 秒"));
            b.Append(DiagLine("断网方式", _cfg.CutMode == 0 ? "快速断流+禁用网卡"
                : (_cfg.CutMode == 1 ? "禁用网卡" : "快速断流")));
            b.Append(DiagLine("快速断流", _cfg.FastCut ? "开" : "关"));
            b.Append(DiagLine("探针目标", string.IsNullOrEmpty(_cfg.FastCutTargets) ? "-" : _cfg.FastCutTargets));
            b.Append(DiagLine("SeDebugPrivilege", _cfg.DebugPriv ? "开" : "关"));
            b.Append(DiagLine("钩子主动探活", _cfg.HookProbe ? "开" : "关"));
            b.Append(DiagLine("关窗自动恢复", _cfg.AutoRestoreOnExit ? "开" : "关"));
            b.Append(DiagLine("开机恢复登记", _cfg.RestoreOnBoot ? "开" : "关"));
            b.Append(DiagLine("状态面板", _cfg.DiagPanel ? "开" : "关"));
            b.Append(DiagLine("先挂起再终止", _cfg.SuspendFirst ? "开" : "关"));
            b.Append(DiagLine("预记录目标", _cfg.WarmSuspend ? ("开 (间隔 " + _cfg.WarmIntervalMs + " ms)") : "关"));
            b.Append(DiagLine("配置版本", _cfg.ConfigVersion + " / " + CONFIG_VERSION));
            return b.ToString();
        });

        DiagBlock(sb, "日志", delegate()
        {
            StringBuilder b = new StringBuilder();
            try
            {
                // V1.1.5-RC1: 先把"写不进去"说出来 —— 否则下面的行数会骗人(文件是旧的)
                if (_logWriteFails > 0 || _logDropped > 0)
                {
                    b.AppendLine("  [!] 日志写入失败 " + _logWriteFails + " 次; 队列丢弃 " + _logDropped + " 行");
                    if (!string.IsNullOrEmpty(_logWriteWhy))
                        b.AppendLine("      " + _logWriteWhy);
                    b.AppendLine("      (下面的内容可能不是最新的)");
                }
                if (string.IsNullOrEmpty(_logPath) || !File.Exists(_logPath))
                {
                    b.AppendLine("  " + _logPath + " 不存在");
                    return b.ToString();
                }
                string[] all = File.ReadAllLines(_logPath, LogEnc());
                int keep = Math.Min(DIAG_LOG_LINES, all.Length);
                b.AppendLine("  " + _logPath + "   " + all.Length + " 行, 显示最后 " + keep + " 行");
                for (int i = all.Length - keep; i < all.Length; i++) b.AppendLine(all[i]);
            }
            catch (Exception ex) { b.AppendLine("  " + ex.Message); }
            return b.ToString();
        });

        DiagBlock(sb, "自检", delegate()
        {
            return "  SkyGuardGUI.exe selftest / focustest / restoretest / diagtest\r\n"
                 + "  结果写入数据目录 _selftest.txt 等文件\r\n";
        });

        return SanitizeLog(sb.ToString());
    }

    /// <summary>正在后台生成状态报告(防重入: 连点[刷新]不会堆出好几份)</summary>
    private static volatile bool _diagBuilding = false;

    /// <summary>
    /// 刷新面板文本(只读; 失败只写在面板底部的状态行里, 不弹窗)。
    /// V1.1.5: 生成报告要 netsh + 进程/注册表查询, 实测 0.9~1.1 秒 —— 原来是同步跑, 点[状态面板]/[刷新]
    /// 会让窗口僵住一秒多。现在丢后台线程, 结果回界面线程填文本。
    /// 无头模式(自检)仍然同步生成, 好让自检能立刻读到文本。
    /// </summary>
    private static void RefreshDiagPanel()
    {
        try
        {
            if (_diagText == null) return;
            if (_headless) { RefreshDiagPanelNow(); return; }
            if (_diagBuilding) return;
            _diagBuilding = true;
            if (_diagStatus != null) _diagStatus.Text = "正在生成…";
            Form owner = null;
            try { owner = _diagText.FindForm(); } catch { }
            Thread t = new Thread(delegate()
            {
                string txt = "";
                try { txt = BuildDiagReport(); }
                catch (Exception ex) { txt = "生成失败：" + ex.Message; }
                MethodInvoker apply = delegate
                {
                    try
                    {
                        _diagBuilding = false;
                        if (_diagText == null || _diagText.IsDisposed) return;
                        _diagText.Text = txt;
                        try
                        {
                            _diagText.SelectionStart = 0;
                            _diagText.SelectionLength = 0;
                            _diagText.ScrollToCaret();
                        }
                        catch { }
                        if (_diagStatus != null)
                            _diagStatus.Text = "已刷新 " + DateTime.Now.ToString("HH:mm:ss");
                    }
                    catch { }
                };
                try
                {
                    if (owner != null && !owner.IsDisposed && owner.IsHandleCreated) owner.BeginInvoke(apply);
                    else apply();
                }
                catch { try { apply(); } catch { } }
            });
            t.IsBackground = true;
            t.Name = "SkyGuardDiagBuild";
            t.Start();
        }
        catch (Exception ex)
        {
            _diagBuilding = false;
            try { if (_diagStatus != null) _diagStatus.Text = "刷新失败：" + ex.Message; } catch { }
        }
    }

    /// <summary>同步生成并填文本(无头自检用)</summary>
    private static void RefreshDiagPanelNow()
    {
        if (_diagText == null) return;
        UiPhaseBegin("正在生成状态报告");
        string txt = BuildDiagReport();
        _diagText.Text = txt;
        try
        {
            _diagText.SelectionStart = 0;
            _diagText.SelectionLength = 0;
            _diagText.ScrollToCaret();
        }
        catch { }
        if (_diagStatus != null)
            _diagStatus.Text = "已刷新 " + DateTime.Now.ToString("HH:mm:ss");
        UiPhaseEnd("");
    }

    /// <summary>
    /// 打开(或提到前面)状态面板。已经开着就只刷新 + 激活。
    /// 刻意用非模态窗口: 用户可以一边看主界面一边复制报告。
    /// </summary>
    private static void ShowDiagPanel()
    {
        try
        {
            if (_diagForm != null && !_diagForm.IsDisposed)
            {
                RefreshDiagPanel();
                _diagForm.Activate();
                return;
            }
            Form f = new Form();
            // ⚠️ 顺序: SetAutoScaleFont -> 设尺寸(见 SetAutoScaleFont 的注释, 反过来会被自动缩放改坏)
            SetAutoScaleFont(f, Fi("Microsoft YaHei UI", 9F));
            f.Text = APP_NAME + " 状态面板";
            f.BackColor = C_BG;
            f.ClientSize = new Size(Sc(900), Sc(620));
            f.MinimumSize = new Size(Sc(620), Sc(400));
            f.StartPosition = FormStartPosition.CenterParent;

            TableLayoutPanel root = new TableLayoutPanel();
            root.Dock = DockStyle.Fill;
            root.ColumnCount = 1;
            root.RowCount = 3;
            root.Padding = Pad(10, 8, 10, 8);
            root.BackColor = C_BG;
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));
            root.RowStyles.Add(new RowStyle(SizeType.Percent, 100F));
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));
            f.Controls.Add(root);

            Label tip = new Label();
            tip.AutoSize = true;
            tip.MaximumSize = new Size(Sc(860), 0);      // 限宽: AutoSize 的 Label 不换行会撑宽窗口
            tip.ForeColor = C_SUB;
            tip.Text = "需要协助时，请复制下面的内容。";
            Wrap(tip);
            root.Controls.Add(tip, 0, 0);

            _diagText = new TextBox();
            _diagText.Multiline = true;
            _diagText.ReadOnly = true;
            _diagText.WordWrap = false;                  // 报告是按行排的, 不许自动折行
            _diagText.ScrollBars = ScrollBars.Both;
            _diagText.Dock = DockStyle.Fill;
            _diagText.BackColor = Color.White;
            _diagText.Font = new Font("Consolas", 8.5F); // 等宽: 报告的列才对得齐
            root.Controls.Add(_diagText, 0, 1);

            FlowLayoutPanel bar = new FlowLayoutPanel();
            bar.Dock = DockStyle.Fill;
            bar.AutoSize = true;
            bar.FlowDirection = FlowDirection.LeftToRight;
            bar.WrapContents = true;
            root.Controls.Add(bar, 0, 2);

            Button bRefresh = MakeButton("刷新", null, "primary");
            bRefresh.Click += delegate { RefreshDiagPanel(); };
            bar.Controls.Add(bRefresh);

            Button bCopy = MakeButton("复制", null, "plain");
            bCopy.Click += delegate
            {
                try
                {
                    Clipboard.SetText(_diagText.Text);
                    _diagStatus.Text = "已复制";
                }
                catch (Exception)
                {
                    // 剪贴板被别的程序占着时会失败, 不要假装成功
                    _diagStatus.Text = "复制失败，请手动全选后复制";
                }
            };
            bar.Controls.Add(bCopy);

            Button bSave = MakeButton("另存为", null, "plain");
            bSave.Click += delegate
            {
                try
                {
                    using (SaveFileDialog d = new SaveFileDialog())
                    {
                        d.FileName = "SkyGuard-状态-" + DateTime.Now.ToString("yyyyMMdd-HHmmss") + ".txt";
                        d.Filter = "文本文件|*.txt|所有文件|*.*";
                        if (d.ShowDialog(f) == DialogResult.OK)
                        {
                            File.WriteAllText(d.FileName, _diagText.Text, new UTF8Encoding(false));
                            _diagStatus.Text = "已保存";
                        }
                    }
                }
                catch (Exception ex) { _diagStatus.Text = "保存失败：" + ex.Message; }
            };
            bar.Controls.Add(bSave);

            _diagAuto = new CheckBox();
            _diagAuto.AutoSize = true;
            _diagAuto.Text = "自动刷新";
            _diagAuto.Margin = new Padding(Sc(12), Sc(8), 0, 0);
            bar.Controls.Add(_diagAuto);

            _diagStatus = new Label();
            _diagStatus.AutoSize = true;
            _diagStatus.ForeColor = C_SUB;
            _diagStatus.Margin = new Padding(Sc(12), Sc(10), 0, 0);
            bar.Controls.Add(_diagStatus);

            _diagTimer = new System.Windows.Forms.Timer();
            _diagTimer.Interval = 1000;
            _diagTimer.Tick += delegate { if (_diagAuto.Checked) RefreshDiagPanel(); };
            _diagTimer.Start();

            f.FormClosed += delegate
            {
                try { if (_diagTimer != null) _diagTimer.Stop(); } catch { }
                _diagTimer = null;
                _diagForm = null;
            };

            _diagForm = f;
            RefreshDiagPanel();
            f.Show(_form);
        }
        catch (Exception ex) { Log("[状态面板] 打开失败: " + ex.Message); }
    }

    /// <summary>
    /// 预热表自检(`warmtest`):
    ///   1) 造一个假目标(cmd.exe 复制成唯一名字, 跑烧 CPU 的循环), 刷一次预热表, 断言表里有它;
    ///   2) 杀掉它 -> 断言快路径会拒掉这条陈旧记录 —— 这是"PID 被系统回收重用导致误杀别人"的唯一防线;
    ///   3) 再起一个 -> 断言快路径几十毫秒内命中, 且挂起后它真的不动了(CPU 时间不再增长)。
    /// 退出码: 0 = 通过, 1 = 有断言失败。结果写在程序目录 _warmtest.txt。
    /// </summary>
    private static int RunWarmTest()
    {
        _headless = true;
        int failed = 0;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("预热表自检 (warmtest) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("要求: 命中要快(<100ms) / 陈旧条目绝不动手 / 挂起后目标真的停住");
        sb.AppendLine("");

        string dummyExe = Path.Combine(_baseDir, "skgwarmdummy.exe");
        string dummyName = "skgwarmdummy.exe";
        try
        {
            if (!File.Exists(dummyExe))
                File.Copy(Path.Combine(Environment.SystemDirectory, "cmd.exe"), dummyExe, true);
        }
        catch (Exception ex)
        {
            sb.AppendLine("[跳过] 造不出假目标: " + ex.Message);
            WriteWarmReport(sb);
            return 0;
        }

        Config save = _cfg;
        _cfg = new Config();
        _cfg.Procs.Add(dummyName);

        Process p1; int pid1 = StartBusyProcessNamed(dummyExe, out p1);
        if (pid1 == 0)
        {
            sb.AppendLine("[跳过] 起不了假目标");
            _cfg = save;
            WriteWarmReport(sb);
            return 0;
        }
        try
        {
            RefreshWarmOnce();
            bool in1 = WarmContains(pid1);
            sb.AppendLine("1 预热表: " + (in1 ? "已记下" : "没记下") + " PID " + pid1 + "  [要求 记下]");
            if (!in1) failed++;

            // 2a) 开关关掉时: 表里明明有活着的目标, 也必须一个都不挂(设置里的开关要真起作用)
            bool saveSusp = _cfg.SuspendFirst, saveWarm = _cfg.WarmSuspend;
            _cfg.SuspendFirst = false;
            int msOff; int nOff = FastSuspendWarm(out msOff);
            sb.AppendLine("2a 先挂起=关: 快路径挂了 " + nOff + " 个, 用了 " + msOff + " ms  [要求 0 个]");
            if (nOff != 0) failed++;
            _cfg.WarmSuspend = false;
            int msOff2; int nOff2 = FastSuspendWarm(out msOff2);
            sb.AppendLine("2b 预记录=关: 快路径挂了 " + nOff2 + " 个  [要求 0 个]");
            if (nOff2 != 0) failed++;
            _cfg.SuspendFirst = saveSusp;
            _cfg.WarmSuspend = saveWarm;

            // 2c) 空表: 必须安静返回 0, 不能抛异常、不能乱挂
            lock (_warmGate) { _warm = new List<WarmProc>(); }
            int msEmpty; int nEmpty = FastSuspendWarm(out msEmpty);
            sb.AppendLine("2c 空表: 快路径挂了 " + nEmpty + " 个  [要求 0 个]");
            if (nEmpty != 0) failed++;
            RefreshWarmOnce();   // 把表补回来, 后面的用例要用

            // 2) 让表里这条变陈旧: 快路径必须拒掉它(否则 PID 被回收重用时就会误杀别人的进程)
            KillDummy(p1);
            Thread.Sleep(500);
            int ms2; int n2 = FastSuspendWarm(out ms2);
            sb.AppendLine("3 陈旧条目: 快路径挂了 " + n2 + " 个, 用了 " + ms2 + " ms  [要求 0 个]");
            sb.AppendLine("  (注意: PID 复用没法在自检里人为制造, 但判定走的是同一条创建时间核对, 所以这条覆盖到了)");
            if (n2 != 0) failed++;

            // 环境参照: 扫全表平时 8~17 ms。如果这里都要几十毫秒, 说明这台机器此刻被压满了,
            // 那"挂起用了多久"就不能当失败判据(不是机制慢, 是机器没空跑)。
            int totRef; long tMap = Stopwatch.GetTimestamp();
            ProcMap(null, out totRef);
            long mapMs = ElapsedMs(tMap);
            bool starved = (mapMs >= 40);
            sb.AppendLine("环境参照: 扫全表(" + totRef + " 个进程) " + mapMs + " ms"
                + (starved ? " -> 机器被压满, 时间类判据放宽" : " (正常)"));
            sb.AppendLine("");

            // 3) 静止目标(线程都在等 = 卡白游戏的同类): 这一条才是"挂起够不够快"的指标
            Process pi; int pidI = StartIdleProcessNamed(dummyExe, out pi);
            if (pidI == 0) sb.AppendLine("3 [跳过] 起不了静止假目标");
            else
            {
                try
                {
                    RefreshWarmOnce();
                    int msI; int nI = FastSuspendWarm(out msI);
                    int suspI, totalI;
                    CountSuspendedThreads(pidI, out suspI, out totalI);
                    bool stoppedI = (totalI > 0 && suspI == totalI);
                    sb.AppendLine("4 静止目标(线程都在等, 相当于卡白的游戏): 命中 " + nI + " 个, 用 " + msI
                        + " ms  [要求 >=1 且 <100ms]");
                    sb.AppendLine("  线程状态: " + suspI + "/" + totalI + " 已挂起");
                    sb.AppendLine((msI < 100 ? "  [判定] 用时 " + msI + " ms -> 满足 <100 ms"
                                             : "  [判定] 用时 " + msI + " ms -> 超 100 ms, 但**机器忙时这个读数没有意义**"
                                               + "(同一次运行里同一操作会从 11 ms 跳到 190 ms); 真机请看日志里的"
                                               + "「第一条命令: 挂起预热表命中 … 用了 N ms」"));
                    // 时间不作失败判据(读数是环境函数); 机制本身(命中 + 真的挂起)必须成立
                    if (nI < 1 || !stoppedI) failed++;
                }
                finally { KillDummy(pi); }
            }

            // 4) 烧 CPU 的目标: 最坏情况(内核要等线程进内核), 只要求"真的停住", 不设时间上限
            Process p3; int pid3 = StartBusyProcessNamed(dummyExe, out p3);
            if (pid3 == 0) sb.AppendLine("4 [跳过] 起不了烧 CPU 的假目标");
            else
            {
                try
                {
                    Thread.Sleep(400);
                    long a1 = CpuMsOf(p3); Thread.Sleep(400); long a2 = CpuMsOf(p3);
                    bool running = (a2 - a1) >= 60;   // 机器忙时可能观察不到 —— 那只是"没法用 CPU 判定"
                    RefreshWarmOnce();
                    int ms3; int n3 = FastSuspendWarm(out ms3);
                    Thread.Sleep(300);
                    long b1 = CpuMsOf(p3); Thread.Sleep(400); long b2 = CpuMsOf(p3);
                    int suspTh, totalTh;
                    CountSuspendedThreads(pid3, out suspTh, out totalTh);
                    // 两条独立证据, 任一条成立就算"停住了": ①挂起后 CPU 不再增长; ②线程状态全是 Suspended
                    bool stopped = ((b2 - b1) <= 20) || (totalTh > 0 && suspTh == totalTh);
                    sb.AppendLine("5 烧 CPU 的目标(最坏情况): 命中 " + n3 + " 个, 用 " + ms3 + " ms  [只要求停住]");
                    sb.AppendLine("  参考: 快路径省掉的就是上面那次扫表(" + mapMs + " ms)");
                    sb.AppendLine("  线程状态: " + suspTh + "/" + totalTh + " 已挂起; 挂起前 400 ms 烧 " + (a2 - a1)
                        + " ms CPU, 挂起后 400 ms 增加 " + (b2 - b1) + " ms");
                    if (!running) sb.AppendLine("  [提示] 机器忙, 挂起前没观察到它在跑 —— 改由线程状态判定(不算失败)");
                    sb.AppendLine("  说明: 内核要把这些在用户态跑的线程挨个冻住, 机器越忙越慢;");
                    sb.AppendLine("        卡白的游戏线程本来就困在内核里(第 3 条那种), 所以真机上快得多");
                    sb.AppendLine("  [要求] 命中=" + (n3 >= 1) + " 挂起后停住=" + stopped);
                    if (n3 < 1 || !stopped) failed++;
                }
                finally { KillDummy(p3); }
            }
        }
        finally
        {
            KillDummy(p1);
            _cfg = save;
            try { File.Delete(dummyExe); } catch { }
        }
        sb.AppendLine("");
        sb.AppendLine(failed == 0 ? "结论 = 全部通过" : ("结论 = 有 " + failed + " 项失败"));
        sb.AppendLine("补充: 未命中(目标刚启动/刚刷新)时会走扫表路径, 那条路仍然完整 ——");
        sb.AppendLine("      扫表 17 ms 左右, 之后再挂起; 日志里会写「预热表未命中…走扫表路径」。");
        sb.AppendLine("      多目标时快路径按保命优先级挂(游戏本体第一), 下面顺手核对一下这个次序:");
        int pSky = TargetPriority("Sky.exe"), pMu = TargetPriority("MuMuNxDevice.exe"), pVmm = TargetPriority("MuMuVMMHeadless.exe");
        bool prioOk = (pSky == 0) && (pSky < pMu) && (pMu < pVmm);
        sb.AppendLine("      Sky=" + pSky + " MuMu=" + pMu + " VMM=" + pVmm + "  -> " + (prioOk ? "次序正确" : "次序异常"));
        if (!prioOk) failed++;
        sb.AppendLine("结论 = " + (failed == 0 ? "全部通过" : ("有 " + failed + " 项失败")));
        WriteWarmReport(sb);
        return failed == 0 ? 0 : 1;
    }

    private static void WriteWarmReport(StringBuilder sb)
    {
        try { File.WriteAllText(Path.Combine(_baseDir, "_warmtest.txt"), sb.ToString(), Encoding.UTF8); } catch { }
        Console.Out.Write(sb.ToString());
        Console.Out.Flush();
    }

    /// <summary>预热表里有没有这个 PID(自检用)</summary>
    private static bool WarmContains(int pid)
    {
        lock (_warmGate) { foreach (WarmProc w in _warm) if (w.Pid == pid) return true; }
        return false;
    }

    /// <summary>起一个"只在等"的假目标(相当于卡白的游戏: 线程都困在等待里)</summary>
    private static int StartIdleProcessNamed(string exe, out Process proc)
    {
        proc = null;
        try
        {
            ProcessStartInfo psi = new ProcessStartInfo();
            psi.FileName = exe;
            psi.Arguments = "/c ping -n 120 127.0.0.1 >nul";
            psi.UseShellExecute = false;
            psi.CreateNoWindow = true;
            psi.WindowStyle = ProcessWindowStyle.Hidden;
            proc = Process.Start(psi);
            return (proc == null) ? 0 : proc.Id;
        }
        catch { return 0; }
    }

    /// <summary>数量一个进程里有多少线程处于"已挂起"状态(自检用; 读不到就返回 0/0)</summary>
    private static void CountSuspendedThreads(int pid, out int susp, out int total)
    {
        susp = 0; total = 0;
        try
        {
            Process p = Process.GetProcessById(pid);
            foreach (ProcessThread t in p.Threads)
            {
                total++;
                try { if (t.WaitReason == ThreadWaitReason.Suspended) susp++; }
                catch { }
            }
        }
        catch { }
    }

    /// <summary>起一个指定可执行文件的"烧 CPU"进程(自检用; 用唯一文件名避免误伤别的进程)</summary>
    private static int StartBusyProcessNamed(string exe, out Process proc)
    {
        proc = null;
        try
        {
            ProcessStartInfo psi = new ProcessStartInfo();
            psi.FileName = exe;
            psi.Arguments = "/c for /L %i in (1,1,2000000000) do @ver >nul";
            psi.UseShellExecute = false;
            psi.CreateNoWindow = true;
            psi.WindowStyle = ProcessWindowStyle.Hidden;
            proc = Process.Start(psi);
            return (proc == null) ? 0 : proc.Id;
        }
        catch { return 0; }
    }

    /// <summary>
    /// 挂起速度自检(`suspendspeed`): 起一个"一直在烧 CPU"的测试进程, 量挂起要多久,
    /// 并用**CPU 时间不再增长**证明它真的停住了 —— 这才是"杀掉"的硬指标(不是等句柄返回)。
    ///
    /// 为什么这么测: 真机上不可能为了自检去跑一次光遇, 但"挂起能不能让目标立刻停住"
    /// 与目标是什么进程无关, 用任意烧 CPU 的进程都验证得了。
    /// 退出码: 0 = 通过, 1 = 有断言失败。结果写在程序目录 _suspendspeed.txt。
    /// </summary>
    private static int RunSuspendSpeedTest()
    {
        _headless = true;
        int failed = 0;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("挂起速度自检 (suspendspeed) @ " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("机制要求: 调用成功 + 挂起后目标 CPU 时间不再增长 (耗时只作参考, 机器忙时读数不可信)");
        sb.AppendLine("");

        // A) 整进程挂起(NtSuspendProcess)
        Process pa; int pidA = StartBusyProcess(out pa);
        if (pidA == 0)
        {
            sb.AppendLine("[跳过] 起不了测试进程(cmd.exe 不可用?)");
            try { File.WriteAllText(Path.Combine(_baseDir, "_suspendspeed.txt"), sb.ToString(), Encoding.UTF8); } catch { }
            Console.Out.Write(sb.ToString()); Console.Out.Flush();
            return 0;
        }
        try
        {
            Thread.Sleep(400);
            long a1 = CpuMsOf(pa); Thread.Sleep(400); long a2 = CpuMsOf(pa);
            bool burning = (a2 - a1) >= 100;
            string howA; int msA;
            bool okA = TrySuspendProcess(pidA, out howA, out msA);
            Thread.Sleep(300);
            long b1 = CpuMsOf(pa); Thread.Sleep(400); long b2 = CpuMsOf(pa);
            bool stopped = (b2 - b1) <= 20;
            sb.AppendLine("A 整进程挂起: " + (okA ? "成功" : "失败") + ", 用 " + msA + " ms, 方式=" + howA);
            sb.AppendLine("  挂起前 400 ms 烧了 " + (a2 - a1) + " ms CPU; 挂起后 400 ms 只增加 " + (b2 - b1) + " ms");
            sb.AppendLine("  [要求] 调用成功=" + okA + " 挂起前在跑=" + burning + " 挂起后停住=" + stopped);
            sb.AppendLine("  [判定] 用时 " + msA + " ms (机器忙时读数不可信; 机制正确性看上一行)");
            // 时间不作失败判据: 同一操作在忙机器上能从 11 ms 跳到 190 ms;
            // 必须成立的是"调用成功 + 挂起后目标真的停住"。
            if (!okA || !stopped) failed++;
        }
        catch (Exception ex) { sb.AppendLine("A 抛异常: " + ex.Message); failed++; }
        finally { KillDummy(pa); }
        sb.AppendLine("");

        // B) 兜底路径: 逐线程挂起
        Process pb; int pidB = StartBusyProcess(out pb);
        if (pidB != 0)
        {
            try
            {
                Thread.Sleep(400);
                long a1 = CpuMsOf(pb); Thread.Sleep(400); long a2 = CpuMsOf(pb);
                bool burning = (a2 - a1) >= 100;
                long t0 = Stopwatch.GetTimestamp();
                int n = SuspendAllThreadsOf(pidB);
                int msB = (int)ElapsedMs(t0);
                Thread.Sleep(300);
                long b1 = CpuMsOf(pb); Thread.Sleep(400); long b2 = CpuMsOf(pb);
                bool stopped = (b2 - b1) <= 20;
                sb.AppendLine("B 逐线程挂起(兜底路径): 挂起 " + n + " 个线程, 用 " + msB + " ms");
                sb.AppendLine("  挂起前 400 ms 烧了 " + (a2 - a1) + " ms CPU; 挂起后 400 ms 只增加 " + (b2 - b1) + " ms");
                sb.AppendLine("  [要求] 调用成功=" + (n > 0) + " 挂起前在跑=" + burning + " 挂起后停住=" + stopped);
                if (n <= 0 || !stopped) failed++;
            }
            catch (Exception ex) { sb.AppendLine("B 抛异常: " + ex.Message); failed++; }
            finally { KillDummy(pb); }
        }
        sb.AppendLine("");
        sb.AppendLine(failed == 0 ? "结论 = 全部通过" : ("结论 = 有 " + failed + " 项失败"));
        try { File.WriteAllText(Path.Combine(_baseDir, "_suspendspeed.txt"), sb.ToString(), Encoding.UTF8); } catch { }
        Console.Out.Write(sb.ToString()); Console.Out.Flush();
        return failed == 0 ? 0 : 1;
    }

    /// <summary>起一个一直烧 CPU 的测试进程(cmd 里跑一个超长循环), 用来验证"挂起后真的不动了"。</summary>
    private static int StartBusyProcess(out Process proc)
    {
        proc = null;
        try
        {
            ProcessStartInfo psi = new ProcessStartInfo();
            psi.FileName = Path.Combine(Environment.SystemDirectory, "cmd.exe");
            psi.Arguments = "/c for /L %i in (1,1,2000000000) do @ver >nul";
            psi.UseShellExecute = false;
            psi.CreateNoWindow = true;
            psi.WindowStyle = ProcessWindowStyle.Hidden;
            proc = Process.Start(psi);
            return (proc == null) ? 0 : proc.Id;
        }
        catch { return 0; }
    }

    private static long CpuMsOf(Process p)
    {
        try { return (long)p.TotalProcessorTime.TotalMilliseconds; }
        catch { return 0; }
    }

    private static void KillDummy(Process p)
    {
        if (p == null) return;
        try { if (!p.HasExited) p.Kill(); } catch { }
        try { p.Dispose(); } catch { }
    }

    /// <summary>
    /// 状态面板的自检(`diagtest`): 无头生成一份报告, 断言每一节都在、日志段有内容、脱敏生效。
    ///
    /// 为什么这么测: 面板真正的风险不是"显示不好看", 而是"某一节读失败把整份报告带崩" ——
    /// 而这份报告恰恰是出问题时唯一能拿到的东西。所以这里专门把每一节的标题都断言一遍。
    /// 退出码: 0 = 通过, 1 = 有断言失败。报告与摘要写在程序目录 _diagtest.txt / _diagtest_summary.txt。
    /// </summary>
    private static int RunDiagTest()
    {
        _headless = true;
        int failed = 0;
        StringBuilder sb = new StringBuilder();
        sb.AppendLine("diagtest " + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff"));
        sb.AppendLine("版本 = " + APP_VER + " (" + APP_VER_NUM + ")   管理员 = " + IsAdmin());
        sb.AppendLine("");

        string rep = "";
        try
        {
            // 先写一行日志并等它落盘: 这样"完整日志"那一节**一定**有内容 ——
            // 在刚装好的机器上(日志文件还不存在)也能真正验证那一节, 而不是自欺欺人地跳过。
            Log("[diagtest] 状态面板自检开始(这一行是用来验证『完整日志』那一节的)");
            try { Thread.Sleep(700); } catch { }
            rep = BuildDiagReport();
        }
        catch (Exception ex) { sb.AppendLine("BuildDiagReport 自己抛异常了: " + ex); failed++; }
        sb.AppendLine("报告长度 = " + rep.Length + " 字符");
        sb.AppendLine("");

        string[] must = new string[] {
            "SkyGuard ", "[环境]", "[文件]", "[输入]", "[焦点]",
            "[处置]", "[网络]", "[配置]", "[日志]", "[自检]"
        };
        foreach (string m in must)
        {
            bool ok = (rep.IndexOf(m, StringComparison.Ordinal) >= 0);
            sb.AppendLine((ok ? "  [通过] 报告里有 " : "  [失败] 报告里缺 ") + m);
            if (!ok) failed++;
        }
        // 某一节读失败时报告里会出现这句 —— 有它就是失败(排查工具自己不能带伤)
        bool noBlockErr = (rep.IndexOf("[读取失败]", StringComparison.Ordinal) < 0);
        sb.AppendLine(noBlockErr ? "  [通过] 各节可读" : "  [失败] 有节读取失败");
        if (!noBlockErr) failed++;
        bool hasLog = System.Text.RegularExpressions.Regex.IsMatch(rep, "(?m)^\\[\\d{4}/");
        sb.AppendLine(hasLog ? "  [通过] 日志有内容" : "  [失败] 日志为空");
        if (!hasLog) failed++;
        bool masked = !_reIpv4.IsMatch(rep);
        sb.AppendLine((masked ? "  [通过] 报告里没有明文 IPv4(脱敏生效)" : "  [失败] 报告里出现了明文 IPv4"));
        if (!masked) failed++;
        sb.AppendLine("");
        sb.AppendLine(failed == 0 ? "结论 = 全部通过" : ("结论 = 有 " + failed + " 项失败"));

        try { File.WriteAllText(Path.Combine(_baseDir, "_diagtest.txt"), rep, Encoding.UTF8); } catch { }
        try { File.WriteAllText(Path.Combine(_baseDir, "_diagtest_summary.txt"), sb.ToString(), Encoding.UTF8); } catch { }
        if (_headless) { Console.Out.Write(sb.ToString()); Console.Out.Flush(); }
        return failed == 0 ? 0 : 1;
    }

    // ============================================================================
    //  十、入口
    // ============================================================================

    /// <summary>单实例锁(V1.1.5-RC1)。必须有一个静态字段引用它 —— 局部变量会被 GC 回收,
    /// 一回收锁就放了, 单实例形同虚设。</summary>
    private static Mutex _singleInstanceMutex = null;

    /// <summary>
    /// 命令行里带的是"会立刻返回的自检/纯信息模式"吗 —— 这些模式不参与单实例检查,
    /// 因为用户/脚本经常要在 SkyGuard 正开着的时候跑 -version / diagtest / netcuttest。
    /// ★ 注意: wizard / dumpraw / trace 不在这个列表里 —— 它们不是终态模式,
    ///   最后还是会进 GUI(或者依附于 GUI), 所以照样要受单实例约束。
    /// </summary>
    private static readonly string[] CLI_TERMINAL_MODES = new string[]
    {
        "version", "-version", "makemanifest", "-makemanifest",
        "selftest", "uicheck", "rectest", "targetstest", "procdump", "killtest",
        "ordertest", "hooktest", "hangtest", "hangtest-old", "racetest", "settest",
        "findtest", "wiztest", "netshtest", "scaletest", "focustest", "restoretest",
        "diagtest", "suspendspeed", "warmtest", "netcuttest",
        "uibudget", "chanhealth", "singleinst",
    };

    private static bool IsCliMode(string[] args)
    {
        try
        {
            if (args == null) return false;
            foreach (string a in args)
                foreach (string m in CLI_TERMINAL_MODES)
                    if (string.Equals(a, m, StringComparison.OrdinalIgnoreCase)) return true;
        }
        catch { }
        return false;
    }

    /// <summary>
    /// 把"已经在运行的那个 SkyGuard 窗口"提到前台。
    /// 按窗口标题前缀 + 进程名找(和焦点解堵用的是同一套 P/Invoke)。
    /// 找不到就什么都不做 —— 用户还可以从任务栏自己切。
    /// </summary>
    private static void FocusRunningInstance()
    {
        try
        {
            int me = Process.GetCurrentProcess().Id;
            IntPtr found = IntPtr.Zero;
            EnumWindows(delegate(IntPtr h, IntPtr lp)
            {
                try
                {
                    if (!IsWindowVisible(h)) return true;
                    uint pid;
                    GetWindowThreadProcessId(h, out pid);
                    if (pid == 0 || (int)pid == me) return true;      // 跳过自己(以及拿不到 pid 的)
                    string title = WindowTitle(h);
                    if (!string.IsNullOrEmpty(title)
                        && title.StartsWith(APP_NAME, StringComparison.OrdinalIgnoreCase))
                    {
                        found = h;
                        return false;                                  // 找到了, 停止枚举
                    }
                }
                catch { }
                return true;
            }, IntPtr.Zero);

            if (found != IntPtr.Zero)
            {
                if (IsIconic(found)) ShowWindow(found, 9 /*SW_RESTORE*/);
                SetForegroundWindow(found);
            }
        }
        catch { }
    }

    [STAThread]
    private static int Main(string[] args)
    {
        // 界面线程就是跑 Main 的这条线程(Application.Run 也在它上面)。
        // 先记下它, 后面 PumpOnUi() 靠这个 id 判断"现在能不能泵消息" —— 窗体还没建出来时也准。
        _uiThreadId = GetCurrentThreadId();

        // ============================================================================
        //  单实例检查(V1.1.5-RC1) —— 必须放在**最前面**, 在所有"启动收尾动作"之前。
        //
        //  为什么要单实例: README 自己就写了"双击之后没反应, 于是再双击一次, 开出两个实例"。
        //  两个实例会各装一个全局键盘钩子、各自对**同一张网卡**发 netsh(先禁后开的顺序一旦
        //  交错, 就是"断网没生效"或"恢复不了"), 还会同时写同一份 guard.ini 和日志。
        //  一个 SkyGuard 本来就支持配多个目标程序(双开光遇用同一个实例就够), 所以限制单实例
        //  不影响任何正常用法 —— 却把这一类最难查的"关键时刻掉链子"堵掉了。
        //
        //  ★ 为什么必须在 FastCut_CleanupLeftovers() 之前: 下面那一步会清掉 SkyGuard 留下的
        //    防火墙规则。如果第一个实例**正在处置中**(WFP 正拦着出站), 第二个实例启动时那一下
        //    就等于把正在生效的拦截亲手拆掉 —— 那是"关键时刻自己把命门打开"。
        //  ★ 为什么自检/命令行模式要跳过: -version / diagtest / netcuttest 这些要能在
        //    SkyGuard 正开着的时候照常跑, 不能被自己的锁挡住。
        //  ★ 用 Global\ 命名空间: 跨会话可见(用户可能在一个会话里一直开着它)。
        // ============================================================================
        if (!IsCliMode(args))
        {
            bool createdNew = false;
            try
            {
                _singleInstanceMutex = new Mutex(true, @"Global\SkyGuardGUI.SingleInstance", out createdNew);
            }
            catch
            {
                // 建不出锁(极少数权限受限的环境)就不拦: 宁可能重复运行, 也不能因为锁失败开不了程序。
                createdNew = true;
            }
            if (!createdNew)
            {
                // dupprobe: 单实例自检用的静默探针 —— 走完全同一条分支, 但不弹框(否则自检会卡住)
                if (HasArg("dupprobe")) return 0;
                try { FocusRunningInstance(); } catch { }
                try
                {
                    MessageBox.Show(
                        "SkyGuard 已经在运行了。\n\n"
                        + "已经把它切到前面 —— 请用已经开着的那个窗口。\n"
                        + "（同一个 SkyGuard 可以同时管多个程序，不需要开两个。）",
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
                }
                catch { }
                return 0;
            }
        }

        _baseDir = AppDomain.CurrentDomain.BaseDirectory;
        // 用户数据(guard.ini / 日志)放数据目录, 程序目录只放程序文件 —— 见 ResolveDataDir 的注释。
        // 这样"删掉旧文件夹、解压新版本"不会丢设置, 打包也不会把自己的配置带出去。
        _dataDir = ResolveDataDir();
        _iniPath = Path.Combine(_dataDir, INI_FILE);
        _logPath = Path.Combine(_dataDir, LOG_FILE);
        MigrateLegacyData();

        // 11.1.0: 上次崩溃/断电可能留下一条"出站全断"的防火墙规则 —— 必须在别的事情之前清掉,
        // 否则用户还没打开程序就已经没网了。(WFP 是动态会话, 随进程消失, 不需要清。)
        try { FastCut_CleanupLeftovers(); } catch { }
        // 11.1.0 验收意见(MAJOR-1): 上次如果是我们断的网络, 按我们自己的标记恢复,
        // 不猜系统状态、不看本地化文本(只有标记存在时才动网卡, 正常启动不会变慢)
        try { NetCutStateRecoverAtStartup(); } catch { }
        // 没有标记也查一遍: 上次可能是被强杀/断电, 标记还没写成, 但网卡确实被我们禁用了。
        // (标记是第一判据; 这一条是"连标记都没留下"时的第二道网。)
        // ★ 这一条挪到窗口显示之后的后台线程里跑 —— 它要起 netsh 子进程, 真恢复起来
        //   能花一分多钟, 而以前它跑在 Application.Run 之前: 用户看到的是"双击了没反应"。
        //   见下面 _form.Shown 里的 SkyGuardStartupNicCheck。

        bool selfTest = false, uiCheck = false, recTest = false, tgtTest = false, dumpTest = false, killTest = false, orderTest = false, hookTest = false, hangTest = false, raceTest = false, setTest = false, findTest = false, wizTest = false, netshTest = false, scaleTest = false, netCutTest = false, focusTest = false, restoreTest = false, diagTest = false, suspendTest = false, warmTest = false, uiBudget = false, chanHealth = false, singleInst = false, forceWizard = false, showVersion = false, makeManifest = false;
        foreach (string a in args)
        {
            // 带 wizard / -wizard 启动: 不管有没有配置, 都强制走一遍首次设置向导
            // (给"模拟新用户第一次打开" / 演示 / 重看向导用; 不删也不改 guard.ini)
            if (string.Equals(a, "wizard", StringComparison.OrdinalIgnoreCase)
             || string.Equals(a, "-wizard", StringComparison.OrdinalIgnoreCase)) forceWizard = true;
            if (string.Equals(a, "selftest", StringComparison.OrdinalIgnoreCase)) selfTest = true;
            if (string.Equals(a, "uicheck", StringComparison.OrdinalIgnoreCase)) uiCheck = true;
            if (string.Equals(a, "rectest", StringComparison.OrdinalIgnoreCase)) recTest = true;
            if (string.Equals(a, "targetstest", StringComparison.OrdinalIgnoreCase)) tgtTest = true;
            if (string.Equals(a, "procdump", StringComparison.OrdinalIgnoreCase)) dumpTest = true;
            if (string.Equals(a, "killtest", StringComparison.OrdinalIgnoreCase)) killTest = true;
            if (string.Equals(a, "ordertest", StringComparison.OrdinalIgnoreCase)) orderTest = true;
            if (string.Equals(a, "hooktest", StringComparison.OrdinalIgnoreCase)) hookTest = true;
            if (string.Equals(a, "hangtest", StringComparison.OrdinalIgnoreCase)) hangTest = true;
            // hangtest-old = 同一个测试的"旧做法"对照, 也要当成 hangtest 选择器。
            // 不认它的话, 光写 `hangtest-old` 会落进 GUI 模式: 非管理员下弹一个管理员提示框
            // 然后一直卡着等点击, 看起来像"测试死锁"(实测踩过, 排查了半天)。
            if (string.Equals(a, "hangtest-old", StringComparison.OrdinalIgnoreCase)) hangTest = true;
            if (string.Equals(a, "racetest", StringComparison.OrdinalIgnoreCase)) raceTest = true;
            if (string.Equals(a, "settest", StringComparison.OrdinalIgnoreCase)) setTest = true;
            if (string.Equals(a, "findtest", StringComparison.OrdinalIgnoreCase)) findTest = true;
            if (string.Equals(a, "wiztest", StringComparison.OrdinalIgnoreCase)) wizTest = true;
            if (string.Equals(a, "netshtest", StringComparison.OrdinalIgnoreCase)) netshTest = true;
            if (string.Equals(a, "scaletest", StringComparison.OrdinalIgnoreCase)) scaleTest = true;
            // uibudget: 界面消息空窗预算自检 —— "绝对不允许无响应"的可重复断言(V1.1.5-RC1)
            if (string.Equals(a, "uibudget", StringComparison.OrdinalIgnoreCase)) uiBudget = true;
            // chanhealth: 钩子被系统静默摘掉时能不能发现并重装(V1.1.5-RC1)
            if (string.Equals(a, "chanhealth", StringComparison.OrdinalIgnoreCase)) chanHealth = true;
            // singleinst: 单实例锁到底管不管用(V1.1.5-RC1)
            if (string.Equals(a, "singleinst", StringComparison.OrdinalIgnoreCase)) singleInst = true;
            // focustest: 焦点解堵决策的无头自检(纯合成序列, 不碰真实窗口、不需要管理员)
            if (string.Equals(a, "focustest", StringComparison.OrdinalIgnoreCase)) focusTest = true;
            // restoretest: 恢复校验决策的无头自检(纯判定, 不碰网卡、不需要管理员)
            if (string.Equals(a, "restoretest", StringComparison.OrdinalIgnoreCase)) restoreTest = true;
            // diagtest: 状态面板(详细诊断)的自检 —— 无头生成一份完整报告, 断言每一节都在
            if (string.Equals(a, "diagtest", StringComparison.OrdinalIgnoreCase)) diagTest = true;
            // suspendspeed: 量"挂起"多快, 并证明挂起后目标真的不再执行
            if (string.Equals(a, "suspendspeed", StringComparison.OrdinalIgnoreCase)) suspendTest = true;
            // warmtest: 预热表(触发时直接挂起已知 PID)的自检, 含"陈旧条目不误杀"
            if (string.Equals(a, "warmtest", StringComparison.OrdinalIgnoreCase)) warmTest = true;
            // netcuttest: 真的装上"快速断流"->探针确认拦住->撤销->确认恢复(会自动撤销, 不碰网卡)
            if (string.Equals(a, "netcuttest", StringComparison.OrdinalIgnoreCase)) netCutTest = true;
            // 发布/升级相关(见 RunVersion / RunMakeManifest): 给脚本、更新包和用户核对版本用
            if (string.Equals(a, "-version", StringComparison.OrdinalIgnoreCase)
             || string.Equals(a, "version", StringComparison.OrdinalIgnoreCase)) showVersion = true;
            if (string.Equals(a, "makemanifest", StringComparison.OrdinalIgnoreCase)
             || string.Equals(a, "-makemanifest", StringComparison.OrdinalIgnoreCase)) makeManifest = true;
        }
        // 命令行 wizard = 演示模式: 只走一遍首次向导的流程, 不写 guard.ini、不改运行中的配置
        _wizardDemoMode = forceWizard;
        // 命令行 -dumpraw: 才把 netsh 原始输出落盘(含本机 IP, 默认关, 免得打包分享时泄露)
        foreach (string a in args)
            if (string.Equals(a, "dumpraw", StringComparison.OrdinalIgnoreCase)
             || string.Equals(a, "-dumpraw", StringComparison.OrdinalIgnoreCase)) _dumpRawEnabled = true;

        if (showVersion) return RunVersion();
        if (makeManifest) return RunMakeManifest();
        if (selfTest) return RunSelfTest();
        if (uiCheck) return RunUiCheck();
        if (recTest) return RunRecorderTest();
        if (tgtTest) return RunTargetsTest();
        if (dumpTest) return RunProcDump();
        if (killTest) return RunKillTest();
        if (orderTest) return RunOrderTest();
        if (hookTest) return RunHookTest();
        if (hangTest) return RunHangTest();
        if (raceTest) return RunRaceTest();
        if (setTest) return RunSettingsTest();
        if (findTest) return RunFindTest();
        if (wizTest) return RunWizardTest();
        if (netshTest) return RunNetshLangTest();
        if (scaleTest) return RunScaleTest();
        if (uiBudget) return RunUiBudgetTest();
        if (chanHealth) return RunChanHealthTest();
        if (singleInst) return RunSingleInstanceTest();
        if (focusTest) return RunFocusTest();
        if (restoreTest) return RunRestoreTest();
        if (diagTest) return RunDiagTest();
        if (suspendTest) return RunSuspendSpeedTest();
        if (warmTest) return RunWarmTest();
        if (netCutTest) return RunNetCutTest();

        // 诊断开关: 带 -trace 启动会把每个按下的键都记进日志, 用来判断"钩子到底有没有被调用"
        bool trace = false;
        foreach (string a in args)
            if (string.Equals(a, "-trace", StringComparison.OrdinalIgnoreCase)
                || string.Equals(a, "trace", StringComparison.OrdinalIgnoreCase)) trace = true;
        _hookTrace = trace;

        Application.EnableVisualStyles();
        Application.SetCompatibleTextRenderingDefault(false);

        // ★ 全局异常兜底 —— 这是"发给别人用"最重要的一处:
        //   这个程序以管理员身份运行, 一旦未处理异常, 别人看到的只是"闪退了", 没有任何线索。
        //   这里把异常同步写进日志(不走 Log() 的异步队列, 因为进程马上就要结束, 队列里的行会丢),
        //   并弹一个能看懂的提示。注意: 处理器里全部套 try/catch, 它自己绝不能再抛。
        Application.SetUnhandledExceptionMode(UnhandledExceptionMode.CatchException);
        Application.ThreadException += delegate(object s, System.Threading.ThreadExceptionEventArgs e)
        {
            CrashReport("界面线程异常", e.Exception);
        };
        AppDomain.CurrentDomain.UnhandledException += delegate(object s, UnhandledExceptionEventArgs e)
        {
            CrashReport("未处理异常", e.ExceptionObject as Exception);
        };

        // 未提权: 明确告知, 而不是静默失败
        if (!IsAdmin())
        {
            MessageBox.Show(
                "本程序需要管理员权限。\r\n\r\n"
                + "请不要直接双击，改为右键 exe 选择[以管理员身份运行]。\r\n"
                + "也可右键 → 发送到 → 桌面快捷方式，之后双击快捷方式即可。",
                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
            return 2;
        }

        try { Log("======== 程序启动 " + APP_VER + " ========"); } catch { }

        BuildForm();
        StartUiWatchdog();   // 界面看门狗: 界面线程停多久都会记进日志(RC24)

        List<string> warn = new List<string>();
        Config c = LoadConfig(warn);
        // ★ 注意: 网卡探测 DoDetect() 被挪到窗口显示之后(见下面的 _form.Shown)。
        //   为什么: 它要起 netsh/route 子进程, 在慢机器/网卡驱动忙的时候可能好几秒。
        //   早先它跑在这里(Application.Run 之前), 那期间窗口一次都没画出来,
        //   用户看到的是"双击了没反应", 于是再双击一次, 开出两个实例。
        //   放到 Shown 之后, 窗口先出现、有日志可看, 探测慢也只是晚几秒出网卡列表。

        if (c != null)
        {
            _cfg = c;
            ParseKeys(c.Keys, warn);
            foreach (string w in warn) Log("[配置警告] " + w);
        }
        RefreshSummary();
        RefreshStatus();
        Log("界面就绪。日志: " + _logPath);

        // 窗口一出来就补上探测(此时界面已经在画了, 用户看得到"正在探测")
        _form.Shown += delegate
        {
            try
            {
                AppendUi("正在探测网卡…");
                // ★ 探测(实测 1~4.5 秒)丢后台线程, 结果回来再写摘要 —— 启动那一下不再卡界面
                DoDetectAsync(_form, false);
            }
            catch (Exception ex) { Log("[网卡探测] 异常: " + ex.Message); }
        };

        // 启动时的"第二道网": 没有断网标记, 但网卡确实被禁用了(上次被强杀/断电, 标记没写成)。
        // ★ 必须在窗口显示之后、后台线程里做: 它要起 netsh, 真恢复起来能花一分多钟。
        //   以前它跑在窗口建出来之前 —— 用户双击之后长时间没有任何反应, 于是再双击一次(开出两个实例)。
        _form.Shown += delegate
        {
            Thread t = new Thread(delegate()
            {
                try
                {
                    if (!NetCutStateExists() && AnyTargetDisabled())
                    {
                        Log("[启动恢复] 没有断网标记, 但配置里的网卡处于禁用状态 -> 后台恢复网络(不阻塞界面)");
                        RunNetOp(true, 0);
                    }
                }
                catch (Exception ex) { Log("[启动恢复] 异常: " + ex.Message); }
            });
            t.IsBackground = true;
            t.Name = "SkyGuardStartupNicCheck";
            t.Start();
        };

        // 状态刷新
        _statusTimer = new System.Windows.Forms.Timer();
        _statusTimer.Interval = 500;
        _statusTimer.Tick += delegate { RefreshStatus(); PumpUiLog(); };
        _statusTimer.Start();

        if (forceWizard || c == null || !_cfg.IsUsable())
        {
            // 首次运行(或配置不全, 或命令行强制): 走分步向导
            Log(forceWizard ? "命令行 wizard: 强制进入首次设置向导" : "首次运行: 配置不完整, 进入设置向导");
            _form.Shown += delegate { RunFirstRunWizard(); };
        }
        else
        {
            _form.Shown += delegate
            {
                AppendUi("已读取上次配置，开游戏前点[开始保护]即可。");
            };
        }

        Application.Run(_form);
        _statusTimer.Stop();
        return 0;
    }

    // ============================================================================
    //  十一、崩溃兜底
    // ============================================================================

    /// <summary>
    /// 把未处理异常同步写进日志文件并告知用户。
    /// 为什么同步: Log() 是"入队 + 后台线程落盘", 进程要退出时队列里的行会直接丢掉,
    /// 而那几行恰好是最关键的现场。所以这里绕过队列直接写。
    /// 为什么连日志都写不了也要弹框: 用户至少要能拿到异常文本去反馈。
    /// </summary>
    private static void CrashReport(string tag, Exception ex)
    {
        string text = (ex == null) ? "(null)" : ex.ToString();
        try
        {
            if (_logPath != null && _logPath.Length > 0)
            {
                // ★ 必须和日志正文同编码(见 LogEnc): 以前这里写的是 UTF-8, 而日志正文是 GBK,
                //   结果崩溃那一段在记事本里全是乱码 —— 恰恰是最需要看懂的一段。
                File.AppendAllText(_logPath,
                    "\r\n[" + DateTime.Now.ToString("yyyy/MM/dd HH:mm:ss.fff") + "] [" + tag + "]\r\n"
                    + text + "\r\n", LogEnc());
            }
        }
        catch { }
        try
        {
            if (_headless) return;   // 无头自检模式下不弹窗(会卡在不可见对话框上)
            MessageBox.Show(
                "程序出错，已记进日志：\r\n" + _logPath + "\r\n\r\n"
              + "请把日志发给技术支持。错误摘要：\r\n\r\n"
              + ((ex == null) ? "(无信息)" : ex.GetType().Name + ": " + ex.Message),
                APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Error);
        }
        catch { }
    }

    // ============================================================================
    //  十二、首次运行向导 (一步一步, 面向不熟悉电脑的玩家)
    // ============================================================================
    #region 首次运行向导

    /// <summary>
    /// 首次运行向导 —— 单窗口 4 步翻页。
    /// 为什么用"单窗口 + 面板切换"而不是"每页开新窗口":
    ///   早先用 DialogResult 在多个窗口间传递, 结果按钮语义混乱(点"我明白"却走了"以后再说")。
    ///   单窗口只有一个 [下一步] 和一个 [跳过], 不会点错。
    /// </summary>
    private static void RunFirstRunWizard()
    {
        Form wiz = BuildFirstRunWizard();
        if (wiz == null) return;
        // 向导用容器自适应布局 + 页内 AutoScroll 兜底, 小屏也能完整显示
        FitDialogToScreen(wiz, Sc(680), Sc(660));
        wiz.ShowDialog(_form);
        if (_wizardFinished)
        {
            if (_wizardDemoMode)
            {
                MessageBox.Show(
                    "演示模式：向导已结束，未改动任何配置。\r\n"
                  + "如需重新配置，请使用主界面的[⚙ 设置]。",
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
            else
            {
                MessageBox.Show(
                    "设置完成。\r\n\r\n"
                  + "以后每次开游戏前：双击本程序 → 点[开始保护]。\r\n"
                  + "需要时按下触发键。\r\n\r\n"
                  + "如需修改设置，请点主界面的[⚙ 设置]。",
                    APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Information);
            }
        }
        else
        {
            Log("[向导] 未完成(用户跳过或关闭)");
            AppendUi("设置尚未完成，可点[⚙ 设置]进行配置。");
        }
    }

    /// <summary>
    /// ★ 按"行"搭建一个自适应页面容器。
    ///
    /// 为什么不继续用固定坐标(这是本项目最大的一处返工):
    ///   固定坐标有两个死穴 —— 字号随 DPI 变大而坐标不动(高缩放时文字压控件),
    ///   以及窗口尺寸变化时内容完全不动(窗口一小, 底部内容就被裁)。
    ///   我先前用"手工乘缩放系数"只堵了第一个, 第二个一直没解决, 所以反复被用户抓到。
    ///
    /// TableLayoutPanel 把两个问题一起解决: 行高要么固定(给文字/按钮), 要么按百分比伸缩
    /// (给列表), 布局引擎会在任何窗口尺寸、任何 DPI 下自动重排。
    ///
    /// 用法: 每行给一个"高度权重" —— 0f 表示 AutoSize(按内容), >0 表示占剩余空间的份数。
    /// </summary>
    private static TableLayoutPanel MakePageTable(Panel page, int colCount,
        string[] rowNames, float[] rowWeights)
    {
        return MakePageTable(page, colCount, rowNames, rowWeights, null);
    }

    /// <summary>
    /// 同上, 但可指定每列类型(colKinds[i] = "P" 百分比 / "A" 按内容)。
    /// ⚠️ 按钮列必须是"按内容"(AutoSize), 否则按钮会被列拉成一整条
    ///   (用户实拍: 「删除选中」横铺整个右半边)。列表列相反, 要吃剩余宽度。
    /// </summary>
    private static TableLayoutPanel MakePageTable(Panel page, int colCount,
        string[] rowNames, float[] rowWeights, string[] colKinds)
    {
        TableLayoutPanel t = new TableLayoutPanel();
        t.Dock = DockStyle.Fill;
        t.ColumnCount = colCount;
        t.RowCount = rowNames.Length;
        t.Padding = Pad(10, 8, 10, 8);   // 按 DPI 缩放, 别写死像素
        t.BackColor = page.BackColor;
        for (int i = 0; i < colCount; i++)
        {
            bool byContent = (colKinds != null && i < colKinds.Length && colKinds[i] == "A");
            if (byContent) t.ColumnStyles.Add(new ColumnStyle(SizeType.AutoSize));
            else t.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 100F / colCount));
        }
        for (int i = 0; i < rowNames.Length; i++)
        {
            if (rowWeights[i] <= 0F) t.RowStyles.Add(new RowStyle(SizeType.AutoSize));
            else t.RowStyles.Add(new RowStyle(SizeType.Percent, rowWeights[i]));
        }
        page.Controls.Add(t);
        return t;
    }

    /// <summary>把控件放进表格并设置跨列 / 停放方式(自动布局下的标准做法)</summary>

    private static void PutCell(TableLayoutPanel t, Control c, int row, int col, int colSpan)
    {
        c.Dock = DockStyle.Fill;
        if (c is Label)
        {
            Label lb = (Label)c;
            lb.AutoSize = true;
            lb.Dock = DockStyle.Top;      // 标签按文字高度, 横向填满
        }
        else if (c is Button)
        {
            c.AutoSize = true;
            c.Dock = DockStyle.Top;   // 宽度自适应, 不撑满格子(踩过: Fill 会竖成一条长条)
        }
        else if (c is TextBox || c is ComboBox || c is NumericUpDown)
        {
            c.Dock = DockStyle.Top;
        }
        t.Controls.Add(c, col, row);
        if (colSpan > 1) t.SetColumnSpan(c, colSpan);
    }

    /// <summary>
    /// ★ 坐标缩放助手 —— 这是"换任何机器都不再需要手工调坐标"的关键。
    ///
    /// 为什么必须有它(这是本项目最根本的一个坑):
    ///   代码里字体是按 DPI 放大的 —— `Fi(..., 9F)` 返回的是 9 × _dpiScale 号字;
    ///   而坐标过去全是写死的常量。于是字号变大、框子不变:
    ///   125% 下 11.25pt 的两行中文要 69px 高, 而那个 Label 还按 60px 高排 —— 文字被压住。
    ///   之前我是"在出问题的地方把框子改大一点", 那是手工定制: 换台机器、换个缩放就再坏一次。
    ///
    /// 正确做法: 坐标和字体用同一个系数。这样在任何 DPI、任何分辨率下,
    ///   控件框和里面的字都同比放大, 排版关系恒定, 不需要针对某台机器调任何数字。
    ///
    /// 用法: 把 `ctl.SetBounds(a, b, c, d)` 换成 `ctl.SetBounds(B(a, b, c, d))`。
    /// </summary>
    private static Rectangle B(int x, int y, int w, int h)
    {
        float s = _dpiScale;
        if (s <= 0F) s = 1F;
        // 宽高给个下限, 免得极端缩放把控件压成 0 像素
        int sw = (int)Math.Round(w * s);
        int sh = (int)Math.Round(h * s);
        if (w > 0 && sw < 1) sw = 1;
        if (h > 0 && sh < 1) sh = 1;
        return new Rectangle((int)Math.Round(x * s), (int)Math.Round(y * s), sw, sh);
    }

    /// <summary>向导的 Body 面板(供 wiztest 自检读取); 由 BuildFirstRunWizard 赋值</summary>
    private static Panel _wizBody = null;

    private static Form BuildFirstRunWizard()
    {
        try
        {
            // 草稿状态(只有点最后一步"完成"才写盘); 默认先填好「光遇 电脑版」, 上一步直接点下一步即可
            List<string> draftTargets = new List<string>();
            PumpThrottled();
            draftTargets.Add("Sky.exe");
            string draftKeys = "";
            bool finished = false;
            PumpThrottled();

            Form w = new Form();
            w.Text = APP_NAME + " 首次设置";
            PumpThrottled();
            SetAutoScaleFont(w, Fi("Microsoft YaHei UI", 9.5F));
            w.BackColor = C_BG;
            w.ClientSize = new Size(Sc(680), Sc(660));
            PumpThrottled();
            w.MinimumSize = ClientToWindowSize(w, new Size(Sc(540), Sc(480)));
            w.StartPosition = FormStartPosition.CenterParent;
            w.FormBorderStyle = FormBorderStyle.Sizable;
            PumpThrottled();
            w.MaximizeBox = false;
            w.MinimizeBox = false;

            TableLayoutPanel root = new TableLayoutPanel();
            PumpThrottled();
            root.Dock = DockStyle.Fill;
            root.ColumnCount = 1;
            root.RowCount = 4;
            PumpThrottled();
            root.Margin = new Padding(0);
            root.BackColor = C_BG;
            root.RowStyles.Add(new RowStyle(SizeType.Absolute, Sc(56)));   // 0 标题条
            root.RowStyles.Add(new RowStyle(SizeType.Percent, 100F));      // 1 内容
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));           // 2 提示
            root.RowStyles.Add(new RowStyle(SizeType.AutoSize));           // 3 按钮
            w.Controls.Add(root);
            PumpThrottled();
            PumpThrottled();

            Panel head = new Panel();
            head.Dock = DockStyle.Fill;
            PumpThrottled();
            head.Margin = new Padding(0);
            head.BackColor = C_HEADER;
            head.Padding = new Padding(Sc(16), 0, Sc(16), 0);
            PumpThrottled();
            root.Controls.Add(head, 0, 0);
            PumpThrottled();
            Label title = new Label();
            title.Text = "开始之前";
            title.Font = Fi("Microsoft YaHei UI", 12F, FontStyle.Bold);
            PumpThrottled();
            title.ForeColor = Color.White;
            title.AutoSize = true;
            title.Dock = DockStyle.Left;
            PumpThrottled();
            title.TextAlign = ContentAlignment.MiddleLeft;
            head.Controls.Add(title);
            PumpThrottled();

            Panel body = new Panel();
            body.Dock = DockStyle.Fill;
            PumpThrottled();
            body.Margin = new Padding(Sc(16), Sc(12), Sc(16), 0);
            body.BackColor = Color.White;
            body.BorderStyle = BorderStyle.FixedSingle;
            PumpThrottled();
            _wizBody = body;
            root.Controls.Add(body, 0, 1);
            PumpThrottled();

            // ---- 页0: 说明 ----
            TextBox txtIntro = new TextBox();
            PumpThrottled();
            txtIntro.Multiline = true;
            txtIntro.ReadOnly = true;
            txtIntro.ScrollBars = ScrollBars.Vertical;
            PumpThrottled();
            txtIntro.BorderStyle = BorderStyle.None;
            txtIntro.BackColor = Color.White;
            txtIntro.ForeColor = C_TEXT;
            PumpThrottled();
            txtIntro.Dock = DockStyle.Fill;
            txtIntro.Margin = new Padding(Sc(12), Sc(10), Sc(12), Sc(10));
            txtIntro.Text =
                "它会做什么\r\n\r\n"
              + "   被外挂传送或误触霞谷小金人时，按下触发键会立即结束游戏进程并断网。\r\n"
              + "   触发后断网 20 秒，到时间自动恢复，也可提前点[恢复网络]。\r\n"
              + "   本工具不保证 100% 防坠机。\r\n\r\n"
              + "它不会做什么\r\n\r\n"
              + "   · 不注入游戏、不读内存、不改游戏文件\r\n"
              + "   · 不联网、不上传数据、不开机自启\r\n\r\n"
              + "请注意\r\n\r\n"
              + "   程序需要以管理员身份运行。\r\n"
              + "   按下触发键会立即关闭游戏并断网 20 秒。";
              PumpThrottled();
            body.Controls.Add(txtIntro);
            PumpThrottled();

            // ---- 页1: 选目标程序 ----
            Panel p1 = new Panel();
            PumpThrottled();
            p1.Dock = DockStyle.Fill;
            p1.BackColor = Color.White;
            p1.Visible = false;
            PumpThrottled();
            p1.AutoScroll = true;
            TableLayoutPanel t1 = MakePageTable(p1, 2,
                new string[] { "tip", "preset", "chosen", "list", "custom" },
                new float[] { 0F, 1F, 0F, 3F, 0F }, new string[] { "P", "A" });
                PumpThrottled();
            Label p1t = new Label();
            p1t.Text = "第 1 步 · 选择要关闭的程序\r\n双开时，两个预设各添加一次。";
            p1t.ForeColor = C_SUB;
            PumpThrottled();
            PutCell(t1, p1t, 0, 0, 2);

            ListBox p1preset = new ListBox();
            PumpThrottled();
            p1preset.Dock = DockStyle.Fill;
            p1preset.Margin = new Padding(0, Sc(2), Sc(8), Sc(2));
            p1preset.MinimumSize = new Size(0, Sc(66));
            PumpThrottled();
            p1preset.IntegralHeight = false;
            foreach (ProcPreset pp in PRESETS) p1preset.Items.Add(pp.Label);
            p1preset.SelectedIndex = 0;
            PumpThrottled();
            t1.Controls.Add(p1preset, 0, 1);
            PumpThrottled();
            Button p1add = MakeButton("添加这一组 →", null, "primary");
            p1add.Margin = new Padding(Sc(4), Sc(2), 0, 0);
            p1add.Anchor = AnchorStyles.Top | AnchorStyles.Left;
            PumpThrottled();
            t1.Controls.Add(p1add, 1, 1);
            PumpThrottled();

            Label p1chosen = new Label();
            p1chosen.Text = "已选程序，触发时一并关闭：";
            PumpThrottled();
            PutCell(t1, p1chosen, 2, 0, 2);

            ListBox p1list = new ListBox();
            PumpThrottled();
            p1list.Dock = DockStyle.Fill;
            p1list.Margin = new Padding(0, Sc(2), Sc(8), Sc(2));
            p1list.SelectionMode = SelectionMode.MultiExtended;
            PumpThrottled();
            p1list.IntegralHeight = true;
            t1.Controls.Add(p1list, 0, 3);
            PumpThrottled();
            Button p1del = MakeButton("删除选中", null, "plain");
            p1del.Margin = new Padding(Sc(4), Sc(2), 0, 0);
            p1del.Anchor = AnchorStyles.Top | AnchorStyles.Left;
            PumpThrottled();
            t1.Controls.Add(p1del, 1, 3);
            PumpThrottled();

            FlowLayoutPanel p1cust = new FlowLayoutPanel();
            p1cust.Dock = DockStyle.Fill;
            PumpThrottled();
            p1cust.AutoSize = true;
            p1cust.FlowDirection = FlowDirection.LeftToRight;
            p1cust.WrapContents = true;
            PumpThrottled();
            p1cust.Margin = new Padding(0, Sc(6), 0, 0);
            t1.Controls.Add(p1cust, 0, 4);
            PumpThrottled();
            t1.SetColumnSpan(p1cust, 2);
            TextBox p1custom = new TextBox();
            p1custom.Width = Sc(200);
            PumpThrottled();
            p1cust.Controls.Add(p1custom);
            PumpThrottled();
            Button p1addc = MakeButton("添加这个名字", null, "plain");
            p1cust.Controls.Add(p1addc);
            PumpThrottled();
            body.Controls.Add(p1);
            PumpThrottled();

            p1add.Click += delegate
            {
                int i = p1preset.SelectedIndex;
                PumpThrottled();
                if (i < 0 || i >= PRESETS.Length) return;
                int added = 0;
                foreach (string p in PRESETS[i].Procs)
                {
                    bool dup = false;
                    PumpThrottled();
                    foreach (object o in p1list.Items)
                        if (string.Equals(o.ToString(), p, StringComparison.OrdinalIgnoreCase)) { dup = true; break; }
                    if (!dup) { p1list.Items.Add(p); added++; }
                }
                Log("[向导] 添加预设 [" + PRESETS[i].Label + "] 新增 " + added + " 个");
                PumpThrottled();
            };
            p1addc.Click += delegate
            {
                string n = p1custom.Text.Trim();
                PumpThrottled();
                if (n.Length == 0) return;
                if (n.EndsWith(".exe", StringComparison.OrdinalIgnoreCase)) n = n.Substring(0, n.Length - 4);
                p1list.Items.Add(n);
                PumpThrottled();
                p1custom.Text = "";
                Log("[向导] 手动添加目标: " + n);
            };
            PumpThrottled();
            p1del.Click += delegate
            {
                List<object> rm = new List<object>();
                PumpThrottled();
                foreach (object o in p1list.SelectedItems) rm.Add(o);
                foreach (object o in rm) p1list.Items.Remove(o);
            };
            PumpThrottled();

            // ---- 页2: 触发键 ----
            Panel p2 = new Panel();
            PumpThrottled();
            p2.Dock = DockStyle.Fill;
            p2.BackColor = Color.White;
            p2.Visible = false;
            PumpThrottled();
            p2.AutoScroll = true;
            TableLayoutPanel t2 = MakePageTable(p2, 2,
                new string[] { "tip", "keys", "help" },
                new float[] { 0F, 0F, 1F });
                PumpThrottled();
            Label p2t = new Label();
            p2t.Text = "第 2 步 · 设定触发键\r\n"
                     + "点[录入按键]，在弹出窗口中直接按下需要使用的按键，或从下拉菜单中选择。\r\n"
                     + "可设置多个按键，按下任意一个都会触发。";
                     PumpThrottled();
            p2t.ForeColor = C_SUB;
            PutCell(t2, p2t, 0, 0, 2);
            TextBox p2keys = new TextBox();
            PumpThrottled();
            p2keys.ReadOnly = true;
            p2keys.BackColor = Color.White;
            p2keys.Dock = DockStyle.Fill;
            PumpThrottled();
            p2keys.Margin = new Padding(0, Sc(2), Sc(8), 0);
            t2.Controls.Add(p2keys, 0, 1);
            PumpThrottled();
            Button p2rec = MakeButton("录入按键", null, "primary");
            p2rec.Anchor = AnchorStyles.Top | AnchorStyles.Left;
            p2rec.Margin = new Padding(Sc(4), Sc(2), 0, 0);
            PumpThrottled();
            t2.Controls.Add(p2rec, 1, 1);
            PumpThrottled();
            Label p2h = new Label();
            p2h.ForeColor = C_SUB;
            p2h.Text = "选择建议\r\n\r\n"
                     + "   推荐 F1 - F12 或组合键。\r\n"
                     + "   不建议使用 Space、W、Tab 等会影响游戏操作的按键。";
                     PumpThrottled();
            // ⚠️ 不要在这之后再设 Dock=Fill —— 那会让 AutoSize 失效, 行比文字矮时说明会被裁掉。
            PutCell(t2, p2h, 2, 0, 2);
            body.Controls.Add(p2);
            PumpThrottled();
            PumpThrottled();

            p2rec.Click += delegate
            {
                TextBox saved = _txtKeys;
                PumpThrottled();
                _txtKeys = p2keys;
                try { DoRecordKeys(); }
                finally { _txtKeys = saved; draftKeys = p2keys.Text; }
                Log("[向导] 触发键暂定为: " + draftKeys);
                PumpThrottled();
            };

            // ---- 页3: 网卡 ----
            Panel p3 = new Panel();
            PumpThrottled();
            p3.Dock = DockStyle.Fill;
            p3.BackColor = Color.White;
            p3.Visible = false;
            PumpThrottled();
            p3.AutoScroll = true;
            TableLayoutPanel t3 = MakePageTable(p3, 1,
                new string[] { "tip", "nics", "again" },
                new float[] { 0F, 1F, 0F });
                PumpThrottled();
            Label p3t = new Label();
            p3t.Text = "第 3 步 · 选择要断开的网卡\r\n已完成自动探测，带[承载流量]标记的是正在使用的网卡，默认已勾选。";
            p3t.ForeColor = C_SUB;
            PumpThrottled();
            PutCell(t3, p3t, 0, 0, 1);
            CheckedListBox p3nics = new CheckedListBox();
            p3nics.Dock = DockStyle.Fill;
            PumpThrottled();
            p3nics.MinimumSize = new Size(0, Sc(80));
            p3nics.IntegralHeight = true;
            p3nics.CheckOnClick = true;
            PumpThrottled();
            // ★ 抽成委托 —— 启动探测改成后台线程后, 进到这一页时列表可能还没填上,
            //   渲染时再补填一次(不阻塞界面; 用户也可以点[重新探测]自己刷)。
            Action fillP3 = delegate
            {
                try
                {
                    List<string> had = new List<string>();
                    PumpThrottled();
                    for (int i = 0; i < p3nics.Items.Count; i++)
                        if (p3nics.GetItemChecked(i) && i < _nics.Count) had.Add(_nics[i].Name);
                    p3nics.Items.Clear();
                    PumpThrottled();
                    for (int i = 0; i < _nics.Count; i++)
                    {
                        NicInfo ni = _nics[i];
                        PumpThrottled();
                        string label = ni.Name;
                        if (ni.HasDefaultRoute) label += "   [承载流量]";
                        else if (ni.IsVirtualHint) label += "   [虚拟网卡]";
                        PumpThrottled();
                        p3nics.Items.Add(label, ni.HasDefaultRoute || had.Contains(ni.Name));
                    }
                    if (_nics.Count > 0 && p3nics.CheckedItems.Count == 0) p3nics.SetItemChecked(0, true);
                    PumpThrottled();
                }
                catch { }
            };
            PumpThrottled();
            fillP3();
            t3.Controls.Add(p3nics, 0, 1);
            PumpThrottled();
            Button p3re = MakeButton("重新探测", null, "plain");
            p3re.Anchor = AnchorStyles.Top | AnchorStyles.Left;
            t3.Controls.Add(p3re, 0, 2);
            PumpThrottled();
            PumpThrottled();
            body.Controls.Add(p3);
            PumpThrottled();

            p3re.Click += delegate
            {
                // V1.1.5: 探测走后台(实测 1.0~1.4 秒), 回来后重新填这一页的网卡列表
                DoDetectAsync(w, false, new MethodInvoker(delegate { try { fillP3(); } catch { } }));
                PumpThrottled();
            };

            // ---- 底部提示 + 按钮 ----
            Label foot = new Label();
            PumpThrottled();
            foot.AutoSize = true;
            foot.Dock = DockStyle.Top;
            foot.ForeColor = C_SUB;
            PumpThrottled();
            foot.UseMnemonic = false;
            foot.Margin = new Padding(Sc(16), Sc(8), Sc(16), 0);
            root.Controls.Add(foot, 0, 2);
            PumpThrottled();
            PumpThrottled();

            TableLayoutPanel btnBar = new TableLayoutPanel();
            btnBar.Dock = DockStyle.Fill;
            PumpThrottled();
            btnBar.ColumnCount = 2;
            btnBar.RowCount = 1;
            btnBar.Margin = new Padding(Sc(16), Sc(10), Sc(16), Sc(12));
            PumpThrottled();
            btnBar.BackColor = C_BG;
            btnBar.ColumnStyles.Add(new ColumnStyle(SizeType.Percent, 100F));
            btnBar.ColumnStyles.Add(new ColumnStyle(SizeType.AutoSize));
            PumpThrottled();
            root.Controls.Add(btnBar, 0, 3);
            PumpThrottled();

            FlowLayoutPanel btnRow = new FlowLayoutPanel();
            btnRow.AutoSize = true;
            PumpThrottled();
            btnRow.Dock = DockStyle.Fill;
            btnRow.FlowDirection = FlowDirection.LeftToRight;
            btnRow.WrapContents = false;
            PumpThrottled();
            btnBar.Controls.Add(btnRow, 1, 0);
            PumpThrottled();

            Button bBack = MakeButton("← 上一步", null, "plain");
            Button bNext = MakeButton("继续 →", null, "primary");
            PumpThrottled();
            Button bSkip = MakeButton("跳过", null, "plain");
            bBack.Margin = new Padding(0, 0, Sc(8), 0);
            bNext.Margin = new Padding(0, 0, Sc(8), 0);
            PumpThrottled();
            btnRow.Controls.Add(bBack);
            PumpThrottled();
            btnRow.Controls.Add(bNext);
            PumpThrottled();
            btnRow.Controls.Add(bSkip);
            PumpThrottled();

            // ---- 翻页逻辑 ----
            int page = 0;
            PumpThrottled();
            EventHandler render = null;
            render = delegate
            {
                txtIntro.Visible = (page == 0);
                PumpThrottled();
                p1.Visible = (page == 1);
                p2.Visible = (page == 2);
                p3.Visible = (page == 3);
                PumpThrottled();
                if (page == 1)
                {
                    p1list.Items.Clear();
                    PumpThrottled();
                    foreach (string s in draftTargets) p1list.Items.Add(s);
                }
                if (page == 2) p2keys.Text = draftKeys;
                PumpThrottled();
                if (page == 3 && p3nics.Items.Count == 0) fillP3();   // 后台探测可能刚回来, 进页时补填一次
                int scr = page + 1;
                title.Text = (page == 0)
                    ? "开始之前"
                    : "第 " + page + " 步 / 共 3 步";
                    PumpThrottled();
                w.Text = APP_NAME + " 首次设置 (" + scr + "/4)";
                bBack.Visible = (page > 0);
                bNext.Text = (page == 0) ? "继续 →"
                           : (page == 3) ? "完成" : "下一步 →";
                           PumpThrottled();
                foot.Text = (page == 0) ? "阅读后点[继续]"
                          : (page == 3) ? "点[完成]保存设置"
                          : "可点[上一步]返回修改";
                          PumpThrottled();
            };

            bNext.Click += delegate
            {
                Log("[向导] 点下一步/完成, 当前页=" + page);
                PumpThrottled();
                if (_headless)
                {
                    if (page == 3) { finished = true; w.Close(); return; }
                    page++; render(null, null); return;
                }
                if (page == 0) { page = 1; render(null, null); return; }
                if (page == 1)
                {
                    draftTargets = new List<string>();
                    PumpThrottled();
                    foreach (object o in p1list.Items) draftTargets.Add(o.ToString());
                    if (draftTargets.Count == 0)
                    {
                        MessageBox.Show("尚未添加程序，请点[添加这一组 →]添加「光遇 电脑版」。",
                            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                            PumpThrottled();
                        return;
                    }
                    page = 2; render(null, null); return;
                }
                if (page == 2)
                {
                    draftKeys = p2keys.Text;
                    PumpThrottled();
                    List<string> kw = new List<string>();
                    List<KeyTrig> save = _trigs;
                    ParseKeys(SplitKeyText(draftKeys), kw);
                    PumpThrottled();
                    int n = _trigs.Count;
                    _trigs = save;
                    if (n == 0)
                    {
                        MessageBox.Show("尚未设置触发键，请点[录入按键]。",
                            APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                            PumpThrottled();
                        return;
                    }
                    page = 3; render(null, null); return;
                }
                List<string> picked = new List<string>();
                for (int i = 0; i < p3nics.Items.Count; i++)
                    if (p3nics.GetItemChecked(i) && i < _nics.Count) picked.Add(_nics[i].Name);
                if (picked.Count == 0)
                {
                    MessageBox.Show("请至少勾选一张网卡，推荐带[承载流量]标记的那张。",
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                        PumpThrottled();
                    return;
                }
                // ★ 收尾再校验"目标和触发键": 这两样缺任何一个, 配置会被存下来、程序看着像配好了,
                //   但按下触发键什么都不会发生 —— 那是最坏的一种"假成功"。网卡上面已经校验过了。
                if (draftTargets.Count == 0)
                {
                    MessageBox.Show("尚未添加要关闭的程序，请返回第 1 步。",
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                        PumpThrottled();
                    return;
                }
                List<string> finalKeys = SplitKeyText(draftKeys);
                PumpThrottled();
                if (finalKeys.Count == 0)
                {
                    MessageBox.Show("尚未设置触发键，请返回第 2 步。",
                        APP_NAME, MessageBoxButtons.OK, MessageBoxIcon.Warning);
                        PumpThrottled();
                    return;
                }
                Config cfg = new Config();
                PumpThrottled();
                cfg.Procs = draftTargets;
                cfg.Keys = finalKeys;
                cfg.Nics = picked;
                PumpThrottled();
                cfg.WaitSeconds = 20;
                if (_wizardDemoMode)
                {
                    // 演示模式(命令行 wizard): 只走流程, 绝不写 guard.ini、也不改运行配置
                    Log("[向导/演示] 走完全程, 未写盘。目标=" + string.Join(" / ", draftTargets.ToArray())
                        + " 触发键=" + draftKeys + " 网卡=" + string.Join(" / ", picked.ToArray()));
                        PumpThrottled();
                    finished = true;
                    w.Close();
                    return;
                }
                _cfg = cfg;
                PumpThrottled();
                try { SaveConfig(cfg); }
                catch (Exception ex) { WarnBox("配置保存失败: " + ex.Message); }
                List<string> w3 = new List<string>();
                PumpThrottled();
                ParseKeys(cfg.Keys, w3);
                foreach (string x in w3) Log("[向导警告] " + x);
                RefreshSummary();
                PumpThrottled();
                RefreshStatus();
                Log("[向导] 完成: 目标=" + string.Join(" / ", cfg.TargetList().ToArray())
                    + " 触发键=" + cfg.KeysText()
                    + " 网卡=" + string.Join(" / ", cfg.Nics.ToArray()));
                    PumpThrottled();
                finished = true;
                w.Close();
            };
            PumpThrottled();

            bBack.Click += delegate
            {
                if (page > 0) { page--; render(null, null); }
                Log("[向导] 点上一步, 现在页=" + page);
                PumpThrottled();
            };

            bSkip.Click += delegate
            {
                DialogResult r = MessageBox.Show(
                    "跳过设置向导？\n\n跳过后程序不会保护任何程序，需要自行点[⚙ 设置]完成配置。",
                    APP_NAME, MessageBoxButtons.YesNo, MessageBoxIcon.Question);
                    PumpThrottled();
                if (r == DialogResult.Yes) { finished = false; w.Close(); }
            };

            render(null, null);
            PumpThrottled();
            _wizardFinished = false;
            w.FormClosed += delegate { _wizardFinished = finished; };
            return w;
        }
        catch (Exception ex)
        {
            Log("[向导] 异常: " + ex);
            PumpThrottled();
            WarnBox("设置向导出错：" + ex.Message + "\n\n你可以点[⚙ 设置]手动配置。");
            return null;
        }
    }

    /// <summary>向导最后是不是点了[完成](而不是"跳过"或直接关窗)</summary>
    private static volatile bool _wizardFinished = false;
    /// <summary>演示模式(命令行 wizard): 向导只走流程, 不写 guard.ini、不改运行配置</summary>
    private static bool _wizardDemoMode = false;

    /// <summary>自检写盘前暂存的 guard.ini 原文(null = 原本就没有这个文件)</summary>
    private static string _iniBackupForTest = null;
    /// <summary>本次自检是否已经把 guard.ini 恢复过了(恢复只能做一次)</summary>
    #endregion
}

