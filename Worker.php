<?php
namespace Workerman;

require_once __DIR__ . '/Lib/Constants.php';//时区，错误配置，定义

use Workerman\Events\EventInterface;
use Workerman\Connection\ConnectionInterface;
use Workerman\Connection\TcpConnection;
use Workerman\Connection\UdpConnection;
use Workerman\Lib\Timer;
//use Exception;//centos7非必须

//端口监听容器
class Worker
{
    const VERSION = '3.3.6';//Version.
    const STATUS_STARTING = 1;//Status starting.
    const STATUS_RUNNING = 2;//Status running.
    const STATUS_SHUTDOWN = 4;//Status shutdown.
    const STATUS_RELOADING = 8;//Status reloading.

    /**
     * After sending the restart command to the child process KILL_WORKER_TIMER_TIME seconds,
     * if the process is still living then forced to kill.
     */
    const KILL_WORKER_TIMER_TIME = 2;

    /**
     * Default backlog. Backlog is the maximum length of the queue of pending connections.
     * 最大连接数？
     */
    const DEFAULT_BACKLOG = 1024;
    const MAX_UDP_PACKAGE_SIZE = 65535;//Max udp package size.
    public $id = 0;//Worker id.
    public $name = 'none';//Name of the worker processes.
    public $count = 1;//Number of worker processes.
    public $user = '';//Unix user of processes, needs appropriate privileges (usually root).
    public $group = '';//Unix group of processes, needs appropriate privileges (usually root).
    public $reloadable = true;//reloadable.
    public $reusePort = false;//reuse port.
    public $onWorkerStart = null;//Emitted when worker processes start.
    public $onConnect = null;//Emitted when a socket connection is successfully established.
    public $onMessage = null;//Emitted when data is received.
    public $onClose = null;//Emitted when the other end of the socket sends a FIN packet.
    public $onError = null;//Emitted when an error occurs with connection.
    public $onBufferFull = null;//Emitted when the send buffer becomes full.
    public $onBufferDrain = null;//Emitted when the send buffer becomes empty.
    public $onWorkerStop = null;//Emitted when worker processes stoped.
    public static $onMasterReload = null;//Emitted when the master process get reload signal.
    public $onWorkerReload = null;//Emitted when worker processes get reload signal.
    public $transport = 'tcp';//Transport layer protocol.
    public $connections = array();//Store all connections of clients.
    public $protocol = '';//Application layer protocol.
    protected $_autoloadRootPath = '';//Root path for autoload.
    public static $daemonize = false;//Daemonize.
    public static $stdoutFile = '/dev/null';//Stdout file.
    public static $pidFile = '';//The file to store master process PID.
    public static $logFile = '';//Log file.
    public static $globalEvent = null;//Global event loop.
    protected static $_masterPid = 0;//The PID of master process.
    protected $_mainSocket = null;//Listening socket.
    protected $_socketName = '';//Socket name. The format is like this http://0.0.0.0:80 .
    protected $_context = null;//Context of socket.
    protected static $_workers = array();//All worker instances.

    /**
     * All worker porcesses pid.
     * The format is like this [worker_id=>[pid=>pid, pid=>pid, ..], ..]
     */
    protected static $_pidMap = array();// 在生存周期的进程id

    /**
     * All worker processes waiting for restart.
     * The format is like this [pid=>pid, pid=>pid].
     */
    protected static $_pidsToRestart = array();

    /**
     * Mapping from PID to worker process ID.
     * The format is like this [worker_id=>[0=>$pid, 1=>$pid, ..], ..].
     */
    protected static $_idMap = array();// 初始化后记录的id
    protected static $_status = self::STATUS_STARTING;//Current status.
    protected static $_maxWorkerNameLength = 12;//Maximum length of the worker names.
    protected static $_maxSocketNameLength = 12;//Maximum length of the socket names.
    protected static $_maxUserNameLength = 12;//Maximum length of the process user names.
    protected static $_statisticsFile = '';//The file to store status info of current worker process.
    protected static $_startFile = '';//Start file.

    /**
     * Status info of current worker process.
     */
    protected static $_globalStatistics = array(
        'start_timestamp'  => 0,
        'worker_exit_info' => array()
    );

    /**
     * Available event loops.
     */
    protected static $_availableEventLoops = array(
        'libevent',
        'event',
        'ev'
    );
    protected static $_eventLoopName = 'select';//Current eventLoop name.

    /**
     * PHP built-in protocols.
     */
    protected static $_builtinTransports = array(
        'tcp'   => 'tcp',
        'udp'   => 'udp',
        'unix'  => 'unix',
        'ssl'   => 'tcp',
        'sslv2' => 'tcp',
        'sslv3' => 'tcp',
        'tls'   => 'tcp'
    );

    //  运行worker所有实例
    public static function runAll()
    {
        self::checkSapiEnv();//非cli模式直接退出
        self::init();//保存pid，日志，初始化状态（定时器任务？？）
        self::parseCommand();// 解析命令
        self::daemonize();// 尝试创建守护进程模式
        self::initWorkers();// 初始化woker和socket服务配置，注册事件监听套接字服务是否可读
        self::installSignal();// 初始化信号处理（主进程）
        self::saveMasterPid();// 保存主进程pid
        // fork子进程,给每子进程绑定loop循环监听事件tcp
        // 初始化Timer定时器
        self::forkWorkers();
        self::displayUI();// 展示启动界面
        self::resetStd();// 尝试重定向标准输入输出
        self::monitorWorkers();// 控制status,reload
    }

    protected static function checkSapiEnv()
    {
        //sapi（the Server API）判断提供PHP接口的类型
        if (php_sapi_name() != "cli") {
            exit("only run in command line mode \n");
        }
    }

    protected static function init()
    {
        //获得当前执行的文件（例如：/home/www.wkm.c7/start.php）
        $backtrace        = debug_backtrace();
        self::$_startFile = $backtrace[count($backtrace) - 1]['file'];

        //保存pid文件的地址
        if (empty(self::$pidFile)) {
            self::$pidFile = __DIR__ . "/../" . str_replace('/', '_', self::$_startFile) . ".pid";
        }

        //生成日志文件
        if (empty(self::$logFile)) {
            self::$logFile = __DIR__ . '/../workerman.log';
        }
        $log_file = (string)self::$logFile;
        touch($log_file);
        chmod($log_file, 0622);// 可读写、写、写
        
        //初始化进程状态
        self::$_status = self::STATUS_STARTING;
        self::$_globalStatistics['start_timestamp'] = time();
        self::$_statisticsFile                      = sys_get_temp_dir() . '/workerman.status';///tmp/workerman.status
        self::setProcessTitle('WorkerMan: master process  start_file=' . self::$_startFile);

        // 初始化$_idMap
        self::initId();

        // 仅注册定时器监听
        // 在run启动进程后初始化事件（Timer::init(self::$globalEvent);）
        // 最后使用add方法加入执行动作
        Timer::init();
    }

    protected static function initWorkers()
    {
        //初始化所有worker实例
        //（注意，这里是在主进程做的，只是生成了一堆 server 并没有设置监听，多进程模型是在子进程做的监听，即IO复用）
        foreach (self::$_workers as $worker) {
            if (empty($worker->name)) {
                $worker->name = 'none';
            }
            $worker_name_length = strlen($worker->name);
            if (self::$_maxWorkerNameLength < $worker_name_length) {
                self::$_maxWorkerNameLength = $worker_name_length;
            }
            $socket_name_length = strlen($worker->getSocketName());
            if (self::$_maxSocketNameLength < $socket_name_length) {
                self::$_maxSocketNameLength = $socket_name_length;
            }
            if (empty($worker->user)) {
                $worker->user = self::getCurrentUser();
            } else {
                if (posix_getuid() !== 0 && $worker->user != self::getCurrentUser()) {
                    self::log('Warning: You must have the root privileges to change uid and gid.');
                }
            }
            $user_name_length = strlen($worker->user);
            if (self::$_maxUserNameLength < $user_name_length) {
                self::$_maxUserNameLength = $user_name_length;
            }
            // 配置socket,注册事件监听套接字服务
            if (!$worker->reusePort) {
                $worker->listen();
            }
        }
    }

    /**
     * Get all worker instances.
     *
     * @return array
     */
    public static function getAllWorkers()
    {
        return self::$_workers;
    }

    /**
     * Get global event-loop instance.
     *
     * @return EventInterface
     */
    public static function getEventLoop()
    {
        return self::$globalEvent;
    }

    /**
     * The format is like this [worker_id=>[0=>$pid, 1=>$pid, ..], ..].
     */
    protected static function initId()
    {
        foreach (self::$_workers as $worker_id => $worker) {
            $new_id_map = array();
            for($key = 0; $key < $worker->count; $key++) {
                $new_id_map[$key] = isset(self::$_idMap[$worker_id][$key]) ? self::$_idMap[$worker_id][$key] : 0;
            }
            self::$_idMap[$worker_id] = $new_id_map;
        }
        /*
        ["000000000680297d0000000012a23334"]=>
        array(4) {
            [0]=>
            int(0)
            ..
        }
        */
    }

    /**
     * Get unix user of current porcess.
     *
     * @return string
     */
    protected static function getCurrentUser()
    {
        //获取进程的当前用户信息
        $user_info = posix_getpwuid(posix_getuid());
        return $user_info['name'];
    }

    protected static function displayUI()
    {
        self::safeEcho("\033[1A\n\033[K-----------------------\033[47;30m WORKERMAN \033[0m-----------------------------\n\033[0m");
        self::safeEcho('Workerman version:'. Worker::VERSION. "          PHP version:". PHP_VERSION. "\n");
        self::safeEcho("------------------------\033[47;30m WORKERS \033[0m-------------------------------\n");
        self::safeEcho("\033[47;30muser\033[0m". str_pad('',
            self::$_maxUserNameLength + 2 - strlen('user')). "\033[47;30mworker\033[0m". str_pad('',
            self::$_maxWorkerNameLength + 2 - strlen('worker')). "\033[47;30mlisten\033[0m". str_pad('',
            self::$_maxSocketNameLength + 2 - strlen('listen')). "\033[47;30mprocesses\033[0m \033[47;30m". "status\033[0m\n");

        foreach (self::$_workers as $worker) {
            self::safeEcho(str_pad($worker->user, self::$_maxUserNameLength + 2). str_pad($worker->name,
                self::$_maxWorkerNameLength + 2). str_pad($worker->getSocketName(),
                self::$_maxSocketNameLength + 2). str_pad(' ' . $worker->count, 9). " \033[32;40m [OK] \033[0m\n");
        }
        self::safeEcho("----------------------------------------------------------------\n");
        if (self::$daemonize) {
            global $argv;
            $start_file = $argv[0];
            self::safeEcho("Input \"php $start_file stop\" to quit. Start success.\n");
        } else {
            self::safeEcho("Press Ctrl-C to quit. Start success.\n");
        }
    }

    /**
     * php yourfile.php start | stop | restart | reload | status
     */
    protected static function parseCommand()
    {
        //无参数即退出
        global $argv;
        $start_file = $argv[0];
        if (!isset($argv[1])) {
            exit("Usage: php yourfile.php {start|stop|restart|reload|status}\n");
        }
        $command  = trim($argv[1]);
        $command2 = isset($argv[2]) ? $argv[2] : '';
        $mode = '';
        if ($command === 'start') {
            if ($command2 === '-d' || Worker::$daemonize) {
                $mode = 'in DAEMON mode';
            } else {
                $mode = 'in DEBUG mode';
            }
        }
        self::log("Workerman[$start_file] $command $mode");

        //发送信号0检测进程（或进程组）是否存活，同时也检测当前用户是否有权限发送系统信号；
        $master_pid      = @file_get_contents(self::$pidFile);
        $master_is_alive = $master_pid && @posix_kill($master_pid, 0);
        if ($master_is_alive) {
            if ($command === 'start' && posix_getpid() != $master_pid) {
                self::log("Workerman[$start_file] already running");
                exit;
            }
        } elseif ($command !== 'start' && $command !== 'restart') {
            self::log("Workerman[$start_file] not run");
            exit;
        }

        // 执行命令
        switch ($command) {
            case 'start':
                if ($command2 === '-d') {
                    Worker::$daemonize = true;
                }
                break;
            case 'status':
                if (is_file(self::$_statisticsFile)) {
                    @unlink(self::$_statisticsFile);
                }
                // 发信号SIGUSR2查询状态（主进程通知所有子进程,通过monitorWorkers执行信号）
                posix_kill($master_pid, SIGUSR2);
                usleep(500000);// 处理信号需要预留磁盘时间
                @readfile(self::$_statisticsFile);// 读取文件中的内容到输出缓冲区
                exit(0);
            case 'restart':
            case 'stop':
                self::log("Workerman[$start_file] is stoping ...");
                $master_pid && posix_kill($master_pid, SIGINT);
                $timeout    = 5;
                $start_time = time();
                // Check master process is still alive?
                while (1) {
                    $master_is_alive = $master_pid && posix_kill($master_pid, 0);
                    if ($master_is_alive) {
                        if (time() - $start_time >= $timeout) {
                            self::log("Workerman[$start_file] stop fail");
                            exit;
                        }
                        usleep(10000);
                        continue;
                    }
                    // Stop success.
                    self::log("Workerman[$start_file] stop success");
                    if ($command === 'stop') {
                        exit(0);
                    }
                    if ($command2 === '-d') {//restart情况
                        Worker::$daemonize = true;
                    }
                    break;
                }
                break;
            case 'reload':
                posix_kill($master_pid, SIGUSR1);
                self::log("Workerman[$start_file] reload");
                exit;
            default :
                exit("Usage: php yourfile.php {start|stop|restart|reload|status}\n");
        }
    }

    // 主进程信号注册
    protected static function installSignal()
    {
        // stop
        pcntl_signal(SIGINT, array('\Workerman\Worker', 'signalHandler'), false);
        // reload
        pcntl_signal(SIGUSR1, array('\Workerman\Worker', 'signalHandler'), false);
        // status
        pcntl_signal(SIGUSR2, array('\Workerman\Worker', 'signalHandler'), false);
        // 忽略SIGPIPE信号
        // 在某些情况下（send到一个已关闭的 socket上两次），系统会发出SIGPIPE信号，该信号会结束进程
        pcntl_signal(SIGPIPE, SIG_IGN, false);
    }


    protected static function reinstallSignal()
    {
        // uninstall stop signal handler
        pcntl_signal(SIGINT, SIG_IGN, false);
        // uninstall reload signal handler
        pcntl_signal(SIGUSR1, SIG_IGN, false);
        // uninstall  status signal handler
        pcntl_signal(SIGUSR2, SIG_IGN, false);
        // reinstall stop signal handler
        self::$globalEvent->add(SIGINT, EventInterface::EV_SIGNAL, array('\Workerman\Worker', 'signalHandler'));
        // reinstall  reload signal handler
        self::$globalEvent->add(SIGUSR1, EventInterface::EV_SIGNAL, array('\Workerman\Worker', 'signalHandler'));
        // reinstall  status signal handler
        self::$globalEvent->add(SIGUSR2, EventInterface::EV_SIGNAL, array('\Workerman\Worker', 'signalHandler'));
    }

    /**
     * Signal handler.
     *
     * @param int $signal
     */
    public static function signalHandler($signal)
    {
        switch ($signal) {
            // Stop.
            case SIGINT:
                self::stopAll();
                break;
            // Reload.
            case SIGUSR1:
                self::$_pidsToRestart = self::getAllWorkerPids();
                self::reload();
                break;
            // Show status.
            case SIGUSR2:
                self::writeStatisticsToStatusFile();
                break;
        }
    }

    protected static function daemonize()
    {
        if (!self::$daemonize) {
            return;
        }
        umask(0);//将默认权限的掩码修改为0，即将要创建的所有的文件你的权限都是777
        $pid = pcntl_fork();
        if (-1 === $pid) {
            throw new Exception('fork fail');
        } elseif ($pid > 0) {
            // 关闭父进程，让子进程成为孤儿进程被init进程收养
            exit(0);
        }
        // 将子进程作为进程组的leader,开启一个新的会话,脱离之前的会话和进程组。即使用户logout也不会终止
        if (-1 === posix_setsid()) {
            throw new Exception("setsid fail");
        }
        // Fork again avoid SVR4 system regain the control of terminal.
        $pid = pcntl_fork();
        if (-1 === $pid) {
            throw new Exception("fork fail");
        } elseif (0 !== $pid) {
            exit(0);
        }
    }

    protected static function resetStd()
    {
        if (!self::$daemonize) {
            return;
        }
        global $STDOUT, $STDERR;
        $handle = fopen(self::$stdoutFile, "a");
        if ($handle) {
            unset($handle);
            @fclose(STDOUT);
            @fclose(STDERR);
            $STDOUT = fopen(self::$stdoutFile, "a");
            $STDERR = fopen(self::$stdoutFile, "a");
        } else {
            throw new Exception('can not open stdoutFile ' . self::$stdoutFile);
        }
    }

    protected static function saveMasterPid()
    {
        //在终端查看系统状态或者执行关闭、重启命令，是通过主进程进行通信，
        //在终端下敲入一个可执行命令，实则是在当前终端下新建一个子进程来执行，
        //向WM主进程发送SIGNAL，这时信号处理函数捕获该信号，并通过回调方式执行。
        self::$_masterPid = posix_getpid();
        if (false === @file_put_contents(self::$pidFile, self::$_masterPid)) {
            throw new Exception('can not save pid to ' . self::$pidFile);
        }
    }

    /**
     * Get event loop name.
     *
     * @return string
     */
    protected static function getEventLoopName()
    {
        if (interface_exists('\React\EventLoop\LoopInterface')) {
            return 'React';
        }
        foreach (self::$_availableEventLoops as $name) {
            if (extension_loaded($name)) {
                self::$_eventLoopName = $name;
                break;
            }
        }
        return self::$_eventLoopName;
    }

    /**
     * Get all pids of worker processes.
     *
     * @return array
     */
    protected static function getAllWorkerPids()
    {
        $pid_array = array();
        foreach (self::$_pidMap as $worker_pid_array) {
            foreach ($worker_pid_array as $worker_pid) {
                $pid_array[$worker_pid] = $worker_pid;
            }
        }
        return $pid_array;
    }

    protected static function forkWorkers()
    {
        foreach (self::$_workers as $worker) {
            if (self::$_status === self::STATUS_STARTING) {
                if (empty($worker->name)) {
                    $worker->name = $worker->getSocketName();
                }
                $worker_name_length = strlen($worker->name);
                if (self::$_maxWorkerNameLength < $worker_name_length) {
                    self::$_maxWorkerNameLength = $worker_name_length;
                }
            }
            $worker->count = $worker->count <= 0 ? 1 : $worker->count;
            while (count(self::$_pidMap[$worker->workerId]) < $worker->count) {
                //创建子进程，设置当前进程用户(root)。在多进程模型中，两个子进程，分别监听不同的server地址，
                //在主进程只是创建server并没有设置监听，也没有生成指定数目的server，原因在于，
                //在一个进程多次创建同一个 socket， woker数目其实就是 socket 数量，也就是该 socket 的子进程数目，否则会报错；
                static::forkOneWorker($worker);
            }
        }
    }

    protected static function forkOneWorker($worker)
    {
        $id = self::getId($worker->workerId, 0);
        if ($id === false) {
            return;
        }
        // fork前子进程继承父进程，共享代码空间，数据完整拷贝
        // 但在pcntl_fork()后子进程和父进程就没有任何继承关系了
        $pid = pcntl_fork();
        // For master process.
        if ($pid > 0) {
            // 将子进程的号码，记录到父进程中
            self::$_pidMap[$worker->workerId][$pid] = $pid;
            // 父进程将自己的pid写入到idMap的第一位（重要）
            self::$_idMap[$worker->workerId][$id]   = $pid;
        } 
        elseif (0 === $pid) {
            if ($worker->reusePort) {
                $worker->listen();
            }
            if (self::$_status === self::STATUS_STARTING) {
                self::resetStd();
            }
            // 将继承父进程_pidMap，_workers初始化
            self::$_pidMap  = array();
            self::$_workers = array($worker->workerId => $worker);
            Timer::delAll();//  取消定时器
            self::setProcessTitle('WorkerMan: worker process  ' . $worker->name . ' ' . $worker->getSocketName());
            // 设置子进程的uid和gid
            $worker->setUserAndGroup();
            $worker->id = $id;
            // 让每个子进程下都开始启动对应worker的服务
            // 初始化Timer
            $worker->run();
            exit(250);
        } else {
            throw new Exception("forkOneWorker fail");
        }
    }

    /**
     * Get worker id.
     *
     * @param int $worker_id
     * @param int $pid
     */
    protected static function getId($worker_id, $pid)
    {
        return array_search($pid, self::$_idMap[$worker_id]);
    }

    // 设置进程的uid和gid
    public function setUserAndGroup()
    {
        // $this->user 在initWorkers初始化
        $user_info = posix_getpwnam($this->user);
        if (!$user_info) {
            self::log("Warning: User {$this->user} not exsits");
            return;
        }
        $uid = $user_info['uid'];
        if ($this->group) {
            $group_info = posix_getgrnam($this->group);
            if (!$group_info) {
                self::log("Warning: Group {$this->group} not exsits");
                return;
            }
            $gid = $group_info['gid'];
        } else {
            $gid = $user_info['gid'];
        }
        // 设置进程的uid和gid
        if ($uid != posix_getuid() || $gid != posix_getgid()) {
            if (!posix_setgid($gid) || !posix_initgroups($user_info['name'], $gid) || !posix_setuid($uid)) {
                self::log("Warning: change gid or uid fail.");
            }
        }
    }

    /**
     * Set process name.
     *
     * @param string $title
     * @return void
     */
    protected static function setProcessTitle($title)
    {
        // >=php 5.5
        if (function_exists('cli_set_process_title')) {
            @cli_set_process_title($title);// 设置当前进程的标题
        } // Need proctitle when php<=5.5 .
        elseif (extension_loaded('proctitle') && function_exists('setproctitle')) {
            // 如果不存在上面的方法，那么使用proc_title扩展
            @setproctitle($title);
        }
    }

    //  监控所有子进程（worker进程）
    protected static function monitorWorkers()
    {
        self::$_status = self::STATUS_RUNNING;
        while (1) {
            pcntl_signal_dispatch();
            $status = 0;// 阻塞等待接收消息或子进程退出，任意与调用进程组ID相同的子进程。
            // WUNTRACED 子进程已经退出并且其状态未报告时返回。返回退出的子进程进程号
            // 发生错误时返回-1（status情况返回-1）
            $pid    = pcntl_wait($status, WUNTRACED);
            // Calls signal handlers for pending signals again.
            pcntl_signal_dispatch();
            // 只有父进程才会监控所有的子进程，因为子进程运行的是run方法
            // 处理退出的子进程
            if ($pid > 0) {
                // Find out witch worker process exited.
                foreach (self::$_pidMap as $worker_id => $worker_pid_array) {
                    if (isset($worker_pid_array[$pid])) {
                        $worker = self::$_workers[$worker_id];
                        if ($status !== 0) {
                            self::log("worker[" . $worker->name . ":$pid] exit with status $status");
                        }
                        if (!isset(self::$_globalStatistics['worker_exit_info'][$worker_id][$status])) {
                            self::$_globalStatistics['worker_exit_info'][$worker_id][$status] = 0;
                        }
                        self::$_globalStatistics['worker_exit_info'][$worker_id][$status]++;//？？？？？？？
                        // Clear process data.
                        unset(self::$_pidMap[$worker_id][$pid]);
                        // Mark id is available.
                        $id = self::getId($worker_id, $pid);
                        self::$_idMap[$worker_id][$id] = 0;
                        break;
                    }
                }
                self::log(self::STATUS_SHUTDOWN);
                // Is still running state then fork a new worker process.
                if (self::$_status !== self::STATUS_SHUTDOWN) {
                    self::forkWorkers();
                    // If reloading continue.
                    if (isset(self::$_pidsToRestart[$pid])) {
                        unset(self::$_pidsToRestart[$pid]);
                        self::reload();
                    }
                } else {
                    // 如果所有进程已结束
                    if (!self::getAllWorkerPids()) {
                        // 删除配置文件
                        self::exitAndClearAll();
                    }
                }
            } else {
                // If shutdown state and all child processes exited then master process exit.
                if (self::$_status === self::STATUS_SHUTDOWN && !self::getAllWorkerPids()) {
                    self::exitAndClearAll();
                }
            }
        }
    }

    /**
     * Exit current process.
     *
     * @return void
     */
    protected static function exitAndClearAll()
    {
        foreach (self::$_workers as $worker) {
            $socket_name = $worker->getSocketName();
            if ($worker->transport === 'unix' && $socket_name) {
                list(, $address) = explode(':', $socket_name, 2);
                @unlink($address);
            }
        }
        @unlink(self::$pidFile);
        self::log("Workerman[" . basename(self::$_startFile) . "] has been stopped");
        exit(0);
    }


    protected static function reload()
    {
        // 在master进程
        if (self::$_masterPid === posix_getpid()) {
            // 设置reload状态
            if (self::$_status !== self::STATUS_RELOADING && self::$_status !== self::STATUS_SHUTDOWN) {
                self::log("Workerman[" . basename(self::$_startFile) . "] reloading");
                self::$_status = self::STATUS_RELOADING;
                // 如果需要执行回调
                if (self::$onMasterReload) {
                    try {
                        call_user_func(self::$onMasterReload);
                    } catch (\Exception $e) {
                        self::log($e);
                        exit(250);
                    } catch (\Error $e) {
                        self::log($e);
                        exit(250);
                    }
                    self::initId();
                }
            }
            // 获得生存周期中的进程ID
            $reloadable_pid_array = array();
            foreach (self::$_pidMap as $worker_id => $worker_pid_array) {
                $worker = self::$_workers[$worker_id];
                if ($worker->reloadable) {
                    foreach ($worker_pid_array as $pid) {
                        $reloadable_pid_array[$pid] = $pid;
                    }
                } else {
                    foreach ($worker_pid_array as $pid) {
                        // Send reload signal to a worker process which reloadable is false.
                        posix_kill($pid, SIGUSR1);
                    }
                }
            }
            // 获得需要重启的进程
            // array_intersect 计算数组的交集
            self::$_pidsToRestart = array_intersect(self::$_pidsToRestart, $reloadable_pid_array);
            if (empty(self::$_pidsToRestart)) {
                if (self::$_status !== self::STATUS_SHUTDOWN) {
                    self::$_status = self::STATUS_RUNNING;
                }
                return;
            }
            $one_worker_pid = current(self::$_pidsToRestart);
            posix_kill($one_worker_pid, SIGUSR1);
            // If the process does not exit after self::KILL_WORKER_TIMER_TIME seconds try to kill it.
            Timer::add(self::KILL_WORKER_TIMER_TIME, 'posix_kill', array($one_worker_pid, SIGKILL), false);
        } // For child processes.
        else {
            $worker = current(self::$_workers);
            // Try to emit onWorkerReload callback.
            if ($worker->onWorkerReload) {
                try {
                    call_user_func($worker->onWorkerReload, $worker);
                } catch (\Exception $e) {
                    self::log($e);
                    exit(250);
                } catch (\Error $e) {
                    self::log($e);
                    exit(250);
                }
            }

            if ($worker->reloadable) {
                self::stopAll();
            }
        }
    }

    /**
     * Stop.
     *
     * @return void
     */
    public static function stopAll()
    {
        self::$_status = self::STATUS_SHUTDOWN;
        // For master process.
        if (self::$_masterPid === posix_getpid()) {
            self::log("Workerman[" . basename(self::$_startFile) . "] Stopping ...");
            $worker_pid_array = self::getAllWorkerPids();
            // Send stop signal to all child processes.
            foreach ($worker_pid_array as $worker_pid) {
                posix_kill($worker_pid, SIGINT);
                Timer::add(self::KILL_WORKER_TIMER_TIME, 'posix_kill', array($worker_pid, SIGKILL), false);
            }
        } // For child processes.
        else {
            // Execute exit.
            foreach (self::$_workers as $worker) {
                $worker->stop();
            }
            exit(0);
        }
    }

    /**
     * Write statistics data to disk.
     *
     * @return void
     */
    protected static function writeStatisticsToStatusFile()
    {
        // For master process.
        if (self::$_masterPid === posix_getpid()) {
            $loadavg = sys_getloadavg();
            file_put_contents(self::$_statisticsFile,
                "---------------------------------------GLOBAL STATUS--------------------------------------------\n");
            file_put_contents(self::$_statisticsFile,
                'Workerman version:' . Worker::VERSION . "          PHP version:" . PHP_VERSION . "\n", FILE_APPEND);
            file_put_contents(self::$_statisticsFile, 'start time:' . date('Y-m-d H:i:s',
                    self::$_globalStatistics['start_timestamp']) . '   run ' . floor((time() - self::$_globalStatistics['start_timestamp']) / (24 * 60 * 60)) . ' days ' . floor(((time() - self::$_globalStatistics['start_timestamp']) % (24 * 60 * 60)) / (60 * 60)) . " hours   \n",
                FILE_APPEND);
            $load_str = 'load average: ' . implode(", ", $loadavg);
            file_put_contents(self::$_statisticsFile,
                str_pad($load_str, 33) . 'event-loop:' . self::getEventLoopName() . "\n", FILE_APPEND);
            file_put_contents(self::$_statisticsFile,
                count(self::$_pidMap) . ' workers       ' . count(self::getAllWorkerPids()) . " processes\n",
                FILE_APPEND);
            file_put_contents(self::$_statisticsFile,
                str_pad('worker_name', self::$_maxWorkerNameLength) . " exit_status     exit_count\n", FILE_APPEND);
            foreach (self::$_pidMap as $worker_id => $worker_pid_array) {
                $worker = self::$_workers[$worker_id];
                if (isset(self::$_globalStatistics['worker_exit_info'][$worker_id])) {
                    foreach (self::$_globalStatistics['worker_exit_info'][$worker_id] as $worker_exit_status => $worker_exit_count) {
                        file_put_contents(self::$_statisticsFile,
                            str_pad($worker->name, self::$_maxWorkerNameLength) . " " . str_pad($worker_exit_status,
                                16) . " $worker_exit_count\n", FILE_APPEND);
                    }
                } else {
                    file_put_contents(self::$_statisticsFile,
                        str_pad($worker->name, self::$_maxWorkerNameLength) . " " . str_pad(0, 16) . " 0\n",
                        FILE_APPEND);
                }
            }
            file_put_contents(self::$_statisticsFile,
                "---------------------------------------PROCESS STATUS-------------------------------------------\n",
                FILE_APPEND);
            file_put_contents(self::$_statisticsFile,
                "pid\tmemory  " . str_pad('listening', self::$_maxSocketNameLength) . " " . str_pad('worker_name',
                    self::$_maxWorkerNameLength) . " connections " . str_pad('total_request',
                    13) . " " . str_pad('send_fail', 9) . " " . str_pad('throw_exception', 15) . "\n", FILE_APPEND);

            chmod(self::$_statisticsFile, 0722);

            foreach (self::getAllWorkerPids() as $worker_pid) {
                posix_kill($worker_pid, SIGUSR2);
            }
            return;
        }

        // For child processes.
        /** @var Worker $worker */
        $worker           = current(self::$_workers);
        $worker_status_str = posix_getpid() . "\t" . str_pad(round(memory_get_usage(true) / (1024 * 1024), 2) . "M",
                7) . " " . str_pad($worker->getSocketName(),
                self::$_maxSocketNameLength) . " " . str_pad(($worker->name === $worker->getSocketName() ? 'none' : $worker->name),
                self::$_maxWorkerNameLength) . " ";
        $worker_status_str .= str_pad(ConnectionInterface::$statistics['connection_count'],
                11) . " " . str_pad(ConnectionInterface::$statistics['total_request'],
                14) . " " . str_pad(ConnectionInterface::$statistics['send_fail'],
                9) . " " . str_pad(ConnectionInterface::$statistics['throw_exception'], 15) . "\n";
        file_put_contents(self::$_statisticsFile, $worker_status_str, FILE_APPEND);
    }

    /**
     * Check errors when current process exited.
     *
     * @return void
     */
    public static function checkErrors()
    {
        if (self::STATUS_SHUTDOWN != self::$_status) {
            $error_msg = "WORKER EXIT UNEXPECTED ";
            $errors    = error_get_last();
            if ($errors && ($errors['type'] === E_ERROR ||
                    $errors['type'] === E_PARSE ||
                    $errors['type'] === E_CORE_ERROR ||
                    $errors['type'] === E_COMPILE_ERROR ||
                    $errors['type'] === E_RECOVERABLE_ERROR)
            ) {
                $error_msg .= self::getErrorType($errors['type']) . " {$errors['message']} in {$errors['file']} on line {$errors['line']}";
            }
            self::log($error_msg);
        }
    }

    /**
     * Get error message by error code.
     *
     * @param integer $type
     * @return string
     */
    protected static function getErrorType($type)
    {
        switch ($type) {
            case E_ERROR: // 1 //
                return 'E_ERROR';
            case E_WARNING: // 2 //
                return 'E_WARNING';
            case E_PARSE: // 4 //
                return 'E_PARSE';
            case E_NOTICE: // 8 //
                return 'E_NOTICE';
            case E_CORE_ERROR: // 16 //
                return 'E_CORE_ERROR';
            case E_CORE_WARNING: // 32 //
                return 'E_CORE_WARNING';
            case E_COMPILE_ERROR: // 64 //
                return 'E_COMPILE_ERROR';
            case E_COMPILE_WARNING: // 128 //
                return 'E_COMPILE_WARNING';
            case E_USER_ERROR: // 256 //
                return 'E_USER_ERROR';
            case E_USER_WARNING: // 512 //
                return 'E_USER_WARNING';
            case E_USER_NOTICE: // 1024 //
                return 'E_USER_NOTICE';
            case E_STRICT: // 2048 //
                return 'E_STRICT';
            case E_RECOVERABLE_ERROR: // 4096 //
                return 'E_RECOVERABLE_ERROR';
            case E_DEPRECATED: // 8192 //
                return 'E_DEPRECATED';
            case E_USER_DEPRECATED: // 16384 //
                return 'E_USER_DEPRECATED';
        }
        return "";
    }

    /**
     * Log.
     *
     * @param string $msg
     * @return void
     */
    public static function log($msg)
    {
        $msg = $msg . "\n";
        if (!self::$daemonize) {
            self::safeEcho($msg);
        }
        file_put_contents((string)self::$logFile, date('Y-m-d H:i:s') . ' ' . 'pid:'. posix_getpid() . ' ' . $msg, FILE_APPEND | LOCK_EX);
    }

    /**
     * Safe Echo.
     *
     * @param $msg
     */
    public static function safeEcho($msg)
    {
        if (!function_exists('posix_isatty') || posix_isatty(STDOUT)) {
            echo $msg;
        }
    }

    /**
     * Construct.
     *
     * @param string $socket_name
     * @param array  $context_option
     */
    public function __construct($socket_name = '', $context_option = array())
    {
        // Save all worker instances.
        $this->workerId                  = spl_object_hash($this);//生成hashid，并且同一个对象生成的id是一样的
        self::$_workers[$this->workerId] = $this;
        self::$_pidMap[$this->workerId]  = array();

        // Get autoload root path.
        $backtrace                = debug_backtrace();
        //例如/home/www.wkm.c7/Workerman/Worker.php
        $this->_autoloadRootPath = dirname($backtrace[0]['file']);

        // Context for socket.
        if ($socket_name) {
            $this->_socketName = $socket_name;
            if (!isset($context_option['socket']['backlog'])) {
                $context_option['socket']['backlog'] = self::DEFAULT_BACKLOG;
            }
            $this->_context = stream_context_create($context_option);//创建资源流上下文？
        }

        // Set an empty onMessage callback.
        $this->onMessage = function () {//？？？？？？？？？？？？
        };
    }

    public function listen()
    {
        if (!$this->_socketName || $this->_mainSocket) {
            return;
        }
        // 例如/home/www.wkm.c7/Workerman/Worker.php
        Autoloader::setRootPath($this->_autoloadRootPath);
        // 例如websocket://0.0.0.0:2346
        $local_socket = $this->_socketName;
        list($scheme, $address) = explode(':', $this->_socketName, 2);
        if (!isset(self::$_builtinTransports[$scheme])) {
            if(class_exists($scheme)){
                $this->protocol = $scheme;
            } else {
                $scheme = ucfirst($scheme);//将字符串第一个字符改大写。
                $this->protocol = '\\Protocols\\' . $scheme;
                if (!class_exists($this->protocol)) {
                    $this->protocol = "\\Workerman\\Protocols\\$scheme";
                    if (!class_exists($this->protocol)) {
                        throw new Exception("class \\Protocols\\$scheme not exist");
                    }
                }
            }
            $local_socket = $this->transport . ":" . $address;
        } else {
            $this->transport = self::$_builtinTransports[$scheme];
        }
        // STREAM_SERVER_BIND = 4
        // STREAM_SERVER_LISTEN = 8
        // STREAM_SERVER_BIND | STREAM_SERVER_LISTEN = 12
        $flags  = $this->transport === 'udp' ? STREAM_SERVER_BIND : STREAM_SERVER_BIND | STREAM_SERVER_LISTEN;
        $errno  = 0;
        $errmsg = '';
        if ($this->reusePort) {
            //对资源流、数据包或者上下文设置参数
            //so_reuseport 允许多个套接字 bind()/listen() 同一个TCP/UDP端口
            stream_context_set_option($this->_context, 'socket', 'so_reuseport', 1);
        }
        // 创建套接字服务
        $this->_mainSocket = stream_socket_server($local_socket, $errno, $errmsg, $flags, $this->_context);
        if (!$this->_mainSocket) {
            throw new Exception($errmsg);
        }
        // Try to open keepalive for tcp and disable Nagle algorithm.
        if (function_exists('socket_import_stream') && $this->transport === 'tcp') {
            // 封装套接字
            $socket = socket_import_stream($this->_mainSocket);
            //设置心跳，长连接必须
            @socket_set_option($socket, SOL_SOCKET, SO_KEEPALIVE, 1);
            //设置最小化传输延迟
            @socket_set_option($socket, SOL_TCP, TCP_NODELAY, 1);
        }
        //设置为非阻塞模式
        //在非阻塞模式下，调用 fgets() 总是会立即返回；而在阻塞模式下，将会一直等到从资源流里面获取到数据才能返回。
        stream_set_blocking($this->_mainSocket, 0);

        // 注册监听服务套接字是否可读
        if (self::$globalEvent) {
            if ($this->transport !== 'udp') {
                // 向socket添加事件监听回调函数
                self::$globalEvent->add($this->_mainSocket, EventInterface::EV_READ, array($this, 'acceptConnection'));
            } else {
                self::$globalEvent->add($this->_mainSocket, EventInterface::EV_READ, array($this, 'acceptUdpConnection'));
            }
        }
    }

    public function getSocketName()
    {
        return $this->_socketName ? lcfirst($this->_socketName) : 'none';
    }

    public function run()
    {
        self::$_status = self::STATUS_RUNNING;
        register_shutdown_function(array("\\Workerman\\Worker", 'checkErrors'));
        Autoloader::setRootPath($this->_autoloadRootPath);
        // 注册监听服务套接字是否可读
        if (!self::$globalEvent) {
            $eventLoopClass    = "\\Workerman\\Events\\" . ucfirst(self::getEventLoopName());
            self::$globalEvent = new $eventLoopClass;
            if ($this->_socketName) {
                if ($this->transport !== 'udp') {
                    // 向socket添加事件监听回调函数
                    self::$globalEvent->add($this->_mainSocket, EventInterface::EV_READ, array($this, 'acceptConnection'));
                } else {
                    self::$globalEvent->add($this->_mainSocket, EventInterface::EV_READ, array($this, 'acceptUdpConnection'));
                }
            }
        }
        // 清除子进程信号注册，使用事件监听信号
        self::reinstallSignal();
        // 仅初始化定时器事件
        Timer::init(self::$globalEvent);
        if ($this->onWorkerStart) {
            try {
                // 执行回调
                call_user_func($this->onWorkerStart, $this);
            } catch (\Exception $e) {
                self::log($e);
                exit(250);
            } catch (\Error $e) {
                self::log($e);
                exit(250);
            }
        }
        // Main loop.
        self::$globalEvent->loop();
    }

    /**
     * Stop current worker instance.
     *
     * @return void
     */
    public function stop()
    {
        // Try to emit onWorkerStop callback.
        if ($this->onWorkerStop) {
            try {
                call_user_func($this->onWorkerStop, $this);
            } catch (\Exception $e) {
                self::log($e);
                exit(250);
            } catch (\Error $e) {
                self::log($e);
                exit(250);
            }
        }
        // Remove listener for server socket.
        self::$globalEvent->del($this->_mainSocket, EventInterface::EV_READ);
        @fclose($this->_mainSocket);
    }

    /**
     * Accept a connection.
     *
     * @param resource $socket
     * @return void
     */
    public function acceptConnection($socket)
    {
        // Accept a connection on server socket.
        $new_socket = @stream_socket_accept($socket, 0, $remote_address);
        // Thundering herd.
        if (!$new_socket) {
            return;
        }

        // TcpConnection.
        $connection                         = new TcpConnection($new_socket, $remote_address);
        $this->connections[$connection->id] = $connection;
        $connection->worker                 = $this;
        $connection->protocol               = $this->protocol;
        $connection->onMessage              = $this->onMessage;
        $connection->onClose                = $this->onClose;
        $connection->onError                = $this->onError;
        $connection->onBufferDrain          = $this->onBufferDrain;
        $connection->onBufferFull           = $this->onBufferFull;

        // Try to emit onConnect callback.
        if ($this->onConnect) {
            try {
                call_user_func($this->onConnect, $connection);
            } catch (\Exception $e) {
                self::log($e);
                exit(250);
            } catch (\Error $e) {
                self::log($e);
                exit(250);
            }
        }
    }

    /**
     * For udp package.
     *
     * @param resource $socket
     * @return bool
     */
    public function acceptUdpConnection($socket)
    {
        $recv_buffer = stream_socket_recvfrom($socket, self::MAX_UDP_PACKAGE_SIZE, 0, $remote_address);
        if (false === $recv_buffer || empty($remote_address)) {
            return false;
        }
        // UdpConnection.
        $connection           = new UdpConnection($socket, $remote_address);
        $connection->protocol = $this->protocol;
        if ($this->onMessage) {
            if ($this->protocol) {
                $parser      = $this->protocol;
                $recv_buffer = $parser::decode($recv_buffer, $connection);
                // Discard bad packets.
                if ($recv_buffer === false)
                    return true;
            }
            ConnectionInterface::$statistics['total_request']++;
            try {
                call_user_func($this->onMessage, $connection, $recv_buffer);
            } catch (\Exception $e) {
                self::log($e);
                exit(250);
            } catch (\Error $e) {
                self::log($e);
                exit(250);
            }
        }
        return true;
    }
}
