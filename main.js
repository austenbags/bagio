const { app, BrowserWindow, Menu, ipcMain } = require('electron');
const path = require('path');
const fs = require('fs');

app.commandLine.appendSwitch('disable-gpu-shader-disk-cache');
app.commandLine.appendSwitch('disable-gpu-process-crash-limit');

const REPO_HEADERS = { 'User-Agent': 'AcidLab' };

let win;
let launcherWin;

function send(channel, payload) {
  if (win && !win.isDestroyed()) win.webContents.send(channel, payload);
}

function sendLauncher(payload) {
  if (launcherWin && !launcherWin.isDestroyed()) launcherWin.webContents.send('launcher-status', payload);
}

function createLauncherWindow() {
  launcherWin = new BrowserWindow({
    width: 380,
    height: 210,
    frame: false,
    resizable: false,
    center: true,
    show: false,
    backgroundColor: '#0c0d0a',
    title: 'Acid Lab',
    icon: path.join(__dirname, 'icon.png'),
    webPreferences: {
      preload: path.join(__dirname, 'preload-launcher.js'),
      contextIsolation: true,
      nodeIntegration: false
    }
  });
  launcherWin.loadFile('launcher.html');
  launcherWin.once('ready-to-show', () => launcherWin.show());
}

function createWindow() {
  win = new BrowserWindow({
    width: 1280,
    height: 820,
    minWidth: 900,
    minHeight: 600,
    backgroundColor: '#0c0d0a',
    title: 'Acid Lab',
    icon: path.join(__dirname, 'icon.png'),
    fullscreen: true,
    autoHideMenuBar: true,
    show: false,
    webPreferences: {
      preload: path.join(__dirname, 'preload.js'),
      contextIsolation: true,
      nodeIntegration: false
    }
  });
  Menu.setApplicationMenu(null);
  win.loadFile('index.html');
  win.once('ready-to-show', () => win.show());
  win.on('close', (e) => {
    e.preventDefault();
    win.webContents.executeJavaScript(
      'if(typeof ac!=="undefined"&&ac&&typeof masterGain!=="undefined"&&masterGain){masterGain.gain.setTargetAtTime(0,ac.currentTime,0.015);}'
    ).catch(()=>{});
    setTimeout(() => { try { win.destroy(); } catch(_){} }, 150);
  });
}

function setupPostWindow() {
  if (!app.isPackaged) {
    ['index.html', 'styles.css', 'app.js'].forEach(f => {
      try {
        fs.watch(path.join(__dirname, f), () => { if (win) win.webContents.reload(); });
      } catch {}
    });
  }

  const patchNotesPath = path.join(app.getPath('userData'), 'patch-notes.json');
  const bundledPatchNotesPath = path.join(__dirname, 'patch-notes.json');

  function readPatchNotes() {
    for (const p of [patchNotesPath, bundledPatchNotesPath]) {
      try { return JSON.parse(fs.readFileSync(p, 'utf8')); } catch {}
    }
    return { version: '0', blocks: [] };
  }

  ipcMain.handle('get-patch-notes', () => readPatchNotes());

  function fetchPatchNotes() {
    const https = require('https');
    const url = 'https://raw.githubusercontent.com/austenbags/bagio/main/patch-notes.json';
    const req = https.get(url, { headers: REPO_HEADERS }, (res) => {
      if (res.statusCode !== 200) return;
      let data = '';
      res.on('data', d => data += d);
      res.on('end', () => {
        try {
          const notes = JSON.parse(data);
          if (!notes.version) return;
          try { fs.writeFileSync(patchNotesPath, JSON.stringify(notes, null, 2)); } catch {}
          send('patch-notes-ready', notes);
        } catch {}
      });
    });
    req.on('error', () => {});
    req.setTimeout(8000, () => req.destroy());
  }
  setTimeout(fetchPatchNotes, 2000);

  let _lastMsgId = null;
  function fetchMessages() {
    const https = require('https');
    const url = 'https://raw.githubusercontent.com/austenbags/bagio/main/messages.json';
    const req = https.get(url, { headers: REPO_HEADERS }, (res) => {
      if (res.statusCode !== 200) return;
      let data = '';
      res.on('data', d => data += d);
      res.on('end', () => {
        try {
          const parsed = JSON.parse(data);
          const msgs = parsed.messages || [];
          if (msgs.length > 0 && msgs[0].id !== _lastMsgId) {
            _lastMsgId = msgs[0].id;
            send('message-received', msgs[0]);
          }
        } catch {}
      });
    });
    req.on('error', () => {});
    req.setTimeout(8000, () => req.destroy());
  }
  setTimeout(fetchMessages, 5000);
  setInterval(fetchMessages, 5 * 60 * 1000);

  ipcMain.handle('get-version',     () => app.getVersion());
  ipcMain.handle('set-window-mode', (_, mode) => {
    if (mode === 'fullscreen') win.setFullScreen(true); else win.setFullScreen(false);
  });
  ipcMain.handle('get-window-mode', () => win.isFullScreen() ? 'fullscreen' : 'windowed');

  app.on('activate', () => {
    if (BrowserWindow.getAllWindows().length === 0) createWindow();
  });
}

app.whenReady().then(() => {
  if (app.isPackaged) {
    createLauncherWindow();

    let proceeded = false;
    function proceedToApp() {
      if (proceeded) return;
      proceeded = true;
      createWindow();
      setupPostWindow();
      setTimeout(() => {
        try { if (launcherWin && !launcherWin.isDestroyed()) launcherWin.close(); } catch {}
        launcherWin = null;
      }, 500);
    }

    if (process.platform === 'darwin') {
      // macOS build is unsigned — skip auto-updater to avoid Gatekeeper errors
      sendLauncher({ state: 'none' });
      setTimeout(proceedToApp, 600);
    } else {
      const { autoUpdater } = require('electron-updater');
      const logPath = path.join(app.getPath('userData'), 'update-log.txt');
      function logUpdate(msg) {
        const line = `[${new Date().toISOString()}] ${msg}\n`;
        try { fs.appendFileSync(logPath, line); } catch {}
        console.log('[updater]', msg);
      }

      autoUpdater.autoDownload = true;
      autoUpdater.autoInstallOnAppQuit = false;
      autoUpdater.allowPrerelease = false;
      autoUpdater.requestHeaders = {};

      autoUpdater.on('checking-for-update', () => {
        logUpdate('Checking for updates…');
        send('update-status', { state: 'checking' });
      });

      autoUpdater.on('update-not-available', (info) => {
        logUpdate(`Up to date: ${info.version}`);
        sendLauncher({ state: 'none' });
        send('update-status', { state: 'none' });
        setTimeout(proceedToApp, 700);
      });

      autoUpdater.on('update-available', (info) => {
        logUpdate(`Update available: ${info.version}`);
        sendLauncher({ state: 'available', version: info.version });
        send('update-status', { state: 'available', version: info.version });
      });

      autoUpdater.on('download-progress', (p) => {
        sendLauncher({ state: 'downloading', percent: Math.round(p.percent) });
        send('update-status', { state: 'downloading', percent: Math.round(p.percent) });
      });

      autoUpdater.on('update-downloaded', (info) => {
        logUpdate(`Update downloaded: ${info.version}`);
        sendLauncher({ state: 'restarting' });
        send('update-status', { state: 'restarting' });
        setTimeout(() => autoUpdater.quitAndInstall(true, true), 1500);
      });

      autoUpdater.on('error', (err) => {
        logUpdate(`Update error: ${String(err)}`);
        sendLauncher({ state: 'error' });
        send('update-status', { state: 'error', message: String(err) });
        setTimeout(proceedToApp, 1200);
      });

      // Fallback — if GitHub takes too long or is unreachable, don't block launch forever
      setTimeout(() => {
        if (!proceeded) {
          logUpdate('Update check timed out — proceeding to app');
          sendLauncher({ state: 'error' });
          send('update-status', { state: 'error', message: 'Update check timed out' });
          proceedToApp();
        }
      }, 10000);

      logUpdate(`App started. Version: ${app.getVersion()}`);
      autoUpdater.checkForUpdates().catch(e => {
        logUpdate('checkForUpdates error: ' + e);
        sendLauncher({ state: 'error' });
        send('update-status', { state: 'error', message: String(e) });
        setTimeout(proceedToApp, 1200);
      });

      ipcMain.on('check-update', () => {
        logUpdate('Manual check triggered');
        send('update-status', { state: 'checking' });
        autoUpdater.checkForUpdates().catch(e => {
          logUpdate('Manual check error: ' + e);
          send('update-status', { state: 'error', message: String(e) });
        });
      });
      ipcMain.on('install-update', () => autoUpdater.quitAndInstall(true, true));
    }

  } else {
    // Dev mode — skip launcher and updater entirely
    createWindow();
    setupPostWindow();
  }
});

app.on('window-all-closed', () => {
  app.quit();
});
