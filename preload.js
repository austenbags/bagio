const { contextBridge, ipcRenderer } = require('electron');

contextBridge.exposeInMainWorld('bagioUpdater', {
  onStatus: (cb) => ipcRenderer.on('update-status', (_e, data) => cb(data)),
  onPatchNotesReady: (cb) => ipcRenderer.on('patch-notes-ready', (_e, data) => cb(data)),
  onMessage: (cb) => ipcRenderer.on('message-received', (_e, msg) => cb(msg)),
  install: () => ipcRenderer.send('install-update'),
  check: () => ipcRenderer.send('check-update'),
  getVersion: () => ipcRenderer.invoke('get-version'),
  setWindowMode: (mode) => ipcRenderer.invoke('set-window-mode', mode),
  getWindowMode: () => ipcRenderer.invoke('get-window-mode'),
  getPatchNotes: () => ipcRenderer.invoke('get-patch-notes'),
});
