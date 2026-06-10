const { contextBridge, ipcRenderer } = require('electron');
contextBridge.exposeInMainWorld('electronLauncher', {
  onStatus: (cb) => ipcRenderer.on('launcher-status', (_, data) => cb(data))
});
