"use strict";
const STEPS=16;
const NOTE_NAMES=["C","C#","D","D#","E","F","F#","G","G#","A","A#","B"];
const BLACK=[1,3,6,8,10];
const WHITE=[0,2,4,5,7,9,11];
const ACID_BASE=36, ACID_ROWS=13;
const POLY_BASE=48, POLY_ROWS=16;
function midiToFreq(m){return 440*Math.pow(2,(m-69)/12);}
function noteLabel(m){return NOTE_NAMES[((m%12)+12)%12]+(Math.floor(m/12)-1);}

const CHORDS={maj:[0,4,7],min:[0,3,7],maj7:[0,4,7,11],min7:[0,3,7,10],dom7:[0,4,7,10],
  sus2:[0,2,7],sus4:[0,5,7],dim:[0,3,6],aug:[0,4,8],min9:[0,3,7,10,14],maj9:[0,4,7,11,14]};

const DRUMS=["kick","snare","clap","hat","ohat","tom","rim","cowbell","ride","shaker"];
const DRUM_LABELS={kick:"kick",snare:"snare",clap:"clap",hat:"hat",ohat:"open hat",tom:"tom",rim:"rim",cowbell:"cowbell",ride:"ride",shaker:"shaker"};

function emptyPattern(){
  const d={}; DRUMS.forEach(k=>d[k]=new Array(STEPS).fill(false));
  return {acid:{notes:new Array(STEPS).fill(null),acc:new Array(STEPS).fill(false),sld:new Array(STEPS).fill(false)},
    poly:Array.from({length:STEPS},()=>new Array(POLY_ROWS).fill(false)),drums:d,pianoRoll:[]};
}
function fixDrums(p){if(!p.drums)p.drums={};DRUMS.forEach(d=>{if(!Array.isArray(p.drums[d])||p.drums[d].length!==STEPS)p.drums[d]=new Array(STEPS).fill(false);});
  if(!p.poly||p.poly.length!==STEPS)p.poly=Array.from({length:STEPS},()=>new Array(POLY_ROWS).fill(false));
  if(!Array.isArray(p.pianoRoll))p.pianoRoll=[];}

let patterns=[emptyPattern()];

let curPattern=0, song=[0], songMode=false, songPos=0;
let AP={wave:"sawtooth",cut:480,res:0.78,env:0.72,dec:0.28,acc:0.6,drv:0.25,dly:0.12};
let PP={wave:"sawtooth",cut:3500,res:0.2,atk:0.01,rel:0.4,dly:0.18,rev:0.3,detune:8,sub:0,fenv:0,lfoRate:0,lfoDepth:0};
let mixLevel={acid:0.85,poly:0.55,kick:0.95,snare:0.7,clap:0.7,hat:0.5,ohat:0.45,tom:0.6,rim:0.45,cowbell:0.45,ride:0.4,shaker:0.4};
let mixMute={}; Object.keys(mixLevel).forEach(k=>mixMute[k]=false);
let tempo=124, swing=0.12, master=0.8, revMix=0.16;
let arp={on:false,mode:"up",rate:2,oct:1};
const arr16=()=>new Array(STEPS).fill(false);
let samples=[], sampleSeq=0;
const polyVoices=new Map();
let patClipboard=null;
let selectedWindows=new Set(), winClipboard=null;

const PRESETS={
  pad:{wave:"sawtooth",detune:18,sub:0.2,cut:1800,res:0.15,fenv:0.2,atk:0.3,rel:1.1,lfoRate:0.4,lfoDepth:700,dly:0.2,rev:0.55},
  pluck:{wave:"sawtooth",detune:6,sub:0,cut:4200,res:0.32,fenv:0.7,atk:0.004,rel:0.25,lfoRate:0,lfoDepth:0,dly:0.12,rev:0.18},
  lead:{wave:"square",detune:10,sub:0.1,cut:5200,res:0.25,fenv:0.3,atk:0.01,rel:0.32,lfoRate:5,lfoDepth:200,dly:0.22,rev:0.2},
  organ:{wave:"square",detune:0,sub:0.32,cut:6500,res:0.1,fenv:0,atk:0.005,rel:0.16,lfoRate:0,lfoDepth:0,dly:0.1,rev:0.12},
  bell:{wave:"triangle",detune:14,sub:0,cut:8500,res:0.22,fenv:0.55,atk:0.002,rel:0.7,lfoRate:0,lfoDepth:0,dly:0.16,rev:0.45},
  strings:{wave:"sawtooth",detune:24,sub:0.1,cut:2600,res:0.12,fenv:0.15,atk:0.25,rel:1.3,lfoRate:0.3,lfoDepth:500,dly:0.18,rev:0.6}
};

/* ---------- audio engine ---------- */
let ac=null,masterGain,comp,eqLow,eqMid,eqHigh,limiter,drySum,noiseBuf,delayNode,delayFb,delaySend,revConv,revSend,recDest,mediaRec,recChunks=[];
const APP_BUSES = {}; // per-app audio routing: {input:GainNode, output:GainNode}
let wmAnalyser=null,wmData=null,wmImg=null;
let recMimeType='audio/webm';
let prevAcidFreq=null;
function makeNoise(ctx){const len=ctx.sampleRate,b=ctx.createBuffer(1,len,ctx.sampleRate),d=b.getChannelData(0);for(let i=0;i<len;i++)d[i]=Math.random()*2-1;return b;}
function makeImpulse(ctx,dur,dec){const len=ctx.sampleRate*dur,b=ctx.createBuffer(2,len,ctx.sampleRate);for(let c=0;c<2;c++){const d=b.getChannelData(c);for(let i=0;i<len;i++)d[i]=(Math.random()*2-1)*Math.pow(1-i/len,dec);}return b;}
function driveCurve(a){const k=a*120,n=2048,c=new Float32Array(n);for(let i=0;i<n;i++){const x=i*2/n-1;c[i]=(3+k)*x*0.3/(1+k*Math.abs(x)*0.1);}return c;}
function ensureAudio(){
  if(ac){if(ac.state==='suspended')ac.resume().catch(()=>{});return;}
  ac=new (window.AudioContext||window.webkitAudioContext)({latencyHint:'balanced'});
  noiseBuf=makeNoise(ac);
  masterGain=ac.createGain();masterGain.gain.value=master;
  comp=ac.createDynamicsCompressor();comp.threshold.value=-8;comp.ratio.value=6;comp.attack.value=0.003;comp.release.value=0.15;
  // --- 3-band master EQ ---
  eqLow=ac.createBiquadFilter();eqLow.type="lowshelf";eqLow.frequency.value=200;eqLow.gain.value=0;
  eqMid=ac.createBiquadFilter();eqMid.type="peaking";eqMid.frequency.value=1000;eqMid.Q.value=0.9;eqMid.gain.value=0;
  eqHigh=ac.createBiquadFilter();eqHigh.type="highshelf";eqHigh.frequency.value=4000;eqHigh.gain.value=0;
  // --- master limiter (fast brickwall-ish) ---
  limiter=ac.createDynamicsCompressor();limiter.threshold.value=-2;limiter.ratio.value=20;limiter.attack.value=0.001;limiter.release.value=0.08;limiter.knee.value=0;
  drySum=ac.createGain();drySum.connect(masterGain);
  delaySend=ac.createGain();delayNode=ac.createDelay(1.0);delayFb=ac.createGain();delayFb.gain.value=0.36;
  const _delayDC=ac.createConstantSource();_delayDC.offset.value=1e-10;_delayDC.start();_delayDC.connect(delayFb);
  delaySend.connect(delayNode);delayNode.connect(delayFb);delayFb.connect(delayNode);delayNode.connect(masterGain);
  revSend=ac.createGain();revConv=ac.createConvolver();revConv.buffer=makeImpulse(ac,2.6,2.2);revSend.connect(revConv);revConv.connect(masterGain);
  masterGain.connect(eqLow);eqLow.connect(eqMid);eqMid.connect(eqHigh);eqHigh.connect(comp);comp.connect(limiter);
  recDest=ac.createMediaStreamDestination();
  limiter.connect(recDest);
  wmAnalyser=ac.createAnalyser();wmAnalyser.fftSize=256;wmAnalyser.smoothingTimeConstant=0.82;
  wmData=new Uint8Array(wmAnalyser.frequencyBinCount);masterGain.connect(wmAnalyser);
  // Route audio through an HTMLAudioElement so we can reliably switch output devices
  let _outEl = document.getElementById('_acid-out');
  if (!_outEl) {
    _outEl = document.createElement('audio');
    _outEl.id = '_acid-out'; _outEl.style.display = 'none'; _outEl.autoplay = true;
    document.body.appendChild(_outEl);
  }
  _outEl.srcObject = recDest.stream;
  _outEl.play().catch(() => {});
  window._acidOutEl = _outEl;
  // Apply saved output device
  const _savedOut = localStorage.getItem('acid-audio-out');
  if (_savedOut && _outEl.setSinkId) _outEl.setSinkId(_savedOut).catch(() => {});
  // Determine best supported recording format
  recMimeType=['audio/webm;codecs=opus','audio/webm','audio/ogg;codecs=opus','audio/ogg'].find(t=>MediaRecorder.isTypeSupported(t))||'audio/webm';
  updateDelayTime();
  initAppBuses();
  // Init buses for any instance windows spawned before audio was ready
  document.querySelectorAll('.window[id]').forEach(w=>{
    const m=w.id.match(/^(.+)-i\d+$/);
    if(m&&!APP_BUSES[w.id])initInstanceBus(w.id,m[1]);
  });
}
// Resume AudioContext whenever the page regains focus (Electron can suspend it on minimize/hide)
document.addEventListener('visibilitychange',()=>{if(ac&&document.visibilityState==='visible'&&ac.state==='suspended')ac.resume().catch(()=>{});});
window.addEventListener('focus',()=>{if(ac&&ac.state==='suspended')ac.resume().catch(()=>{});});
function updateDelayTime(){if(delayNode)delayNode.delayTime.value=(60/tempo)*0.75;}
function out(node, key, targetBus) {
  const g = ac.createGain(); g.gain.value = mixMute[key] ? 0 : 1;
  node.connect(g); g.connect(targetBus || drySum); return g;
}
function initAppBuses() {
  const ids = ['win-keyboard','win-acid','win-poly','win-drum','win-sampler',
               'win-mixer','win-effects','win-spectrum','win-reverb','win-compressor',
               'win-arp','win-lfo','win-transport','win-patterns','win-pianoroll','win-settings',
               'win-eq','win-delay','win-scope','win-lofi','win-gate','win-chordgen','win-tone',
               'win-merge','win-vol','win-pan','win-chorus','win-tremolo','win-phaser',
               'win-granular','win-flanger','win-ringmod','win-autofilter','win-noise',
               'win-padboard','win-bitcrush','win-cabinet','win-stereoimg','win-comb',
               'win-distortion','win-multicomp','win-wavetable','win-stepseq','win-tape',
               'win-formant','win-sidechain','win-glitch','win-osc-bank','win-freqshift'];
  ids.forEach(id => {
    if (!APP_BUSES[id]) {
      const input = ac.createGain();
      const output = ac.createGain();
      output.connect(drySum);
      APP_BUSES[id] = {input, output};
    }
  });
  // Reverb: input → predelay → convolver → wet+dry → output
  (function(){
    const b = APP_BUSES['win-reverb'];
    const pre = ac.createDelay(0.1); pre.delayTime.value = 0.015;
    const conv = ac.createConvolver(); conv.buffer = makeImpulse(ac, 1.8, 2.2);
    const wet = ac.createGain(); wet.gain.value = 0.35;
    const dry = ac.createGain(); dry.gain.value = 0.65;
    const damp = ac.createBiquadFilter(); damp.type = 'lowpass'; damp.frequency.value = 8000;
    b.input.connect(dry); dry.connect(b.output);
    b.input.connect(pre); pre.connect(conv); conv.connect(damp); damp.connect(wet); wet.connect(b.output);
    b._rev = {pre, conv, wet, dry, damp};
  })();
  // Compressor: input → dynamics compressor → makeup gain → output
  (function(){
    const b = APP_BUSES['win-compressor'];
    const node = ac.createDynamicsCompressor();
    node.threshold.value = -18; node.ratio.value = 4;
    node.attack.value = 0.01; node.release.value = 0.1; node.knee.value = 3;
    const makeup = ac.createGain(); makeup.gain.value = Math.pow(10, 4/20);
    b.input.connect(node); node.connect(makeup); makeup.connect(b.output);
    b._comp = {node, makeup};
  })();
  // Spectrum: tap monitor — audio passes through while being analysed
  (function(){
    const b = APP_BUSES['win-spectrum'];
    const analyser = ac.createAnalyser(); analyser.fftSize = 2048; analyser.smoothingTimeConstant = 0.8;
    b.input.connect(analyser);
    b.input.connect(b.output);
    try { b.output.disconnect(drySum); } catch(e) {}
    b._analyser = analyser;
  })();
  // EQ 5-band: lowshelf@80 → peaking@250 → peaking@1k → peaking@4k → highshelf@12k
  (function(){
    const b=APP_BUSES['win-eq'];
    const freqs=[80,250,1000,4000,12000];
    const types=['lowshelf','peaking','peaking','peaking','highshelf'];
    const bands=freqs.map((f,i)=>{const n=ac.createBiquadFilter();n.type=types[i];n.frequency.value=f;if(types[i]==='peaking')n.Q.value=0.8;return n;});
    b.input.connect(bands[0]);
    bands.forEach((bn,i)=>{if(bands[i+1])bn.connect(bands[i+1]);});
    bands[bands.length-1].connect(b.output);
    b._bands=bands;
  })();
  // Delay: input → dry+delay(feedback loop) → panner → output
  (function(){
    const b=APP_BUSES['win-delay'];
    const dly=ac.createDelay(2.0);dly.delayTime.value=0.5;
    const fb=ac.createGain();fb.gain.value=0.35;
    const dry=ac.createGain();dry.gain.value=0.7;
    const wet=ac.createGain();wet.gain.value=0.4;
    const panner=ac.createStereoPanner();panner.pan.value=0;
    b.input.connect(dry);dry.connect(b.output);
    b.input.connect(dly);dly.connect(fb);fb.connect(dly);dly.connect(wet);wet.connect(panner);panner.connect(b.output);
    b._dly={dly,fb,dry,wet,panner};
  })();
  // Scope: tap with analyser, passthrough
  (function(){
    const b=APP_BUSES['win-scope'];
    const analyser=ac.createAnalyser();analyser.fftSize=2048;analyser.smoothingTimeConstant=0.3;
    b.input.connect(analyser);b.input.connect(b.output);
    try{b.output.disconnect(drySum);}catch(e){}
    b._scopeAnalyser=analyser;
  })();
  // Lo-Fi: drive (soft-clip) → WaveShaper (bit crush) + lowpass warmth
  (function(){
    const b=APP_BUSES['win-lofi'];
    const drive=ac.createWaveShaper();drive.oversample='4x';drive.curve=new Float32Array([-1,0,1]);
    const crusher=ac.createWaveShaper();crusher.oversample='4x';
    const warmth=ac.createBiquadFilter();warmth.type='lowpass';warmth.frequency.value=20000;
    b.input.connect(drive);drive.connect(crusher);crusher.connect(warmth);warmth.connect(b.output);
    function makeCrushCurve(bits){const steps=Math.pow(2,bits),n=4096,c=new Float32Array(n);for(let i=0;i<n;i++){const x=(i*2/n)-1;c[i]=Math.round(x*steps)/steps;}return c;}
    function makeDriveCurve(amt){const n=256,c=new Float32Array(n+1);const k=amt<0.001?0:(2*amt)/(1-Math.min(amt,.999));for(let i=0;i<=n;i++){const x=i*2/n-1;c[i]=k===0?x:x*(k+1)/(k*Math.abs(x)+1);}return c;}
    b._lofi={crusher,warmth,drive,makeCrushCurve,makeDriveCurve};
    crusher.curve=makeCrushCurve(16);
  })();
  // Gate: analyser drives a gain node
  (function(){
    const b=APP_BUSES['win-gate'];
    const gateGain=ac.createGain();gateGain.gain.value=1;
    const analyser=ac.createAnalyser();analyser.fftSize=512;
    b.input.connect(analyser);b.input.connect(gateGain);gateGain.connect(b.output);
    b._gate={gateGain,analyser,open:false};
  })();
  // Merge: 4 inputs all route to same input GainNode (natural summation), passthrough to output
  (function(){
    const b=APP_BUSES['win-merge'];
    b.input.connect(b.output);
  })();
  // Volume: input → gainNode → output; gain controllable via UI
  (function(){
    const b=APP_BUSES['win-vol'];
    const vol=ac.createGain();vol.gain.value=0.8;
    b.input.connect(vol);vol.connect(b.output);
    b._vol=vol;
  })();
  // Pan: input → StereoPannerNode → output
  (function(){
    const b=APP_BUSES['win-pan'];
    const panner=ac.createStereoPanner();panner.pan.value=0;
    b.input.connect(panner);panner.connect(b.output);
    b._panner=panner;
  })();
  // Mixer: acts as master collector, goes to masterGain directly
  (function(){
    const b = APP_BUSES['win-mixer'];
    const vol = ac.createGain(); vol.gain.value = 0.85;
    b.input.connect(vol); vol.connect(b.output);
    try { b.output.disconnect(drySum); } catch(e) {}
    b.output.connect(masterGain);
    b._vol = vol;
  })();
  // Effects (generic passthrough insert)
  (function(){
    const b = APP_BUSES['win-effects'];
    b.input.connect(b.output);
  })();
  // Drum per-channel routing buses — each sound gets its own tap point
  (function(){
    const b = APP_BUSES['win-drum'];
    const chNames = ['kick','snare','clap','hat','ohat','tom','rim','cowbell','ride','shaker'];
    const ch = {};
    chNames.forEach(name => { const g = ac.createGain(); g.connect(b.output); ch[name] = g; });
    b._ch = ch;
  })();
  // Chorus: 3-voice delay modulation
  (function(){
    const b=APP_BUSES['win-chorus'];
    const delay1=ac.createDelay(0.05);delay1.delayTime.value=0.02;
    const delay2=ac.createDelay(0.05);delay2.delayTime.value=0.025;
    const delay3=ac.createDelay(0.05);delay3.delayTime.value=0.015;
    const lfo1=ac.createOscillator();lfo1.frequency.value=0.8;lfo1.start();
    const lfo2=ac.createOscillator();lfo2.frequency.value=1.1;lfo2.start();
    const lfo3=ac.createOscillator();lfo3.frequency.value=0.65;lfo3.start();
    const lfoGain1=ac.createGain();lfoGain1.gain.value=0.005;
    const lfoGain2=ac.createGain();lfoGain2.gain.value=0.005;
    const lfoGain3=ac.createGain();lfoGain3.gain.value=0.005;
    lfo1.connect(lfoGain1);lfoGain1.connect(delay1.delayTime);
    lfo2.connect(lfoGain2);lfoGain2.connect(delay2.delayTime);
    lfo3.connect(lfoGain3);lfoGain3.connect(delay3.delayTime);
    const dry=ac.createGain();dry.gain.value=0.6;
    const wet1=ac.createGain();wet1.gain.value=0.3;
    const wet2=ac.createGain();wet2.gain.value=0.3;
    const wet3=ac.createGain();wet3.gain.value=0.3;
    b.input.connect(dry);dry.connect(b.output);
    b.input.connect(delay1);delay1.connect(wet1);wet1.connect(b.output);
    b.input.connect(delay2);delay2.connect(wet2);wet2.connect(b.output);
    b.input.connect(delay3);delay3.connect(wet3);wet3.connect(b.output);
    b._chorus={delay1,delay2,delay3,lfo1,lfo2,lfo3,lfoGain1,lfoGain2,lfoGain3,dry,wet1,wet2,wet3};
  })();
  // Tremolo: LFO amplitude modulation
  (function(){
    const b=APP_BUSES['win-tremolo'];
    const lfo=ac.createOscillator();lfo.type='sine';lfo.frequency.value=4;lfo.start();
    const lfoGain=ac.createGain();lfoGain.gain.value=0.5;
    const tremoloGain=ac.createGain();tremoloGain.gain.value=1;
    const dcOffset=ac.createConstantSource();dcOffset.offset.value=0.5;dcOffset.start();
    const dcGain=ac.createGain();dcGain.gain.value=1;
    dcOffset.connect(dcGain);dcGain.connect(tremoloGain.gain);
    lfo.connect(lfoGain);lfoGain.connect(tremoloGain.gain);
    b.input.connect(tremoloGain);tremoloGain.connect(b.output);
    b._tremolo={lfo,lfoGain,tremoloGain,dcGain};
  })();
  // Phaser: 4-stage all-pass filter chain modulated by LFO
  (function(){
    const b=APP_BUSES['win-phaser'];
    const stages=4;
    const allpass=Array.from({length:stages},()=>{const f=ac.createBiquadFilter();f.type='allpass';f.frequency.value=800;f.Q.value=0.35;return f;});
    const lfo=ac.createOscillator();lfo.type='sine';lfo.frequency.value=0.5;lfo.start();
    const lfoGain=ac.createGain();lfoGain.gain.value=600;
    const dcOS=ac.createConstantSource();dcOS.offset.value=800;dcOS.start();
    lfo.connect(lfoGain);
    allpass.forEach(f=>{lfoGain.connect(f.frequency);dcOS.connect(f.frequency);});
    const dry=ac.createGain();dry.gain.value=0.7;
    const wet=ac.createGain();wet.gain.value=0.5;
    b.input.connect(dry);dry.connect(b.output);
    b.input.connect(allpass[0]);
    for(let i=0;i<stages-1;i++)allpass[i].connect(allpass[i+1]);
    allpass[stages-1].connect(wet);wet.connect(b.output);
    b._phaser={allpass,lfo,lfoGain,dcOS,dry,wet};
  })();
  // Granular: captures audio into ring buffer, plays back overlapping grains
  (function(){
    const b=APP_BUSES['win-granular'];
    const SR=ac.sampleRate, bufLen=SR*3; // 3s ring buffer
    const capBuf=ac.createBuffer(1,bufLen,SR);
    let writePos=0;
    const sp=ac.createScriptProcessor(2048,1,1);
    sp.onaudioprocess=ev=>{
      const id=ev.inputBuffer.getChannelData(0);
      const cd=capBuf.getChannelData(0);
      if(!b._gran?.params?.frozen){for(let i=0;i<id.length;i++){cd[(writePos++)%bufLen]=id[i];}}
      ev.outputBuffer.getChannelData(0).set(id);
    };
    b.input.connect(sp);sp.connect(b.output); // passthrough + capture
    const grainOut=ac.createGain();grainOut.gain.value=0.8;grainOut.connect(b.output);
    b._gran={capBuf,bufLen,writePos:()=>writePos,grainOut,
      params:{size:120,scatter:0.25,pitch:1.0,density:8,pos:0.5,frozen:false,reverse:false},timer:null};
    function tick(){
      const p=b._gran.params,SR2=ac.sampleRate;
      const gsz=Math.max(64,Math.floor(p.size*SR2/1000));
      const scat=Math.floor(p.scatter*b._gran.bufLen);
      const center=p.frozen?Math.floor(p.pos*b._gran.bufLen):((writePos-gsz+b._gran.bufLen)%b._gran.bufLen);
      const start=(center+Math.floor((Math.random()-.5)*scat*2)+b._gran.bufLen)%b._gran.bufLen;
      const gb=ac.createBuffer(1,gsz,SR2);const gd=gb.getChannelData(0);
      const cd=b._gran.capBuf.getChannelData(0);
      for(let i=0;i<gsz;i++){
        const ri=p.reverse?gsz-1-i:i;
        const w=0.5*(1-Math.cos(2*Math.PI*ri/gsz));
        gd[i]=(cd[(start+ri)%b._gran.bufLen]||0)*w;
      }
      const src=ac.createBufferSource();src.buffer=gb;src.playbackRate.value=p.pitch;
      const eg=ac.createGain();eg.gain.value=1;
      src.connect(eg);eg.connect(grainOut);src.start();
      src.onended=()=>{try{src.disconnect();eg.disconnect();}catch(_){}};
    }
    function startGrains(){
      if(b._gran.timer)clearInterval(b._gran.timer);
      b._gran.timer=setInterval(tick,1000/Math.max(1,b._gran.params.density));
    }
    b._gran.startGrains=startGrains;
    b._stop=()=>{if(b._gran.timer){clearInterval(b._gran.timer);b._gran.timer=null;}};
    startGrains();
  })();
  // Flanger: short delay (0.1-20ms) + LFO + feedback → classic jet sweep
  (function(){
    const b=APP_BUSES['win-flanger'];
    const dly=ac.createDelay(0.025);dly.delayTime.value=0.005;
    const fb=ac.createGain();fb.gain.value=0.5;
    const dry=ac.createGain();dry.gain.value=0.7;
    const wet=ac.createGain();wet.gain.value=0.5;
    const lfo=ac.createOscillator();lfo.type='sine';lfo.frequency.value=0.3;lfo.start();
    const lfoG=ac.createGain();lfoG.gain.value=0.004;
    const dcS=ac.createConstantSource();dcS.offset.value=0.005;dcS.start();
    lfo.connect(lfoG);lfoG.connect(dly.delayTime);dcS.connect(dly.delayTime);
    b.input.connect(dry);dry.connect(b.output);
    b.input.connect(dly);dly.connect(fb);fb.connect(dly);dly.connect(wet);wet.connect(b.output);
    b._flanger={dly,fb,dry,wet,lfo,lfoG,dcS};
  })();
  // Ring Mod: carrier × modulator multiplication
  (function(){
    const b=APP_BUSES['win-ringmod'];
    // carrier port → input (first gain), mod port → second dedicated gain connected to ring gain's .gain param
    const ringGain=ac.createGain();ringGain.gain.value=0;
    const modBus=ac.createGain();modBus.gain.value=1;
    const dry=ac.createGain();dry.gain.value=0.3;
    b.input.connect(ringGain);    // carrier through ring gain
    modBus.connect(ringGain.gain); // mod controls the gain (multiplication)
    ringGain.connect(b.output);
    b.input.connect(dry);dry.connect(b.output); // dry blend
    b._ring={ringGain,modBus,dry};
    // Second in port (mod) — handled in addWire by port id 'mod'
    b._modBus=modBus;
  })();
  // Auto-Filter: envelope follower → BiquadFilter cutoff
  (function(){
    const b=APP_BUSES['win-autofilter'];
    const filt=ac.createBiquadFilter();filt.type='lowpass';filt.frequency.value=800;filt.Q.value=2;
    const env=ac.createAnalyser();env.fftSize=256;
    const buf=new Float32Array(env.frequencyBinCount);
    b.input.connect(filt);filt.connect(b.output);
    b.input.connect(env);
    let baseF=800,modAmt=4000,atk=0.01,rel=0.2,envVal=0;
    const follow=()=>{
      env.getFloatTimeDomainData(buf);
      let rms=0;for(let i=0;i<buf.length;i++)rms+=buf[i]*buf[i];
      rms=Math.sqrt(rms/buf.length);
      const target=Math.min(1,rms*8);
      const coef=target>envVal?atk:rel;
      envVal+=(target-envVal)*coef;
      filt.frequency.value=Math.min(20000,baseF+envVal*modAmt);
    };
    b._af={filt,baseF:v=>{baseF=v;},modAmt:v=>{modAmt=v;},atk:v=>{atk=v;},rel:v=>{rel=v;},
      type:t=>{filt.type=t;},q:v=>{filt.Q.value=v;}};
    (function loop(){requestAnimationFrame(loop);follow();})();
  })();
  // Noise: white/pink/brown noise generator
  (function(){
    const b=APP_BUSES['win-noise'];
    let noiseNode=null,noiseType='white',noiseOn=false;
    const hp=ac.createBiquadFilter();hp.type='highpass';hp.frequency.value=20;hp.Q.value=0.7;
    const lp=ac.createBiquadFilter();lp.type='lowpass';lp.frequency.value=20000;lp.Q.value=0.7;
    const out=ac.createGain();out.gain.value=0;
    hp.connect(lp);lp.connect(out);out.connect(b.output);
    try{b.output.disconnect(drySum);}catch(e){}b.output.connect(drySum);
    function makeNoise(type){
      if(noiseNode){try{noiseNode.stop();}catch(_){}noiseNode=null;}
      if(!noiseOn)return;
      const bufSize=2*ac.sampleRate;const buf=ac.createBuffer(1,bufSize,ac.sampleRate);const d=buf.getChannelData(0);
      if(type==='white'){for(let i=0;i<bufSize;i++)d[i]=(Math.random()*2-1);}
      else if(type==='pink'){let b0=0,b1=0,b2=0,b3=0,b4=0,b5=0,b6=0;
        for(let i=0;i<bufSize;i++){const w=Math.random()*2-1;b0=.99886*b0+w*.0555179;b1=.99332*b1+w*.0750759;b2=.96900*b2+w*.1538520;b3=.86650*b3+w*.3104856;b4=.55000*b4+w*.5329522;b5=-.7616*b5-w*.0168980;d[i]=(b0+b1+b2+b3+b4+b5+b6+w*.5362)*0.11;b6=w*0.115926;}}
      else{let lastOut=0;for(let i=0;i<bufSize;i++){const w=Math.random()*2-1;d[i]=(lastOut+(.02*w))/1.02;lastOut=d[i];d[i]*=3.5;}}
      const src=ac.createBufferSource();src.buffer=buf;src.loop=true;
      src.connect(hp);src.start();noiseNode=src;
    }
    function setNoiseOn(v,level){
      noiseOn=v;
      out.gain.setTargetAtTime(v?((level??30)/100):0,ac.currentTime,0.008);
      if(v)makeNoise(noiseType);
      else if(noiseNode){try{noiseNode.stop();}catch(_){}noiseNode=null;}
    }
    b._noise={makeNoise,out,hp,lp,setType:t=>{noiseType=t;makeNoise(t);},setOn:setNoiseOn,get on(){return noiseOn;}};
    b._stop=()=>setNoiseOn(false);
  })();
  // Distortion: waveshaper with dry/wet
  (function(){
    const b=APP_BUSES['win-distortion'];
    const wsh=ac.createWaveShaper();wsh.oversample='4x';
    const tone=ac.createBiquadFilter();tone.type='highshelf';tone.frequency.value=4000;tone.gain.value=0;
    const level=ac.createGain();level.gain.value=0.8;
    const wetMix=ac.createGain();wetMix.gain.value=1;
    const dryMix=ac.createGain();dryMix.gain.value=0;
    b.input.connect(wsh);wsh.connect(tone);tone.connect(level);level.connect(wetMix);wetMix.connect(b.output);
    b.input.connect(dryMix);dryMix.connect(b.output);
    function makeCurve(mode,drive){
      const n=512,curve=new Float32Array(n),k=1+drive*40;
      for(let i=0;i<n;i++){
        const x=(i*2/n)-1;
        if(mode==='tube')curve[i]=x*(27+k*k)/(27+k*k*Math.abs(x));
        else if(mode==='transistor')curve[i]=(1-Math.exp(-Math.abs(k*x)))*Math.sign(x);
        else if(mode==='fuzz')curve[i]=Math.sign(x)*(1-Math.exp(-Math.abs(k*x*2.5)));
        else if(mode==='octave')curve[i]=Math.abs(Math.tanh(k*x))*2-1;
        else curve[i]=Math.max(-0.85,Math.min(0.85,k*x*0.08));
      }
      return curve;
    }
    b._dist={wsh,tone,level,wetMix,dryMix,makeCurve,mode:'tube',
      setDrive:d=>{wsh.curve=makeCurve(b._dist.mode,d);}};
    b._dist.setDrive(0.2);
  })();
  // Multi-band compressor: 3 crossover bands
  (function(){
    const b=APP_BUSES['win-multicomp'];
    const lo=ac.createBiquadFilter();lo.type='lowpass';lo.frequency.value=400;lo.Q.value=0.7;
    const loC=ac.createDynamicsCompressor();loC.threshold.value=-18;loC.ratio.value=4;loC.attack.value=0.01;loC.release.value=0.15;
    const loG=ac.createGain();loG.gain.value=1;
    const midHP=ac.createBiquadFilter();midHP.type='highpass';midHP.frequency.value=400;midHP.Q.value=0.7;
    const midLP=ac.createBiquadFilter();midLP.type='lowpass';midLP.frequency.value=4000;midLP.Q.value=0.7;
    const midC=ac.createDynamicsCompressor();midC.threshold.value=-18;midC.ratio.value=4;midC.attack.value=0.008;midC.release.value=0.12;
    const midG=ac.createGain();midG.gain.value=1;
    const hi=ac.createBiquadFilter();hi.type='highpass';hi.frequency.value=4000;hi.Q.value=0.7;
    const hiC=ac.createDynamicsCompressor();hiC.threshold.value=-18;hiC.ratio.value=4;hiC.attack.value=0.005;hiC.release.value=0.1;
    const hiG=ac.createGain();hiG.gain.value=1;
    const loAn=ac.createAnalyser();loAn.fftSize=256;
    const midAn=ac.createAnalyser();midAn.fftSize=256;
    const hiAn=ac.createAnalyser();hiAn.fftSize=256;
    const masterOut=ac.createGain();masterOut.gain.value=0.8;masterOut.connect(b.output);
    b.input.connect(lo);lo.connect(loC);loC.connect(loG);loG.connect(masterOut);loC.connect(loAn);
    b.input.connect(midHP);midHP.connect(midLP);midLP.connect(midC);midC.connect(midG);midG.connect(masterOut);midC.connect(midAn);
    b.input.connect(hi);hi.connect(hiC);hiC.connect(hiG);hiG.connect(masterOut);hiC.connect(hiAn);
    b._mc={
      bands:[
        {filt:lo,comp:loC,gain:loG,an:loAn},
        {filtHP:midHP,filtLP:midLP,comp:midC,gain:midG,an:midAn},
        {filt:hi,comp:hiC,gain:hiG,an:hiAn}
      ],xo1:400,xo2:4000,master:masterOut,
      setXO:(xo1,xo2)=>{
        lo.frequency.value=xo1;midHP.frequency.value=xo1;
        midLP.frequency.value=xo2;hi.frequency.value=xo2;
        b._mc.xo1=xo1;b._mc.xo2=xo2;
      }
    };
  })();
  // Wavetable synth: PeriodicWave voices + lowpass filter
  (function(){
    const b=APP_BUSES['win-wavetable'];
    const N=64;
    function mkPW(harms){const r=new Float32Array(N),im=new Float32Array(N);harms.forEach(([n,a])=>{if(n<N)im[n]=a;});return ac.createPeriodicWave(r,im,{disableNormalization:false});}
    const waves=[
      mkPW([[1,1]]),
      mkPW([[1,1],[3,.33],[5,.2],[7,.14],[9,.11]]),
      mkPW([[1,1],[2,.5],[3,.33],[4,.25],[5,.2],[6,.17],[7,.14],[8,.12]]),
      mkPW([[1,1],[2,.5],[4,.25],[8,.12],[16,.06]]),
      mkPW([[1,1],[2,.3],[3,.2],[5,.15],[7,.08]]),
      mkPW([[1,1],[3,.5],[5,.35],[7,.25],[9,.18]]),
      mkPW([[1,1],[2,.15],[3,.08],[4,.04]]),
      mkPW([[1,1],[2,.6],[3,.4],[4,.28],[5,.2],[6,.14],[7,.1]])
    ];
    const filt=ac.createBiquadFilter();filt.type='lowpass';filt.frequency.value=4000;filt.Q.value=1;
    const masterG=ac.createGain();masterG.gain.value=0.45;
    filt.connect(masterG);masterG.connect(b.output);
    const voices=new Map();
    function playNote(freq,vel){
      const id=freq.toFixed(2);if(voices.has(id))stopNote(freq);
      const osc=ac.createOscillator();osc.setPeriodicWave(b._wt.currentWave);osc.frequency.value=freq;
      const env=ac.createGain();env.gain.setValueAtTime(0,ac.currentTime);env.gain.linearRampToValueAtTime(vel*0.45,ac.currentTime+b._wt.attack);
      osc.connect(env);env.connect(filt);osc.start();voices.set(id,{osc,env});
    }
    function stopNote(freq){
      const id=freq.toFixed(2);const v=voices.get(id);if(!v)return;
      v.env.gain.cancelScheduledValues(ac.currentTime);
      v.env.gain.setTargetAtTime(0,ac.currentTime,b._wt.release/4);
      setTimeout(()=>{try{v.osc.stop();}catch(_){}voices.delete(id);},b._wt.release*1600+200);
    }
    b._wt={waves,currentWave:waves[0],voices,filt,masterG,attack:0.015,release:0.35,
      morphPos:0,setMorph:p=>{const i=Math.min(7,Math.floor(p*8));b._wt.currentWave=waves[i];b._wt.morphPos=p;},
      playNote,stopNote,setFilter:(f,q)=>{filt.frequency.value=f;filt.Q.value=q;}};
    b._stop=()=>{voices.forEach((_,f)=>stopNote(parseFloat(f)));};
  })();
  // Step sequencer: passthrough, triggers external poly/wavetable voices
  (function(){
    const b=APP_BUSES['win-stepseq'];
    b.input.connect(b.output);
    b._seq={steps:Array.from({length:16},()=>({active:true,note:60,vel:80,prob:1})),running:false,step:0};
  })();
  // Tape machine: wow/flutter delay + saturation
  (function(){
    const b=APP_BUSES['win-tape'];
    const sat=ac.createWaveShaper();sat.oversample='2x';
    const wowDly=ac.createDelay(0.05);wowDly.delayTime.value=0.01;
    const wowLFO=ac.createOscillator();wowLFO.type='sine';wowLFO.frequency.value=0.5;wowLFO.start();
    const wowGain=ac.createGain();wowGain.gain.value=0.0015;
    const flutLFO=ac.createOscillator();flutLFO.type='sine';flutLFO.frequency.value=9;flutLFO.start();
    const flutGain=ac.createGain();flutGain.gain.value=0.0003;
    const bias=ac.createBiquadFilter();bias.type='highshelf';bias.frequency.value=8000;bias.gain.value=0;
    const out=ac.createGain();out.gain.value=0.95;
    wowLFO.connect(wowGain);flutLFO.connect(flutGain);
    wowGain.connect(wowDly.delayTime);flutGain.connect(wowDly.delayTime);
    b.input.connect(sat);sat.connect(wowDly);wowDly.connect(bias);bias.connect(out);out.connect(b.output);
    function mkSat(amt){const n=512,c=new Float32Array(n),k=0.5+amt*8;for(let i=0;i<n;i++){const x=(i*2/n)-1;c[i]=x*(27+k*k)/(27+k*k*Math.abs(x));}return c;}
    sat.curve=mkSat(0.05);
    b._tape={sat,wowDly,wowLFO,wowGain,flutLFO,flutGain,bias,out,mkSat,
      setWow:v=>{wowGain.gain.value=v*0.003;},
      setFlutter:v=>{flutGain.gain.value=v*0.0008;},
      setWowRate:v=>{wowLFO.frequency.value=0.1+v*2;},
      setSat:v=>{sat.curve=mkSat(0.02+v*0.98);},
      setBias:v=>{bias.gain.value=v*-14;}
    };
  })();
  // Formant vowel filter: 3 peaking filters
  (function(){
    const b=APP_BUSES['win-formant'];
    const f1=ac.createBiquadFilter();f1.type='peaking';f1.gain.value=14;f1.Q.value=4;f1.frequency.value=800;
    const f2=ac.createBiquadFilter();f2.type='peaking';f2.gain.value=11;f2.Q.value=5;f2.frequency.value=1200;
    const f3=ac.createBiquadFilter();f3.type='peaking';f3.gain.value=9;f3.Q.value=6;f3.frequency.value=2500;
    const wet=ac.createGain();wet.gain.value=0.7;
    const dry=ac.createGain();dry.gain.value=0.3;
    b.input.connect(f1);f1.connect(f2);f2.connect(f3);f3.connect(wet);wet.connect(b.output);
    b.input.connect(dry);dry.connect(b.output);
    const VOWELS={A:[800,1200,2500],E:[400,2000,2800],I:[300,2500,3200],O:[500,800,2500],U:[300,700,2400]};
    b._formant={f1,f2,f3,wet,dry,VOWELS,
      setFormants:(f1v,f2v,f3v)=>{f1.frequency.value=f1v;f2.frequency.value=f2v;f3.frequency.value=f3v;},
      setQ:q=>{f1.Q.value=q;f2.Q.value=q*1.1;f3.Q.value=q*1.3;},
      setMix:v=>{wet.gain.value=v;dry.gain.value=1-v*0.6;}
    };
  })();
  // Sidechain compressor: main path with gain-reduction driven by SC analyser
  (function(){
    const b=APP_BUSES['win-sidechain'];
    const compG=ac.createGain();compG.gain.value=1;
    const scAn=ac.createAnalyser();scAn.fftSize=256;
    const scIn=ac.createGain();scIn.connect(scAn);
    b.input.connect(compG);compG.connect(b.output);
    const scBuf=new Float32Array(scAn.frequencyBinCount);
    let thr=-20,ratio=8,atk=0.005,rel=0.12,depth=1,envVal=0,grNow=0;
    function scLoop(){
      scAn.getFloatTimeDomainData(scBuf);
      let rms=0;for(let i=0;i<scBuf.length;i++)rms+=scBuf[i]*scBuf[i];
      rms=Math.sqrt(rms/scBuf.length);
      const dB=rms>0?20*Math.log10(rms):-Infinity;
      const excess=Math.max(0,dB-thr);
      const gr=excess>0?(excess*(1-1/ratio)):0;
      const target=gr;
      const coef=target>envVal?atk:rel;
      envVal+=(target-envVal)*coef;
      grNow=envVal;
      const linGR=Math.pow(10,-envVal*depth/20);
      compG.gain.setTargetAtTime(linGR,ac.currentTime,0.002);
      requestAnimationFrame(scLoop);
    }
    scLoop();
    b._sc={compG,scAn,scIn,
      get grNow(){return grNow;},
      setThr:v=>{thr=v;},setRatio:v=>{ratio=v;},
      setAtk:v=>{atk=v;},setRel:v=>{rel=v;},setDepth:v=>{depth=v;},
      connectSC:node=>{node.connect(scIn);}
    };
    // Expose SC input for wire routing
    b._scBus=scIn;
  })();
  // Glitch: gate-switching stutter + delay feedback
  (function(){
    const b=APP_BUSES['win-glitch'];
    const gateG=ac.createGain();gateG.gain.value=1;
    const dly=ac.createDelay(1);dly.delayTime.value=0.125;
    const fb=ac.createGain();fb.gain.value=0;
    b.input.connect(gateG);gateG.connect(b.output);
    b.input.connect(dly);dly.connect(fb);fb.connect(dly);dly.connect(gateG);
    const _pat=[[true,false,false,false,true,false,false,false],[false,false,false,false,false,false,false,false]];
    let _gStep=0,_gTimer=null,_gRateMs=125;
    function _gTick(){const a=_pat[0][_gStep]||_pat[1][_gStep];if(a){gateG.gain.setValueAtTime(0,ac.currentTime);gateG.gain.setValueAtTime(1,ac.currentTime+Math.max(0.01,dly.delayTime.value*0.5));}_gStep=(_gStep+1)%8;}
    function _startG(){clearInterval(_gTimer);_gTimer=setInterval(_gTick,_gRateMs);}
    _startG();
    b._glitch={gateG,dly,fb,pat2d:_pat,
      trigger:(t,dur)=>{gateG.gain.setValueAtTime(0,t);gateG.gain.setValueAtTime(1,t+Math.max(0.01,dur));},
      setFB:v=>{fb.gain.value=v*0.85;},
      setDly:v=>{dly.delayTime.value=v;},
      setFireRate:v=>{_gRateMs=v*1000;_startG();}
    };
    b._stop=()=>{clearInterval(_gTimer);};
  })();
  // Oscillator bank: 8 harmonic oscillators (additive synthesis)
  (function(){
    const b=APP_BUSES['win-osc-bank'];
    const master=ac.createGain();master.gain.value=0.4;master.connect(b.output);
    const oscs=[],gains=[];
    for(let h=1;h<=8;h++){
      const osc=ac.createOscillator();osc.type='sine';osc.frequency.value=220*h;
      const g=ac.createGain();g.gain.value=0;
      osc.connect(g);g.connect(master);osc.start();
      oscs.push(osc);gains.push(g);
    }
    b._bank={oscs,gains,master,fundamental:220,
      setFundamental:f=>{b._bank.fundamental=f;oscs.forEach((o,i)=>o.frequency.value=f*(i+1));},
      setHarmonic:(i,v)=>{gains[i].gain.value=v;},
      setMaster:v=>{master.gain.value=v;}
    };
    b._stop=()=>{oscs.forEach(o=>{try{o.stop();}catch(_){}});};
  })();
  // Frequency shifter: ring-modulation approximation
  (function(){
    const b=APP_BUSES['win-freqshift'];
    const carrier=ac.createOscillator();carrier.type='sine';carrier.frequency.value=100;carrier.start();
    const carGain=ac.createGain();carGain.gain.value=0;carrier.connect(carGain.gain);
    const wet=ac.createGain();wet.gain.value=1;
    const dry=ac.createGain();dry.gain.value=0;
    b.input.connect(carGain);carGain.connect(wet);wet.connect(b.output);
    b.input.connect(dry);dry.connect(b.output);
    b._fs={carrier,carGain,wet,dry,shiftHz:100,
      setShift:f=>{b._fs.shiftHz=f;carrier.frequency.value=Math.max(0.1,Math.abs(f));},
      setMix:v=>{wet.gain.value=v;dry.gain.value=1-v;}
    };
    b._stop=()=>{try{carrier.stop();}catch(_){}};
  })();
  // All remaining apps get audio passthrough so signal can flow through any connection
  ['win-keyboard','win-acid','win-poly','win-drum','win-sampler',
   'win-arp','win-lfo','win-transport','win-patterns','win-pianoroll','win-settings'].forEach(id => {
    const b = APP_BUSES[id];
    if (b) try { b.input.connect(b.output); } catch(e) {}
  });
  // Re-apply audio routing for any wires drawn before audio was initialised
  const alreadyDisconnected = new Set();
  connections.forEach(c => {
    const fb = APP_BUSES[c.from.win], tb = APP_BUSES[c.to.win];
    if (!fb || !tb) return;
    if (!alreadyDisconnected.has(c.from.win)) {
      try { fb.output.disconnect(drySum); } catch(e) {}
      alreadyDisconnected.add(c.from.win);
    }
    fb.output.connect(tb.input);
  });
}

// ===== TITLEBAR PEAK METERS =====
const _meterBufs={};
function _initTitlebarMeters(){
  Object.keys(APP_BUSES).forEach(id=>{
    const b=APP_BUSES[id];
    if(!b||b._meterAn)return;
    try{
      const an=ac.createAnalyser();an.fftSize=256;an.smoothingTimeConstant=0.6;
      b.output.connect(an);
      b._meterAn=an;
    }catch(_){}
  });
  // Add canvas to any open window titlebars
  document.querySelectorAll('.window.open').forEach(_addMeterCanvas);
}
function _addMeterCanvas(win){
  if(!win||win.querySelector('.tb-peak'))return;
  const bar=win.querySelector('.titlebar');if(!bar)return;
  const cv=document.createElement('canvas');cv.className='tb-peak';cv.width=28;cv.height=10;
  bar.appendChild(cv);
}
(function _meterLoop(){
  requestAnimationFrame(_meterLoop);
  if(!ac)return;
  document.querySelectorAll('.window.open').forEach(win=>{
    const cv=win.querySelector('.tb-peak');
    if(!cv){_addMeterCanvas(win);return;}
    const b=APP_BUSES[win.id];
    if(!b)return;
    if(!b._meterAn){
      try{const an=ac.createAnalyser();an.fftSize=256;an.smoothingTimeConstant=0.6;b.output.connect(an);b._meterAn=an;}catch(_){return;}
    }
    const buf=new Float32Array(b._meterAn.frequencyBinCount);
    b._meterAn.getFloatTimeDomainData(buf);
    let rms=0;for(let i=0;i<buf.length;i++)rms+=buf[i]*buf[i];
    rms=Math.sqrt(rms/buf.length);
    const db=20*Math.log10(Math.max(rms,1e-6));
    const norm=Math.max(0,Math.min(1,(db+60)/60));
    const ctx2=cv.getContext('2d');
    const w=cv.width,h=cv.height;
    const fill=norm>0.85?'#ff3333':norm>0.6?'#ffaa00':'rgba(232,104,32,0.9)';
    ctx2.clearRect(0,0,w,h);
    ctx2.fillStyle='rgba(0,0,0,0.3)';ctx2.fillRect(0,0,w,h);
    ctx2.fillStyle=fill;ctx2.fillRect(0,h*0.2,w*norm,h*0.6);
  });
})();

function playAcidNote(midi,accent,slide,prevSlide,time){
  const freq=midiToFreq(midi),stepDur=(60/tempo)/4;
  const osc=ac.createOscillator();osc.type=AP.wave;
  const drv=ac.createWaveShaper();drv.curve=driveCurve(AP.drv);drv.oversample="2x";
  const vcf=ac.createBiquadFilter();vcf.type="lowpass";vcf.Q.value=1+AP.res*27;
  const vca=ac.createGain();const trk=ac.createGain();trk.gain.value=mixLevel.acid*(mixMute.acid?0:1);
  if(prevSlide&&prevAcidFreq){osc.frequency.setValueAtTime(prevAcidFreq,time);osc.frequency.exponentialRampToValueAtTime(freq,time+stepDur*0.6);}
  else osc.frequency.setValueAtTime(freq,time);
  prevAcidFreq=freq;
  const base=AP.cut,envScale=AP.env*(accent?1+AP.acc*1.4:1);
  const peak=Math.min(base+envScale*7000+(accent?AP.acc*2500:0),14000);
  vcf.frequency.setValueAtTime(Math.max(peak,base),time);
  vcf.frequency.exponentialRampToValueAtTime(Math.max(base,60),time+AP.dec);
  const vol=accent?0.95:0.6,len=slide?stepDur*1.1:stepDur*0.92;
  vca.gain.setValueAtTime(0.0001,time);vca.gain.exponentialRampToValueAtTime(vol,time+0.004);
  vca.gain.setValueAtTime(vol,time+len*0.5);vca.gain.exponentialRampToValueAtTime(0.0001,time+len);
  osc.connect(drv);drv.connect(vcf);vcf.connect(vca);vca.connect(trk);out(trk,"acid",APP_BUSES['win-acid']?.output);
  osc.start(time);osc.stop(time+len+0.05);
}
function playAcidStep(pa,col,time){const row=pa.notes[col];if(row===null)return;
  const prevCol=(col+STEPS-1)%STEPS;const prevSlide=pa.sld[prevCol]&&pa.notes[prevCol]!==null;
  playAcidNote(ACID_BASE+row,pa.acc[col],pa.sld[col],prevSlide,time);}

function triggerPoly(midiArr,time,dur){
  if(!midiArr.length)return;
  const trk=ac.createGain();trk.gain.value=mixLevel.poly*(mixMute.poly?0:1);
  const vcf=ac.createBiquadFilter();vcf.type="lowpass";vcf.Q.value=1+PP.res*12;
  const t0=time,peakT=t0+PP.atk,endT=t0+Math.max(PP.atk+0.03,dur),relEnd=endT+PP.rel;
  if(PP.fenv>0){const top=Math.min(PP.cut*(1+PP.fenv*4),14000);vcf.frequency.setValueAtTime(top,t0);vcf.frequency.exponentialRampToValueAtTime(Math.max(PP.cut,80),t0+PP.atk+0.25);}
  else vcf.frequency.setValueAtTime(PP.cut,t0);
  if(PP.lfoDepth>0&&PP.lfoRate>0){const lfo=ac.createOscillator();lfo.type="sine";lfo.frequency.value=PP.lfoRate;const lg=ac.createGain();lg.gain.value=PP.lfoDepth;lfo.connect(lg);lg.connect(vcf.frequency);lfo.start(t0);lfo.stop(relEnd+0.1);}
  const vca=ac.createGain();
  const peak=0.5/Math.max(1,Math.sqrt(midiArr.length));
  vca.gain.setValueAtTime(0.0001,t0);
  vca.gain.linearRampToValueAtTime(peak,peakT);
  vca.gain.setValueAtTime(peak,endT);
  vca.gain.exponentialRampToValueAtTime(0.0001,relEnd);
  midiArr.forEach(m=>{const f=midiToFreq(m);
    const o1=ac.createOscillator();o1.type=PP.wave;o1.frequency.value=f;o1.detune.value=PP.detune;o1.connect(vca);o1.start(t0);o1.stop(relEnd+0.1);
    const o2=ac.createOscillator();o2.type=PP.wave;o2.frequency.value=f;o2.detune.value=-PP.detune;o2.connect(vca);o2.start(t0);o2.stop(relEnd+0.1);
    if(PP.sub>0){const sub=ac.createOscillator();sub.type="sine";sub.frequency.value=f/2;const sg=ac.createGain();sg.gain.value=PP.sub;sub.connect(sg);sg.connect(vca);sub.start(t0);sub.stop(relEnd+0.1);}
  });
  vca.connect(vcf);vcf.connect(trk);out(trk,"poly",APP_BUSES['win-poly']?.output);
}
function playPolyStep(pp,col,time){const stepDur=(60/tempo)/4;const byLen={};
  for(let r=0;r<POLY_ROWS;r++){const L=pp[col][r];if(L>0){const ln=(L===true)?1:L;(byLen[ln]=byLen[ln]||[]).push(POLY_BASE+r);}}
  if(arp.on){
    // gather all notes starting at this column (any length) and arpeggiate them across the step
    let notes=[];Object.keys(byLen).forEach(ln=>{notes=notes.concat(byLen[ln]);});
    if(!notes.length)return;
    notes=Array.from(new Set(notes)).sort((a,b)=>a-b);
    // expand octaves
    let pool=[];for(let o=0;o<arp.oct;o++)notes.forEach(n=>pool.push(n+12*o));
    // order
    if(arp.mode==="down")pool=pool.slice().reverse();
    else if(arp.mode==="updown"){const d=pool.slice().reverse().slice(1,-1);pool=pool.concat(d);}
    const sub=arp.rate;const subDur=stepDur/sub;
    for(let i=0;i<sub;i++){
      let idx;
      if(arp.mode==="random")idx=Math.floor(Math.random()*pool.length);
      else idx=(arpCounter+i)%pool.length;
      triggerPoly([pool[idx]],time+i*subDur,subDur*0.9);
    }
    arpCounter=(arpCounter+sub)%Math.max(1,pool.length);
    return;
  }
  Object.keys(byLen).forEach(ln=>triggerPoly(byLen[ln],time,stepDur*ln*0.95));}
let arpCounter=0;

function polyNoteOn(id,midiArr){
  ensureAudio();if(ac.state==="suspended")ac.resume();
  if(polyVoices.has(id)||!midiArr.length)return;
  const t=ac.currentTime;
  const trk=ac.createGain();trk.gain.value=mixLevel.poly*(mixMute.poly?0:1);
  const vcf=ac.createBiquadFilter();vcf.type="lowpass";vcf.Q.value=1+PP.res*12;
  if(PP.fenv>0){const top=Math.min(PP.cut*(1+PP.fenv*4),14000);vcf.frequency.setValueAtTime(top,t);vcf.frequency.exponentialRampToValueAtTime(Math.max(PP.cut,80),t+PP.atk+0.25);}
  else vcf.frequency.setValueAtTime(PP.cut,t);
  let lfo=null;
  if(PP.lfoDepth>0&&PP.lfoRate>0){lfo=ac.createOscillator();lfo.type="sine";lfo.frequency.value=PP.lfoRate;const lg=ac.createGain();lg.gain.value=PP.lfoDepth;lfo.connect(lg);lg.connect(vcf.frequency);lfo.start(t);}
  const vca=ac.createGain();const peak=0.45/Math.max(1,Math.sqrt(midiArr.length));
  vca.gain.setValueAtTime(0.0001,t);vca.gain.linearRampToValueAtTime(peak,t+PP.atk);
  const oscs=[];
  midiArr.forEach(m=>{const f=midiToFreq(m);
    const o1=ac.createOscillator();o1.type=PP.wave;o1.frequency.value=f;o1.detune.value=PP.detune;o1.connect(vca);o1.start(t);oscs.push(o1);
    const o2=ac.createOscillator();o2.type=PP.wave;o2.frequency.value=f;o2.detune.value=-PP.detune;o2.connect(vca);o2.start(t);oscs.push(o2);
    if(PP.sub>0){const sub=ac.createOscillator();sub.type="sine";sub.frequency.value=f/2;const sg=ac.createGain();sg.gain.value=PP.sub;sub.connect(sg);sg.connect(vca);sub.start(t);oscs.push(sub);}});
  vca.connect(vcf);vcf.connect(trk);out(trk,"poly",APP_BUSES['win-poly']?.output);
  polyVoices.set(id,{oscs,vca,lfo});
}
function polyNoteOff(id){const v=polyVoices.get(id);if(!v)return;polyVoices.delete(id);
  const t=ac.currentTime;
  try{v.vca.gain.cancelScheduledValues(t);v.vca.gain.setValueAtTime(Math.max(v.vca.gain.value,0.0001),t);v.vca.gain.exponentialRampToValueAtTime(0.0001,t+PP.rel);}catch(e){}
  const stopT=t+PP.rel+0.06;
  v.oscs.forEach(o=>{try{o.stop(stopT);}catch(e){}});
  if(v.lfo){try{v.lfo.stop(stopT);}catch(e){}}
}

function reverseBuffer(buf){const nb=ac.createBuffer(buf.numberOfChannels,buf.length,buf.sampleRate);
  for(let c=0;c<buf.numberOfChannels;c++){const sd=buf.getChannelData(c),dd=nb.getChannelData(c);for(let i=0,j=buf.length-1;i<buf.length;i++,j--)dd[i]=sd[j];}return nb;}
function playSampleVoice(s,time){
  if(!s.buffer)return null;
  const buf=s.reverse?(s.bufferRev||(s.bufferRev=reverseBuffer(s.buffer))):s.buffer;
  const dur=buf.duration;
  const st=Math.max(0,Math.min(1,s.start??0)), en=Math.max(0,Math.min(1,s.end??1));
  let a=Math.min(st,en), b=Math.max(st,en);
  let offset=(s.reverse?(1-b):a)*dur;
  let segDur=Math.max(0.02,(b-a)*dur);
  const rate=Math.pow(2,(s.pitch||0)/12);
  const playDur=segDur/rate;
  const src=ac.createBufferSource();src.buffer=buf;src.playbackRate.value=rate;
  const key="smp"+s.id;
  // drive
  let node=src;
  if((s.drive||0)>0){const ws=ac.createWaveShaper();ws.curve=driveCurve(s.drive);ws.oversample="2x";src.connect(ws);node=ws;}
  // filters: highpass then lowpass
  const hp=ac.createBiquadFilter();hp.type="highpass";hp.frequency.value=s.hp??20;
  const lp=ac.createBiquadFilter();lp.type="lowpass";lp.frequency.value=s.cutoff??12000;
  node.connect(hp);hp.connect(lp);
  // amp envelope
  const g=ac.createGain();const base=(mixLevel[key]??0.8)*(mixMute[key]?0:1);
  const atk=Math.min(s.attack??0.005,playDur*0.5), rel=Math.min(s.release??0.02,playDur*0.8);
  g.gain.setValueAtTime(0.0001,time);
  g.gain.linearRampToValueAtTime(Math.max(base,0.0001),time+Math.max(atk,0.002));
  g.gain.setValueAtTime(Math.max(base,0.0001),time+Math.max(playDur-rel,atk+0.002));
  g.gain.exponentialRampToValueAtTime(0.0001,time+playDur+0.01);
  lp.connect(g);g.connect(APP_BUSES['win-sampler']?.output || drySum);
  src.onended=()=>{try{src.disconnect();hp.disconnect();lp.disconnect();g.disconnect();}catch(e){}};
  try{src.start(time,offset,segDur);}catch(e){try{src.start(time);}catch(e2){}}
  return src;
}

function playKick(t){const o=ac.createOscillator(),g=ac.createGain(),trk=ac.createGain();trk.gain.value=mixLevel.kick*(mixMute.kick?0:1);
  o.frequency.setValueAtTime(150,t);o.frequency.exponentialRampToValueAtTime(48,t+0.11);g.gain.setValueAtTime(1,t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.34);
  o.connect(g);g.connect(trk);out(trk,"kick",APP_BUSES['win-drum']?._ch?.kick??APP_BUSES['win-drum']?.output);o.start(t);o.stop(t+0.4);}
function playSnare(t){const n=ac.createBufferSource();n.buffer=noiseBuf;const bp=ac.createBiquadFilter();bp.type="bandpass";bp.frequency.value=1900;bp.Q.value=0.8;
  const ng=ac.createGain();ng.gain.setValueAtTime(0.7,t);ng.gain.exponentialRampToValueAtTime(0.0001,t+0.18);
  const o=ac.createOscillator();o.type="triangle";o.frequency.value=190;const og=ac.createGain();og.gain.setValueAtTime(0.5,t);og.gain.exponentialRampToValueAtTime(0.0001,t+0.1);
  const trk=ac.createGain();trk.gain.value=mixLevel.snare*(mixMute.snare?0:1);
  n.connect(bp);bp.connect(ng);ng.connect(trk);o.connect(og);og.connect(trk);out(trk,"snare",APP_BUSES['win-drum']?._ch?.snare??APP_BUSES['win-drum']?.output);n.start(t);n.stop(t+0.22);o.start(t);o.stop(t+0.12);}
function playClap(t){const n=ac.createBufferSource();n.buffer=noiseBuf;const bp=ac.createBiquadFilter();bp.type="bandpass";bp.frequency.value=1600;bp.Q.value=1.2;
  const g=ac.createGain();g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(0.9,t+0.005);g.gain.exponentialRampToValueAtTime(0.0001,t+0.16);
  const trk=ac.createGain();trk.gain.value=mixLevel.clap*(mixMute.clap?0:1);n.connect(bp);bp.connect(g);g.connect(trk);out(trk,"clap",APP_BUSES['win-drum']?._ch?.clap??APP_BUSES['win-drum']?.output);n.start(t);n.stop(t+0.2);}
function playHat(t,open){const n=ac.createBufferSource();n.buffer=noiseBuf;const hp=ac.createBiquadFilter();hp.type="highpass";hp.frequency.value=7800;
  const key=open?"ohat":"hat",dec=open?0.32:0.05;const g=ac.createGain();g.gain.setValueAtTime(0.7,t);g.gain.exponentialRampToValueAtTime(0.0001,t+dec);
  const trk=ac.createGain();trk.gain.value=mixLevel[key]*(mixMute[key]?0:1);n.connect(hp);hp.connect(g);g.connect(trk);out(trk,key,APP_BUSES['win-drum']?._ch?.[key]??APP_BUSES['win-drum']?.output);n.start(t);n.stop(t+dec+0.05);}
function playTom(t){const o=ac.createOscillator(),g=ac.createGain(),trk=ac.createGain();trk.gain.value=mixLevel.tom*(mixMute.tom?0:1);
  o.frequency.setValueAtTime(180,t);o.frequency.exponentialRampToValueAtTime(90,t+0.18);g.gain.setValueAtTime(0.8,t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.28);
  o.connect(g);g.connect(trk);out(trk,"tom",APP_BUSES['win-drum']?._ch?.tom??APP_BUSES['win-drum']?.output);o.start(t);o.stop(t+0.32);}
function playRim(t){const n=ac.createBufferSource();n.buffer=noiseBuf;const bp=ac.createBiquadFilter();bp.type="bandpass";bp.frequency.value=2400;bp.Q.value=3;
  const g=ac.createGain();g.gain.setValueAtTime(0.7,t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.04);
  const trk=ac.createGain();trk.gain.value=mixLevel.rim*(mixMute.rim?0:1);n.connect(bp);bp.connect(g);g.connect(trk);out(trk,"rim",APP_BUSES['win-drum']?._ch?.rim??APP_BUSES['win-drum']?.output);n.start(t);n.stop(t+0.06);}
function playCowbell(t){const trk=ac.createGain();trk.gain.value=mixLevel.cowbell*(mixMute.cowbell?0:1);
  const g=ac.createGain();g.gain.setValueAtTime(0.5,t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.3);
  const bp=ac.createBiquadFilter();bp.type="bandpass";bp.frequency.value=800;bp.Q.value=2;
  [540,800].forEach(fr=>{const o=ac.createOscillator();o.type="square";o.frequency.value=fr;o.connect(g);o.start(t);o.stop(t+0.32);});
  g.connect(bp);bp.connect(trk);out(trk,"cowbell",APP_BUSES['win-drum']?._ch?.cowbell??APP_BUSES['win-drum']?.output);}
function playRide(t){const n=ac.createBufferSource();n.buffer=noiseBuf;const hp=ac.createBiquadFilter();hp.type="highpass";hp.frequency.value=9000;
  const g=ac.createGain();g.gain.setValueAtTime(0.4,t);g.gain.exponentialRampToValueAtTime(0.0001,t+0.5);
  const trk=ac.createGain();trk.gain.value=mixLevel.ride*(mixMute.ride?0:1);n.connect(hp);hp.connect(g);g.connect(trk);out(trk,"ride",APP_BUSES['win-drum']?._ch?.ride??APP_BUSES['win-drum']?.output);n.start(t);n.stop(t+0.55);}
function playShaker(t){const n=ac.createBufferSource();n.buffer=noiseBuf;const bp=ac.createBiquadFilter();bp.type="bandpass";bp.frequency.value=6000;bp.Q.value=1.4;
  const g=ac.createGain();g.gain.setValueAtTime(0.0001,t);g.gain.exponentialRampToValueAtTime(0.45,t+0.01);g.gain.exponentialRampToValueAtTime(0.0001,t+0.06);
  const trk=ac.createGain();trk.gain.value=mixLevel.shaker*(mixMute.shaker?0:1);n.connect(bp);bp.connect(g);g.connect(trk);out(trk,"shaker",APP_BUSES['win-drum']?._ch?.shaker??APP_BUSES['win-drum']?.output);n.start(t);n.stop(t+0.1);}
const DRUMFN={kick:playKick,snare:playSnare,clap:playClap,hat:t=>playHat(t,false),ohat:t=>playHat(t,true),tom:playTom,rim:playRim,cowbell:playCowbell,ride:playRide,shaker:playShaker};

/* ---------- scheduler ---------- */
let isPlaying=false,currentStep=0,nextNoteTime=0,timerID=null,drawQueue=[],playStartTime=0;
const lookahead=25,scheduleAhead=0.12;
function playingPatternIdx(){return songMode&&song.length?song[songPos]:curPattern;}
function scheduleStep(step,time){const pat=patterns[playingPatternIdx()];
  playAcidStep(pat.acid,step,time);playPolyStep(pat.poly,step,time);
  if(window.__prScheduleStep)window.__prScheduleStep(step,time);
  DRUMS.forEach(d=>{if(pat.drums[d][step])DRUMFN[d](time);});
  const pidx=playingPatternIdx();samples.forEach(s=>{if(s.patterns[pidx]&&s.patterns[pidx][step])playSampleVoice(s,time);});
  drawQueue.push({step,time,pat:playingPatternIdx()});}
function advance(){const sixteenth=(60/tempo)/4,sw=swing*0.5;
  nextNoteTime+=(currentStep%2===0)?sixteenth*(1+sw):sixteenth*(1-sw);currentStep++;
  if(currentStep>=STEPS){currentStep=0;if(songMode&&song.length)songPos=(songPos+1)%song.length;}}
function scheduler(){
  if(ac&&ac.state==='suspended'){ac.resume().catch(()=>{});timerID=setTimeout(scheduler,lookahead);return;}
  // If nextNoteTime is far in the past (e.g., after context suspension), resync to now
  if(nextNoteTime < ac.currentTime - 0.5) nextNoteTime = ac.currentTime + 0.02;
  while(nextNoteTime<ac.currentTime+scheduleAhead){scheduleStep(currentStep,nextNoteTime);advance();}
  timerID=setTimeout(scheduler,lookahead);
}
let lastStep=-1,lastPat=-1;
function draw(){
  if(ac){let s=lastStep,p=lastPat;
    while(drawQueue.length&&drawQueue[0].time<ac.currentTime){const q=drawQueue.shift();s=q.step;p=q.pat;}
    if(p!==lastPat&&songMode){lastPat=p;curPattern=p;renderPatternBtns();refreshAll();}
    if(s!==lastStep){lastStep=s;paintPlayhead(s);}
  }
  if(!wmImg)wmImg=document.querySelector('#watermark img');
  if(wmImg&&wmAnalyser&&isPlaying){
    wmAnalyser.getByteFrequencyData(wmData);
    let bass=0;for(let i=0;i<8;i++)bass+=wmData[i];
    bass/=(8*255);
    wmImg.style.transform='scale('+(1+bass*0.45)+')';
  }else if(wmImg){wmImg.style.transform='';}
  requestAnimationFrame(draw);
}

/* ---------- transport ---------- */
const playBtn=document.getElementById("playBtn");
playBtn.addEventListener("click",()=>{ensureAudio();if(ac.state==="suspended")ac.resume();
  if(!isPlaying){isPlaying=true;currentStep=0;songPos=0;nextNoteTime=ac.currentTime+0.06;playStartTime=nextNoteTime;prevAcidFreq=null;playBtn.classList.add("on");scheduler();}
  else{isPlaying=false;clearTimeout(timerID);playBtn.classList.remove("on");paintPlayhead(-1);}});
// Tap tempo
(function(){
  let _taps=[],_tapTimer=null;
  document.getElementById('tapTempoBtn')?.addEventListener('click',()=>{
    const now=performance.now();
    _taps.push(now);
    clearTimeout(_tapTimer);
    _tapTimer=setTimeout(()=>{_taps=[];},2500);
    if(_taps.length>1){
      const intervals=_taps.slice(1).map((t,i)=>t-_taps[i]);
      const avg=intervals.reduce((a,b)=>a+b,0)/intervals.length;
      const bpm=Math.round(60000/avg);
      const clamped=Math.max(40,Math.min(250,bpm));
      tempo=clamped;
      const bpmEl=document.getElementById('bpm');
      if(bpmEl){bpmEl.value=clamped;bpmEl.dispatchEvent(new Event('input'));}
    }
    if(_taps.length>8)_taps=_taps.slice(-4);
  });
})();
// Panic — stop all audio immediately
document.getElementById('panicBtn')?.addEventListener('click',()=>{
  if(!ac)return;
  // Stop transport
  if(isPlaying){isPlaying=false;clearTimeout(timerID);document.getElementById('playBtn').classList.remove("on");paintPlayhead(-1);}
  // Disconnect and reconnect master gain to kill all sound instantly
  try{masterGain.gain.cancelScheduledValues(ac.currentTime);masterGain.gain.setValueAtTime(0,ac.currentTime);}catch(_){}
  // Stop all active AudioBufferSourceNodes / OscillatorNodes across buses
  Object.values(APP_BUSES).forEach(b=>{try{if(typeof b._stop==='function')b._stop();}catch(_){}});
  // Fade back in after 200ms
  setTimeout(()=>{if(masterGain){masterGain.gain.cancelScheduledValues(ac.currentTime);masterGain.gain.setTargetAtTime(master,ac.currentTime,0.05);}},200);
});
// Panic keyboard shortcut: Ctrl+.
document.addEventListener('keydown',e=>{if((e.ctrlKey||e.metaKey)&&e.key==='.')document.getElementById('panicBtn')?.click();});
const recBtn=document.getElementById("recBtn"),reclink=document.getElementById("reclink");let recording=false;
recBtn.addEventListener("click",()=>{
  ensureAudio();if(ac.state==="suspended")ac.resume();
  if(!recording){
    recChunks=[];
    mediaRec=new MediaRecorder(recDest.stream,{mimeType:recMimeType,audioBitsPerSecond:320000});
    mediaRec.ondataavailable=e=>{if(e.data&&e.data.size>0)recChunks.push(e.data);};
    mediaRec.onstop=()=>{
      const blob=new Blob(recChunks,{type:recMimeType});
      const ext=recMimeType.startsWith('audio/ogg')?'ogg':'webm';
      reclink.href=URL.createObjectURL(blob);reclink.download='acidlab-song.'+ext;
      reclink.textContent='↓ '+ext;reclink.style.display='inline-block';
    };
    mediaRec.start(250);
    recording=true;reclink.style.display="none";recBtn.classList.add("on");
  } else {
    recording=false;recBtn.classList.remove("on");
    if(mediaRec&&mediaRec.state!=='inactive')mediaRec.stop();
  }
});
document.getElementById("bpm").addEventListener("input",e=>{tempo=Math.min(200,Math.max(60,+e.target.value||124));updateDelayTime();});
document.getElementById("masterVol").addEventListener("input",e=>{master=+e.target.value;if(masterGain){masterGain.gain.cancelScheduledValues(ac.currentTime);masterGain.gain.setTargetAtTime(master,ac.currentTime,0.008);}});

/* ---------- param bindings ---------- */
function bindP(id,obj,key,fmt){const el=document.getElementById(id),v=document.getElementById("v"+id);
  const show=()=>{if(v)v.textContent=fmt?fmt(obj[key]):obj[key];};el.addEventListener("input",e=>{obj[key]=+e.target.value;show();});show();}
bindP("aCut",AP,"cut",x=>Math.round(x)+"hz");bindP("aRes",AP,"res",x=>Math.round(x*100)+"%");bindP("aEnv",AP,"env",x=>Math.round(x*100)+"%");
bindP("aDec",AP,"dec",x=>x.toFixed(2)+"s");bindP("aAcc",AP,"acc",x=>Math.round(x*100)+"%");bindP("aDrv",AP,"drv",x=>Math.round(x*100)+"%");bindP("aDly",AP,"dly",x=>Math.round(x*100)+"%");
bindP("pCut",PP,"cut",x=>Math.round(x)+"hz");bindP("pRes",PP,"res",x=>Math.round(x*100)+"%");bindP("pAtk",PP,"atk",x=>x.toFixed(2)+"s");bindP("pRel",PP,"rel",x=>x.toFixed(2)+"s");
bindP("pDetune",PP,"detune",x=>x+"c");bindP("pSub",PP,"sub",x=>Math.round(x*100)+"%");bindP("pFenv",PP,"fenv",x=>Math.round(x*100)+"%");
bindP("pLfoR",PP,"lfoRate",x=>x.toFixed(1)+" hz");bindP("pLfoD",PP,"lfoDepth",x=>Math.round(x)+" hz");bindP("pDly",PP,"dly",x=>Math.round(x*100)+"%");bindP("pRev",PP,"rev",x=>Math.round(x*100)+"%");
const swingEl=document.getElementById("kSwing");swingEl.addEventListener("input",e=>{swing=+e.target.value;document.getElementById("vSwing").textContent=Math.round(swing*100)+"%";});document.getElementById("vSwing").textContent=Math.round(swing*100)+"%";
const revEl=document.getElementById("kRev");revEl.addEventListener("input",e=>{revMix=+e.target.value;document.getElementById("vRev").textContent=Math.round(revMix*100)+"%";});document.getElementById("vRev").textContent=Math.round(revMix*100)+"%";
// EQ + limiter
function bindDb(sliderId,valId,apply){const s=document.getElementById(sliderId),v=document.getElementById(valId);
  const upd=()=>{const x=+s.value;v.textContent=(x>0?"+":"")+x+" dB";apply(x);};s.addEventListener("input",upd);upd();}
bindDb("kEqLo","vEqLo",x=>{if(eqLow)eqLow.gain.value=x;});
bindDb("kEqMid","vEqMid",x=>{if(eqMid)eqMid.gain.value=x;});
bindDb("kEqHi","vEqHi",x=>{if(eqHigh)eqHigh.gain.value=x;});
bindDb("kLim","vLim",x=>{if(limiter)limiter.threshold.value=x;});
// arpeggiator controls
const arpOnBtn=document.getElementById("arpOn");
arpOnBtn.addEventListener("click",()=>{arp.on=!arp.on;arpOnBtn.classList.toggle("on",arp.on);arpOnBtn.textContent=arp.on?"on":"off";arpCounter=0;});
document.getElementById("arpMode").addEventListener("change",e=>{arp.mode=e.target.value;});
document.getElementById("arpRate").addEventListener("change",e=>{arp.rate=+e.target.value;});
document.getElementById("arpOct").addEventListener("change",e=>{arp.oct=+e.target.value;});

function waveBtns(ids,obj){ids.forEach(([id,val])=>{document.getElementById(id).addEventListener("click",()=>{obj.wave=val;ids.forEach(([i])=>document.getElementById(i).classList.remove("on"));document.getElementById(id).classList.add("on");});});}
const ACID_WAVES=[["aSaw","sawtooth"],["aSqr","square"],["aTri","triangle"]];
const POLY_WAVES=[["pSaw","sawtooth"],["pSqr","square"],["pTri","triangle"],["pSine","sine"]];
waveBtns(ACID_WAVES,AP);waveBtns(POLY_WAVES,PP);

/* presets */
function applyPolyUI(){
  [["pCut","cut"],["pRes","res"],["pAtk","atk"],["pRel","rel"],["pDetune","detune"],["pSub","sub"],["pFenv","fenv"],["pLfoR","lfoRate"],["pLfoD","lfoDepth"],["pDly","dly"],["pRev","rev"]]
    .forEach(([id,key])=>{const el=document.getElementById(id);el.value=PP[key];el.dispatchEvent(new Event("input"));});
  POLY_WAVES.forEach(([i,v])=>document.getElementById(i).classList.toggle("on",PP.wave===v));
}
document.querySelectorAll(".presets button[data-preset]").forEach(b=>{
  b.addEventListener("click",()=>{const p=PRESETS[b.dataset.preset];if(p){Object.assign(PP,p);applyPolyUI();}});
});

/* ---------- acid grid ---------- */
function buildKeys(el,base,rows){el.innerHTML="";for(let r=0;r<rows;r++){const semi=(base+r)%12;const k=document.createElement("div");k.className="keyl"+(BLACK.includes(semi)?" black":"");k.textContent=noteLabel(base+r);el.appendChild(k);}}
buildKeys(document.getElementById("aKeys"),ACID_BASE,ACID_ROWS);
const aGrid=document.getElementById("aGrid"),aCells=[];
for(let r=ACID_ROWS-1;r>=0;r--){const row=document.createElement("div");row.className="pianorow";
  for(let c=0;c<STEPS;c++){const cell=document.createElement("div");cell.className="cell";cell.dataset.r=r;cell.dataset.c=c;
    cell.addEventListener("click",()=>{pushUndo();const p=patterns[curPattern].acid;p.notes[c]=(p.notes[c]===r)?null:r;refreshAcid();});
    row.appendChild(cell);aCells.push(cell);}aGrid.appendChild(row);}
const accRow=document.getElementById("accRow"),sldRow=document.getElementById("sldRow"),accCells=[],sldCells=[];
for(let c=0;c<STEPS;c++){const a=document.createElement("div");a.className="tog acc";a.textContent="A";a.addEventListener("click",()=>{const p=patterns[curPattern].acid;p.acc[c]=!p.acc[c];a.classList.toggle("on",p.acc[c]);});accRow.appendChild(a);accCells.push(a);
  const s=document.createElement("div");s.className="tog sld";s.textContent="S";s.addEventListener("click",()=>{const p=patterns[curPattern].acid;p.sld[c]=!p.sld[c];s.classList.toggle("on",p.sld[c]);});sldRow.appendChild(s);sldCells.push(s);}
function refreshAcid(){const p=patterns[curPattern].acid;aCells.forEach(cell=>cell.classList.toggle("on",p.notes[+cell.dataset.c]===+cell.dataset.r));
  accCells.forEach((c,i)=>c.classList.toggle("on",p.acc[i]));sldCells.forEach((c,i)=>c.classList.toggle("on",p.sld[i]));}

/* ---------- poly grid ---------- */
buildKeys(document.getElementById("pKeys"),POLY_BASE,POLY_ROWS);
const pGrid=document.getElementById("pGrid"),pCells=[];
const pCellIndex={}; // key r*100+c -> cell
function pCellAt(c,r){return pCellIndex[r*100+c];}
let polyDraw="single"; // or "chord"
let polyDrag=null;      // {startCol,rows}
function chordRowsFrom(rootRow){const iv=CHORDS[chordType.value]||[0];const rows=[];iv.forEach(i=>{const rr=rootRow+i;if(rr>=0&&rr<POLY_ROWS)rows.push(rr);});return rows.length?rows:[rootRow];}
function clearTail(g,startCol,row,len){for(let k=1;k<len;k++){const cc=startCol+k;if(cc<STEPS)g[cc][row]=0;}}
function polyDown(col,row){
  pushUndo();
  const g=patterns[curPattern].poly;
  if(g[col][row]>0){ // clicking a note head removes it (whole chord in chord mode)
    if(polyDraw==="chord"){for(let r=0;r<POLY_ROWS;r++)g[col][r]=0;}else{g[col][row]=0;}
    polyDrag=null;refreshPoly();return;
  }
  const rows=(polyDraw==="chord")?chordRowsFrom(row):[row];
  rows.forEach(rr=>g[col][rr]=1);
  polyDrag={startCol:col,rows};refreshPoly();
}
function polyEnter(col){
  if(!polyDrag)return;const g=patterns[curPattern].poly;
  if(col<polyDrag.startCol)return;
  const len=col-polyDrag.startCol+1;
  polyDrag.rows.forEach(rr=>{g[polyDrag.startCol][rr]=len;clearTail(g,polyDrag.startCol,rr,len);});
  refreshPoly();
}
for(let r=POLY_ROWS-1;r>=0;r--){const row=document.createElement("div");row.className="pianorow";
  for(let c=0;c<STEPS;c++){const cell=document.createElement("div");cell.className="cell poly";cell.dataset.r=r;cell.dataset.c=c;
    cell.addEventListener("pointerdown",ev=>{ev.preventDefault();polyDown(c,r);});
    cell.addEventListener("pointerenter",()=>{polyEnter(c);});
    row.appendChild(cell);pCells.push(cell);pCellIndex[r*100+c]=cell;}
  pGrid.appendChild(row);}
document.addEventListener("pointerup",()=>{polyDrag=null;});
function refreshPoly(){const g=patterns[curPattern].poly;
  pCells.forEach(cell=>cell.classList.remove("on","head","tail"));
  for(let col=0;col<STEPS;col++)for(let r=0;r<POLY_ROWS;r++){const raw=g[col][r];if(raw>0){const L=(raw===true)?1:raw;
    for(let k=0;k<L&&col+k<STEPS;k++){const cell=pCellAt(col+k,r);if(cell){cell.classList.add("on");cell.classList.add(k===0?"head":"tail");}}}}
}
document.getElementById("drawSingle").addEventListener("click",function(){polyDraw="single";this.classList.add("on");document.getElementById("drawChord").classList.remove("on");});
document.getElementById("drawChord").addEventListener("click",function(){polyDraw="chord";this.classList.add("on");document.getElementById("drawSingle").classList.remove("on");});


/* ---------- drum grid ---------- */
const DRUM_TIPS={kick:'Kick drum — deep bass thud. The foundation of the beat.',snare:'Snare drum — sharp crack on beats 2 and 4.',clap:'Clap — layered hand-clap transient, sits with snare.',hat:'Closed hi-hat — tight tick, keeps the groove moving.',ohat:'Open hi-hat — longer shimmering sustain.',tom:'Tom — mid-range drum hit, fills and rolls.',rim:'Rimshot — dry, cutting snap from the snare rim.',cowbell:'Cowbell — classic metallic accent. More cowbell.',ride:'Ride cymbal — sustained shimmer for jazz-style grooves.',shaker:'Shaker — fine rhythmic texture, sits at the top of the mix.'};
const drumgrid=document.getElementById("drumgrid"),drumCells={};
DRUMS.forEach(d=>{drumCells[d]=[];const row=document.createElement("div");row.className="seqrow";row.dataset.drum=d;
  const name=document.createElement("div");name.className="rowname";name.textContent=DRUM_LABELS[d];name.dataset.tip=DRUM_TIPS[d]||'';
  const steps=document.createElement("div");steps.className="steps";
  for(let c=0;c<STEPS;c++){const cell=document.createElement("div");cell.className="cell"+(d==="kick"?" kick":"");
    cell.addEventListener("click",()=>{pushUndo();const a=patterns[curPattern].drums[d];a[c]=!a[c];cell.classList.toggle("on",a[c]);});
    steps.appendChild(cell);drumCells[d].push(cell);}
  row.appendChild(name);row.appendChild(steps);drumgrid.appendChild(row);});
function refreshDrums(){DRUMS.forEach(d=>{const a=patterns[curPattern].drums[d];drumCells[d].forEach((cell,i)=>cell.classList.toggle("on",a[i]));});}
function refreshAll(){refreshAcid();refreshPoly();refreshDrums();if(typeof refreshSamples==="function")refreshSamples();}

/* ---------- mixer ---------- */
const MIX_KEYS=[["acid","acid"],["poly","poly"],["kick","kick"],["snare","snare"],["clap","clap"],["hat","hat"],["ohat","ohat"],["tom","tom"],["rim","rim"],["cowbell","cowbell"],["ride","ride"],["shaker","shaker"]];
const mixer=document.getElementById("mixer");
function addMixChannel(key,label){const ch=document.createElement("div");ch.className="ch";ch.dataset.key=key;
  const sl=document.createElement("input");sl.type="range";sl.min=0;sl.max=1;sl.step=0.01;sl.value=mixLevel[key]??0.8;sl.addEventListener("input",e=>mixLevel[key]=+e.target.value);
  const nm=document.createElement("div");nm.className="cname";nm.textContent=label;
  const mb=document.createElement("button");mb.className="mbtn";mb.textContent="M";mb.addEventListener("click",()=>{mixMute[key]=!mixMute[key];mb.classList.toggle("on",mixMute[key]);});
  ch.appendChild(sl);ch.appendChild(nm);ch.appendChild(mb);mixer.appendChild(ch);return ch;}
MIX_KEYS.forEach(([key,label])=>addMixChannel(key,DRUM_LABELS[label]||label));

/* ---------- patterns + song ---------- */
const patBtns=document.getElementById("patBtns");
function patLabel(i){let s="";i++;while(i>0){s=String.fromCharCode(65+(i-1)%26)+s;i=Math.floor((i-1)/26);}return s;}
function deepPattern(p){return JSON.parse(JSON.stringify(p));}
/* ---------- undo / redo ---------- */
let undoStack=[],redoStack=[];const UNDO_MAX=60;
function snapState(){return JSON.stringify({patterns,curPattern,song,smp:samples.map(s=>s.patterns)});}
function pushUndo(){undoStack.push(snapState());if(undoStack.length>UNDO_MAX)undoStack.shift();redoStack.length=0;}
function applyState(str){const st=JSON.parse(str);patterns=st.patterns;curPattern=st.curPattern;song=st.song;
  if(st.smp)samples.forEach((s,i)=>{if(st.smp[i])s.patterns=st.smp[i];});
  renderPatternBtns();renderChain();refreshAll();}
function doUndo(){if(!undoStack.length)return;redoStack.push(snapState());applyState(undoStack.pop());}
function doRedo(){if(!redoStack.length)return;undoStack.push(snapState());applyState(redoStack.pop());}
document.addEventListener("keydown",e=>{
  const inInput=e.target.tagName==='INPUT'||e.target.tagName==='TEXTAREA'||e.target.isContentEditable;
  if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==="z"){e.preventDefault();if(e.shiftKey)doRedo();else doUndo();}
  else if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==="y"){e.preventDefault();doRedo();}
  else if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='a'&&!inInput){
    e.preventDefault();
    document.querySelectorAll('.window.open').forEach(w=>{selectedWindows.add(w.id);w.classList.add('win-selected');});
  }
  else if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='c'&&selectedWindows.size>0&&!inInput){
    e.preventDefault();
    winClipboard=[...selectedWindows].map(id=>{const w=document.getElementById(id);return{id,wx:parseFloat(w?.dataset.wx)||0,wy:parseFloat(w?.dataset.wy)||0};});
  }
  else if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='v'&&winClipboard&&!inInput){
    e.preventDefault();
    const off=60/wsZoom;
    winClipboard.forEach(item=>{
      const baseId=item.id.replace(/-i\d+$/,'');
      if(APP_FACTORIES[baseId]){
        spawnWindow(baseId,item.wx+off,item.wy+off);
      }else{
        const w=document.getElementById(baseId);if(!w)return;
        openWindow(baseId,item.wx+off,item.wy+off);
      }
    });
  }
  else if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='d'&&selectedWindows.size>0&&!inInput){
    e.preventDefault();
    const off=60/wsZoom;
    [...selectedWindows].forEach(id=>{
      const w=document.getElementById(id);if(!w)return;
      const baseId=id.replace(/-i\d+$/,'');
      const wx=(parseFloat(w.dataset.wx)||0)+off, wy=(parseFloat(w.dataset.wy)||0)+off;
      if(APP_FACTORIES[baseId])spawnWindow(baseId,wx,wy);
      else openWindow(baseId,wx,wy);
    });
  }
  else if(e.key==='Delete'&&selectedWindows.size>0&&!inInput){
    e.preventDefault();[...selectedWindows].forEach(id=>closeWindow(id));selectedWindows.clear();
  }
  else if(e.key==='Escape'&&!inInput){
    selectedWindows.forEach(id=>document.getElementById(id)?.classList.remove('win-selected'));selectedWindows.clear();
    if(wireDrawing){wireDrawing.previewPaths?.forEach(pp=>pp.path.remove());wireDrawing.pendingCursorPaths?.forEach(p=>p.remove());wireDrawing.tempPath.remove();document.querySelectorAll('.port-jack.target-highlight').forEach(el=>el.classList.remove('target-highlight'));wireDrawing=null;}
    pendingOutPorts.forEach(pq=>pq.jackEl.classList.remove('pending-out'));pendingOutPorts.length=0;
    pendingInPorts.forEach(pi=>pi.jackEl.classList.remove('pending-in'));pendingInPorts.length=0;
  }
});
function syncSampleLanes(){samples.forEach(s=>{while(s.patterns.length<patterns.length)s.patterns.push(arr16());s.patterns.length=patterns.length;});}
function renderPatternBtns(){patBtns.innerHTML="";patterns.forEach((_,i)=>{const b=document.createElement("button");b.textContent=patLabel(i);if(i===curPattern)b.classList.add("on");
  b.addEventListener("click",()=>{curPattern=i;renderPatternBtns();refreshAll();});patBtns.appendChild(b);});}
const chainEl=document.getElementById("chain");
function renderChain(){chainEl.innerHTML="";if(!song.length){chainEl.innerHTML='<span class="hint" style="margin:0">chain empty — add a pattern</span>';return;}
  song.forEach((p,idx)=>{const c=document.createElement("div");c.className="chip"+(songMode&&idx===songPos?" cur":"");c.textContent=patLabel(p);
    c.title="click to remove";c.addEventListener("click",()=>{song.splice(idx,1);renderChain();});chainEl.appendChild(c);});}
document.getElementById("addToSong").addEventListener("click",()=>{song.push(curPattern);renderChain();});
document.getElementById("clearSong").addEventListener("click",()=>{song=[];renderChain();});
const songToggle=document.getElementById("songToggle");
songToggle.addEventListener("click",()=>{songMode=!songMode;songPos=0;songToggle.textContent=songMode?"play song":"play loop";songToggle.classList.toggle("on",songMode);renderChain();});
// pattern controls
document.getElementById("patAdd").addEventListener("click",()=>{patterns.push(emptyPattern());syncSampleLanes();curPattern=patterns.length-1;renderPatternBtns();refreshAll();});
document.getElementById("patDup").addEventListener("click",()=>{patterns.splice(curPattern+1,0,deepPattern(patterns[curPattern]));
  samples.forEach(s=>s.patterns.splice(curPattern+1,0,s.patterns[curPattern].slice()));curPattern++;renderPatternBtns();refreshAll();});
document.getElementById("patCopy").addEventListener("click",()=>{patClipboard={pat:deepPattern(patterns[curPattern]),smp:samples.map(s=>s.patterns[curPattern].slice())};});
document.getElementById("patPaste").addEventListener("click",()=>{if(!patClipboard)return;patterns[curPattern]=deepPattern(patClipboard.pat);fixDrums(patterns[curPattern]);
  samples.forEach((s,i)=>{if(patClipboard.smp[i])s.patterns[curPattern]=patClipboard.smp[i].slice();});refreshAll();});
document.getElementById("patDel").addEventListener("click",()=>{if(patterns.length<=1)return;
  patterns.splice(curPattern,1);samples.forEach(s=>s.patterns.splice(curPattern,1));
  song=song.filter(p=>p!==curPattern).map(p=>p>curPattern?p-1:p);
  if(curPattern>=patterns.length)curPattern=patterns.length-1;renderPatternBtns();renderChain();refreshAll();});

/* ---------- keyboard & chord tool ---------- */
let kbTarget="poly",kbMode="single",kbOct=4,writeMode=false,writeStep=0;
let kbRecArmed=false; const recHeld=new Map();
const octLbl=document.getElementById("octLbl"),writeLbl=document.getElementById("writeLbl");
function setOctLbl(){octLbl.textContent=noteLabel(kbOct*12);}
document.getElementById("octDn").addEventListener("click",()=>{kbOct=Math.max(1,kbOct-1);setOctLbl();});
document.getElementById("octUp").addEventListener("click",()=>{kbOct=Math.min(7,kbOct+1);setOctLbl();});
function pickTarget(t){kbTarget=t;document.getElementById("tgtPoly").classList.toggle("on",t==="poly");document.getElementById("tgtAcid").classList.toggle("on",t==="acid");}
document.getElementById("tgtPoly").addEventListener("click",()=>pickTarget("poly"));
document.getElementById("tgtAcid").addEventListener("click",()=>pickTarget("acid"));
function pickMode(m){kbMode=m;document.getElementById("modeSingle").classList.toggle("on",m==="single");document.getElementById("modeChord").classList.toggle("on",m==="chord");}
document.getElementById("modeSingle").addEventListener("click",()=>pickMode("single"));
document.getElementById("modeChord").addEventListener("click",()=>pickMode("chord"));
document.getElementById("kbWrite").addEventListener("click",function(){writeMode=!writeMode;this.classList.toggle("on",writeMode);});
document.getElementById("kbRec").addEventListener("click",function(){
  kbRecArmed=!kbRecArmed;this.classList.toggle("on",kbRecArmed);
  if(kbRecArmed){pickTarget("poly");if(!isPlaying)playBtn.click();}
  else{recHeld.clear();}
});
const chordType=document.getElementById("chordType");

function notesForKey(midi){
  if(kbMode==="chord"){const iv=CHORDS[chordType.value]||[0];return iv.map(i=>midi+i);}
  return [midi];
}
function stampToGrid(midiArr){
  const g=patterns[curPattern].poly[writeStep];
  midiArr.forEach(m=>{let row=m-POLY_BASE;while(row>=POLY_ROWS)row-=12;while(row<0)row+=12;if(row>=0&&row<POLY_ROWS)g[row]=1;});
  refreshPoly();writeStep=(writeStep+1)%STEPS;writeLbl.textContent=writeStep+1;
}
function litOn(midi){const el=pianoKeyEls[midi];if(el)el.classList.add("held");}
function litOff(midi){const el=pianoKeyEls[midi];if(el)el.classList.remove("held");}
function curStepFloat(){const sixteenth=(60/tempo)/4;return((ac.currentTime-playStartTime)/sixteenth);}
function kbDown(id,rootMidi,litMidi){
  ensureAudio();if(ac.state==="suspended")ac.resume();
  const notes=notesForKey(rootMidi);
  if(kbTarget==="acid"){notes.forEach(m=>playAcidNote(m,false,false,false,ac.currentTime));}
  else{polyNoteOn(id,notes);}
  if(litMidi!=null)litOn(litMidi);
  if(writeMode&&kbTarget==="poly")stampToGrid(notes);
  if(kbRecArmed&&isPlaying&&kbTarget==="poly"){recHeld.set(id,{notes:notes.slice(),startF:curStepFloat()});}
}
function kbUp(id,litMidi){
  polyNoteOff(id);if(litMidi!=null)litOff(litMidi);
  if(recHeld.has(id)){const h=recHeld.get(id);recHeld.delete(id);
    const startStep=((Math.round(h.startF)%STEPS)+STEPS)%STEPS;
    let lenSteps=Math.max(1,Math.round(curStepFloat()-h.startF));
    if(lenSteps>STEPS)lenSteps=STEPS;if(startStep+lenSteps>STEPS)lenSteps=STEPS-startStep;
    const g=patterns[curPattern].poly;
    h.notes.forEach(m=>{let row=m-POLY_BASE;while(row>=POLY_ROWS)row-=12;while(row<0)row+=12;
      if(row>=0&&row<POLY_ROWS){g[startStep][row]=lenSteps;for(let k=1;k<lenSteps;k++)if(startStep+k<STEPS)g[startStep+k][row]=0;}});
    refreshPoly();
  }
}

const piano=document.getElementById("piano");const pianoKeyEls={};
function kbOctBase(){return kbOct*12;}
function buildPiano(){piano.innerHTML="";for(const k in pianoKeyEls)delete pianoKeyEls[k];const startMidi=kbOctBase();const octs=2;
  for(let o=0;o<octs;o++){WHITE.forEach(w=>{const midi=startMidi+o*12+w;
    const wk=document.createElement("div");wk.className="wkey";wk.dataset.midi=midi;
    const lab=document.createElement("div");lab.className="klabel";lab.textContent=noteLabel(midi);wk.appendChild(lab);
    wk.addEventListener("pointerdown",ev=>{ev.preventDefault();try{wk.setPointerCapture(ev.pointerId);}catch(e){}kbDown("m"+midi,midi,midi);});
    wk.addEventListener("pointerup",ev=>{ev.preventDefault();kbUp("m"+midi,midi);});
    piano.appendChild(wk);pianoKeyEls[midi]=wk;
    const bSemi=w+1;if(BLACK.includes(bSemi)){const bmidi=startMidi+o*12+bSemi;
      const bk=document.createElement("div");bk.className="bkey";bk.dataset.midi=bmidi;
      bk.addEventListener("pointerdown",ev=>{ev.preventDefault();ev.stopPropagation();try{bk.setPointerCapture(ev.pointerId);}catch(e){}kbDown("m"+bmidi,bmidi,bmidi);});
      bk.addEventListener("pointerup",ev=>{ev.preventDefault();ev.stopPropagation();kbUp("m"+bmidi,bmidi);});
      wk.appendChild(bk);pianoKeyEls[bmidi]=bk;}
  });}
}
buildPiano();
const _setOctLbl=setOctLbl;setOctLbl=function(){_setOctLbl();buildPiano();};

/* QWERTY */
const QMAP={a:0,w:1,s:2,e:3,d:4,f:5,t:6,g:7,y:8,h:9,u:10,j:11,k:12};
const heldKeys=new Set();
document.addEventListener("keydown",e=>{
  const tag=(e.target&&e.target.tagName)||"";if(tag==="INPUT"||tag==="SELECT"||tag==="TEXTAREA")return;
  if(e.code==="Space"){e.preventDefault();playBtn.click();return;}
  if(e.key.toLowerCase()==="l"&&!e.repeat){
    e.preventDefault();
    const step=lastStep>=0?lastStep:0;
    const p=patterns[curPattern].acid;
    p.sld[step]=!p.sld[step];
    sldCells[step].classList.toggle("on",p.sld[step]);
    return;
  }
  const k=e.key.toLowerCase();if(!(k in QMAP)||heldKeys.has(k)||e.repeat)return;
  heldKeys.add(k);const midi=kbOctBase()+QMAP[k];kbDown("q"+k,midi,midi);
});
document.addEventListener("keyup",e=>{const k=e.key.toLowerCase();if(heldKeys.has(k)){heldKeys.delete(k);const midi=kbOctBase()+QMAP[k];kbUp("q"+k,midi);}});

/* ---------- sampler ---------- */
const samplesWrap=document.getElementById("samplesWrap");
const uploadBtn=document.getElementById("uploadBtn"),sampleFileIn=document.getElementById("sampleFileIn");
uploadBtn.addEventListener("click",()=>{ensureAudio();if(ac.state==="suspended")ac.resume();sampleFileIn.click();});
function decodeAudio(arr){return new Promise((resolve,reject)=>{
  let settled=false;
  const p=ac.decodeAudioData(arr,b=>{if(!settled){settled=true;resolve(b);}},e=>{if(!settled){settled=true;reject(e||new Error("decode failed"));}});
  if(p&&p.then)p.then(b=>{if(!settled){settled=true;resolve(b);}},e=>{if(!settled){settled=true;reject(e||new Error("decode failed"));}});
});}
sampleFileIn.addEventListener("change",async e=>{
  const files=Array.from(e.target.files||[]);
  for(const f of files){
    try{const arr=await f.arrayBuffer();const buf=await decodeAudio(arr);
      const s={id:sampleSeq++,name:f.name.replace(/\.[^.]+$/,""),buffer:buf,bufferRev:null,pitch:0,start:0,end:1,attack:0.005,release:0.02,hp:20,cutoff:12000,drive:0,dly:0,rev:0.15,reverse:false,_previewSrc:null,
        patterns:Array.from({length:patterns.length},()=>arr16())};
      mixLevel["smp"+s.id]=0.8;mixMute["smp"+s.id]=false;samples.push(s);addMixChannel("smp"+s.id,s.name.slice(0,8));
      const hint=samplesWrap.querySelector(".hint");if(hint)hint.remove();
      samplesWrap.appendChild(buildSampleRow(s));
    }catch(err){alert("Could not load "+f.name+": "+(err&&err.message?err.message:"unsupported audio format")+". Try a WAV or MP3.");}
  }
  sampleFileIn.value="";
});
function buildSampleRow(s){
  const row=document.createElement("div");row.className="smprow";row.dataset.smp=s.id;
  const head=document.createElement("div");head.className="smphead";
  const nm=document.createElement("div");nm.className="smpname";nm.textContent=s.name;nm.title=s.name;head.appendChild(nm);
  const mk=(lbl,min,max,step,val,fmt,on)=>{const d=document.createElement("div");d.className="smp-mini";
    const l=document.createElement("span");l.className="lbl";l.textContent=lbl;
    const inp=document.createElement("input");inp.type="range";inp.min=min;inp.max=max;inp.step=step;inp.value=val;
    const v=document.createElement("span");v.className="val";v.textContent=fmt(val);
    inp.addEventListener("input",e=>{on(+e.target.value);v.textContent=fmt(+e.target.value);});
    d.appendChild(l);d.appendChild(inp);d.appendChild(v);return d;};
  head.appendChild(mk("pitch",-24,24,1,s.pitch,x=>x+"st",x=>s.pitch=x));
  head.appendChild(mk("start",0,1,0.01,s.start,x=>Math.round(x*100)+"%",x=>s.start=x));
  head.appendChild(mk("end",0,1,0.01,s.end,x=>Math.round(x*100)+"%",x=>s.end=x));
  head.appendChild(mk("attack",0,0.5,0.005,s.attack,x=>x.toFixed(2)+"s",x=>s.attack=x));
  head.appendChild(mk("release",0,1,0.01,s.release,x=>x.toFixed(2)+"s",x=>s.release=x));
  head.appendChild(mk("hi-pass",20,8000,10,s.hp,x=>Math.round(x)+"hz",x=>s.hp=x));
  head.appendChild(mk("lo-pass",300,16000,10,s.cutoff,x=>Math.round(x)+"hz",x=>s.cutoff=x));
  head.appendChild(mk("drive",0,1,0.01,s.drive,x=>Math.round(x*100)+"%",x=>s.drive=x));
  head.appendChild(mk("delay",0,0.7,0.01,s.dly,x=>Math.round(x*100)+"%",x=>s.dly=x));
  head.appendChild(mk("reverb",0,0.9,0.01,s.rev,x=>Math.round(x*100)+"%",x=>s.rev=x));
  const rev=document.createElement("button");rev.className="smpbtn"+(s.reverse?" on":"");rev.textContent="reverse";
  rev.addEventListener("click",()=>{s.reverse=!s.reverse;rev.classList.toggle("on",s.reverse);});head.appendChild(rev);
  const prev=document.createElement("button");prev.className="smpbtn prev";prev.textContent="▶ preview";
  function stopPreview(){if(s._previewSrc){try{s._previewSrc.onended=null;s._previewSrc.stop();}catch(e){}s._previewSrc=null;}prev.textContent="▶ preview";prev.classList.remove("on");}
  prev.addEventListener("click",()=>{
    ensureAudio();if(ac.state==="suspended")ac.resume();
    if(s._previewSrc){stopPreview();return;}
    const src=playSampleVoice(s,ac.currentTime+0.01);
    if(src){s._previewSrc=src;prev.textContent="■ stop";prev.classList.add("on");src.addEventListener("ended",()=>{if(s._previewSrc===src)stopPreview();});}
  });head.appendChild(prev);
  const del=document.createElement("button");del.className="smpbtn del";del.textContent="✕";
  del.addEventListener("click",()=>{stopPreview();samples=samples.filter(x=>x!==s);delete mixLevel["smp"+s.id];delete mixMute["smp"+s.id];
    const ch=mixer.querySelector('.ch[data-key="smp'+s.id+'"]');if(ch)ch.remove();row.remove();
    if(!samples.length)samplesWrap.innerHTML='<span class="hint" style="margin:0">No samples yet — click “upload sound”.</span>';});head.appendChild(del);
  row.appendChild(head);
  const lane=document.createElement("div");lane.className="seqrow";
  const ln=document.createElement("div");ln.className="rowname";ln.textContent="trigger";
  const steps=document.createElement("div");steps.className="steps";
  s._cells=[];
  for(let c=0;c<STEPS;c++){const cell=document.createElement("div");cell.className="cell smp";
    if(s.patterns[curPattern]&&s.patterns[curPattern][c])cell.classList.add("on");
    cell.addEventListener("click",()=>{const ln2=s.patterns[curPattern];ln2[c]=!ln2[c];cell.classList.toggle("on",ln2[c]);});
    steps.appendChild(cell);s._cells.push(cell);}
  lane.appendChild(ln);lane.appendChild(steps);row.appendChild(lane);
  return row;
}
function renderSamples(){
  samplesWrap.innerHTML="";
  if(!samples.length){samplesWrap.innerHTML='<span class="hint" style="margin:0">No samples yet — click “upload sound”.</span>';return;}
  samples.forEach(s=>samplesWrap.appendChild(buildSampleRow(s)));
}
function refreshSamples(){samples.forEach(s=>{if(!s._cells)return;s._cells.forEach((cell,i)=>cell.classList.toggle("on",!!(s.patterns[curPattern]&&s.patterns[curPattern][i])));});}
renderSamples();


function buildProject(){return{v:8,tempo,swing,master,revMix,arp,AP,PP,mixLevel,mixMute,patterns,song,
  openWins:[...document.querySelectorAll('.window.open')].map(w=>({id:w.id,wx:parseFloat(w.dataset.wx)||null,wy:parseFloat(w.dataset.wy)||null})),
  wires:connections.map(c=>({from:c.from,to:c.to})),
  samples:samples.map(s=>({name:s.name,pitch:s.pitch,start:s.start,end:s.end,attack:s.attack,release:s.release,hp:s.hp,cutoff:s.cutoff,drive:s.drive,dly:s.dly,rev:s.rev,reverse:s.reverse,patterns:s.patterns}))};}
document.getElementById("saveBtn").addEventListener("click",()=>{const blob=new Blob([JSON.stringify(buildProject())],{type:"application/json"});
  const a=document.createElement("a");a.href=URL.createObjectURL(blob);a.download="acidlab-project.json";a.click();});
const fileIn=document.getElementById("fileIn");
document.getElementById("loadBtn").addEventListener("click",()=>fileIn.click());
fileIn.addEventListener("change",e=>{const f=e.target.files[0];if(!f)return;const rd=new FileReader();
  rd.onload=()=>{try{const j=JSON.parse(rd.result);
    tempo=j.tempo??tempo;swing=j.swing??swing;master=j.master??master;revMix=j.revMix??revMix;
    if(j.arp){Object.assign(arp,j.arp);const ab=document.getElementById("arpOn");ab.classList.toggle("on",arp.on);ab.textContent=arp.on?"on":"off";document.getElementById("arpMode").value=arp.mode;document.getElementById("arpRate").value=arp.rate;document.getElementById("arpOct").value=arp.oct;}
    Object.assign(AP,j.AP||{});Object.assign(PP,j.PP||{});Object.assign(mixLevel,j.mixLevel||{});Object.assign(mixMute,j.mixMute||{});
    if(Array.isArray(j.patterns)&&j.patterns.length){patterns=j.patterns;patterns.forEach(fixDrums);}
    if(Array.isArray(j.song))song=j.song;curPattern=0;
    syncSampleLanes();
    applyToUI();
    // Close all open windows, then restore saved open windows with their positions
    document.querySelectorAll('.window.open').forEach(w=>closeWindow(w.id));
    if(Array.isArray(j.openWins)){
      let cascOff=0;
      j.openWins.forEach(entry=>{
        const id   = typeof entry==='string' ? entry : entry?.id;
        const wx   = typeof entry==='object' && entry?.wx!=null ? entry.wx : null;
        const wy   = typeof entry==='object' && entry?.wy!=null ? entry.wy : null;
        if(!id)return;
        if(wx!=null){
          try{openWindow(id,wx,wy);}catch(_){}
        } else {
          // Old file — cascade from center so windows don't all stack
          const win=document.getElementById(id); if(!win)return;
          const w=parseInt(win.style.width)||360;
          const cx=((window.innerWidth-w*wsZoom)/2-wsPanX)/wsZoom+cascOff;
          const cy=(Math.max(60,(window.innerHeight-280*wsZoom)/2+26)-wsPanY)/wsZoom+cascOff;
          try{openWindow(id,cx,cy);}catch(_){}
          cascOff+=32;
        }
      });
    }
    // Restore wire connections
    if(Array.isArray(j.wires)){
      [...connections].forEach(c=>removeWire(c));
      j.wires.forEach(w=>{try{addWire(w.from.win,w.from.port,w.to.win,w.to.port);}catch(_){}});
    }
  }catch(err){console.error('Load error:',err);alert("Could not load project — the file may be corrupted or from an incompatible version.");}};
  rd.readAsText(f);fileIn.value="";});
function setVal(id,val){const el=document.getElementById(id);if(el){el.value=val;el.dispatchEvent(new Event("input"));}}
function applyToUI(){
  setVal("bpm",tempo);setVal("masterVol",master);setVal("kSwing",swing);setVal("kRev",revMix);
  setVal("aCut",AP.cut);setVal("aRes",AP.res);setVal("aEnv",AP.env);setVal("aDec",AP.dec);setVal("aAcc",AP.acc);setVal("aDrv",AP.drv);setVal("aDly",AP.dly);
  applyPolyUI();
  ACID_WAVES.forEach(([i,v])=>document.getElementById(i).classList.toggle("on",AP.wave===v));
  Array.from(mixer.children).forEach(ch=>{const k=ch.dataset.key;if(k==null)return;const inp=ch.querySelector("input");if(inp)inp.value=mixLevel[k]??0.8;const mb=ch.querySelector(".mbtn");if(mb)mb.classList.toggle("on",!!mixMute[k]);});
  renderPatternBtns();renderChain();refreshAll();
}

/* ---------- playhead ---------- */
function paintPlayhead(step){document.querySelectorAll(".cell.playcol").forEach(c=>c.classList.remove("playcol"));if(step<0)return;
  aCells.forEach(c=>{if(+c.dataset.c===step)c.classList.add("playcol");});
  pCells.forEach(c=>{if(+c.dataset.c===step)c.classList.add("playcol");});
  DRUMS.forEach(d=>drumCells[d][step].classList.add("playcol"));
  samples.forEach(s=>{if(s._cells&&s._cells[step])s._cells[step].classList.add("playcol");});}

/* ---------- init ---------- */
setOctLbl();renderPatternBtns();renderChain();refreshAll();requestAnimationFrame(draw);

/* ====================================================================
   DESKTOP SHELL: dock, draggable windows, mirrored transport, settings
==================================================================== */
const DOCK_APPS=[
  // INSTRUMENTS
  {id:"win-acid",icon:"acid_303.png",name:"Acid 303",cat:"Instruments"},
  {id:"win-poly",icon:"poly_synth.png",name:"Poly Synth",cat:"Instruments"},
  {id:"win-drum",icon:"drum_machine.png",name:"Drum Machine",cat:"Instruments"},
  {id:"win-sampler",icon:"sampler.png",name:"Sampler",cat:"Instruments"},
  {id:"win-keyboard",icon:"keyboard.png",name:"Keyboard",cat:"Instruments"},
  {id:"win-chordgen",icon:"chord.svg",name:"Chord Generator",cat:"Instruments"},
  {id:"win-padboard",icon:"padboard.svg",name:"Chord Pad",cat:"Instruments"},
  // SEQUENCERS
  {id:"win-transport",icon:"recorder.png",name:"Transport",cat:"Sequencers"},
  {id:"win-patterns",icon:"patterns.png",name:"Patterns / Song",cat:"Sequencers"},
  {id:"win-pianoroll",icon:"piano_roll.png",name:"Piano Roll",cat:"Sequencers"},
  {id:"win-arp",icon:"arpeggiator.svg",name:"Arpeggiator",cat:"Sequencers"},
  {id:"win-lfo",icon:"lfo.svg",name:"LFO",cat:"Sequencers"},
  // EFFECTS
  {id:"win-reverb",icon:"reverb.svg",name:"Reverb Studio",cat:"Effects"},
  {id:"win-delay",icon:"delay.svg",name:"Delay",cat:"Effects"},
  {id:"win-chorus",icon:"chorus.svg",name:"Chorus",cat:"Effects"},
  {id:"win-phaser",icon:"phaser.svg",name:"Phaser",cat:"Effects"},
  {id:"win-flanger",icon:"flanger.svg",name:"Flanger",cat:"Effects"},
  {id:"win-tremolo",icon:"tremolo.svg",name:"Tremolo",cat:"Effects"},
  {id:"win-ringmod",icon:"ringmod.svg",name:"Ring Mod",cat:"Effects"},
  {id:"win-lofi",icon:"lofi.svg",name:"Lo-Fi",cat:"Effects"},
  {id:"win-autofilter",icon:"autofilter.svg",name:"Auto-Filter",cat:"Effects"},
  {id:"win-granular",icon:"granular.svg",name:"Granular",cat:"Effects"},
  {id:"win-bitcrush",icon:"bitcrush.svg",name:"Bit Crusher",cat:"Effects"},
  {id:"win-cabinet",icon:"cabinet.svg",name:"Cabinet Sim",cat:"Effects"},
  {id:"win-comb",icon:"comb.svg",name:"Comb Filter",cat:"Effects"},
  // DYNAMICS
  {id:"win-compressor",icon:"compressor.svg",name:"Compressor",cat:"Dynamics"},
  {id:"win-eq",icon:"eq.svg",name:"EQ 5-Band",cat:"Dynamics"},
  {id:"win-gate",icon:"gate.svg",name:"Gate",cat:"Dynamics"},
  {id:"win-vol",icon:"vol.svg",name:"Volume",cat:"Dynamics"},
  {id:"win-pan",icon:"pan.svg",name:"Pan",cat:"Dynamics"},
  {id:"win-mixer",icon:"mixer.png",name:"Mixer",cat:"Dynamics"},
  {id:"win-stereoimg",icon:"stereoimg.svg",name:"Stereo Imager",cat:"Dynamics"},
  // ANALYSIS
  {id:"win-spectrum",icon:"spectrum.svg",name:"Spectrum",cat:"Analysis"},
  {id:"win-scope",icon:"scope.svg",name:"Oscilloscope",cat:"Analysis"},
  {id:"win-tone",icon:"tone.svg",name:"Tone Generator",cat:"Analysis"},
  {id:"win-noise",icon:"noise.svg",name:"Noise",cat:"Analysis"},
  // NEW MAJOR APPS
  {id:"win-distortion",icon:"distortion.svg",name:"Distortion",cat:"Effects"},
  {id:"win-multicomp",icon:"multicomp.svg",name:"Multi-Band Comp",cat:"Dynamics"},
  {id:"win-wavetable",icon:"wavetable.svg",name:"Wavetable Synth",cat:"Instruments"},
  {id:"win-stepseq",icon:"stepseq.svg",name:"Step Sequencer",cat:"Instruments"},
  {id:"win-tape",icon:"tape.svg",name:"Tape Machine",cat:"Effects"},
  {id:"win-formant",icon:"formant.svg",name:"Vowel Filter",cat:"Effects"},
  {id:"win-sidechain",icon:"sidechain.svg",name:"Sidechain Comp",cat:"Dynamics"},
  {id:"win-glitch",icon:"glitch.svg",name:"Glitch",cat:"Effects"},
  {id:"win-osc-bank",icon:"oscbank.svg",name:"Oscillator Bank",cat:"Instruments"},
  {id:"win-freqshift",icon:"freqshift.svg",name:"Freq Shifter",cat:"Effects"},
  // UTILITIES
  {id:"win-merge",icon:"merge.svg",name:"Merge",cat:"Utilities"},
  {id:"win-effects",icon:"effects.png",name:"Effects Rack",cat:"Utilities"},
  {id:"win-settings",icon:"settings.png",name:"Settings",cat:"Utilities"},
];
let zTop=10;
// Undo/redo history for knob changes
const _undoStack=[], _redoStack=[], _UNDO_MAX=50;
function _pushUndo(fn){_undoStack.push(fn);if(_undoStack.length>_UNDO_MAX)_undoStack.shift();_redoStack.length=0;}
document.addEventListener('keydown',e=>{
  if(e.target.tagName==='INPUT'||e.target.tagName==='SELECT')return;
  if((e.ctrlKey||e.metaKey)&&!e.shiftKey&&e.key.toLowerCase()==='z'){e.preventDefault();const fn=_undoStack.pop();if(fn){const redo=fn();if(redo)_redoStack.push(redo);}}
  if((e.ctrlKey||e.metaKey)&&(e.shiftKey&&e.key.toLowerCase()==='z'||e.key.toLowerCase()==='y')){e.preventDefault();const fn=_redoStack.pop();if(fn){const undo=fn();if(undo)_undoStack.push(undo);}}
});
function focusWindow(win){zTop++;win.style.zIndex=zTop;document.querySelectorAll(".window.focused").forEach(w=>{w.classList.remove("focused");w.style.opacity='0.85';});win.classList.add("focused");win.style.opacity='1';}
function saveWinPos(win){
  try{
    const r=win.getBoundingClientRect();
    const data={x:parseFloat(win.style.left)||r.left,y:parseFloat(win.style.top)||r.top,
      w:win.style.width||'',h:win.style.height||''};
    const store=JSON.parse(localStorage.getItem('acid-win-pos')||'{}');
    store[win.id]=data;localStorage.setItem('acid-win-pos',JSON.stringify(store));
  }catch(_){}
}
function restoreWinPos(win){
  try{
    const store=JSON.parse(localStorage.getItem('acid-win-pos')||'{}');
    const d=store[win.id];if(!d)return false;
    win.style.left=d.x+'px';win.style.top=d.y+'px';
    if(d.w)win.style.width=d.w;if(d.h)win.style.height=d.h;
    win.dataset.wx=(d.x-wsPanX)/wsZoom;win.dataset.wy=(d.y-wsPanY)/wsZoom;
    return true;
  }catch(_){return false;}
}
function openWindow(id, atWx, atWy){
  const win=document.getElementById(id);if(!win)return;
  // Lazy-init factory UI on first open (handles windows whose HTML was added after first load)
  const baseId=id.replace(/-i\d+$/,'');
  if(APP_FACTORIES[baseId]){
    const wb=win.querySelector('.wbody');
    if(wb&&!wb.children.length)APP_FACTORIES[baseId](win);
  }
  // Restore from minimized if needed
  win.classList.remove('minimized');
  const wb2=win.querySelector('.wbody');if(wb2)wb2.style.display='';
  let wx, wy;
  if(atWx!=null){
    wx=atWx; wy=atWy;
    win.dataset.wx=wx; win.dataset.wy=wy;
    win.style.left=(wx*wsZoom+wsPanX)+'px';
    win.style.top=(wy*wsZoom+wsPanY)+'px';
  } else if(!restoreWinPos(win)){
    const w=parseInt(win.style.width)||360;
    const sx=(window.innerWidth-w*wsZoom)/2;
    const sy=Math.max(60,(window.innerHeight-280*wsZoom)/2+26);
    wx=(sx-wsPanX)/wsZoom; wy=(sy-wsPanY)/wsZoom;
    win.dataset.wx=wx; win.dataset.wy=wy;
    win.style.left=(wx*wsZoom+wsPanX)+'px';
    win.style.top=(wy*wsZoom+wsPanY)+'px';
  }
  win.style.transform=`scale(${wsZoom})`;
  win.style.transformOrigin='0 0';
  win.classList.remove("closing");
  win.getAnimations().forEach(a=>a.cancel());
  win.classList.add("open");
  recordRecentApp(id);
  win.animate([
    {opacity:0,transform:`translateY(14px) scale(${wsZoom*0.93})`,offset:0},
    {opacity:1,transform:`translateY(0) scale(${wsZoom})`,offset:1}
  ],{duration:300,easing:'cubic-bezier(.22,1,.36,1)',fill:'none'});
  focusWindow(win);updateDock();updateLibraryInUse();if(typeof redrawWires==='function')redrawWires();
  if(typeof initSliders==='function')initSliders();
  const d=dock&&dock.querySelector('.dock-app[data-win="'+baseId+'"]');
  if(d){d.classList.remove("bounce");void d.offsetWidth;d.classList.add("bounce");}
}
function closeWindow(id){
  const win=document.getElementById(id);if(!win)return;
  [...connections].filter(c=>c.from.win===id||c.to.win===id).forEach(c=>removeWire(c));
  // Kill audio output and any playing voices
  if(APP_BUSES[id]){
    try{APP_BUSES[id].output.disconnect();}catch(_){}
    try{if(typeof APP_BUSES[id]._stop==='function')APP_BUSES[id]._stop();}catch(_){}
  }
  const curT=win.style.transform||`scale(${wsZoom})`;
  win.getAnimations().forEach(a=>a.cancel());
  win.classList.add("closing");
  const anim=win.animate([
    {opacity:1,transform:curT},
    {opacity:0,transform:`scale(${wsZoom*0.88}) translateY(8px)`}
  ],{duration:160,easing:'cubic-bezier(.4,0,1,1)',fill:'forwards'});
  anim.onfinish=()=>{
    anim.cancel();
    win.classList.remove("open","closing","maxd");
    if(/^win-.+-i\d+$/.test(id)){
      win.remove();
      delete APP_BUSES[id];
      delete PORT_DEFS[id];
    }else{
      win.style.removeProperty("transform");
      win.style.removeProperty("transformOrigin");
      win.style.removeProperty("height");
    }
    updateDock();
    updateLibraryInUse();
  };
}
function toggleWindow(id){const win=document.getElementById(id);if(!win)return;if(win.classList.contains("open")&&win.classList.contains("focused")){closeWindow(id);}else if(win.classList.contains("open")){focusWindow(win);}else{openWindow(id);}}
function maximizeWindow(win){
  if(win.classList.contains("maxd")){
    win.classList.remove("maxd");
    if(win._restore)win.style.width=win._restore.w;
    win.style.height="";
    const wx=parseFloat(win.dataset.wx)||0,wy=parseFloat(win.dataset.wy)||0;
    win.style.left=(wx*wsZoom+wsPanX)+'px';
    win.style.top=(wy*wsZoom+wsPanY)+'px';
    win.style.transform=`scale(${wsZoom})`;
    win.style.transformOrigin='0 0';
  }else{
    win._restore={w:win.style.width};
    win.classList.add("maxd");
    win.style.transform='none';win.style.transformOrigin='';
    win.style.left="2vw";win.style.top="60px";win.style.width="96vw";win.style.height="calc(100vh - 84px)";
  }
  focusWindow(win);
}

// ===== DOCK + APP LIBRARY =====
const dock=document.getElementById("dock");

// Full app catalogue
const ALL_DOCK_APPS=DOCK_APPS;

// id of the icon currently being dragged (set on dragstart, cleared on drop/dragend)
let dragId=null;

// Hotbar: ordered list of app IDs pinned to the visible dock
let hotbarIds=(function(){
  try{const s=JSON.parse(localStorage.getItem('acid-hotbar'));if(Array.isArray(s)&&s.length)return s;}catch(_){}
  return []; // start with empty hotbar on first launch
})();
function saveHotbar(){localStorage.setItem('acid-hotbar',JSON.stringify(hotbarIds));}
function triggerHotbarShake(){
  [document.getElementById('dock'),document.getElementById('dock-library')].forEach(el=>{
    if(!el)return;
    el.classList.remove('shake');
    void el.offsetWidth;
    el.classList.add('shake');
    el.addEventListener('animationend',()=>el.classList.remove('shake'),{once:true});
  });
}

function getIconSrc(appId){
  const winEl=document.getElementById(appId);
  const ti=winEl?winEl.querySelector('.titlebar img'):null;
  if(ti)return ti.getAttribute('src');
  const app=ALL_DOCK_APPS.find(a=>a.id===appId);
  return app?'assets/'+app.icon:'';
}

function makeDockIcon(app){
  const d=document.createElement('div');d.className='dock-app';d.dataset.win=app.id;
  const wrap=document.createElement('div');wrap.className='dock-icon-wrap';
  const img=document.createElement('img');img.src=getIconSrc(app.id);img.alt=app.name;
  wrap.appendChild(img);
  const shell=document.createElement('span');shell.className='fgis-shell';shell.setAttribute('aria-hidden','true');
  const tip=document.createElement('span');tip.className='tip';tip.textContent=app.name;
  d.appendChild(wrap);d.appendChild(shell);d.appendChild(tip);
  d.addEventListener('click',e=>{
    if((e.ctrlKey||e.metaKey)&&APP_FACTORIES[app.id]){
      spawnWindow(app.id); // Ctrl+Click always spawns new instance
    }else{
      toggleWindow(app.id);
    }
  });
  d.addEventListener('auxclick',e=>{
    if(e.button===1&&APP_FACTORIES[app.id]){e.preventDefault();spawnWindow(app.id);}
  });
  d.setAttribute('draggable','true');
  d.addEventListener('dragstart',e=>{dragId=app.id;d.classList.add('dragging');e.dataTransfer.effectAllowed='move';try{e.dataTransfer.setData('text/plain',app.id);}catch(_){}});
  d.addEventListener('dragend',e=>{
    d.classList.remove('dragging');
    if(dragId){
      const over=document.elementFromPoint(e.clientX,e.clientY);
      if(over&&!over.closest('#dock')&&!over.closest('#dock-library')&&!over.closest('#topbar')&&!over.closest('.window')){
        const wx=(e.clientX-wsPanX)/wsZoom, wy=(e.clientY-wsPanY)/wsZoom;
        if(APP_FACTORIES[app.id]&&document.getElementById(app.id)?.classList.contains('open')){
          spawnWindow(app.id,wx,wy);
        }else{
          openWindow(app.id,wx,wy);
        }
      }
      dragId=null;
    }
  });
  return d;
}

function renderHotbar(){
  dock.querySelectorAll('.dock-app').forEach(el=>el.remove());
  hotbarIds.forEach(id=>{
    const app=ALL_DOCK_APPS.find(a=>a.id===id);
    if(app)dock.insertBefore(makeDockIcon(app),dockSep);
  });
  updateDock();
}

function updateDock(){
  ALL_DOCK_APPS.forEach(app=>{
    const el=dock.querySelector('.dock-app[data-win="'+app.id+'"]');
    const win=document.getElementById(app.id);
    // Also check if any spawned instance is open
    const anyOpen=win?.classList.contains('open')
      || !!document.querySelector(`.window.open[id^="${app.id}-i"]`);
    if(el)el.classList.toggle('running',anyOpen);
  });
}

// Separator + library button
const dockSep=document.createElement('div');dockSep.className='dock-separator';dock.appendChild(dockSep);
const dockLibBtn=document.createElement('div');dockLibBtn.className='dock-lib-btn';
dockLibBtn.setAttribute('aria-label','App Library');
dock.appendChild(dockLibBtn);
// Folder-style preview: a mini grid of the app icons contained in the library
function renderLibBtn(){
  dockLibBtn.innerHTML='';
  const grid=document.createElement('div');grid.className='lib-btn-grid';
  ALL_DOCK_APPS.slice(0,4).forEach(app=>{
    const im=document.createElement('img');im.src=getIconSrc(app.id);im.alt='';im.className='lib-btn-mini';
    grid.appendChild(im);
  });
  dockLibBtn.appendChild(grid);
}
renderLibBtn();

// Library panel (appended to body so it floats above dock)
const libPanel=document.createElement('div');libPanel.id='dock-library';
libPanel.innerHTML='<div class="lib-search-pill"><span class="lib-search-icon"><svg width="16" height="16" viewBox="0 0 16 16" fill="none"><circle cx="6.5" cy="6.5" r="4.5" stroke="currentColor" stroke-width="1.6"/><line x1="10.5" y1="10.5" x2="14" y2="14" stroke="currentColor" stroke-width="1.6" stroke-linecap="round"/></svg></span><input type="text" class="lib-search" id="lib-search" placeholder="Search apps…" autocomplete="off" spellcheck="false"></div><div class="lib-inner"><div class="lib-header"><div class="lib-nav" id="lib-nav"></div></div><div class="lib-scroll"><div id="lib-grid"></div></div></div>';
document.body.appendChild(libPanel);

function getIconGlowColor(img){
  try{
    const cv=document.createElement('canvas');cv.width=cv.height=16;
    const cx=cv.getContext('2d');cx.drawImage(img,0,0,16,16);
    const data=cx.getImageData(0,0,16,16).data;
    let br=180,bg=100,bb=60,best=-1;
    for(let i=0;i<data.length;i+=4){
      const a=data[i+3];if(a<30)continue;
      const r=data[i],g=data[i+1],b=data[i+2];
      const mx=Math.max(r,g,b),mn=Math.min(r,g,b),lum=(r+g+b)/3;
      const sat=mx===0?0:(mx-mn)/mx;
      const score=sat*Math.min(lum/200,1);
      if(score>best&&lum>30&&sat>.12){best=score;br=r;bg=g;bb=b;}
    }
    return `${br},${bg},${bb}`;
  }catch(e){return '180,100,60';}
}

function makeLibCell(app, animate, cellIndex){
  const inHotbar=hotbarIds.includes(app.id);
  const cell=document.createElement('div');cell.className='lib-cell'+(inHotbar?' in-hotbar':'');cell.dataset.win=app.id;
  const wrap=document.createElement('div');wrap.className='dock-icon-wrap';
  const img=document.createElement('img');img.src=getIconSrc(app.id);img.alt=app.name;
  wrap.appendChild(img);
  const shell=document.createElement('span');shell.className='fgis-shell';shell.setAttribute('aria-hidden','true');
  const name=document.createElement('span');name.className='lib-name';name.textContent=app.name;
  cell.appendChild(wrap);cell.appendChild(shell);cell.appendChild(name);
  let glow='180,100,60';
  function applyGlow(hovered){
    const pinned=hotbarIds.includes(app.id);
    let shadow='';
    if(pinned&&hovered)shadow=`0 0 0 2.5px rgba(${glow},.95),0 0 30px rgba(${glow},.65),0 8px 20px rgba(0,0,0,.5)`;
    else if(pinned)shadow=`0 0 0 2.5px rgba(${glow},.85),0 0 22px rgba(${glow},.5),0 4px 14px rgba(0,0,0,.35)`;
    else if(hovered)shadow=`0 8px 26px rgba(${glow},.45),0 3px 10px rgba(0,0,0,.3)`;
    wrap.style.boxShadow=shadow;
  }
  cell._applyGlow=applyGlow;
  function onLoad(){glow=getIconGlowColor(img);applyGlow(false);}
  if(img.complete&&img.naturalWidth>0)onLoad();else img.addEventListener('load',onLoad);
  cell.addEventListener('mouseenter',()=>applyGlow(true));
  cell.addEventListener('mouseleave',()=>applyGlow(false));
  if(animate){cell.style.animation='libCellIn .38s cubic-bezier(.16,1,.3,1) both';cell.style.animationDelay=(cellIndex*18)+'ms';}
  cell.setAttribute('draggable','true');
  cell.addEventListener('dragstart',e=>{dragId=app.id;cell.classList.add('dragging');e.dataTransfer.effectAllowed='copyMove';try{e.dataTransfer.setData('text/plain',app.id);}catch(_){};setTimeout(()=>{if(libOpen)closeLib();},50);});
  cell.addEventListener('dragend',()=>{cell.classList.remove('dragging');dragId=null;});
  cell.addEventListener('click',()=>{
    const wasInHotbar=hotbarIds.includes(app.id);
    if(!wasInHotbar&&hotbarIds.length>=10){triggerHotbarShake();return;}
    cell.classList.add('pin-pop');
    setTimeout(()=>{
      if(wasInHotbar){hotbarIds=hotbarIds.filter(id=>id!==app.id);}
      else{hotbarIds=[...hotbarIds,app.id];}
      saveHotbar();renderHotbar();renderLibrary(false);
      if(!wasInHotbar){const el=dock.querySelector('.dock-app[data-win="'+app.id+'"]');if(el){void el.offsetWidth;el.classList.add('pin-in');el.addEventListener('animationend',()=>el.classList.remove('pin-in'),{once:true});}}
    },200);
  });
  return cell;
}

const LIB_RECENT_KEY='bagio-recent-apps';
const LIB_RECENT_MAX=8;
function getRecentApps(){try{return JSON.parse(localStorage.getItem(LIB_RECENT_KEY)||'[]');}catch{return [];}}
function recordRecentApp(id){
  const base=id.replace(/-i\d+$/,'');
  let list=getRecentApps().filter(x=>x!==base);
  list.unshift(base);
  if(list.length>LIB_RECENT_MAX)list=list.slice(0,LIB_RECENT_MAX);
  try{localStorage.setItem(LIB_RECENT_KEY,JSON.stringify(list));}catch{}
}

function renderLibNav(visibleCats){
  const nav=document.getElementById('lib-nav');if(!nav)return;
  nav.innerHTML='';
  visibleCats.forEach(cat=>{
    const pill=document.createElement('button');pill.className='lib-nav-pill';pill.textContent=cat;pill.dataset.cat=cat;
    pill.addEventListener('click',()=>{
      const hdr=[...document.querySelectorAll('#lib-grid .lib-cat-header')].find(h=>h.textContent===cat);
      if(hdr)hdr.closest('.lib-cat')?.scrollIntoView({behavior:'smooth',block:'start'});
      nav.querySelectorAll('.lib-nav-pill').forEach(p=>p.classList.remove('nav-active'));
      pill.classList.add('nav-active');
    });
    nav.appendChild(pill);
  });
}

const NEW_APP_IDS=['win-distortion','win-multicomp','win-wavetable','win-stepseq','win-tape','win-formant','win-sidechain','win-glitch','win-osc-bank','win-freqshift'];
function renderLibrary(animate){
  const grid=document.getElementById('lib-grid');if(!grid)return;
  grid.innerHTML='';
  const q=(document.getElementById('lib-search')?.value||'').trim().toLowerCase();
  const visibleCats=[];
  let cellIdx=0;
  // New apps section — always first, glows with accent colour
  const newApps=ALL_DOCK_APPS.filter(a=>NEW_APP_IDS.includes(a.id)&&(!q||a.name.toLowerCase().includes(q)));
  if(newApps.length){
    const sec=document.createElement('div');sec.className='lib-cat lib-new';sec.dataset.cat='New';
    const hdr=document.createElement('div');hdr.className='lib-cat-header lib-new-hdr';hdr.textContent='New';
    const row=document.createElement('div');row.className='lib-cat-grid';
    newApps.forEach(app=>{row.appendChild(makeLibCell(app,animate,cellIdx++));});
    sec.append(hdr,row);grid.appendChild(sec);
    visibleCats.push('New');
  }
  // Recent section — only when not searching
  if(!q){
    const recentIds=getRecentApps();
    const recentApps=recentIds.map(id=>ALL_DOCK_APPS.find(a=>a.id===id)).filter(Boolean).filter(a=>!NEW_APP_IDS.includes(a.id));
    if(recentApps.length){
      const sec=document.createElement('div');sec.className='lib-cat';sec.dataset.cat='Recent';
      const hdr=document.createElement('div');hdr.className='lib-cat-header';hdr.textContent='Recent';
      const row=document.createElement('div');row.className='lib-cat-grid';
      recentApps.forEach(app=>{row.appendChild(makeLibCell(app,animate,cellIdx++));});
      sec.append(hdr,row);grid.appendChild(sec);
      visibleCats.push('Recent');
    }
  }
  const cats=['Instruments','Sequencers','Effects','Dynamics','Analysis','Utilities'];
  cats.forEach(cat=>{
    // Exclude new apps from their regular category so they don't appear twice
    const apps=ALL_DOCK_APPS.filter(a=>a.cat===cat&&!NEW_APP_IDS.includes(a.id)&&(!q||a.name.toLowerCase().includes(q)));
    if(!apps.length)return;
    const sec=document.createElement('div');sec.className='lib-cat';sec.dataset.cat=cat;
    const hdr=document.createElement('div');hdr.className='lib-cat-header';hdr.textContent=cat;
    const row=document.createElement('div');row.className='lib-cat-grid';
    apps.forEach(app=>{row.appendChild(makeLibCell(app,animate,cellIdx++));});
    sec.append(hdr,row);grid.appendChild(sec);
    visibleCats.push(cat);
  });
  if(q){
    const shown=new Set(cats.flatMap(c=>ALL_DOCK_APPS.filter(a=>a.cat===c).map(a=>a.id)));
    const rest=ALL_DOCK_APPS.filter(a=>!shown.has(a.id)&&a.name.toLowerCase().includes(q));
    if(rest.length){const row=document.createElement('div');row.className='lib-cat-grid';rest.forEach(app=>row.appendChild(makeLibCell(app,animate,cellIdx++)));grid.appendChild(row);}
  }
  renderLibNav(visibleCats);
}

function updateLibraryInUse(){
  document.querySelectorAll('.lib-cell').forEach(cell=>{
    if(typeof cell._applyGlow==='function')cell._applyGlow(false);
  });
}

let libOpen=false;
function openLib(){libOpen=true;libPanel.classList.add('open');dockLibBtn.classList.add('active');renderLibrary(true);setTimeout(()=>document.getElementById('lib-search')?.focus(),80);}
function closeLib(){libOpen=false;libPanel.classList.remove('open');dockLibBtn.classList.remove('active');}
dockLibBtn.addEventListener('click',e=>{e.stopPropagation();libOpen?closeLib():openLib();});
// Library stays open until the user clicks the library button — no outside-click close
libPanel.addEventListener('input',e=>{if(e.target.id==='lib-search')renderLibrary(false);});
libPanel.addEventListener('keydown',e=>{if(e.key==='Escape')closeLib();});

// ----- Drag & drop: reorder hotbar, pin from library, unpin into library -----
// Find the insertion index among the visible dock apps for a given cursor x
function dockDropIndex(clientX){
  const items=[...dock.querySelectorAll('.dock-app')];
  for(let i=0;i<items.length;i++){
    const r=items[i].getBoundingClientRect();
    if(clientX<r.left+r.width/2)return i;
  }
  return items.length;
}
dock.addEventListener('dragover',e=>{if(dragId){e.preventDefault();e.dataTransfer.dropEffect='move';}});
dock.addEventListener('drop',e=>{
  if(!dragId)return;
  e.preventDefault();
  let idx=dockDropIndex(e.clientX);
  const cur=hotbarIds.indexOf(dragId);
  if(cur===-1&&hotbarIds.length>=10){triggerHotbarShake();dragId=null;return;}
  if(cur!==-1){if(cur<idx)idx--;hotbarIds.splice(cur,1);}
  hotbarIds.splice(idx,0,dragId);
  saveHotbar();renderHotbar();if(libOpen)renderLibrary();
  dragId=null;
});
// Dropping a pinned app back into the library panel removes it from the hotbar
libPanel.addEventListener('dragover',e=>{if(dragId&&hotbarIds.includes(dragId)){e.preventDefault();e.dataTransfer.dropEffect='move';}});
libPanel.addEventListener('drop',e=>{
  if(dragId&&hotbarIds.includes(dragId)){
    e.preventDefault();
    hotbarIds=hotbarIds.filter(id=>id!==dragId);
    saveHotbar();renderHotbar();renderLibrary();
  }
  dragId=null;
});
// Drag from library and drop onto workspace: open window at drop position
document.addEventListener('dragover',e=>{
  if(dragId&&!e.target.closest('.window')&&!e.target.closest('#dock')&&!e.target.closest('#dock-library')&&!e.target.closest('#topbar')){
    e.preventDefault();e.dataTransfer.dropEffect='copy';
  }
});
document.addEventListener('drop',e=>{
  if(!dragId||e.target.closest('#dock')||e.target.closest('#dock-library')||e.target.closest('#topbar'))return;
  if(!e.target.closest('.window')){
    e.preventDefault();
    const wx=(e.clientX-wsPanX)/wsZoom;
    const wy=(e.clientY-wsPanY)/wsZoom;
    const id=dragId; dragId=null;
    if(APP_FACTORIES[id]&&document.getElementById(id)?.classList.contains('open')){
      spawnWindow(id,wx,wy);
    }else{
      openWindow(id,wx,wy);
    }
    if(libOpen)closeLib();
  }
});

renderHotbar();

// window traffic lights + focus on click + drag by titlebar
document.querySelectorAll(".window").forEach(win=>initWindowFrame(win));

// mirror transport: top bar (primary) <-> transport window (secondary)
function mirror(primaryId,secondaryId,evt){const a=document.getElementById(primaryId),b=document.getElementById(secondaryId);
  if(!a||!b)return;
  b.addEventListener(evt,()=>a.dispatchEvent(new Event(evt.startsWith("click")?"click":evt)));
}
// play/rec window buttons trigger the real top-bar buttons
document.getElementById("playBtn2").addEventListener("click",()=>document.getElementById("playBtn").click());
document.getElementById("recBtn2").addEventListener("click",()=>document.getElementById("recBtn").click());
// keep window buttons' label/state synced with the real ones via observer
function syncBtn(srcId,dstId){const src=document.getElementById(srcId),dst=document.getElementById(dstId);if(!src||!dst)return;
  const obs=new MutationObserver(()=>{dst.classList.toggle("on",src.classList.contains("on"));});
  obs.observe(src,{attributes:true,childList:false,subtree:false});}
syncBtn("playBtn","playBtn2");syncBtn("recBtn","recBtn2");
// bpm mirror both directions
const bpmTop=document.getElementById("bpm"),bpmWin=document.getElementById("bpm2");
bpmWin.addEventListener("input",()=>{bpmTop.value=bpmWin.value;bpmTop.dispatchEvent(new Event("input"));});
bpmTop.addEventListener("input",()=>{bpmWin.value=bpmTop.value;});

// ---------- settings / reset ----------
const DEFAULT_AP={wave:"sawtooth",cut:480,res:0.78,env:0.72,dec:0.28,acc:0.6,drv:0.25,dly:0.12};
const DEFAULT_PP={wave:"sawtooth",cut:3500,res:0.2,atk:0.01,rel:0.4,dly:0.18,rev:0.3,detune:8,sub:0,fenv:0,lfoRate:0,lfoDepth:0};
function resetSynthKnobs(){
  Object.assign(AP,DEFAULT_AP);Object.assign(PP,DEFAULT_PP);revMix=0.16;
  setVal("aCut",AP.cut);setVal("aRes",AP.res);setVal("aEnv",AP.env);setVal("aDec",AP.dec);setVal("aAcc",AP.acc);setVal("aDrv",AP.drv);setVal("aDly",AP.dly);
  ACID_WAVES.forEach(([i,v])=>document.getElementById(i).classList.toggle("on",AP.wave===v));
  applyPolyUI();setVal("kRev",revMix);
}
document.getElementById("resetSynths").addEventListener("click",resetSynthKnobs);
document.getElementById("resetAll").addEventListener("click",()=>{
  if(!confirm("Reset everything? This clears all patterns, samples and settings."))return;
  // Remove all wires and close all windows
  [...connections].forEach(c=>removeWire(c));
  document.querySelectorAll('.window.open').forEach(w=>closeWindow(w.id));
  // clear samples + their mixer channels
  samples.slice().forEach(s=>{const ch=mixer.querySelector('.ch[data-key="smp'+s.id+'"]');if(ch)ch.remove();delete mixLevel["smp"+s.id];delete mixMute["smp"+s.id];});
  samples=[];renderSamples();
  patterns=[emptyPattern()];curPattern=0;song=[0];songMode=false;
  tempo=124;swing=0.12;master=0.8;
  resetSynthKnobs();setVal("bpm",124);setVal("masterVol",0.8);setVal("kSwing",0.12);
  songToggle.textContent="play loop";songToggle.classList.remove("on");
  renderPatternBtns();renderChain();refreshAll();
});

updateDock();

/* ======== PIANO ROLL ======== */
(function(){
  const MIDI_MIN=24,MIDI_MAX=96;
  const N=MIDI_MAX-MIDI_MIN+1;
  const NH=13,KW=56,SW0=24,SH=20,STEPS=64;
  const BLACK_SEMI=new Set([1,3,6,8,10]);

  let prSx=0,prSy=Math.max(0,(N-24)*NH*0.4);
  let prZoom=1.4,prSnap=1,prTool='draw';
  let prDrawing=null,prResizing=null,prInited=false;

  function prNotes(){const p=patterns[curPattern];if(!Array.isArray(p.pianoRoll))p.pianoRoll=[];return p.pianoRoll;}
  function stepW(){return SW0*prZoom;}
  function gridW(){return STEPS*stepW();}
  function gridH(){return N*NH;}

  let prCanvas,prCtx,prWrap;

  function prInit(){
    if(prInited)return;
    prCanvas=document.getElementById('pr-canvas');
    if(!prCanvas||prCanvas.clientWidth===0)return;
    prCtx=prCanvas.getContext('2d');
    prWrap=document.getElementById('pr-viewport');
    prInited=true;
    new ResizeObserver(prResize).observe(prWrap);
    prResize();
    prCanvas.addEventListener('contextmenu',e=>e.preventDefault());
    prCanvas.addEventListener('wheel',prOnWheel,{passive:false});
    prCanvas.addEventListener('pointerdown',prOnDown);
    prCanvas.addEventListener('pointermove',prOnMove);
    prCanvas.addEventListener('pointerup',prOnUp);
    prCanvas.addEventListener('pointerleave',prOnUp);
    document.getElementById('pr-draw-btn').addEventListener('click',()=>prSetTool('draw'));
    document.getElementById('pr-erase-btn').addEventListener('click',()=>prSetTool('erase'));
    document.getElementById('pr-clear-btn').addEventListener('click',()=>{pushUndo();prNotes().length=0;});
    document.getElementById('pr-zoom-in').addEventListener('click',()=>{prZoom=Math.min(4,prZoom*1.35);});
    document.getElementById('pr-zoom-out').addEventListener('click',()=>{prZoom=Math.max(0.4,prZoom/1.35);});
    document.getElementById('pr-snap').addEventListener('change',e=>{prSnap=+e.target.value;});
    requestAnimationFrame(prLoop);
  }

  function prSetTool(t){prTool=t;document.getElementById('pr-draw-btn').classList.toggle('on',t==='draw');document.getElementById('pr-erase-btn').classList.toggle('on',t==='erase');prCanvas.style.cursor=t==='erase'?'not-allowed':'cell';}
  function prResize(){if(!prWrap||!prCanvas)return;prCanvas.width=prWrap.clientWidth||880;prCanvas.height=prWrap.clientHeight||360;}

  function prPos(e){
    const r=prCanvas.getBoundingClientRect();
    const px=e.clientX-r.left,py=e.clientY-r.top;
    const step=Math.max(0,Math.min(STEPS-1,Math.floor((px-KW+prSx)/stepW())));
    const noteIdx=Math.max(0,Math.min(N-1,Math.floor((py-SH+prSy)/NH)));
    const midi=MIDI_MAX-noteIdx;
    const snapped=Math.max(0,Math.floor(step/prSnap)*prSnap);
    return{px,py,inKeys:px<KW,step,snapped,midi};
  }

  function prOnDown(e){
    e.preventDefault();
    const p=prPos(e);
    if(p.inKeys){ensureAudio();if(ac.state==='suspended')ac.resume();polyNoteOn('prk'+p.midi,[p.midi]);prCanvas.setPointerCapture(e.pointerId);return;}
    if(e.button===2||prTool==='erase'){pushUndo();const idx=prNotes().findIndex(n=>n.midi===p.midi&&p.step>=n.start&&p.step<n.start+n.dur);if(idx!==-1)prNotes().splice(idx,1);return;}
    // resize handle?
    const existing=prNotes().find(n=>n.midi===p.midi&&p.step>=n.start&&p.step<n.start+n.dur);
    const handleX=existing?KW+((existing.start+existing.dur)*stepW())-prSx:0;
    if(existing&&p.px>=handleX-8&&p.px<=handleX+2){pushUndo();prResizing={note:existing,x0:p.px,d0:existing.dur};prCanvas.setPointerCapture(e.pointerId);return;}
    // draw new
    pushUndo();
    prDrawing={midi:p.midi,start:p.snapped,dur:prSnap,vel:0.8};
    prNotes().push(prDrawing);
    prCanvas.setPointerCapture(e.pointerId);
  }

  function prOnMove(e){
    const p=prPos(e);
    if(prDrawing){const end=Math.max(0,Math.floor((p.px-KW+prSx)/stepW()));const snappedEnd=Math.floor(end/prSnap)*prSnap;prDrawing.dur=Math.max(prSnap,snappedEnd+prSnap-prDrawing.start);prDrawing.dur=Math.min(prDrawing.dur,STEPS-prDrawing.start);}
    else if(prResizing){const dx=p.px-prResizing.x0;const dd=Math.round(dx/stepW()/prSnap)*prSnap;prResizing.note.dur=Math.max(prSnap,Math.min(prResizing.d0+dd,STEPS-prResizing.note.start));}
  }

  function prOnUp(){
    prDrawing=null;prResizing=null;
    for(let m=MIDI_MIN;m<=MIDI_MAX;m++)polyNoteOff('prk'+m);
  }

  function prOnWheel(e){
    e.preventDefault();
    if(e.shiftKey){prSx=Math.max(0,Math.min(Math.max(0,gridW()-50),prSx+e.deltaY*0.5));}
    else{prSy=Math.max(0,Math.min(Math.max(0,gridH()-100),prSy+e.deltaY*0.5));}
  }

  function prLoop(){
    if(!prInited){prInit();requestAnimationFrame(prLoop);return;}
    prRender();requestAnimationFrame(prLoop);
  }

  function prRender(){
    if(!prCanvas||!prCtx||prCanvas.width===0)return;
    const W=prCanvas.width,H=prCanvas.height;
    const ctx=prCtx;
    ctx.clearRect(0,0,W,H);

    // ruler
    ctx.fillStyle='#1a1c12';ctx.fillRect(0,0,W,SH);
    ctx.fillStyle='#1d2014';ctx.fillRect(KW,0,W-KW,SH);
    for(let s=0;s<STEPS;s++){
      const x=KW+s*stepW()-prSx;if(x<KW-1||x>W)continue;
      const isBar=s%16===0,isBeat=s%4===0;
      ctx.fillStyle=isBar?'#E86820':isBeat?'#8C4012':'#2A2820';
      ctx.fillRect(x,0,isBar?2:1,isBar?SH:isBeat?SH*0.65:SH*0.3);
      if(isBeat){ctx.fillStyle='#7A6040';ctx.font='8px Space Grotesk,system-ui,sans-serif';ctx.textAlign='left';ctx.fillText(isBar?'bar '+(s/16+1):''+(s/4+1),x+3,SH-3);}
    }
    if(isPlaying){const px=KW+currentStep*stepW()-prSx;if(px>=KW&&px<W){ctx.fillStyle='rgba(232,104,32,0.9)';ctx.fillRect(px-1,0,2,SH);}}

    // clip grid
    ctx.save();ctx.beginPath();ctx.rect(KW,SH,W-KW,H-SH);ctx.clip();

    // row backgrounds
    for(let i=0;i<N;i++){
      const y=SH+i*NH-prSy;if(y+NH<SH||y>H)continue;
      const midi=MIDI_MAX-i,semi=((midi%12)+12)%12;
      ctx.fillStyle=BLACK_SEMI.has(semi)?'#111307':'#161808';
      ctx.fillRect(KW,y,gridW(),NH);
      if(semi===0){ctx.fillStyle='#2b2f1c';ctx.fillRect(KW,y,gridW(),1);}
    }

    // vertical grid lines
    for(let s=0;s<=STEPS;s++){
      const x=KW+s*stepW()-prSx;if(x<KW-1||x>W)continue;
      ctx.fillStyle=s%16===0?'#3a4020':s%4===0?'#252a14':'#1c2010';
      ctx.fillRect(x,SH,1,H-SH);
    }

    // notes
    prNotes().forEach(n=>{
      const i=MIDI_MAX-n.midi,y=SH+i*NH-prSy+1,x=KW+n.start*stepW()-prSx+1,nw=n.dur*stepW()-2;
      if(y+NH-2<SH||y>H||x+nw<KW||x>W)return;
      ctx.fillStyle=n===prDrawing?'rgba(232,104,32,0.6)':'#E86820';
      if(ctx.roundRect){ctx.beginPath();ctx.roundRect(x,y,Math.max(3,nw),NH-2,2);ctx.fill();}
      else ctx.fillRect(x,y,Math.max(3,nw),NH-2);
      if(nw>10){ctx.fillStyle='rgba(0,0,0,0.35)';ctx.fillRect(x+nw-5,y,5,NH-2);}
    });

    // playhead
    if(isPlaying){const px=KW+currentStep*stepW()-prSx;if(px>=KW&&px<W){ctx.fillStyle='rgba(232,104,32,0.35)';ctx.fillRect(px-1,SH,2,H-SH);}}

    ctx.restore();

    // piano keyboard (overlay)
    ctx.save();ctx.beginPath();ctx.rect(0,SH,KW,H-SH);ctx.clip();
    ctx.fillStyle='#16180f';ctx.fillRect(0,SH,KW,H-SH);
    for(let i=0;i<N;i++){
      const midi=MIDI_MAX-i,semi=((midi%12)+12)%12,isB=BLACK_SEMI.has(semi);
      const y=SH+i*NH-prSy;if(y+NH<SH||y>H)continue;
      if(!isB){
        ctx.fillStyle='#cdd2bd';ctx.fillRect(1,y+1,KW-3,NH-1);
        ctx.fillStyle='rgba(0,0,0,0.1)';ctx.fillRect(1,y+NH-1,KW-3,1);
        if(semi===0){ctx.fillStyle='#7A7260';ctx.font='8px Space Grotesk,system-ui,sans-serif';ctx.textAlign='left';ctx.fillText('C'+(Math.floor(midi/12)-1),3,y+NH-2);}
      }else{ctx.fillStyle='#0c0d0a';ctx.fillRect(1,y,Math.floor(KW*0.62),NH);}
    }
    ctx.fillStyle='#2b2f1c';ctx.fillRect(KW-1,SH,1,H-SH);
    ctx.restore();

    // ruler left cap
    ctx.fillStyle='#1a1c12';ctx.fillRect(0,0,KW,SH);
  }

  // called by the main scheduler on every step
  window.__prScheduleStep=function(step,time){
    const stepDur=(60/tempo)/4;
    prNotes().filter(n=>n.start===step).forEach(n=>triggerPoly([n.midi],time,stepDur*n.dur*0.95));
  };

  // lazy-init: fires when the viewport gets its size (window opened)
  new ResizeObserver(()=>{if(!prInited)prInit();}).observe(document.getElementById('pr-viewport'));
})();

/* ======== TOPBAR MENU ======== */
(function(){
  const btn=document.getElementById('tbMenuBtn');
  const drop=document.getElementById('tbDropdown');
  if(!btn||!drop)return;

  btn.addEventListener('click',e=>{e.stopPropagation();drop.classList.toggle('open');});
  document.addEventListener('click',()=>drop.classList.remove('open'));
  drop.addEventListener('click',e=>e.stopPropagation());

  function close(){drop.classList.remove('open');}

  document.getElementById('menu-new').addEventListener('click',()=>{
    close();
    if(!confirm('Start a new project? Unsaved work will be lost.'))return;
    document.getElementById('resetAll').click();
  });
  document.getElementById('menu-save').addEventListener('click',()=>{close();document.getElementById('saveBtn').click();});
  document.getElementById('menu-load').addEventListener('click',()=>{close();document.getElementById('fileIn').click();});
  document.getElementById('menu-export').addEventListener('click',()=>{
    close();
    const rec=document.getElementById('recBtn');
    if(!rec.classList.contains('on')){rec.click();}
  });
  document.getElementById('menu-settings').addEventListener('click',()=>{close();toggleWindow('win-settings');});
  document.getElementById('menu-patch-notes').addEventListener('click',()=>{close();showPatchNotes();});

  // keyboard shortcuts
  document.addEventListener('keydown',e=>{
    if(e.target.tagName==='INPUT'||e.target.tagName==='SELECT')return;
    if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='s'){e.preventDefault();document.getElementById('saveBtn').click();}
    if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='o'){e.preventDefault();document.getElementById('fileIn').click();}
    if((e.ctrlKey||e.metaKey)&&e.key.toLowerCase()==='n'){e.preventDefault();if(confirm('New project?'))document.getElementById('resetAll').click();}
    if((e.ctrlKey||e.metaKey)&&e.shiftKey&&e.key.toLowerCase()==='t'){e.preventDefault();autoTidyWires();}
    // Zoom: Ctrl+= in, Ctrl+- out, Ctrl+0 reset
    if((e.ctrlKey||e.metaKey)&&(e.key==='='||e.key==='+')){e.preventDefault();setZoom(wsZoom*1.1);}
    if((e.ctrlKey||e.metaKey)&&e.key==='-'){e.preventDefault();setZoom(wsZoom/1.1);}
    if((e.ctrlKey||e.metaKey)&&e.key==='0'){e.preventDefault();setZoom(1);}
    // Ctrl+Shift+W — close all open windows
    if((e.ctrlKey||e.metaKey)&&e.shiftKey&&e.key.toLowerCase()==='w'){
      e.preventDefault();
      document.querySelectorAll('.window.open').forEach(w=>closeWindow(w.id));
    }
    // / — focus app library search
    if(e.key==='/'&&!e.ctrlKey&&!e.metaKey){
      const lib=document.getElementById('dock-library');
      const search=lib?.querySelector('input[type="search"],input[type="text"],.lib-search');
      if(search){e.preventDefault();lib.classList.add('visible');search.focus();}
    }
    // ? — shortcuts panel
    if(e.key==='?'&&!e.ctrlKey&&!e.metaKey){
      e.preventDefault();
      document.getElementById('shortcuts-overlay')?.classList.toggle('visible');
    }
  });
  document.getElementById('tbTidyWires')?.addEventListener('click',()=>autoTidyWires());
  // Global mute
  let _muted=false;
  const _muteBtn=document.getElementById('tbMute');
  function toggleMute(){
    _muted=!_muted;
    if(masterGain){
      masterGain.gain.cancelScheduledValues(ac.currentTime);
      masterGain.gain.setTargetAtTime(_muted?0:master,ac.currentTime,0.02);
    }
    _muteBtn?.classList.toggle('active',_muted);
    const waves=_muteBtn?.querySelectorAll('.mute-waves');
    const xs=_muteBtn?.querySelectorAll('.mute-x');
    waves?.forEach(el=>el.style.display=_muted?'none':'');
    xs?.forEach(el=>el.style.display=_muted?'':'none');
  }
  _muteBtn?.addEventListener('click',toggleMute);
  document.addEventListener('keydown',e=>{
    if(e.target.tagName==='INPUT'||e.target.tagName==='SELECT')return;
    if(e.key.toLowerCase()==='m'&&!e.ctrlKey&&!e.metaKey){toggleMute();}
  });
})();

/* ======== PATCH NOTES ======== */
(function(){
  const overlay = document.getElementById('patch-notes-overlay');
  const body    = document.getElementById('pn-body');
  const closeBtn= document.getElementById('pn-close');
  if (!overlay || !body) return;

  function renderNotes(notes) {
    body.innerHTML = '';
    const todayStr = new Date().toLocaleDateString(undefined, {year:'numeric',month:'long',day:'numeric'});
    (notes.blocks || []).forEach(b => {
      const el = document.createElement('div');
      el.className = 'pn-block';
      el.textContent = (b.text || '').replace(/\{\{DATE\}\}/g, todayStr);
      el.style.cssText = `font-size:${b.size||14}px;font-weight:${b.bold?700:400};color:${b.color||'rgba(255,255,255,.85)'};margin-bottom:${(b.size||14)>=18?'6':'1'}px`;
      body.appendChild(el);
    });
  }

  window.showPatchNotes = () => overlay.classList.add('visible');
  window.hidePatchNotes = () => overlay.classList.remove('visible');
  if (closeBtn) closeBtn.addEventListener('click', window.hidePatchNotes);
  document.getElementById('shortcuts-close')?.addEventListener('click',()=>document.getElementById('shortcuts-overlay')?.classList.remove('visible'));
  document.getElementById('shortcuts-overlay')?.addEventListener('click',e=>{if(e.target===e.currentTarget)e.currentTarget.classList.remove('visible');});

  const seenKey = 'acid-lab-seen-patch-ver';

  function checkAndShow(notes) {
    if (!notes || !notes.version) return;
    renderNotes(notes);
    if (localStorage.getItem(seenKey) !== String(notes.version)) {
      window.showPatchNotes();
      localStorage.setItem(seenKey, notes.version);
    }
  }

  if (window.bagioUpdater) {
    // Load bundled notes immediately
    if (window.bagioUpdater.getPatchNotes) {
      window.bagioUpdater.getPatchNotes().then(checkAndShow).catch(() => {});
    }
    // Also react when main fetches fresh notes from GitHub
    if (window.bagioUpdater.onPatchNotesReady) {
      window.bagioUpdater.onPatchNotesReady(checkAndShow);
    }
  }
})();

/* ---------- version display ---------- */
// Developer broadcast messages
if(window.bagioUpdater?.onMessage){
  window.bagioUpdater.onMessage(msg=>{
    const lastId=localStorage.getItem('acid-last-msg-id');
    if(String(msg.id)===lastId)return;
    localStorage.setItem('acid-last-msg-id',String(msg.id));
    const notif=document.getElementById('msg-notif');
    const textEl=document.getElementById('msg-notif-text');
    if(!notif||!textEl)return;
    textEl.textContent=msg.text;
    notif.style.display='block';
    clearTimeout(notif._t);
    notif._t=setTimeout(()=>{ notif.style.display='none'; },30000);
  });
  document.getElementById('msg-notif-close')?.addEventListener('click',()=>{
    const n=document.getElementById('msg-notif');
    if(n)n.style.display='none';
  });
}

if(window.bagioUpdater&&window.bagioUpdater.getVersion){
  window.bagioUpdater.getVersion().then(v=>{
    const el=document.querySelector(".tb-version");
    if(el)el.textContent="v"+v;
  }).catch(()=>{});
}

/* ---------- in-app updater (only present in the desktop app) ---------- */
(function(){
  const btn=document.getElementById("updateBtn");
  if(!btn||!window.bagioUpdater)return; // browser build: no updater
  function show(txt,clickable){btn.style.display="inline-block";btn.textContent=txt;btn.style.cursor=clickable?"pointer":"default";}
  const statusEl=document.getElementById('updateStatusLine');
  window.bagioUpdater.onStatus(s=>{
    if(s.state==="checking"){if(statusEl)statusEl.textContent='Checking for updates…';}
    else if(s.state==="available"){show("↓ update "+(s.version||""),false);if(statusEl)statusEl.textContent='Update available: v'+(s.version||'');}
    else if(s.state==="downloading"){show("↓ updating "+(s.percent||0)+"%",false);if(statusEl)statusEl.textContent='Downloading: '+(s.percent||0)+'%';}
    else if(s.state==="restarting"){show("restarting…",false);if(statusEl)statusEl.textContent='Restarting to apply update…';}
    else if(s.state==="none"){btn.style.display="none";if(statusEl)statusEl.textContent='Up to date.';}
    else if(s.state==="error"){btn.style.display="none";if(statusEl)statusEl.textContent='Update error: '+(s.message||'unknown error');}
  });
  document.getElementById('manualCheckUpdate')?.addEventListener('click',()=>{
    if(window.bagioUpdater?.check){window.bagioUpdater.check();if(statusEl)statusEl.textContent='Checking…';}
  });
})();

/* ---------- learn mode / tooltip system ---------- */
const APP_TIPS={
  'win-acid':'TB-303-style acid bass synthesizer with resonant filter, envelope, and distortion drive.',
  'win-poly':'Polyphonic synthesizer — play chords and pads with multiple simultaneous voices.',
  'win-drum':'16-step drum machine with 10 kit pieces. Click cells to toggle hits on/off.',
  'win-sampler':'Sample player — drag audio files in, trim start/end, and loop.',
  'win-mixer':'Mix the levels of all instruments. Each channel has volume and mute.',
  'win-effects':'Master effects chain — delay and reverb sends applied to the full output.',
  'win-spectrum':'Frequency analyser — see what frequencies are present in the signal.',
  'win-reverb':'Convolution reverb with four algorithm types: Room, Hall, Plate, and Spring.',
  'win-compressor':'Dynamics compressor — squashes peaks and brings up quiet parts. Controls threshold, ratio, attack, release, and makeup gain.',
  'win-arp':'Arpeggiator — automatically plays notes in an up, down, or random pattern.',
  'win-lfo':'Low-frequency oscillator — a slow wave signal for modulating other parameters.',
  'win-transport':'Transport controls — play/stop, tempo, swing, and song mode.',
  'win-patterns':'Pattern manager — create, duplicate, and chain patterns into a full song.',
  'win-pianoroll':'Piano roll editor — draw in polyphonic note patterns with precise timing.',
  'win-settings':'App settings — accent colour, themes, audio devices, and more.',
  'win-eq':'5-band equaliser — boost or cut at five key frequency points.',
  'win-delay':'Digital delay — echo with controllable time, feedback, and dry/wet mix. Includes ping-pong mode.',
  'win-scope':'Oscilloscope — displays the waveform of the signal over time.',
  'win-lofi':'Lo-Fi processor — bit crushing and sample rate reduction for gritty digital texture.',
  'win-gate':'Noise gate — silences the signal when it drops below a set threshold level.',
  'win-chordgen':'Chord generator — instantly triggers a full chord into the polyphonic synth.',
  'win-tone':'Tone generator — a pure sine, square, sawtooth, or triangle wave at any frequency.',
  'win-merge':'4-to-1 signal merger — combines up to four inputs into a single output.',
  'win-vol':'Volume control — adjusts the gain of the signal passing through.',
  'win-pan':'Stereo panner — positions the signal in the left-right stereo field.',
  'win-chorus':'Chorus — thickens the sound by adding slightly pitch-shifted, delayed copies.',
  'win-tremolo':'Tremolo — rhythmically modulates the volume using an LFO.',
  'win-phaser':'Phaser — sweeps a series of notch filters through the spectrum for a swirling effect.',
  'win-granular':'Granular synthesizer — chops audio into tiny grains and scatters them. Controls: SIZE (grain length), SCATTER (position offset), PITCH (rate), DENSITY (grains/sec). Includes FREEZE and REVERSE.',
  'win-flanger':'Flanger — short modulated delay creates a jet-plane comb-filter sweep. RATE = LFO speed, DEPTH = sweep width, FDBK = feedback.',
  'win-ringmod':'Ring modulator — multiplies two signals together for metallic, robotic tones. Use the XY pad to control carrier frequency and dry amount.',
  'win-autofilter':'Auto-filter — envelope follower drives a resonant filter. Louder input = higher cutoff. Shows a live frequency response curve.',
  'win-noise':'Noise generator — white, pink, or brown noise source with HP and LP filter controls. Press ON to activate.',
};

// Tooltip element
const _tipEl=document.createElement('div');_tipEl.id='acid-tip';document.body.appendChild(_tipEl);
let _tipHideTimer=null;
function showTip(text,x,y){
  if(!localStorage.getItem('acid-learn-mode'))return;
  clearTimeout(_tipHideTimer);
  _tipEl.textContent=text;
  const vw=window.innerWidth,vh=window.innerHeight;
  const m=12;
  _tipEl.style.opacity='0';_tipEl.classList.add('visible');
  requestAnimationFrame(()=>{
    const tw=_tipEl.offsetWidth||220,th=_tipEl.offsetHeight||60;
    let tx=x+m,ty=y-th-m;
    if(tx+tw>vw-m)tx=x-tw-m;if(tx<m)tx=m;
    if(ty<m)ty=y+m;if(ty+th>vh-m)ty=vh-th-m;
    _tipEl.style.left=tx+'px';_tipEl.style.top=ty+'px';_tipEl.style.opacity='';
  });
}
function hideTip(){clearTimeout(_tipHideTimer);_tipHideTimer=setTimeout(()=>_tipEl.classList.remove('visible'),80);}

// Wire tooltips to titlebar .tt spans
document.querySelectorAll('.window').forEach(win=>{
  const baseId=win.id.replace(/-i\d+$/,'');
  const tip=APP_TIPS[baseId];if(!tip)return;
  const tt=win.querySelector('.tt');if(!tt)return;
  tt.addEventListener('mouseenter',e=>showTip(tip,e.clientX,e.clientY));
  tt.addEventListener('mousemove',e=>showTip(tip,e.clientX,e.clientY));
  tt.addEventListener('mouseleave',hideTip);
});

// H key — hint mode: hold H to see all control descriptions on hover
let _hintMode=false;
document.addEventListener('keydown',e=>{if(e.key.toLowerCase()==='h'&&!e.ctrlKey&&!e.metaKey&&e.target.tagName!=='INPUT'){_hintMode=true;document.body.classList.add('hint-mode');}});
document.addEventListener('keyup',e=>{if(e.key.toLowerCase()==='h'){_hintMode=false;document.body.classList.remove('hint-mode');}});

// Wire tooltips to data-tip elements (controls)
document.addEventListener('mouseover',e=>{
  const el=e.target.closest('[data-tip]');
  if(el&&el.dataset.tip)showTip(el.dataset.tip,e.clientX,e.clientY);
});
document.addEventListener('mouseout',e=>{
  if(e.target.closest('[data-tip]'))hideTip();
});
document.addEventListener('mousemove',e=>{
  if(_tipEl.classList.contains('visible')){
    const el=e.target.closest('[data-tip]');
    if(el){showTip(el.dataset.tip,e.clientX,e.clientY);}
  }
});

/* ========== CUSTOMISATION SYSTEM ========== */
(function(){
  const root=document.documentElement;
  let curAccent='#E86820', curTheme='acid', curGlass=30;

  function hexToRgb(h){return{r:parseInt(h.slice(1,3),16),g:parseInt(h.slice(3,5),16),b:parseInt(h.slice(5,7),16)};}
  function darken(h,f){const{r,g,b}=hexToRgb(h);return'#'+[r,g,b].map(v=>Math.round(v*f).toString(16).padStart(2,'0')).join('');}

  function hexToHsl(h){
    let{r,g,b}=hexToRgb(h);r/=255;g/=255;b/=255;
    const max=Math.max(r,g,b),min=Math.min(r,g,b);
    let hh,s,l=(max+min)/2;
    if(max===min){hh=s=0;}
    else{const d=max-min;s=l>0.5?d/(2-max-min):d/(max+min);
      switch(max){case r:hh=(g-b)/d+(g<b?6:0);break;case g:hh=(b-r)/d+2;break;default:hh=(r-g)/d+4;}hh/=6;}
    return[hh*360,s*100,l*100];
  }
  function hslToHex(h,s,l){
    s/=100;l/=100;
    const c=(1-Math.abs(2*l-1))*s,x=c*(1-Math.abs((h/60)%2-1)),m=l-c/2;
    let r=0,g=0,b=0;
    if(h<60){r=c;g=x;}else if(h<120){r=x;g=c;}else if(h<180){g=c;b=x;}
    else if(h<240){g=x;b=c;}else if(h<300){r=x;b=c;}else{r=c;b=x;}
    return'#'+[r+m,g+m,b+m].map(v=>Math.round(Math.min(v,1)*255).toString(16).padStart(2,'0')).join('');
  }

  function applyAccent(hex){
    curAccent=hex;
    root.style.setProperty('--acid',hex);
    root.style.setProperty('--acid-dim',darken(hex,0.48));
    const{r,g,b}=hexToRgb(hex);
    // Background glow
    root.style.setProperty('--bg-glow1',`rgba(${r},${g},${b},.16)`);
    root.style.setProperty('--bg-glow2',`rgba(${r},${g},${b},.08)`);
    root.style.setProperty('--bg-glow3',`rgba(${r},${g},${b},.05)`);
    // Alpha tints for hover/focus states + canvas draws
    root.style.setProperty('--acid-rgb',`${r},${g},${b}`);
    root.style.setProperty('--acid-a10',`rgba(${r},${g},${b},.10)`);
    root.style.setProperty('--acid-a15',`rgba(${r},${g},${b},.15)`);
    root.style.setProperty('--acid-a20',`rgba(${r},${g},${b},.20)`);
    root.style.setProperty('--acid-a30',`rgba(${r},${g},${b},.30)`);
    root.style.setProperty('--acid-a38',`rgba(${r},${g},${b},.38)`);
    root.style.setProperty('--acid-a55',`rgba(${r},${g},${b},.55)`);
    root.style.setProperty('--acid-a88',`rgba(${r},${g},${b},.88)`);
    root.style.setProperty('--acid-glow',`rgba(${r},${g},${b},.55)`);
    // Generate palette variants via HSL
    const[hh,ss,ll]=hexToHsl(hex);
    // Split-complementary: +150° and +210° give genuinely distinct hues for any base accent
    const warm=hslToHex((hh+30)%360,Math.min(ss*1.05,100),Math.min(ll*1.04,88));
    const cool=hslToHex((hh+150)%360,Math.min(ss*0.95,100),Math.min(ll*1.08,88));
    const muted=hslToHex((hh+210)%360,ss*0.80,Math.min(ll*1.18,85));
    root.style.setProperty('--accent-warm',warm);
    root.style.setProperty('--accent-cool',cool);
    root.style.setProperty('--accent-muted',muted);
    document.querySelectorAll('.accent-swatch').forEach(s=>s.classList.toggle('active',s.dataset.accent===hex));
    const ci=document.getElementById('accentCustom');if(ci)ci.value=hex;
    save();
  }

  const THEMES={
    acid: {bg:'#0D0C09',panel:'#151410',panel2:'#1C1B14',line:'#2A2820',ink:'#EDE8D0',mute:'#7A7260',cell:'#1E1D15',ga:'#1a1008',gb:'#0d0906',gc:'#0a0806'},
    carbon:{bg:'#07070a',panel:'#0d0d12',panel2:'#131318',line:'#1e1e26',ink:'#eaeaf5',mute:'#58586a',cell:'#0f0f14',ga:'#08080d',gb:'#050508',gc:'#030306'},
    slate: {bg:'#070c11',panel:'#0c1218',panel2:'#12181f',line:'#1c262e',ink:'#d8eaf5',mute:'#507080',cell:'#0e141a',ga:'#090f16',gb:'#060c12',gc:'#04090e'},
    noir:  {bg:'#0c0a08',panel:'#141210',panel2:'#1c1a16',line:'#2a2520',ink:'#f5ead8',mute:'#7a6a58',cell:'#161410',ga:'#1a1208',gb:'#0e0b06',gc:'#0a0804'},
  };

  function applyTheme(name){
    curTheme=name;
    const t=THEMES[name]||THEMES.acid;
    ['bg','panel','panel2','line','ink','mute','cell'].forEach(k=>root.style.setProperty('--'+k,t[k]));
    root.style.setProperty('--bg-grad-a',t.ga);
    root.style.setProperty('--bg-grad-b',t.gb);
    root.style.setProperty('--bg-grad-c',t.gc);
    document.querySelectorAll('.theme-card').forEach(c=>c.classList.toggle('active',c.dataset.theme===name));
    save();
  }


  function applyPortColors(outColor, inColor){
    const r=document.documentElement;
    if(outColor)r.style.setProperty('--port-out',outColor);
    if(inColor)r.style.setProperty('--port-in',inColor);
  }

  function save(){
    const portOut=document.getElementById('portOutColor')?.value||'';
    const portIn=document.getElementById('portInColor')?.value||'';
    const wireCol=document.getElementById('wireColor')?.value||'';
    localStorage.setItem('acid-customisation',JSON.stringify({accent:curAccent,theme:curTheme,portOut,portIn,wireCol}));
  }

  function load(){
    try{
      const s=JSON.parse(localStorage.getItem('acid-customisation')||'{}');
      if(s.theme)applyTheme(s.theme);
      if(s.accent)applyAccent(s.accent);
      if(s.portOut){applyPortColors(s.portOut,null);const el=document.getElementById('portOutColor');if(el)el.value=s.portOut;}
      if(s.portIn){applyPortColors(null,s.portIn);const el=document.getElementById('portInColor');if(el)el.value=s.portIn;}
      if(s.wireCol){document.documentElement.style.setProperty('--wire-color',s.wireCol);const el=document.getElementById('wireColor');if(el)el.value=s.wireCol;}
    }catch(_){}
  }

  // Wire controls
  document.querySelectorAll('.accent-swatch').forEach(s=>s.addEventListener('click',()=>applyAccent(s.dataset.accent)));
  const ac=document.getElementById('accentCustom');if(ac)ac.addEventListener('input',e=>applyAccent(e.target.value));
  document.querySelectorAll('.theme-card[data-theme]').forEach(c=>c.addEventListener('click',()=>applyTheme(c.dataset.theme)));
  const poc=document.getElementById('portOutColor');if(poc)poc.addEventListener('input',e=>{applyPortColors(e.target.value,null);save();});
  const pic=document.getElementById('portInColor');if(pic)pic.addEventListener('input',e=>{applyPortColors(null,e.target.value);save();});
  const wc=document.getElementById('wireColor');if(wc)wc.addEventListener('input',e=>{document.documentElement.style.setProperty('--wire-color',e.target.value);save();});

  // Collapsible secthead sections in settings
  document.querySelectorAll('#win-settings .secthead').forEach(head=>{
    head.style.cursor='pointer';
    head.style.userSelect='none';
    head.style.display='flex';head.style.alignItems='center';head.style.justifyContent='space-between';
    const ind=document.createElement('span');
    ind.style.cssText='font-size:14px;opacity:.7;transition:transform .2s;line-height:1;color:var(--acid);flex-shrink:0;margin-left:8px';
    ind.textContent='⌄';
    head.appendChild(ind);
    // Collect sibling content until next secthead
    function getSiblings(){
      const els=[];
      let el=head.nextElementSibling;
      while(el&&!el.classList.contains('secthead')){els.push(el);el=el.nextElementSibling;}
      return els;
    }
    head.addEventListener('click',()=>{
      const siblings=getSiblings();
      const collapsed=head.dataset.collapsed==='1';
      siblings.forEach(el=>{el.style.display=collapsed?'':'none';});
      head.dataset.collapsed=collapsed?'':'1';
      ind.style.transform=collapsed?'':'rotate(-90deg)';
    });
  });

  // Window mode
  document.querySelectorAll('.theme-card[data-mode]').forEach(btn=>{
    btn.addEventListener('click',()=>{
      const mode=btn.dataset.mode;
      if(window.bagioUpdater&&window.bagioUpdater.setWindowMode)window.bagioUpdater.setWindowMode(mode);
      document.querySelectorAll('.theme-card[data-mode]').forEach(b=>b.classList.toggle('active',b===btn));
      localStorage.setItem('acid-window-mode',mode);
    });
  });
  // Restore window mode button state
  const savedMode=localStorage.getItem('acid-window-mode')||'windowed';
  document.querySelectorAll('.theme-card[data-mode]').forEach(b=>b.classList.toggle('active',b.dataset.mode===savedMode));

  // ---- Wallpaper ----
  function applyWallpaper(url){
    const el=document.getElementById('bg-wallpaper');
    if(!el)return;
    if(url){
      el.style.backgroundImage=`url("${url.replace(/"/g,'%22')}")`;
      document.body.style.backgroundImage='none';
      document.body.style.animation='none';
      document.body.classList.add('has-wallpaper');
    }else{
      el.style.backgroundImage='none';
      document.body.style.backgroundImage='';
      document.body.style.animation='';
      document.body.classList.remove('has-wallpaper');
    }
  }

  const wpUpload=document.getElementById('wallpaperUpload');
  if(wpUpload){
    wpUpload.addEventListener('click',()=>{
      const inp=document.createElement('input');
      inp.type='file';inp.accept='image/*';
      inp.addEventListener('change',()=>{
        const file=inp.files[0];if(!file)return;
        const path=file.path||(file.name?URL.createObjectURL(file):null);
        if(!path)return;
        const url=file.path?('file:///'+file.path.replace(/\\/g,'/').replace(/^\/+/,'')):path;
        applyWallpaper(url);
        localStorage.setItem('acid-wallpaper',url);
      });
      inp.click();
    });
  }

  const wpClear=document.getElementById('wallpaperClear');
  if(wpClear){
    wpClear.addEventListener('click',()=>{
      applyWallpaper(null);
      localStorage.removeItem('acid-wallpaper');
    });
  }

  // Load saved wallpaper
  const savedWp=localStorage.getItem('acid-wallpaper');
  if(savedWp)applyWallpaper(savedWp);

  // ---- Label style (Simple / Pro) ----
  function applyTermMode(mode) {
    document.querySelectorAll('[data-s]').forEach(el => {
      el.textContent = mode === 'pro' ? el.dataset.p : el.dataset.s;
    });
    localStorage.setItem('acid-term-mode', mode);
    document.getElementById('termSimple')?.classList.toggle('active', mode !== 'pro');
    document.getElementById('termPro')?.classList.toggle('active', mode === 'pro');
  }
  document.getElementById('termSimple')?.addEventListener('click', () => applyTermMode('simple'));
  document.getElementById('termPro')?.addEventListener('click', () => applyTermMode('pro'));
  applyTermMode(localStorage.getItem('acid-term-mode') || 'simple');

  // ---- Audio devices ----
  async function loadAudioDevices() {
    const inSel = document.getElementById('audioInputSel');
    const outSel = document.getElementById('audioOutputSel');
    if (!inSel || !outSel) return;
    try {
      // Request mic permission to get labelled device list
      try { const s = await navigator.mediaDevices.getUserMedia({audio:true}); s.getTracks().forEach(t=>t.stop()); } catch {}
      const devices = await navigator.mediaDevices.enumerateDevices();
      const savedIn = localStorage.getItem('acid-audio-in') || '';
      const savedOut = localStorage.getItem('acid-audio-out') || '';
      inSel.innerHTML = '<option value="">System default</option>' +
        devices.filter(d => d.kind==='audioinput').map(d =>
          `<option value="${d.deviceId}"${d.deviceId===savedIn?' selected':''}>${d.label||'Microphone '+d.deviceId.slice(0,6)}</option>`
        ).join('');
      outSel.innerHTML = '<option value="">System default</option>' +
        devices.filter(d => d.kind==='audiooutput').map(d =>
          `<option value="${d.deviceId}"${d.deviceId===savedOut?' selected':''}>${d.label||'Speaker '+d.deviceId.slice(0,6)}</option>`
        ).join('');
    } catch(e) {
      inSel.innerHTML = '<option value="">Could not enumerate devices</option>';
      outSel.innerHTML = '<option value="">Could not enumerate devices</option>';
    }
  }
  document.getElementById('audioInputSel')?.addEventListener('change', function() {
    localStorage.setItem('acid-audio-in', this.value);
  });
  document.getElementById('audioOutputSel')?.addEventListener('change', function() {
    const deviceId = this.value || '';
    localStorage.setItem('acid-audio-out', deviceId);
    const el = window._acidOutEl;
    if (el && typeof el.setSinkId === 'function') {
      el.setSinkId(deviceId).catch(err => console.warn('setSinkId:', err));
    }
  });
  document.getElementById('audioDevRefresh')?.addEventListener('click', loadAudioDevices);
  // Load on settings open
  document.getElementById('win-settings')?.addEventListener('transitionend', loadAudioDevices, {once:false});
  const settingsWin = document.getElementById('win-settings');
  if (settingsWin) {
    const settingsObs = new MutationObserver(() => {
      if (settingsWin.classList.contains('open')) loadAudioDevices();
    });
    settingsObs.observe(settingsWin, {attributes:true, attributeFilter:['class']});
  }

  // ---- Learn Mode ----
  const learnBtn=document.getElementById('learnModeToggle');
  function applyLearnMode(on){
    localStorage[on?'setItem':'removeItem']('acid-learn-mode',on?'1':undefined);
    if(learnBtn){learnBtn.textContent=on?'ON':'OFF';learnBtn.classList.toggle('on',on);}
  }
  learnBtn?.addEventListener('click',()=>applyLearnMode(!localStorage.getItem('acid-learn-mode')));
  applyLearnMode(!!localStorage.getItem('acid-learn-mode'));

  load();
})();

/* =====================================================
   WORKSPACE ZOOM + PAN
   ===================================================== */
const workspace = document.getElementById('workspace');
let wsZoom = 1, wsPanX = 0, wsPanY = 0;
// Store workspace-space coords so per-window zoom can reposition correctly
document.querySelectorAll('.window').forEach(win => {
  win.dataset.wx = parseFloat(win.style.left) || 0;
  win.dataset.wy = parseFloat(win.style.top) || 0;
});
const zoomIndicator = document.createElement('div');
zoomIndicator.id = 'zoom-indicator';
document.body.appendChild(zoomIndicator);
let zoomFadeTimer = null;
function showZoomIndicator() {
  zoomIndicator.textContent = Math.round(wsZoom * 100) + '%';
  zoomIndicator.classList.add('visible');
  clearTimeout(zoomFadeTimer);
  zoomFadeTimer = setTimeout(() => zoomIndicator.classList.remove('visible'), 1200);
}
function setZoom(newZoom){
  const cx=window.innerWidth/2, cy=window.innerHeight/2;
  const wsX=(cx-wsPanX)/wsZoom, wsY=(cy-wsPanY)/wsZoom;
  wsZoom=Math.max(0.2,Math.min(2.5,newZoom));
  wsPanX=cx-wsX*wsZoom; wsPanY=cy-wsY*wsZoom;
  applyWorkspaceTransform();showZoomIndicator();if(typeof redrawWires==='function')redrawWires();
}
function applyWorkspaceTransform() {
  document.querySelectorAll('.window.open').forEach(win => {
    if (win.classList.contains('maxd')) return;
    const wx = parseFloat(win.dataset.wx) || 0;
    const wy = parseFloat(win.dataset.wy) || 0;
    win.style.left = (wx * wsZoom + wsPanX) + 'px';
    win.style.top  = (wy * wsZoom + wsPanY) + 'px';
    win.style.transform = `scale(${wsZoom})`;
    win.style.transformOrigin = '0 0';
  });
  // Notify canvas draw loops to re-rasterize at the new effective scale
  document.dispatchEvent(new CustomEvent('workspace-zoom'));
}
document.addEventListener('wheel', e => {
  if (e.target.closest('#dock') || e.target.closest('#topbar') || e.target.closest('#dock-library')) return;
  e.preventDefault();
  const factor = e.deltaY < 0 ? 1.08 : 1 / 1.08;
  const newZoom = Math.max(0.2, Math.min(2.5, wsZoom * factor));
  const mx = e.clientX, my = e.clientY;
  const wsMouseX = (mx - wsPanX) / wsZoom;
  const wsMouseY = (my - wsPanY) / wsZoom;
  wsZoom = newZoom;
  wsPanX = mx - wsMouseX * wsZoom;
  wsPanY = my - wsMouseY * wsZoom;
  applyWorkspaceTransform();
  showZoomIndicator();
  redrawWires();
}, {passive: false});

// Middle-mouse or Alt+drag to pan; left-click on empty background = rubber-band select
let mPan = null, mBand = null;
document.addEventListener('mousedown', e => {
  const onWindow = e.target.closest('.window');
  const onUI = e.target.closest('#dock') || e.target.closest('#topbar') || e.target.closest('#dock-library');
  if (e.button === 1 || (e.button === 0 && e.altKey && !onUI)) {
    mPan = {sx: e.clientX, sy: e.clientY, px: wsPanX, py: wsPanY};
    e.preventDefault();
  } else if (e.button === 0 && !onWindow && !onUI && !e.altKey) {
    if (libOpen) closeLib();
    if (!e.shiftKey) {
      selectedWindows.forEach(id => document.getElementById(id)?.classList.remove('win-selected'));
      selectedWindows.clear();
    }
    const el = document.createElement('div');
    el.className = 'rubber-band';
    el.style.cssText = `left:${e.clientX}px;top:${e.clientY}px;width:0;height:0`;
    document.body.appendChild(el);
    mBand = {sx: e.clientX, sy: e.clientY, el};
    e.preventDefault();
  }
});
document.addEventListener('mousemove', e => {
  if (mPan) {
    wsPanX = mPan.px + (e.clientX - mPan.sx);
    wsPanY = mPan.py + (e.clientY - mPan.sy);
    applyWorkspaceTransform();
    redrawWires();
  }
  if (mBand) {
    const x = Math.min(e.clientX, mBand.sx), y = Math.min(e.clientY, mBand.sy);
    const w = Math.abs(e.clientX - mBand.sx), h = Math.abs(e.clientY - mBand.sy);
    mBand.el.style.left = x + 'px'; mBand.el.style.top = y + 'px';
    mBand.el.style.width = w + 'px'; mBand.el.style.height = h + 'px';
  }
});
document.addEventListener('mouseup', () => {
  mPan = null;
  if (mBand) {
    const br = mBand.el.getBoundingClientRect();
    if (br.width > 6 || br.height > 6) {
      document.querySelectorAll('.window.open').forEach(w => {
        const wr = w.getBoundingClientRect();
        if (wr.left < br.right && wr.right > br.left && wr.top < br.bottom && wr.bottom > br.top) {
          selectedWindows.add(w.id); w.classList.add('win-selected');
        }
      });
      // Also capture port jacks inside the rubber-band
      document.querySelectorAll('.port-jack').forEach(jack => {
        const jr = jack.getBoundingClientRect();
        const cx = jr.left + jr.width/2, cy = jr.top + jr.height/2;
        if (cx >= br.left && cx <= br.right && cy >= br.top && cy <= br.bottom) {
          if (jack.dataset.dir === 'out') {
            const already = pendingOutPorts.find(q => q.win===jack.dataset.win && q.port===jack.dataset.port);
            if (!already) { pendingOutPorts.push({win:jack.dataset.win, port:jack.dataset.port, jackEl:jack}); jack.classList.add('pending-out'); }
          } else if (jack.dataset.dir === 'in') {
            const already = pendingInPorts.find(q => q.win===jack.dataset.win && q.port===jack.dataset.port);
            if (!already) { pendingInPorts.push({win:jack.dataset.win, port:jack.dataset.port, jackEl:jack}); jack.classList.add('pending-in'); }
          }
        }
      });
    }
    mBand.el.remove(); mBand = null;
    // Rubber-band captured output ports → immediately start wire drawing so lines follow the mouse
    if (pendingOutPorts.length > 0 && !wireDrawing) {
      const first = pendingOutPorts.shift();
      first.jackEl.classList.remove('pending-out');
      startWireDrawing(first.win, first.port, first.jackEl);
    }
  } else {
    // Tiny movement = click on empty workspace → cancel all pending ports and any active wire
    mBand.el.remove(); mBand = null;
    if (wireDrawing) {
      wireDrawing.previewPaths?.forEach(pp=>pp.path.remove());
      wireDrawing.pendingCursorPaths?.forEach(p=>p.remove());
      wireDrawing.tempPath.remove();
      document.querySelectorAll('.port-jack.target-highlight').forEach(el=>el.classList.remove('target-highlight'));
      wireDrawing = null;
    }
    pendingOutPorts.forEach(pq=>pq.jackEl.classList.remove('pending-out')); pendingOutPorts.length=0;
    pendingInPorts.forEach(pi=>pi.jackEl.classList.remove('pending-in')); pendingInPorts.length=0;
  }
});

// ===== WORKSPACE RIGHT-CLICK CONTEXT MENU =====
let _wsLocked=false;
(function(){
  const menu=document.createElement('div');menu.id='ws-ctx-menu';
  menu.innerHTML=`<div class="ws-ctx-item" data-action="tile">Tile windows</div><div class="ws-ctx-item" data-action="cascade">Cascade windows</div><div class="ws-ctx-sep"></div><div class="ws-ctx-item" data-action="lock" id="ws-ctx-lock">Lock workspace</div><div class="ws-ctx-sep"></div><div class="ws-ctx-item" data-action="closeall">Close all windows</div>`;
  document.body.appendChild(menu);
  function hide(){menu.style.display='none';}
  document.addEventListener('contextmenu',e=>{
    if(e.target.closest('.window')||e.target.closest('#dock')||e.target.closest('#topbar')||e.target.closest('#dock-library')||e.target.closest('#ws-ctx-menu'))return;
    e.preventDefault();
    menu.style.display='block';
    const mx=Math.min(e.clientX,window.innerWidth-menu.offsetWidth-8);
    const my=Math.min(e.clientY,window.innerHeight-menu.offsetHeight-8);
    menu.style.left=mx+'px';menu.style.top=my+'px';
  });
  document.addEventListener('pointerdown',e=>{if(!e.target.closest('#ws-ctx-menu'))hide();});
  document.addEventListener('keydown',e=>{if(e.key==='Escape')hide();});
  menu.addEventListener('click',e=>{
    const item=e.target.closest('.ws-ctx-item');if(!item)return;
    const action=item.dataset.action;hide();
    const wins=[...document.querySelectorAll('.window.open:not(.maxd)')];
    if(action==='tile'){
      const cols=Math.ceil(Math.sqrt(wins.length))||1;
      const tw=Math.max(280,(window.innerWidth-80)/(cols*wsZoom));
      const th=Math.max(200,(window.innerHeight-120)/(Math.ceil(wins.length/cols)*wsZoom));
      wins.forEach((w,i)=>{
        const col=i%cols,row=Math.floor(i/cols);
        const sx=40+col*(tw*wsZoom+8),sy=80+row*(th*wsZoom+8);
        w.dataset.wx=(sx-wsPanX)/wsZoom;w.dataset.wy=(sy-wsPanY)/wsZoom;
        w.style.left=sx+'px';w.style.top=sy+'px';
        saveWinPos(w);
      });
    } else if(action==='cascade'){
      wins.forEach((w,i)=>{
        const sx=60+i*30,sy=80+i*30;
        w.dataset.wx=(sx-wsPanX)/wsZoom;w.dataset.wy=(sy-wsPanY)/wsZoom;
        w.style.left=sx+'px';w.style.top=sy+'px';
        saveWinPos(w);
      });
    } else if(action==='lock'){
      _wsLocked=!_wsLocked;
      document.getElementById('ws-ctx-lock').textContent=_wsLocked?'Unlock workspace':'Lock workspace';
      document.body.classList.toggle('ws-locked',_wsLocked);
    } else if(action==='closeall'){
      wins.forEach(w=>{try{closeWindow(w.id);}catch(_){}});
    }
    if(typeof redrawWires==='function')redrawWires();
  });
})();

/* =====================================================
   PORT + WIRE SYSTEM
   ===================================================== */
const DRUM_PORT_CH = {
  'kick-out':'kick', 'snare-out':'snare', 'clap-out':'clap',
  'hat-out':'hat',   'ohat-out':'ohat',   'tom-out':'tom',
  'rim-out':'rim',   'cbell-out':'cowbell','ride-out':'ride', 'shk-out':'shaker',
  'kick-in':'kick',  'snare-in':'snare',  'clap-in':'clap',
  'hat-in':'hat',    'ohat-in':'ohat',    'tom-in':'tom',
  'rim-in':'rim',    'cbell-in':'cowbell','ride-in':'ride',  'shk-in':'shaker',
};
const PORT_DEFS = {
  'win-transport': {out:[{id:'out'}]},
  'win-patterns':  {out:[{id:'out'}]},
  'win-pianoroll': {out:[{id:'out'}]},
  'win-keyboard':  {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-acid':      {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-poly':      {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-drum': {
    in:  [{id:'kick-in',label:'KICK'},{id:'snare-in',label:'SNARE'},{id:'clap-in',label:'CLAP'},
          {id:'hat-in',label:'HAT'},{id:'ohat-in',label:'O.HAT'},{id:'tom-in',label:'TOM'},
          {id:'rim-in',label:'RIM'},{id:'cbell-in',label:'BELL'},{id:'ride-in',label:'RIDE'},{id:'shk-in',label:'SHK'}],
    out: [{id:'kick-out',label:'KICK'},{id:'snare-out',label:'SNARE'},{id:'clap-out',label:'CLAP'},
          {id:'hat-out',label:'HAT'},{id:'ohat-out',label:'O.HAT'},{id:'tom-out',label:'TOM'},
          {id:'rim-out',label:'RIM'},{id:'cbell-out',label:'BELL'},{id:'ride-out',label:'RIDE'},{id:'shk-out',label:'SHK'}],
  },
  'win-sampler':   {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-mixer':     {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-effects':   {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-spectrum':  {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-reverb':    {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-compressor':{in:[{id:'in'}],  out:[{id:'out'}]},
  'win-arp':       {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-lfo':       {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-eq':        {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-delay':     {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-scope':     {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-lofi':      {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-gate':      {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-chordgen':  {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-tone':      {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-merge':     {in:[{id:'m1',label:'1'},{id:'m2',label:'2'},{id:'m3',label:'3'},{id:'m4',label:'4'}], out:[{id:'out'}]},
  'win-vol':       {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-pan':       {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-chorus':    {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-tremolo':   {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-phaser':    {in:[{id:'in'}],  out:[{id:'out'}]},
  // New apps — June 2026 batch
  'win-granular':  {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-flanger':   {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-ringmod':   {in:[{id:'carrier',label:'SRC'},{id:'mod',label:'MOD'}], out:[{id:'out'}]},
  'win-autofilter':{in:[{id:'in'}],  out:[{id:'out'}]},
  'win-noise':     {out:[{id:'out'}]},
  // New mini apps — June 2026 batch
  'win-padboard':  {out:[{id:'out'}]},
  'win-bitcrush':  {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-cabinet':   {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-stereoimg': {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-comb':      {in:[{id:'in'}],  out:[{id:'out'}]},
  // New major apps
  'win-distortion':{in:[{id:'in'}],  out:[{id:'out'}]},
  'win-multicomp': {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-wavetable': {out:[{id:'out'}]},
  'win-stepseq':   {out:[{id:'out'}]},
  'win-tape':      {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-formant':   {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-sidechain': {in:[{id:'in',label:'MAIN'},{id:'sc',label:'SC'}], out:[{id:'out'}]},
  'win-glitch':    {in:[{id:'in'}],  out:[{id:'out'}]},
  'win-osc-bank':  {out:[{id:'out'}]},
  'win-freqshift': {in:[{id:'in'}],  out:[{id:'out'}]},
};
const wireSVGLayer = document.getElementById('wire-layer');
const connections = [];
let wireDrawing = null;
let pendingOutPorts = [];
let pendingInPorts = [];
const CV_PARAM_MAP = {
  'win-acid':       {'in':{sliderId:'aCut'}},
  'win-poly':       {'in':{sliderId:'pCut'}},
  'win-drum':       {'in':{sliderId:'kSwing'}},
  'win-sampler':    {'in':{sliderId:'masterVol'}},
  'win-reverb':     {'in':{sliderId:'rv-mix'}},
  'win-compressor': {'in':{sliderId:'cp-thr'}},
  'win-mixer':      {'in':{sliderId:'mix-vol'}},
  'win-effects':    {'in':{sliderId:'kRev'}},
  'win-arp':        {'in':{sliderId:'kSwing'}},
};

function portCenter(jackEl) {
  const dot = jackEl.querySelector('.port-dot') || jackEl;
  const r = dot.getBoundingClientRect();
  if (!r.width && !r.height) return null; // element hidden or detached
  return {x: r.left + r.width / 2, y: r.top + r.height / 2};
}
function bezierD(x1, y1, x2, y2) {
  const cx = Math.max(Math.abs(x2-x1)*0.55, 80);
  return `M${x1},${y1} C${x1+cx},${y1} ${x2-cx},${y2} ${x2},${y2}`;
}
function getPortDotSize(jackEl){
  const dot=jackEl.querySelector('.port-dot');if(!dot)return 14;
  const r=dot.getBoundingClientRect();return(r.width+r.height)/2;
}
function redrawWires() {
  connections.forEach(c => {
    const fEl = document.querySelector(`.port-jack[data-win="${c.from.win}"][data-port="${c.from.port}"][data-dir="out"]`);
    const tEl = document.querySelector(`.port-jack[data-win="${c.to.win}"][data-port="${c.to.port}"][data-dir="in"]`);
    if (!fEl || !tEl) return;
    const p1 = portCenter(fEl), p2 = portCenter(tEl);
    if (!p1 || !p2) { c.path.setAttribute('d',''); if(c.hit)c.hit.setAttribute('d',''); return; }
    const {x:x1,y:y1} = p1, {x:x2,y:y2} = p2;
    const d = bezierD(x1,y1,x2,y2);
    c.path.setAttribute('d', d);
    if (c.hit) c.hit.setAttribute('d', d);
    const sw = Math.max(1, (getPortDotSize(fEl)+getPortDotSize(tEl))/2*0.18);
    c.path.style.strokeWidth = sw + 'px';
    if (c.hit) c.hit.style.strokeWidth = Math.max(14, sw+8) + 'px';
  });
}
function addWire(fromWin, fromPort, toWin, toPort) {
  if (fromWin === toWin) return; // no self-connections
  if (connections.some(c => c.from.win===fromWin && c.from.port===fromPort && c.to.win===toWin && c.to.port===toPort)) return; // no duplicates
  const path = document.createElementNS('http://www.w3.org/2000/svg','path');
  path.classList.add('wire-path');
  const baseFrom=fromWin.replace(/-i\d+$/,'');
  const wireSigType=baseFrom==='win-lfo'?'cv':baseFrom==='win-patterns'||baseFrom==='win-pianoroll'||baseFrom==='win-arp'?'midi':'audio';
  path.dataset.sigtype=wireSigType;
  const hit = document.createElementNS('http://www.w3.org/2000/svg','path');
  hit.setAttribute('stroke','transparent');
  hit.setAttribute('stroke-width','16');
  hit.setAttribute('fill','none');
  hit.style.pointerEvents = 'stroke';
  hit.style.cursor = 'pointer';
  wireSVGLayer.appendChild(path);
  wireSVGLayer.appendChild(hit);
  const conn = {from:{win:fromWin,port:fromPort},to:{win:toWin,port:toPort},path,hit};
  // Audio routing — connect source bus to destination bus
  if (ac) {
    const fb = APP_BUSES[fromWin], tb = APP_BUSES[toWin];
    const fromChBus = (fromWin === 'win-drum' && fb?._ch) ? fb._ch[DRUM_PORT_CH[fromPort]] : null;
    const toChBus   = (toWin   === 'win-drum' && tb?._ch) ? tb._ch[DRUM_PORT_CH[toPort]]   : null;
    const srcNode = fromChBus || fb?.output;
    // Ring mod 'mod' port routes to the modulator bus; sidechain 'sc' port routes to SC input bus
    const baseToWin=toWin.replace(/-i\d+$/,'');
    const dstNode = toChBus ||
      (baseToWin === 'win-ringmod' && toPort === 'mod' ? tb?._modBus :
       baseToWin === 'win-sidechain' && toPort === 'sc' ? tb?._sc?.scIn :
       tb?.input);
    if (srcNode && dstNode) {
      const hadConn = fromChBus
        ? connections.some(c => c.from.win === fromWin && c.from.port === fromPort)
        : connections.some(c => c.from.win === fromWin);
      connections.push(conn);
      if (!hadConn) {
        if (fromChBus) try { fromChBus.disconnect(fb.output); } catch(e) {}
        else try { fb.output.disconnect(drySum); } catch(e) {}
      }
      srcNode.connect(dstNode);
    } else { connections.push(conn); }
  } else { connections.push(conn); }
  if(fromWin === 'win-lfo') {
    const pm = CV_PARAM_MAP[toWin];
    if(pm && pm[toPort]) { const sl = document.getElementById(pm[toPort].sliderId); conn.lfoBase = sl ? +sl.value : undefined; }
  }
  document.querySelector(`.port-jack[data-win="${fromWin}"][data-port="${fromPort}"][data-dir="out"]`)?.classList.add('connected');
  document.querySelector(`.port-jack[data-win="${toWin}"][data-port="${toPort}"][data-dir="in"]`)?.classList.add('connected');
  hit.addEventListener('contextmenu', e => { e.preventDefault(); removeWire(conn); });
  redrawWires();
}
function removeWire(conn) {
  if(conn.from.win === 'win-lfo' && conn.lfoBase !== undefined) {
    const pm = CV_PARAM_MAP[conn.to.win];
    if(pm && pm[conn.to.port]) { const sl = document.getElementById(pm[conn.to.port].sliderId); if(sl){sl.value=conn.lfoBase;sl.dispatchEvent(new Event('input'));} }
  }
  conn.path.remove();
  conn.hit?.remove();
  const i = connections.indexOf(conn);
  if (i > -1) connections.splice(i,1);
  // Audio unrouting
  if (ac) {
    const fb = APP_BUSES[conn.from.win], tb = APP_BUSES[conn.to.win];
    const fromChBus = (conn.from.win === 'win-drum' && fb?._ch) ? fb._ch[DRUM_PORT_CH[conn.from.port]] : null;
    const toChBus   = (conn.to.win   === 'win-drum' && tb?._ch) ? tb._ch[DRUM_PORT_CH[conn.to.port]]   : null;
    const srcNode = fromChBus || fb?.output;
    const dstNode = toChBus   || tb?.input;
    if (srcNode && dstNode) {
      try { srcNode.disconnect(dstNode); } catch(e) {}
      const stillOut = fromChBus
        ? connections.some(c => c.from.win === conn.from.win && c.from.port === conn.from.port)
        : connections.some(c => c.from.win === conn.from.win);
      if (!stillOut) {
        if (fromChBus) fromChBus.connect(fb.output);
        else fb.output.connect(drySum);
      }
    }
  }
  const fStill = connections.some(c=>c.from.win===conn.from.win&&c.from.port===conn.from.port);
  const tStill = connections.some(c=>c.to.win===conn.to.win&&c.to.port===conn.to.port);
  if (!fStill) document.querySelector(`.port-jack[data-win="${conn.from.win}"][data-port="${conn.from.port}"][data-dir="out"]`)?.classList.remove('connected');
  if (!tStill) document.querySelector(`.port-jack[data-win="${conn.to.win}"][data-port="${conn.to.port}"][data-dir="in"]`)?.classList.remove('connected');
}
function findNearestInputPort(mx, my, fromWin) {
  let best = null, minDist = 50;
  document.querySelectorAll('.port-jack[data-dir="in"]').forEach(jack => {
    if (jack.dataset.win === fromWin) return;
    const pos = portCenter(jack);
    if (!pos) return;
    const dist = Math.sqrt((pos.x - mx) ** 2 + (pos.y - my) ** 2);
    if (dist < minDist) { minDist = dist; best = jack; }
  });
  return best;
}
function refreshFanPreviews(wd) {
  wd.previewPaths?.forEach(pp => pp.path.remove());
  wd.previewPaths = [];
  connections
    .filter(c => c.from.win === wd.fromWin && c.from.port === wd.fromPort)
    .forEach(conn => {
      const tgtJack = document.querySelector(`.port-jack[data-win="${conn.to.win}"][data-port="${conn.to.port}"][data-dir="in"]`);
      if (!tgtJack) return;
      const {x:sx, y:sy} = portCenter(wd.jackEl);
      const {x:tx, y:ty} = portCenter(tgtJack);
      const p = document.createElementNS('http://www.w3.org/2000/svg','path');
      p.classList.add('wire-preview');
      p.style.pointerEvents = 'none';
      p.setAttribute('d', bezierD(sx, sy, tx, ty));
      wireSVGLayer.appendChild(p);
      wd.previewPaths.push({path:p, tgtJack});
    });
}
function autoTidyWires() {
  if (connections.length === 0) { showMessage('No wires to tidy'); return; }

  // Collect only open windows that appear in connections
  const winSet = new Set();
  connections.forEach(c => {
    const fw = document.getElementById(c.from.win), tw = document.getElementById(c.to.win);
    if (fw && fw.classList.contains('open')) winSet.add(c.from.win);
    if (tw && tw.classList.contains('open')) winSet.add(c.to.win);
  });
  if (winSet.size === 0) { showMessage('No wired windows open'); return; }

  // Build out/in adjacency sets (only within the open set)
  const out = {}, inp = {};
  winSet.forEach(id => { out[id] = new Set(); inp[id] = new Set(); });
  connections.forEach(c => {
    if (winSet.has(c.from.win) && winSet.has(c.to.win)) {
      out[c.from.win].add(c.to.win);
      inp[c.to.win].add(c.from.win);
    }
  });

  // Assign columns via longest-path BFS from source nodes (nodes with no in-edges)
  const col = {};
  winSet.forEach(id => col[id] = 0);
  const queue = [...winSet].filter(id => inp[id].size === 0);
  const visited = new Set(queue);
  while (queue.length) {
    const id = queue.shift();
    out[id].forEach(next => {
      col[next] = Math.max(col[next], col[id] + 1);
      if (!visited.has(next)) { visited.add(next); queue.push(next); }
    });
  }

  // Group by column; within each column sort by connection order for fewer crossings
  const byCol = {};
  winSet.forEach(id => { const c = col[id]; (byCol[c] = byCol[c] || []).push(id); });

  // Measure actual window dimensions in workspace units
  const getSize = id => {
    const w = document.getElementById(id);
    return { w: w ? w.offsetWidth / wsZoom : 340, h: w ? w.offsetHeight / wsZoom : 220 };
  };

  const GAP_X = 90, GAP_Y = 36;
  const sortedCols = Object.keys(byCol).map(Number).sort((a,b) => a-b);

  // Calculate per-column max width and cumulative x positions
  const colX = {}, colMaxW = {};
  let curX = 80;
  sortedCols.forEach(c => {
    colMaxW[c] = Math.max(...byCol[c].map(id => getSize(id).w));
    colX[c] = curX;
    curX += colMaxW[c] + GAP_X;
  });

  // Total height per column for vertical centering
  const colTotalH = c => byCol[c].reduce((s, id) => s + getSize(id).h + GAP_Y, -GAP_Y);
  const maxH = Math.max(...sortedCols.map(colTotalH));
  const startY = 80;

  // Reposition all windows in the tidy layout
  sortedCols.forEach(c => {
    const x = colX[c];
    let y = startY + (maxH - colTotalH(c)) / 2;
    byCol[c].forEach(id => {
      const { h } = getSize(id);
      const win = document.getElementById(id);
      if (!win) return;
      win.dataset.wx = x; win.dataset.wy = y;
      win.style.left = (x * wsZoom + wsPanX) + 'px';
      win.style.top  = (y * wsZoom + wsPanY) + 'px';
      y += h + GAP_Y;
    });
  });

  redrawWires();
  showMessage('Wires tidied — ' + winSet.size + ' apps arranged');
}
function startWireDrawing(winId, portId, jack) {
  const tempPath = document.createElementNS('http://www.w3.org/2000/svg','path');
  tempPath.classList.add('wire-temp');
  tempPath.style.pointerEvents = 'none';
  wireSVGLayer.appendChild(tempPath);
  wireDrawing = {fromWin:winId, fromPort:portId, jackEl:jack, tempPath, previewPaths:[]};
  document.querySelectorAll('.port-jack[data-dir="in"]').forEach(el => el.classList.add('target-highlight'));
  refreshFanPreviews(wireDrawing);
}
function makePortJack(winId, p, dir) {
  const jack = document.createElement('div');
  jack.className = 'port-jack';
  jack.dataset.win = winId; jack.dataset.port = p.id; jack.dataset.dir = dir;
  const dot = document.createElement('div');
  dot.className = 'port-dot';
  jack.appendChild(dot);
  if (dir === 'out') {
    jack.addEventListener('mousedown', e => {
      e.stopPropagation();
      if (e.shiftKey) {
        // Shift held: distinguish click (queue) vs drag (fan-out wireDrawing)
        const sx = e.clientX, sy = e.clientY;
        function startDraw() { startWireDrawing(winId, p.id, jack); }
        function onMove(me) {
          if (Math.hypot(me.clientX - sx, me.clientY - sy) > 5) {
            document.removeEventListener('mousemove', onMove);
            document.removeEventListener('mouseup', onUp);
            startDraw();
          }
        }
        function onUp(ue) {
          document.removeEventListener('mousemove', onMove);
          document.removeEventListener('mouseup', onUp);
          if (Math.hypot(ue.clientX - sx, ue.clientY - sy) <= 5) {
            // Shift+click (no drag) → toggle in pendingOutPorts
            const idx = pendingOutPorts.findIndex(q => q.win === winId && q.port === p.id);
            if (idx >= 0) {
              pendingOutPorts.splice(idx, 1);
              jack.classList.remove('pending-out');
            } else {
              pendingOutPorts.push({win:winId, port:p.id, jackEl:jack});
              jack.classList.add('pending-out');
            }
          }
        }
        document.addEventListener('mousemove', onMove);
        document.addEventListener('mouseup', onUp);
      } else {
        // Regular click: deselect if already pending, otherwise start wire
        const idx = pendingOutPorts.findIndex(q => q.win === winId && q.port === p.id);
        if (idx >= 0) {
          pendingOutPorts.splice(idx, 1);
          jack.classList.remove('pending-out');
        } else {
          startWireDrawing(winId, p.id, jack);
        }
      }
    });
  }
  if (dir === 'in') {
    jack.addEventListener('mousedown', e => {
      e.stopPropagation();
      const idx = pendingInPorts.findIndex(q => q.win === winId && q.port === p.id);
      if (idx >= 0) {
        pendingInPorts.splice(idx, 1);
        jack.classList.remove('pending-in');
        e.preventDefault();
      }
    });
  }
  return jack;
}
function renderPorts(winId) {
  const win = document.getElementById(winId);
  const def = PORT_DEFS[winId];
  if (!win || !def) return;
  win.querySelector('.port-bar')?.remove();
  win.querySelector('.port-side-in')?.remove();
  win.querySelector('.port-side-out')?.remove();
  const ins = def.in || [], outs = def.out || [];
  if (ins.length) {
    const side = document.createElement('div');
    side.className = 'port-side-in' + (ins.length > 3 ? ' multi' : '');
    ins.forEach(p => side.appendChild(makePortJack(winId, p, 'in')));
    win.appendChild(side);
  }
  if (outs.length) {
    const side = document.createElement('div');
    side.className = 'port-side-out' + (outs.length > 3 ? ' multi' : '');
    outs.forEach(p => side.appendChild(makePortJack(winId, p, 'out')));
    win.appendChild(side);
  }
}
document.addEventListener('mousemove', e => {
  if (!wireDrawing) return;
  const src = portCenter(wireDrawing.jackEl);
  if (!src) return;
  const {x,y} = src;
  wireDrawing.tempPath.setAttribute('d', bezierD(x,y,e.clientX,e.clientY));
  wireDrawing.previewPaths?.forEach(pp => {
    const t = portCenter(pp.tgtJack);
    if (!t) return;
    pp.path.setAttribute('d', bezierD(x, y, t.x, t.y));
  });
  // Draw lines from each pending-out port to cursor
  if (pendingOutPorts.length) {
    if (!wireDrawing.pendingCursorPaths) wireDrawing.pendingCursorPaths = [];
    while (wireDrawing.pendingCursorPaths.length < pendingOutPorts.length) {
      const p = document.createElementNS('http://www.w3.org/2000/svg','path');
      p.classList.add('wire-temp'); p.style.pointerEvents='none'; p.style.opacity='0.55';
      wireSVGLayer.appendChild(p);
      wireDrawing.pendingCursorPaths.push(p);
    }
    while (wireDrawing.pendingCursorPaths.length > pendingOutPorts.length)
      wireDrawing.pendingCursorPaths.pop().remove();
    pendingOutPorts.forEach((pq,i) => {
      const pos = portCenter(pq.jackEl);
      if (!pos) return;
      wireDrawing.pendingCursorPaths[i].setAttribute('d', bezierD(pos.x,pos.y,e.clientX,e.clientY));
    });
  } else if (wireDrawing.pendingCursorPaths?.length) {
    wireDrawing.pendingCursorPaths.forEach(p=>p.remove());
    wireDrawing.pendingCursorPaths = [];
  }
});
document.addEventListener('mouseup', e => {
  if (!wireDrawing) return;
  document.querySelectorAll('.port-jack.target-highlight').forEach(el => el.classList.remove('target-highlight'));
  wireDrawing.previewPaths?.forEach(pp => pp.path.remove());
  wireDrawing.pendingCursorPaths?.forEach(p => p.remove());
  wireDrawing.tempPath.remove();
  const target = findNearestInputPort(e.clientX, e.clientY, wireDrawing.fromWin);
  if (target) {
    addWire(wireDrawing.fromWin, wireDrawing.fromPort, target.dataset.win, target.dataset.port);
    // batch-connect any rubber-banded input ports to this source
    pendingInPorts.forEach(pi => {
      if (pi.win !== wireDrawing.fromWin && (pi.win !== target.dataset.win || pi.port !== target.dataset.port))
        addWire(wireDrawing.fromWin, wireDrawing.fromPort, pi.win, pi.port);
      pi.jackEl.classList.remove('pending-in');
    });
    pendingInPorts.length = 0;
    // batch-connect any queued pending output ports to the same target (skip self-connections)
    pendingOutPorts.forEach(pq => {
      if (pq.win !== target.dataset.win) addWire(pq.win, pq.port, target.dataset.win, target.dataset.port);
      pq.jackEl.classList.remove('pending-out');
    });
    pendingOutPorts.length = 0;
    if (e.shiftKey) {
      // fan-out: keep wireDrawing alive from the same source port
      const {fromWin, fromPort, jackEl} = wireDrawing;
      const newTemp = document.createElementNS('http://www.w3.org/2000/svg','path');
      newTemp.classList.add('wire-temp');
      newTemp.style.pointerEvents = 'none';
      wireSVGLayer.appendChild(newTemp);
      wireDrawing = {fromWin, fromPort, jackEl, tempPath:newTemp, previewPaths:[]};
      document.querySelectorAll('.port-jack[data-dir="in"]').forEach(el => el.classList.add('target-highlight'));
      refreshFanPreviews(wireDrawing);
      return;
    }
  } else {
    // Released on empty workspace — cancel all pending ports
    pendingOutPorts.forEach(pq=>pq.jackEl.classList.remove('pending-out')); pendingOutPorts.length=0;
    pendingInPorts.forEach(pi=>pi.jackEl.classList.remove('pending-in')); pendingInPorts.length=0;
  }
  wireDrawing = null;
});
function alignDrumPorts() {
  const win = document.getElementById('win-drum');
  if (!win || !win.classList.contains('open')) return;
  const rows = [...win.querySelectorAll('.seqrow')];
  if (!rows.length) return;
  const winRect = win.getBoundingClientRect();
  // Use wsZoom directly — the window has transform:scale(wsZoom) applied by workspace logic.
  // jack.style.top is in the window's own layout pixels; viewport offset / wsZoom converts correctly.
  ['port-side-in','port-side-out'].forEach(cls => {
    const side = win.querySelector('.' + cls);
    if (!side) return;
    [...side.querySelectorAll('.port-jack')].forEach((jack, i) => {
      const row = rows[i];
      if (!row) return;
      const r = row.getBoundingClientRect();
      jack.style.top = ((r.top + r.height / 2 - winRect.top) / wsZoom) + 'px';
    });
  });
}
// Continuous wire + drum port alignment update (drum ports only every 3rd frame to reduce layout reads)
let _wireFrame=0;
(function wireLoop(){ redrawWires(); if(++_wireFrame%3===0)alignDrumPorts(); requestAnimationFrame(wireLoop); })();
// Render ports on all windows
Object.keys(PORT_DEFS).forEach(id => renderPorts(id));

/* =====================================================
   MODULE-LEVEL UTILITIES for window management
   ===================================================== */
function attachResizeScale(win){
  if(win._resObs)return;
  const baseW=parseInt(win.style.width)||win.offsetWidth||360;
  win._baseW=baseW;
  win._resObs=new ResizeObserver(()=>{
    if(!win.classList.contains('open'))return;
    const zoom=Math.max(0.3,Math.min(3,win.offsetWidth/win._baseW));
    const wb=win.querySelector('.wbody');
    if(wb)wb.style.zoom=zoom;
    win.style.setProperty('--port-dot-scale',zoom);
  });
  win._resObs.observe(win);
}

function initWindowFrame(win){
  win.addEventListener('pointerdown',()=>focusWindow(win),true);
  win.querySelectorAll('.light').forEach(l=>l.addEventListener('click',e=>{
    e.stopPropagation();
    const act=l.dataset.act;
    if(act==='close'){
      // Call any registered stop hooks before closing
      const b=APP_BUSES[win.id];
      if(b&&typeof b._stop==='function')b._stop();
      if(typeof win._stopAudio==='function')win._stopAudio();
      closeWindow(win.id);
    }
    else if(act==='min'){
      // Minimize: collapse wbody to titlebar only; audio continues
      const wb=win.querySelector('.wbody');
      if(wb){
        const mini=win.classList.toggle('minimized');
        wb.style.display=mini?'none':'';
      }
    }
    else if(act==='max')maximizeWindow(win);
  }));
  const bar=win.querySelector('.titlebar');
  if(!bar)return;
  let drag=null;
  bar.addEventListener('pointerdown',e=>{
    if(e.target.closest('.lights'))return;
    // Ctrl+Click toggles window selection without dragging
    if(e.ctrlKey||e.metaKey){
      if(selectedWindows.has(win.id)){selectedWindows.delete(win.id);win.classList.remove('win-selected');}
      else{selectedWindows.add(win.id);win.classList.add('win-selected');}
      return;
    }
    if(win.classList.contains('maxd')||_wsLocked)return;
    const r=win.getBoundingClientRect();
    drag={dx:e.clientX-r.left,dy:e.clientY-r.top};
    win.classList.add('dragging');
    try{bar.setPointerCapture(e.pointerId);}catch(_){}
    focusWindow(win);e.preventDefault();
  });
  bar.addEventListener('pointermove',e=>{
    if(!drag)return;
    const sx=e.clientX-drag.dx, sy=e.clientY-drag.dy;
    win.dataset.wx=(sx-wsPanX)/wsZoom;
    win.dataset.wy=(sy-wsPanY)/wsZoom;
    win.style.left=sx+'px';win.style.top=sy+'px';win.style.right='auto';
    if(typeof redrawWires==='function')redrawWires();
  });
  bar.addEventListener('pointerup',()=>{drag=null;win.classList.remove('dragging');saveWinPos(win);});
  const grip=document.createElement('div');grip.className='resize-grip';win.appendChild(grip);
  let rsz=null;
  grip.addEventListener('pointerdown',e=>{
    e.stopPropagation();e.preventDefault();
    const r=win.getBoundingClientRect();
    rsz={sx:e.clientX,sy:e.clientY,w:r.width/wsZoom,h:r.height/wsZoom};
    if(!win.style.height)win.style.height=(r.height/wsZoom)+'px';
    grip.setPointerCapture(e.pointerId);focusWindow(win);
  });
  grip.addEventListener('pointermove',e=>{
    if(!rsz)return;
    const dw=(e.clientX-rsz.sx)/wsZoom, dh=(e.clientY-rsz.sy)/wsZoom;
    win.style.width=Math.max(280,rsz.w+dw)+'px';
    win.style.height=Math.max(120,rsz.h+dh)+'px';
    if(typeof redrawWires==='function')redrawWires();
  });
  grip.addEventListener('pointerup',()=>{rsz=null;saveWinPos(win);});
  grip.addEventListener('pointercancel',()=>{rsz=null;});
}

/* =====================================================
   WIDGET HELPERS — knob, slider, toggle, XY pad
   ===================================================== */

function acidColor(alpha){
  const rgb=getComputedStyle(document.documentElement).getPropertyValue('--acid-rgb')||'232,104,32';
  return `rgba(${rgb.trim()},${alpha})`;
}

/* =====================================================
   CANVAS HELPER — crisp rendering at any DPR + zoom
   Sets canvas buffer to physical pixel size, scales ctx so
   all drawing code continues to use CSS pixel coordinates.
   ===================================================== */
function setupCanvas(cv, fallW, fallH) {
  const dpr = window.devicePixelRatio || 1;
  const zoom = (typeof wsZoom !== 'undefined' ? wsZoom : 1);
  const scale = dpr * zoom;
  const W = cv.offsetWidth || fallW;
  const H = cv.offsetHeight || fallH;
  cv.width  = Math.round(W * scale);
  cv.height = Math.round(H * scale);
  cv.style.width  = W + 'px';
  cv.style.height = H + 'px';
  const ctx = cv.getContext('2d');
  ctx.scale(scale, scale);
  return { ctx, W, H };
}

function makeSlider({label, min=0, max=100, value=50, unit='', step=0, decimals=0, tip='', format=null, onChange}){
  const row=document.createElement('div');row.className='acid-slider-row';
  const lbl=document.createElement('span');lbl.className='acid-slider-lbl';lbl.textContent=label;
  if(tip)lbl.dataset.tip=tip;
  const sl=document.createElement('input');sl.type='range';sl.min=min;sl.max=max;sl.value=value;
  if(step)sl.step=step;
  const valEl=document.createElement('span');valEl.className='acid-slider-val';
  const fmt=format?format:v=>decimals?parseFloat(v).toFixed(decimals)+unit:Math.round(v)+unit;
  let cur=+value;
  function updateFill(){const t=(sl.value-min)/(max-min);sl.style.setProperty('--fill',(t*100)+'%');}
  sl.addEventListener('input',()=>{cur=+sl.value;valEl.textContent=fmt(cur);updateFill();onChange(cur);});
  updateFill();valEl.textContent=fmt(cur);
  row.append(lbl,sl,valEl);
  row._val=()=>cur;
  row._update=v=>{cur=Math.max(min,Math.min(max,v));sl.value=cur;valEl.textContent=fmt(cur);updateFill();onChange(cur);};
  return row;
}

function makeToggle({label, value=false, tip='', onChange}){
  const row=document.createElement('div');row.className='acid-toggle-row';
  const lbl=document.createElement('span');lbl.className='acid-toggle-lbl';lbl.textContent=label;
  if(tip)lbl.dataset.tip=tip;
  const track=document.createElement('button');track.className='acid-toggle-track'+(value?' on':'');
  track.setAttribute('role','switch');track.setAttribute('aria-checked',String(value));
  let cur=value;
  track.addEventListener('click',()=>{cur=!cur;track.classList.toggle('on',cur);track.setAttribute('aria-checked',String(cur));onChange(cur);});
  row.append(lbl,track);
  row._val=()=>cur;
  row._set=v=>{cur=!!v;track.classList.toggle('on',cur);track.setAttribute('aria-checked',String(cur));};
  return row;
}

function makeXYPad({labelX='X', labelY='Y', minX=0, maxX=100, minY=0, maxY=100, valueX=50, valueY=50, tip='', onChange}){
  const wrap=document.createElement('div');wrap.className='acid-xy-wrap';
  const pad=document.createElement('div');pad.className='acid-xy-pad';
  if(tip)pad.dataset.tip=tip;
  const dot=document.createElement('div');dot.className='acid-xy-dot';
  const labels=document.createElement('div');labels.className='acid-xy-labels';
  const ly=document.createElement('span');ly.className='acid-xy-lbl';ly.textContent='↕ '+labelY;
  const lx=document.createElement('span');lx.className='acid-xy-lbl';lx.textContent=labelX+' →';
  labels.append(ly,lx);
  let cx=valueX,cy=valueY,dragging=false;
  function moveDot(nx,ny){
    cx=Math.max(minX,Math.min(maxX,nx));cy=Math.max(minY,Math.min(maxY,ny));
    dot.style.left=((cx-minX)/(maxX-minX)*100)+'%';
    dot.style.top=((1-(cy-minY)/(maxY-minY))*100)+'%';
    onChange(cx,cy);
  }
  function handleMove(e){
    if(!dragging)return;
    const r=pad.getBoundingClientRect();
    moveDot(minX+(e.clientX-r.left)/r.width*(maxX-minX),maxY-(e.clientY-r.top)/r.height*(maxY-minY));
  }
  pad.addEventListener('pointerdown',e=>{dragging=true;pad.setPointerCapture(e.pointerId);handleMove(e);});
  pad.addEventListener('pointermove',handleMove);
  pad.addEventListener('pointerup',()=>dragging=false);
  pad.appendChild(dot);
  wrap.append(labels,pad);
  moveDot(valueX,valueY);
  wrap._set=(nx,ny)=>moveDot(nx,ny);wrap._x=()=>cx;wrap._y=()=>cy;
  return wrap;
}

function makeWavePicker({waves, value, tip='', onChange}){
  const SVG_WAVES={
    sine:'M0,9 Q8,0 16,9 Q24,18 32,9',
    square:'M0,3 L0,3 L0,15 L16,15 L16,3 L32,3',
    sawtooth:'M0,15 L16,3 L16,15 L32,3',
    triangle:'M0,15 L8,3 L16,15 L24,3 L32,15',
  };
  const wrap=document.createElement('div');wrap.className='acid-wave-picker';
  if(tip)wrap.dataset.tip=tip;
  let cur=value;
  waves.forEach(w=>{
    const btn=document.createElement('button');btn.className='acid-wave-btn'+(w===cur?' active':'');
    btn.dataset.wave=w;
    const NS='http://www.w3.org/2000/svg';
    const svg=document.createElementNS(NS,'svg');svg.setAttribute('viewBox','0 0 32 18');svg.setAttribute('width','32');svg.setAttribute('height','18');
    const path=document.createElementNS(NS,'path');path.setAttribute('d',SVG_WAVES[w]||SVG_WAVES.sine);path.setAttribute('fill','none');
    svg.appendChild(path);btn.appendChild(svg);
    btn.addEventListener('click',()=>{
      wrap.querySelectorAll('.acid-wave-btn').forEach(b=>b.classList.remove('active'));
      btn.classList.add('active');cur=w;onChange(w);
    });
    wrap.appendChild(btn);
  });
  wrap._val=()=>cur;
  wrap._set=v=>{cur=v;wrap.querySelectorAll('.acid-wave-btn').forEach(b=>b.classList.toggle('active',b.dataset.wave===v));};
  return wrap;
}

/* =====================================================
   KNOB WIDGET
   ===================================================== */
function makeKnob({label, min, max, value, unit='', decimals=0, tip='', size='md', onChange}){
  const NS='http://www.w3.org/2000/svg';
  const DIM={sm:{sz:34,r:11,sw:3},md:{sz:48,r:16,sw:4},lg:{sz:68,r:22,sw:5}};
  const {sz:SZ,r:R,sw:SW}=DIM[size]||DIM.md;
  const CX=SZ/2,CY=SZ/2,START=-135,SWEEP=270;
  const toXY=ang=>{const r=(ang-90)*Math.PI/180;return [CX+R*Math.cos(r),CY+R*Math.sin(r)];};
  const fmt=v=>decimals?v.toFixed(decimals)+unit:Math.round(v)+unit;
  const la=ang=>ang>180?1:0;
  const [sx,sy]=toXY(START);
  const [ex,ey]=toXY(START+SWEEP);
  const svg=document.createElementNS(NS,'svg');
  svg.setAttribute('viewBox',`0 0 ${SZ} ${SZ}`);svg.setAttribute('width',SZ);svg.setAttribute('height',SZ);
  const bg=document.createElementNS(NS,'circle');bg.setAttribute('cx',CX);bg.setAttribute('cy',CY);bg.setAttribute('r',SZ/2-2);bg.setAttribute('class','knob-bg');
  const track=document.createElementNS(NS,'path');
  track.setAttribute('d',`M${sx} ${sy} A${R} ${R} 0 1 1 ${ex} ${ey}`);track.setAttribute('class','knob-arc-track');track.setAttribute('stroke-width',SW);
  const arc=document.createElementNS(NS,'path');arc.setAttribute('class','knob-arc-fill');arc.setAttribute('stroke-width',SW);
  const dot=document.createElementNS(NS,'circle');dot.setAttribute('r',size==='lg'?3.5:size==='sm'?2:2.5);dot.setAttribute('class','knob-dot');
  svg.append(bg,track,arc,dot);
  const body=document.createElement('div');body.className='knob-body';body.appendChild(svg);
  const valEl=document.createElement('div');valEl.className='knob-val';
  const lblEl=document.createElement('div');lblEl.className='knob-lbl';lblEl.textContent=label;
  if(tip)lblEl.dataset.tip=tip;
  const wrap=document.createElement('div');wrap.className='knob-ctrl'+' '+size;wrap.append(body,valEl,lblEl);
  let cur=value;
  function update(v){
    cur=Math.max(min,Math.min(max,v));
    const t=(cur-min)/(max-min);
    const ang=START+t*SWEEP;
    const [ax,ay]=toXY(ang);
    const sweepNow=t*SWEEP;
    if(sweepNow<0.5){arc.setAttribute('d',`M${sx} ${sy} L${sx} ${sy}`);}
    else{arc.setAttribute('d',`M${sx} ${sy} A${R} ${R} 0 ${la(sweepNow)} 1 ${ax} ${ay}`);}
    // indicator dot at edge
    const dr=(ang-90)*Math.PI/180;
    dot.setAttribute('cx',CX+(R-1)*Math.cos(dr));dot.setAttribute('cy',CY+(R-1)*Math.sin(dr));
    valEl.textContent=fmt(cur);
    onChange(cur);
  }
  // pointer drag
  let ds=null;
  body.addEventListener('pointerdown',e=>{ds={y:e.clientY,v:cur,snap:cur};body.setPointerCapture(e.pointerId);e.preventDefault();});
  body.addEventListener('pointermove',e=>{if(!ds)return;update(ds.v+(ds.y-e.clientY)/100*(max-min));});
  body.addEventListener('pointerup',()=>{ds=null;});
  // scroll — Shift=fine (÷5), Ctrl=coarse (×5)
  body.addEventListener('wheel',e=>{
    e.preventDefault();e.stopPropagation();
    const step=(max-min)/100*(e.shiftKey?0.2:e.ctrlKey?5:1);
    update(cur+(e.deltaY<0?1:-1)*step);
  },{passive:false});
  // dblclick → reset to default
  body.addEventListener('dblclick',e=>{e.preventDefault();update(value);});
  // right-click → type a value
  body.addEventListener('contextmenu',e=>{
    e.preventDefault();e.stopPropagation();
    const inp=document.createElement('input');inp.type='text';inp.value=cur.toFixed(decimals);
    inp.style.cssText='position:fixed;z-index:9999;font:inherit;font-size:11px;padding:2px 6px;border-radius:5px;border:1px solid var(--acid);background:#0f0d09;color:var(--acid);width:58px;text-align:center;outline:none';
    const rc=body.getBoundingClientRect();inp.style.left=(rc.left+rc.width/2-29)+'px';inp.style.top=(rc.top-28)+'px';
    document.body.appendChild(inp);inp.select();
    const commit=()=>{const v=parseFloat(inp.value);if(!isNaN(v))update(v);inp.remove();};
    inp.addEventListener('keydown',e=>{if(e.key==='Enter')commit();if(e.key==='Escape')inp.remove();e.stopPropagation();});
    inp.addEventListener('blur',commit);
  });
  // click → focus for arrow key control
  body.tabIndex=0;
  body.addEventListener('click',()=>body.focus());
  body.addEventListener('keydown',e=>{
    if(e.key==='ArrowUp'||e.key==='ArrowRight'){e.preventDefault();update(cur+(e.shiftKey?0.2:1)*(max-min)/100);}
    if(e.key==='ArrowDown'||e.key==='ArrowLeft'){e.preventDefault();update(cur-(e.shiftKey?0.2:1)*(max-min)/100);}
  });
  // value pill on drag
  const pill=document.createElement('div');
  pill.style.cssText='position:fixed;z-index:9999;background:#1a1a1a;border:1px solid var(--acid);color:var(--acid);font-size:10px;padding:2px 7px;border-radius:10px;pointer-events:none;display:none;white-space:nowrap';
  document.body.appendChild(pill);
  body.addEventListener('pointerdown',()=>{pill.style.display='block';});
  body.addEventListener('pointermove',e=>{
    if(!ds)return;
    pill.style.left=(e.clientX+12)+'px';pill.style.top=(e.clientY-18)+'px';
    pill.textContent=fmt(cur);
  });
  body.addEventListener('pointerup',()=>{
    pill.style.display='none';
    if(ds&&ds.snap!==cur){
      const prev=ds.snap,next=cur;
      _pushUndo(()=>{update(prev);return()=>{update(next);return()=>{update(prev);};};});
    }
    ds=null;
  });
  update(value);
  wrap._update=update;wrap._val=()=>cur;
  return wrap;
}

function makeStepper({label,steps,index=0,tip='',onChange}){
  // steps = array of {label,value} or plain values
  const getL=i=>{const s=steps[i];return typeof s==='object'?s.label:String(s);};
  const getV=i=>{const s=steps[i];return typeof s==='object'?s.value:s;};
  const row=document.createElement('div');row.className='acid-stepper-row';
  const lbl=document.createElement('span');lbl.className='acid-stepper-lbl';lbl.textContent=label;if(tip)lbl.dataset.tip=tip;
  const ctrl=document.createElement('div');ctrl.className='acid-stepper-ctrl';
  const prev=document.createElement('button');prev.className='acid-stepper-btn';prev.textContent='◀';prev.type='button';
  const valEl=document.createElement('div');valEl.className='acid-stepper-val';
  const next=document.createElement('button');next.className='acid-stepper-btn';next.textContent='▶';next.type='button';
  ctrl.append(prev,valEl,next);row.append(lbl,ctrl);
  let cur=Math.max(0,Math.min(steps.length-1,index));
  function set(i){cur=((i%steps.length)+steps.length)%steps.length;valEl.textContent=getL(cur);onChange(getV(cur),cur);}
  prev.addEventListener('click',()=>set(cur-1));next.addEventListener('click',()=>set(cur+1));
  set(cur);
  row._val=()=>getV(cur);row._idx=()=>cur;row._set=i=>{cur=i;valEl.textContent=getL(cur);};
  return row;
}

function makeVertFader({label,min=0,max=100,value=50,unit='',tip='',decimals=0,format=null,height=110,onChange}){
  const fmt=format?format:v=>decimals?parseFloat(v).toFixed(decimals)+unit:Math.round(v)+unit;
  const THUMB_H=14;
  const wrap=document.createElement('div');wrap.className='acid-vfader-wrap';if(tip)wrap.dataset.tip=tip;
  const track=document.createElement('div');track.className='acid-vfader-track';track.style.height=height+'px';
  const fill=document.createElement('div');fill.className='acid-vfader-fill';
  const thumb=document.createElement('div');thumb.className='acid-vfader-thumb';
  track.append(fill,thumb);
  const valEl=document.createElement('div');valEl.className='acid-vfader-val';
  const lblEl=document.createElement('div');lblEl.className='acid-vfader-lbl';lblEl.textContent=label;
  wrap.append(track,valEl,lblEl);
  let cur=value;
  function update(v){
    cur=Math.max(min,Math.min(max,v));
    const t=(cur-min)/(max-min);
    const usable=height-THUMB_H-4;
    thumb.style.top=Math.max(0,(1-t)*usable)+'px';
    fill.style.height=Math.max(0,t*(height-4))+'px';
    valEl.textContent=fmt(cur);onChange(cur);
  }
  let ds=null;
  thumb.addEventListener('pointerdown',e=>{ds={y:e.clientY,v:cur};thumb.setPointerCapture(e.pointerId);e.preventDefault();});
  thumb.addEventListener('pointermove',e=>{if(!ds)return;update(ds.v+(ds.y-e.clientY)/(height-THUMB_H)*(max-min));});
  thumb.addEventListener('pointerup',()=>ds=null);
  track.addEventListener('click',e=>{if(e.target===thumb)return;const r=track.getBoundingClientRect();update(min+(1-(e.clientY-r.top)/r.height)*(max-min));});
  wrap.addEventListener('wheel',e=>{e.preventDefault();e.stopPropagation();update(cur+(e.deltaY<0?1:-1)*(max-min)/100);},{passive:false});
  update(value);
  wrap._update=update;wrap._val=()=>cur;
  return wrap;
}

function makeNumDrag({label,min=0,max=100,value=50,unit='',step=1,decimals=0,tip='',format=null,onChange}){
  const wrap=document.createElement('div');wrap.className='acid-num-drag';if(tip)wrap.dataset.tip=tip;
  const numEl=document.createElement('div');numEl.className='acid-num-drag-val';
  const unitEl=document.createElement('div');unitEl.className='acid-num-drag-unit';unitEl.textContent=unit;
  const lblEl=document.createElement('div');lblEl.className='acid-num-drag-lbl';lblEl.textContent=label;
  const hintEl=document.createElement('div');hintEl.className='acid-num-drag-hint';hintEl.textContent='↕ drag  ∙  dbl-click to type';
  wrap.append(numEl,unitEl,lblEl,hintEl);
  let cur=value;
  const fmt=format?format:v=>decimals?parseFloat(v).toFixed(decimals):Math.round(v);
  function update(v){cur=Math.max(min,Math.min(max,v));numEl.textContent=fmt(cur);onChange(cur);}
  let ds=null;
  wrap.addEventListener('pointerdown',e=>{ds={y:e.clientY,v:cur};wrap.setPointerCapture(e.pointerId);e.preventDefault();});
  wrap.addEventListener('pointermove',e=>{if(!ds)return;update(ds.v+(ds.y-e.clientY)/120*(max-min));});
  wrap.addEventListener('pointerup',()=>ds=null);
  wrap.addEventListener('wheel',e=>{e.preventDefault();e.stopPropagation();update(cur+(e.deltaY<0?1:-1)*step);},{passive:false});
  wrap.addEventListener('dblclick',()=>{
    const inp=document.createElement('input');inp.type='text';inp.value=cur.toFixed(decimals);
    inp.style.cssText='position:fixed;z-index:9999;font:inherit;font-size:12px;padding:3px 8px;border-radius:6px;border:1px solid var(--acid);background:#0f0d09;color:var(--acid);width:72px;text-align:center;outline:none';
    const rc=wrap.getBoundingClientRect();inp.style.left=(rc.left+rc.width/2-36)+'px';inp.style.top=(rc.top+rc.height/2-13)+'px';
    document.body.appendChild(inp);inp.select();
    const commit=()=>{const v=parseFloat(inp.value);if(!isNaN(v))update(v);inp.remove();};
    inp.addEventListener('keydown',e=>{if(e.key==='Enter')commit();if(e.key==='Escape')inp.remove();e.stopPropagation();});
    inp.addEventListener('blur',commit);
  });
  update(value);
  wrap._update=update;wrap._val=()=>cur;
  return wrap;
}

const APP_FACTORIES = {};
let _spawnCounter = 0;

APP_FACTORIES['win-compressor'] = function setupCompressorUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getBus=()=>APP_BUSES[winId]?._comp;
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='DYNAMICS';
  // Ratio stepper (discrete values make musical sense)
  const RATIOS=[{label:'2:1',value:2},{label:'4:1',value:4},{label:'8:1',value:8},{label:'20:1',value:20},{label:'∞:1',value:100}];
  const ratStep=makeStepper({label:'RATIO',steps:RATIOS,index:1,tip:'Compression ratio — how aggressively signal above threshold is reduced',onChange:v=>{const c=getBus();if(c)c.node.ratio.value=v;}});
  // Layout: vert threshold fader left + knobs right
  const layout=document.createElement('div');layout.style.cssText='display:flex;gap:14px;align-items:flex-start;padding:8px 0;';
  const thrFader=makeVertFader({label:'THRESH',min:-60,max:0,value:-18,unit:' dB',height:110,
    tip:'Threshold — compression kicks in when signal exceeds this level',
    format:v=>(v<0?'−'+Math.abs(Math.round(v)):Math.round(v))+' dB',
    onChange:v=>{const c=getBus();if(c)c.node.threshold.value=v;}});
  const rightCol=document.createElement('div');rightCol.style.cssText='display:flex;flex-direction:column;gap:6px;flex:1;';
  const kAtk=makeKnob({label:'ATTACK',min:1,max:200,value:10,unit:' ms',size:'sm',onChange:v=>{const c=getBus();if(c)c.node.attack.value=v/1000;}});
  const kRel=makeKnob({label:'RELEASE',min:10,max:2000,value:100,unit:' ms',size:'sm',onChange:v=>{const c=getBus();if(c)c.node.release.value=v/1000;}});
  const kGain=makeKnob({label:'MAKEUP',min:0,max:24,value:4,unit:' dB',size:'md',onChange:v=>{const c=getBus();if(c)c.makeup.gain.value=Math.pow(10,v/20);}});
  const smRow=document.createElement('div');smRow.style.cssText='display:flex;gap:6px;flex-wrap:wrap;';smRow.append(kAtk,kRel);
  const kneeToggle=makeToggle({label:'SOFT KNEE',value:true,tip:'Soft knee applies compression gradually above threshold. Hard = abrupt.',onChange:v=>{const c=getBus();if(c)c.node.knee.value=v?6:0;}});
  rightCol.append(smRow,kGain,kneeToggle);
  layout.append(thrFader,rightCol);
  // GR meter
  const sec2=document.createElement('div');sec2.className='acid-section';
  const grLbl=document.createElement('span');grLbl.className='app-section-lbl';grLbl.textContent='GAIN REDUCTION';
  const grRow=document.createElement('div');grRow.style.cssText='display:flex;align-items:center;gap:8px;padding:4px 0';
  const grBg=document.createElement('div');grBg.style.cssText='flex:1;height:8px;background:rgba(255,255,255,.06);border-radius:4px;overflow:hidden';
  const grBar=document.createElement('div');grBar.style.cssText='height:100%;width:0%;background:linear-gradient(90deg,var(--acid),var(--accent-warm));border-radius:4px;transition:width .05s';
  const grVal=document.createElement('span');grVal.className='app-val';grVal.style.minWidth='44px';grVal.textContent='0.0 dB';
  grBg.appendChild(grBar);grRow.append(grBg,grVal);sec2.append(grLbl,grRow);
  sec.append(lbl,ratStep,layout);ui.append(sec,sec2);wb.appendChild(ui);
  (function animGR(){if(!win.isConnected)return;const c=getBus()?.node;const gr=c?Math.abs(c.reduction):0;grBar.style.width=Math.min(gr*4,100)+'%';grVal.textContent='−'+gr.toFixed(1)+' dB';requestAnimationFrame(animGR);})();
};

APP_FACTORIES['win-reverb'] = function setupReverbUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const RV_TYPES={room:{sz:20,dc:25,pr:8,dm:60,tip:'Small room — tight, natural reflections.'},hall:{sz:80,dc:75,pr:20,dm:20,tip:'Concert hall — long, expansive decay.'},plate:{sz:55,dc:50,pr:5,dm:75,tip:'Metal plate — dense, bright reverb with fast buildup.'},spring:{sz:30,dc:35,pr:15,dm:45,tip:'Spring tank — classic guitar amp spring character.'}};
  let sz=45,dc=40,pr=15,dm=30,mx=40;
  const ui=document.createElement('div');ui.className='acid-app-ui';
  // Algorithm type buttons
  const typeSec=document.createElement('div');typeSec.className='app-section';
  const typeLbl=document.createElement('span');typeLbl.className='app-section-lbl';typeLbl.textContent='TYPE';
  const typeBtns=document.createElement('div');typeBtns.style.cssText='display:flex;gap:5px;margin-bottom:4px;';
  typeSec.append(typeLbl,typeBtns);
  // Two LARGE hero knobs: size + decay
  const heroSec=document.createElement('div');heroSec.className='app-section';
  const heroLbl=document.createElement('span');heroLbl.className='app-section-lbl';heroLbl.textContent='SPACE';
  const heroRow=document.createElement('div');heroRow.style.cssText='display:flex;gap:12px;justify-content:center;padding:4px 0;';
  function rvUpdate(){const r=APP_BUSES[winId]?._rev;if(!r||!ac)return;r.conv.buffer=makeImpulse(ac,sz/100*5+0.3,dc/100*5+0.5);r.pre.delayTime.value=pr/1000;r.damp.frequency.value=500+(1-dm/100)*15500;r.wet.gain.value=mx/100;r.dry.gain.value=1-mx/100;}
  const kSz=makeKnob({label:'SIZE',min:1,max:100,value:sz,unit:'%',size:'lg',tip:'Room size — controls the physical dimension of the simulated space',onChange:v=>{sz=v;rvUpdate();}});
  const kDc=makeKnob({label:'DECAY',min:1,max:100,value:dc,unit:'%',size:'lg',tip:'Decay time — how long reflections ring before fading to silence',onChange:v=>{dc=v;rvUpdate();}});
  heroRow.append(kSz,kDc);heroSec.append(heroLbl,heroRow);
  // Pre-delay stepper + damp/wet sliders
  const detailSec=document.createElement('div');detailSec.className='app-section';
  const PR_STEPS=[{label:'0 ms',value:0},{label:'8 ms',value:8},{label:'16 ms',value:16},{label:'32 ms',value:32},{label:'64 ms',value:64}];
  const prStep=makeStepper({label:'PRE-DELAY',steps:PR_STEPS,index:2,tip:'Pre-delay — gap before first reflections arrive. Creates space between dry signal and reverb.',onChange:v=>{pr=v;rvUpdate();}});
  const sDm=makeSlider({label:'DAMP',min:0,max:100,value:dm,unit:'%',tip:'Dampening — absorbs high frequencies, making the reverb darker and less bright.',onChange:v=>{dm=v;rvUpdate();}});
  const sMx=makeSlider({label:'WET',min:0,max:100,value:mx,unit:'%',tip:'Wet level — how much reverb is mixed into the output.',onChange:v=>{mx=v;rvUpdate();}});
  detailSec.append(prStep,sDm,sMx);
  ui.append(typeSec,heroSec,detailSec);wb.appendChild(ui);
  Object.entries(RV_TYPES).forEach(([key,t])=>{
    const btn=document.createElement('button');btn.className='seg-btn';btn.textContent=key.toUpperCase();btn.dataset.tip=t.tip;
    btn.addEventListener('click',()=>{typeBtns.querySelectorAll('.seg-btn').forEach(b=>b.classList.remove('active'));btn.classList.add('active');sz=t.sz;dc=t.dc;pr=t.pr;dm=t.dm;kSz._update(sz);kDc._update(dc);prStep._set(PR_STEPS.findIndex(s=>s.value===t.pr)||0);sDm._update(dm);});
    typeBtns.appendChild(btn);
  });
  typeBtns.querySelector('.seg-btn').classList.add('active');
};

APP_FACTORIES['win-eq'] = function setupEQUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const BANDS=[
    {lbl:'LOW',freq:80,tip:'Bass shelf — boost or cut below 80 Hz.'},
    {lbl:'LO-MID',freq:250,tip:'Low-mid peak — muddy or warm range around 250 Hz.'},
    {lbl:'MID',freq:1000,tip:'Midrange peak — presence and boxiness around 1 kHz.'},
    {lbl:'HI-MID',freq:4000,tip:'High-mid peak — attack and clarity around 4 kHz.'},
    {lbl:'HIGH',freq:12000,tip:'Treble shelf — boost or cut above 12 kHz.'},
  ];
  const gains=[0,0,0,0,0];
  const ui=document.createElement('div');ui.className='acid-app-ui';
  // Live EQ curve canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#050408;border-radius:6px;padding:4px;margin-bottom:8px;';
  const canvas=document.createElement('canvas');canvas.height=52;canvas.style.cssText='width:100%;display:block;border-radius:4px;';cvWrap.appendChild(canvas);
  const FREQS=[80,250,1000,4000,12000];const TYPES=['lowshelf','peaking','peaking','peaking','highshelf'];
  function drawEQ(){
    const {ctx,W,H}=setupCanvas(canvas,300,52);
    ctx.fillStyle='#050408';ctx.fillRect(0,0,W,H);
    ctx.beginPath();ctx.strokeStyle=acidColor(.8);ctx.lineWidth=1.5;
    const logMin=Math.log10(20),logMax=Math.log10(20000);
    for(let x=0;x<W;x++){
      const f=Math.pow(10,logMin+(x/W)*(logMax-logMin));
      let db=0;
      gains.forEach((g,i)=>{
        const f0=FREQS[i],t=TYPES[i];
        if(t==='lowshelf'){const r=f/f0;db+=g*(r<1?1:1/(1+Math.pow(r,3)));}
        else if(t==='highshelf'){const r=f0/f;db+=g*(r<1?1:1/(1+Math.pow(r,3)));}
        else{const bw=f/f0-f0/f;db+=g/(bw*bw*0.8+1);}
      });
      const y=H/2-Math.max(-15,Math.min(15,db))*(H/36);
      if(x===0)ctx.moveTo(x,y);else ctx.lineTo(x,y);
    }
    ctx.stroke();
    ctx.beginPath();ctx.strokeStyle='rgba(255,255,255,.07)';ctx.lineWidth=1;ctx.moveTo(0,H/2);ctx.lineTo(W,H/2);ctx.stroke();
  }
  ui.appendChild(cvWrap);
  BANDS.forEach((b,i)=>{
    const sl=makeSlider({label:b.lbl+' '+b.freq+'Hz',min:-15,max:15,value:0,unit:' dB',tip:b.tip,
      format:v=>(v>=0?'+':'')+Math.round(v)+' dB',
      onChange:v=>{gains[i]=v;drawEQ();if(APP_BUSES[winId]?._bands)APP_BUSES[winId]._bands[i].gain.value=v;}});
    ui.appendChild(sl);
  });
  wb.appendChild(ui);
  document.addEventListener('workspace-zoom',drawEQ);new ResizeObserver(()=>{if(canvas.offsetWidth>0)drawEQ();}).observe(canvas);
  drawEQ();
};

APP_FACTORIES['win-delay'] = function setupDelayUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getD=()=>APP_BUSES[winId]?._dly;
  // Time num-drag (big ms display, tempo-sync buttons below)
  const sec1=document.createElement('div');sec1.className='acid-section';
  const l1=document.createElement('span');l1.className='app-section-lbl';l1.textContent='ECHO TIME';
  const timeDrag=makeNumDrag({label:'DELAY',unit:' ms',min:1,max:2000,value:500,step:1,tip:'Delay time — how long before the echo is heard. Drag to tune.',onChange:v=>{const d=getD();if(d)d.dly.delayTime.value=v/1000;}});
  const timeDragRow=document.createElement('div');timeDragRow.style.cssText='display:flex;justify-content:center;padding:4px 0 8px;';timeDragRow.appendChild(timeDrag);
  // Tempo sync stepper
  const SYNC_STEPS=[{label:'1/8 note',value:()=>Math.round(60000/tempo/2)},{label:'1/4 note',value:()=>Math.round(60000/tempo)},{label:'1/2 note',value:()=>Math.round(60000/tempo*2)},{label:'1/1 note',value:()=>Math.round(60000/tempo*4)}];
  const syncRow=document.createElement('div');syncRow.style.cssText='display:flex;gap:5px;margin-bottom:6px;';
  [{l:'1/8'},{l:'1/4'},{l:'1/2'},{l:'1/1'}].forEach(({l},idx)=>{
    const btn=document.createElement('button');btn.className='seg-btn';btn.textContent=l;
    btn.dataset.tip=`Snap delay time to ${l} note at current BPM`;
    btn.addEventListener('click',()=>{const ms=Math.min(2000,SYNC_STEPS[idx].value());timeDrag._update(ms);const d=getD();if(d)d.dly.delayTime.value=ms/1000;});
    syncRow.appendChild(btn);
  });
  sec1.append(l1,timeDragRow,syncRow);
  // Feedback large knob + dry/wet sliders + ping-pong toggle
  const sec2=document.createElement('div');sec2.className='acid-section';
  const layout=document.createElement('div');layout.style.cssText='display:flex;gap:14px;align-items:flex-start;justify-content:center;padding:4px 0 8px;';
  const kFb=makeKnob({label:'FEEDBACK',min:0,max:95,value:35,unit:'%',size:'lg',tip:'Feedback — how much echo repeats back. High values = long trails.',onChange:v=>{const d=getD();if(d)d.fb.gain.value=v/100;}});
  const rightSliders=document.createElement('div');rightSliders.style.cssText='flex:1;display:flex;flex-direction:column;gap:6px;';
  const sDry=makeSlider({label:'DRY',min:0,max:100,value:70,unit:'%',tip:'Level of the original dry signal.',onChange:v=>{const d=getD();if(d)d.dry.gain.value=v/100;}});
  const sWet=makeSlider({label:'WET',min:0,max:100,value:40,unit:'%',tip:'Level of the delayed echo.',onChange:v=>{const d=getD();if(d)d.wet.gain.value=v/100;}});
  const tPP=makeToggle({label:'PING-PONG',value:false,tip:'Bounces the echo between left and right channels.',onChange:v=>{const d=getD();if(d?.panner)d.panner.pan.value=v?0.85:0;}});
  rightSliders.append(sDry,sWet,tPP);layout.append(kFb,rightSliders);sec2.appendChild(layout);
  ui.append(sec1,sec2);wb.appendChild(ui);
};

APP_FACTORIES['win-lofi'] = function setupLoFiUI(win){
  const winId=win.id;
  const wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getB=()=>APP_BUSES[winId]?._lofi;
  // Hero canvas — live degrading waveform that reacts to bit depth + rate settings
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#05030a;border-radius:8px;overflow:hidden;margin-bottom:2px;';
  const canvas=document.createElement('canvas');canvas.height=54;canvas.style.cssText='width:100%;display:block;';
  cvWrap.appendChild(canvas);
  // Section 1: Saturation (large drive knob + small warmth knob)
  const sec1=document.createElement('div');sec1.className='acid-section';
  const s1l=document.createElement('span');s1l.className='app-section-lbl';s1l.textContent='SATURATION';
  const kRow=document.createElement('div');kRow.style.cssText='display:flex;gap:12px;justify-content:center;align-items:flex-start;padding:4px 0 6px;';
  const kDrive=makeKnob({label:'DRIVE',min:0,max:95,value:0,unit:'%',size:'lg',
    tip:'Soft saturation/overdrive applied before bit-crushing. Adds warmth and harmonic grit.',
    onChange:v=>{const b=getB();if(b&&b.drive)b.drive.curve=b.makeDriveCurve(v/100);}});
  const kWarm=makeKnob({label:'WARMTH',min:0,max:100,value:0,unit:'%',size:'sm',
    tip:'Low-pass warmth filter — rolls off harsh digital highs.',onChange:updateLoFi});
  kRow.append(kDrive,kWarm);sec1.append(s1l,kRow);
  // Section 2: Digital crush (bit depth num-drag + rate stepper)
  const sec2=document.createElement('div');sec2.className='acid-section';
  const s2l=document.createElement('span');s2l.className='app-section-lbl';s2l.textContent='DIGITAL CRUSH';
  const crushRow=document.createElement('div');crushRow.style.cssText='display:flex;gap:14px;align-items:flex-start;justify-content:center;padding:6px 0;';
  const bitsND=makeNumDrag({label:'BIT DEPTH',unit:' BIT',min:4,max:16,value:16,step:1,decimals:0,
    format:v=>Math.round(v),tip:'Bit depth — lower values create harsh digital distortion. 16 bit is clean, 4 bit is crunchy.',onChange:updateLoFi});
  crushRow.appendChild(bitsND);
  const RATE_STEPS=[{label:'OFF',value:1},{label:'½',value:2},{label:'¼',value:4},{label:'⅛',value:8},{label:'1/16',value:16},{label:'1/32',value:32}];
  const rateStep=makeStepper({label:'RATE CRUSH',steps:RATE_STEPS,index:0,
    tip:'Sample rate reduction — skips samples to create aliased, metallic texture.',onChange:updateLoFi});
  sec2.append(s2l,crushRow,rateStep);
  function updateLoFi(){
    const b=getB();if(!b)return;
    b.crusher.curve=b.makeCrushCurve(Math.round(bitsND._val()));
    const rate=rateStep._val(),warm=kWarm._val();
    const wfFreq=20000-(warm/100)*17000;
    b.warmth.frequency.value=rate<=1?Math.max(wfFreq,200):Math.min(wfFreq,20000/rate);
  }
  ui.append(cvWrap,sec1,sec2);wb.appendChild(ui);
  let lfPhase=0;
  (function drawLF(){
    requestAnimationFrame(drawLF);if(!win.classList.contains('open'))return;
    const bits=Math.max(1,Math.round(bitsND._val())),rate=Math.max(1,Math.round(rateStep._val())),drive=kDrive._val()/100;
    const {ctx:ctx2,W,H}=setupCanvas(canvas,280,54);
    ctx2.fillStyle='rgba(5,3,10,.92)';ctx2.fillRect(0,0,W,H);
    ctx2.beginPath();ctx2.strokeStyle=acidColor(.85);ctx2.lineWidth=1.5;
    const steps=Math.pow(2,bits);const crush=v=>Math.round(v*steps)/steps;
    let last=0;
    for(let i=0;i<W;i++){
      let v=Math.sin(i/W*Math.PI*10+lfPhase)*0.6+Math.sin(i/W*Math.PI*4.3+lfPhase*0.5)*0.3;
      v=Math.tanh(v*(1+drive*5));
      if(i%rate===0)last=crush(v);
      const y=H/2-last*H*0.42;
      i===0?ctx2.moveTo(i,y):ctx2.lineTo(i,y);
    }
    ctx2.stroke();
    if(bits<=10){const na=(16-bits)/16;for(let n=0;n<W*na*0.4;n++){ctx2.fillStyle=acidColor(Math.random()*0.22*na);ctx2.fillRect(~~(Math.random()*W),~~(Math.random()*H),1,1);}}
    lfPhase+=0.05;
  })();
  updateLoFi();
};

APP_FACTORIES['win-gate'] = function setupGateUI(win){
  const winId=win.id;
  const wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getG=()=>APP_BUSES[winId]?._gate;
  // Hero section: segmented level meter canvas + LED + threshold num-drag
  const sec1=document.createElement('div');sec1.className='acid-section';
  const s1l=document.createElement('span');s1l.className='app-section-lbl';s1l.textContent='SIGNAL LEVEL';
  const meterRow=document.createElement('div');meterRow.style.cssText='display:flex;gap:12px;align-items:flex-start;justify-content:center;padding:6px 0;';
  const meterWrap=document.createElement('div');meterWrap.style.cssText='display:flex;flex-direction:column;align-items:center;gap:5px;';
  const meterCv=document.createElement('canvas');meterCv.width=22;meterCv.height=90;meterCv.style.cssText='border-radius:4px;display:block;';
  const led=document.createElement('div');led.style.cssText='width:10px;height:10px;border-radius:50%;background:#303030;transition:background .08s;box-shadow:0 0 6px #303030;';
  const ledLbl=document.createElement('span');ledLbl.style.cssText='font-size:6px;letter-spacing:1.5px;color:rgba(255,255,255,.28);text-transform:uppercase;';ledLbl.textContent='OPEN';
  meterWrap.append(meterCv,led,ledLbl);
  const thrND=makeNumDrag({label:'THRESHOLD',unit:' dB',min:-80,max:0,value:-40,step:1,decimals:0,
    format:v=>v<0?'−'+Math.abs(Math.round(v)):Math.round(v),
    tip:'Signal level below which the gate closes, cutting the audio.'});
  meterRow.append(meterWrap,thrND);sec1.append(s1l,meterRow);
  // Envelope section: attack/release steppers + hold slider
  const sec2=document.createElement('div');sec2.className='acid-section';
  const s2l=document.createElement('span');s2l.className='app-section-lbl';s2l.textContent='ENVELOPE';
  const ATK_STEPS=[{label:'1 ms',value:1},{label:'5 ms',value:5},{label:'10 ms',value:10},{label:'20 ms',value:20},{label:'50 ms',value:50}];
  const REL_STEPS=[{label:'50 ms',value:50},{label:'100 ms',value:100},{label:'200 ms',value:200},{label:'500 ms',value:500},{label:'1 s',value:1000},{label:'2 s',value:2000}];
  const atkStep=makeStepper({label:'ATTACK',steps:ATK_STEPS,index:1,tip:'How fast the gate opens when signal rises above threshold.'});
  const relStep=makeStepper({label:'RELEASE',steps:REL_STEPS,index:2,tip:'How fast the gate closes when signal falls below threshold.'});
  const sHold=makeSlider({label:'HOLD',min:0,max:500,value:0,unit:' ms',tip:'Hold time — gate stays open for this duration after signal drops below threshold. Prevents rapid chatter.',onChange:()=>{}});
  sec2.append(s2l,atkStep,relStep,sHold);
  ui.append(sec1,sec2);wb.appendChild(ui);
  // Gate loop — reads analyser, drives meter canvas + LED + gain
  let gateOpen=false,holdUntil=0,smoothLevel=-80;
  function gateLoop(){
    if(!win.isConnected)return;
    requestAnimationFrame(gateLoop);
    const {ctx:mCtx,W,H}=setupCanvas(meterCv,22,90);
    const g=getG();
    mCtx.fillStyle='#050505';mCtx.fillRect(0,0,W,H);
    if(!g)return;
    const data=new Uint8Array(g.analyser.frequencyBinCount);
    g.analyser.getByteFrequencyData(data);
    let sum=0;for(let i=0;i<data.length;i++)sum+=data[i];
    const dbRaw=-80+(sum/data.length/255)*80;
    smoothLevel+=(dbRaw-smoothLevel)*0.2;
    const thrV=thrND._val();
    const aboveThr=dbRaw>=thrV;
    const now=performance.now();
    if(aboveThr)holdUntil=now+sHold._val();
    const shouldOpen=aboveThr||(now<holdUntil);
    if(shouldOpen!==gateOpen){
      gateOpen=shouldOpen;
      const atk=atkStep._val()/1000,rel=relStep._val()/1000;
      g.gateGain.gain.setTargetAtTime(gateOpen?1:0,ac.currentTime,gateOpen?atk/3:rel/3);
      led.style.background=gateOpen?'var(--acid)':'#303030';
      led.style.boxShadow=gateOpen?'0 0 8px var(--acid-glow)':'0 0 6px #303030';
    }
    // Segmented meter
    const levelFrac=Math.max(0,Math.min(1,(smoothLevel+80)/80));
    const thrFrac=Math.max(0,Math.min(1,(thrV+80)/80));
    for(let y=H-4;y>0;y-=6){
      const frac=1-(y/H);
      const lit=frac<=levelFrac;
      mCtx.fillStyle=lit?(gateOpen?acidColor(.9):'rgba(90,90,90,.8)'):'rgba(255,255,255,.05)';
      mCtx.fillRect(2,y,W-4,4);
    }
    // Threshold line in red
    const thrY=H-(thrFrac*H);
    mCtx.fillStyle='rgba(255,70,70,.95)';mCtx.fillRect(0,thrY,W,2);
  }
  gateLoop();
};

APP_FACTORIES['win-vol'] = function setupVolUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='VOLUME';
  const faderRow=document.createElement('div');faderRow.style.cssText='display:flex;justify-content:center;padding:10px 0 4px;';
  const fader=makeVertFader({label:'GAIN',min:0,max:100,value:80,unit:'%',height:130,
    tip:'Volume level of the signal passing through.',
    onChange:v=>{const b=APP_BUSES[winId];if(b&&b._vol)b._vol.gain.setTargetAtTime(v/100,ac?ac.currentTime:0,0.01);}});
  faderRow.appendChild(fader);sec.append(lbl,faderRow);ui.appendChild(sec);wb.appendChild(ui);
};

APP_FACTORIES['win-pan'] = function setupPanUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='STEREO PAN';
  // Arc canvas display
  const canvas=document.createElement('canvas');canvas.height=70;canvas.style.cssText='width:100%;display:block;margin-bottom:10px;cursor:pointer;border-radius:8px;';
  let panVal=0;
  function drawArc(v){
    const {ctx,W,H}=setupCanvas(canvas,220,70);
    ctx.clearRect(0,0,W,H);
    const cx=W/2,cy=H,r=Math.min(H-8,W/2-12);
    ctx.beginPath();ctx.arc(cx,cy,r,Math.PI,0,false);ctx.strokeStyle='rgba(255,255,255,.07)';ctx.lineWidth=8;ctx.stroke();
    const norm=(v+100)/200;
    const sAng=Math.PI,eAng=Math.PI+norm*Math.PI;
    ctx.beginPath();ctx.arc(cx,cy,r,sAng,eAng,false);ctx.strokeStyle=acidColor(.85);ctx.lineWidth=8;ctx.lineCap='round';ctx.stroke();
    const ang=Math.PI+norm*Math.PI;
    ctx.beginPath();ctx.arc(cx+Math.cos(ang)*r,cy+Math.sin(ang)*r,5,0,Math.PI*2);ctx.fillStyle='#fff';ctx.fill();
    ctx.font='8px monospace';ctx.fillStyle='rgba(255,255,255,.3)';ctx.textAlign='left';ctx.fillText('L',6,H-6);
    ctx.textAlign='right';ctx.fillText('R',W-6,H-6);
    ctx.textAlign='center';
    const tag=v===0?'CENTER':v<0?Math.abs(v)+'L':v+'R';
    ctx.font='bold 13px inherit';ctx.fillStyle='rgba(255,255,255,.85)';ctx.fillText(tag,cx,cy-r*0.45);
  }
  const getB=()=>APP_BUSES[winId];
  const sl=makeSlider({label:'PAN',min:-100,max:100,value:0,unit:'',
    format:v=>v===0?'CENTER':v<0?Math.abs(Math.round(v))+'L':Math.round(v)+'R',
    tip:'Stereo panning — positions the signal in the stereo field',
    onChange:v=>{panVal=v;drawArc(v);const b=getB();if(b&&b._panner)b._panner.pan.setTargetAtTime(v/100,ac?ac.currentTime:0,0.01);}});
  canvas.addEventListener('click',e=>{const r=canvas.getBoundingClientRect();const x=e.clientX-r.left;sl._update(Math.round(Math.max(-100,Math.min(100,(x/r.width)*200-100))));});
  sec.append(lbl,canvas,sl);ui.appendChild(sec);wb.appendChild(ui);
  document.addEventListener('workspace-zoom',()=>drawArc(panVal));
  new ResizeObserver(()=>{if(canvas.offsetWidth>0)drawArc(panVal);}).observe(canvas);
  drawArc(0);
};

APP_FACTORIES['win-chorus'] = function setupChorusUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='CHORUS';
  const getB=()=>APP_BUSES[winId]?._chorus;
  // Large rate knob is the creative heart; depth+wet as sliders; spread as stepper
  const kRate=makeKnob({label:'RATE',min:0.1,max:8,value:0.8,unit:' Hz',decimals:1,size:'lg',tip:'LFO rate — how fast the pitch wobbles. Slow is lush, fast is vibrato.',onChange:v=>{const b=getB();if(b){b.l1.frequency.value=v;b.l2.frequency.value=v*1.3;}}});
  const rateRow=document.createElement('div');rateRow.style.cssText='display:flex;justify-content:center;padding:4px 0 8px;';rateRow.appendChild(kRate);
  const sDepth=makeSlider({label:'DEPTH',min:0,max:20,value:5,unit:' ms',tip:'Depth — how wide the pitch wobble is.',onChange:v=>{const b=getB();if(b){b.lg1.gain.value=v/1000;b.lg2.gain.value=v/1000;}}});
  const sWet=makeSlider({label:'WET',min:0,max:100,value:40,unit:'%',tip:'Wet mix — how much chorused signal is blended in.',onChange:v=>{const b=getB();if(b){b.w1.gain.value=v/100*0.5;b.w2.gain.value=v/100*0.5;b.dry.gain.value=1-v/100*0.6;}}});
  const SPREADS=[{label:'0 ms',value:0},{label:'5 ms',value:5},{label:'10 ms',value:10},{label:'20 ms',value:20},{label:'30 ms',value:30}];
  const spreadStep=makeStepper({label:'SPREAD',steps:SPREADS,index:2,tip:'Voice spread — stagger between the two chorus voices for wider stereo.',onChange:v=>{const b=getB();if(b){b.d1.delayTime.value=0.01+v/1000;b.d2.delayTime.value=0.01+v/1000*1.5;}}});
  sec.append(lbl,rateRow,sDepth,sWet,spreadStep);ui.appendChild(sec);wb.appendChild(ui);
};

APP_FACTORIES['win-tremolo'] = function setupTremoloUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='TREMOLO';
  const getB=()=>APP_BUSES[winId]?._tremolo;
  // Animated rate indicator canvas + large rate knob
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:rgba(0,0,0,.3);border-radius:6px;padding:4px;margin-bottom:8px;';
  const cv=document.createElement('canvas');cv.height=32;cv.style.cssText='width:100%;display:block;border-radius:4px;';cvWrap.appendChild(cv);
  let rateVal=4,depthVal=60,phase=0;
  function drawTrem(){
    const {ctx,W,H}=setupCanvas(cv,220,32);
    ctx.fillStyle='rgba(0,0,0,.8)';ctx.fillRect(0,0,W,H);
    ctx.beginPath();ctx.strokeStyle=acidColor(.7);ctx.lineWidth=1.5;
    for(let x=0;x<W;x++){const t=x/W;const y=H/2-(Math.sin(t*Math.PI*8)*depthVal/200)*H*0.45;if(x===0)ctx.moveTo(x,y);else ctx.lineTo(x,y);}
    ctx.stroke();
  }
  document.addEventListener('workspace-zoom',drawTrem);new ResizeObserver(()=>{if(cv.offsetWidth>0)drawTrem();}).observe(cv);
  // Large rate knob + depth vertical fader side by side
  const layout=document.createElement('div');layout.style.cssText='display:flex;gap:12px;align-items:flex-start;justify-content:center;padding:4px 0 8px;';
  const kRate=makeKnob({label:'RATE',min:0.1,max:20,value:4,unit:' Hz',decimals:1,size:'lg',tip:'Tremolo rate — speed of the volume oscillation.',onChange:v=>{rateVal=v;drawTrem();const b=getB();if(b)b.lfo.frequency.value=v;}});
  const depthFader=makeVertFader({label:'DEPTH',min:0,max:100,value:60,unit:'%',height:80,tip:'Depth — how much the volume drops at the lowest point.',onChange:v=>{depthVal=v;drawTrem();const b=getB();if(b){b.lg.gain.value=v/200;b.dcg.gain.value=1-v/200;}}});
  layout.append(kRate,depthFader);
  // Wave picker
  const sec2=document.createElement('div');sec2.className='acid-section';
  const l2=document.createElement('span');l2.className='app-section-lbl';l2.textContent='SHAPE';
  const wPicker=makeWavePicker({waves:['sine','square','triangle'],value:'sine',tip:'LFO shape — sine fades smoothly, square is abrupt, triangle is linear.',onChange:w=>{const b=getB();if(b)b.lfo.type=w;}});
  sec2.append(l2,wPicker);
  sec.append(lbl,cvWrap,layout);ui.append(sec,sec2);wb.appendChild(ui);
  drawTrem();
};

APP_FACTORIES['win-phaser'] = function setupPhaserUI(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='PHASER';
  const getB=()=>APP_BUSES[winId]?._phaser;
  // XY pad: X = center freq, Y = sweep range — the most expressive way to control a phaser
  const xyPad=makeXYPad({labelX:'CENTER',labelY:'SWEEP',minX:200,maxX:4000,minY:50,maxY:2000,valueX:800,valueY:600,
    tip:'X axis sets center frequency of the phase shift. Y axis sets the sweep range width.',
    onChange:(x,y)=>{const b=getB();if(b){b.dc.offset.value=x;b.lg.gain.value=y;}}});
  // Rate stepper with musical labels
  const RATES=[{label:'SLOW  0.05Hz',value:0.05},{label:'MED  0.5Hz',value:0.5},{label:'FAST  2Hz',value:2},{label:'SPIN  4Hz',value:4}];
  const rateStep=makeStepper({label:'RATE',steps:RATES,index:1,tip:'LFO speed — how fast the phase sweeps.',onChange:v=>{const b=getB();if(b)b.lfo.frequency.value=v;}});
  const sWet=makeSlider({label:'WET',min:0,max:100,value:50,unit:'%',tip:'How much phased signal is blended in.',onChange:v=>{const b=getB();if(b){b.wet.gain.value=v/100;b.dry.gain.value=1-v/200;}}});
  sec.append(lbl,xyPad,rateStep,sWet);ui.appendChild(sec);wb.appendChild(ui);
};

// --- TONE factory
APP_FACTORIES['win-tone'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getB=()=>APP_BUSES[winId];
  const params={freq:440,vol:70,detune:0,wave:'sine'};
  let osc=null,gainNode=null;
  // Hero: large frequency num-drag
  const sec1=document.createElement('div');sec1.className='acid-section';
  const l1=document.createElement('span');l1.className='app-section-lbl';l1.textContent='TONE GEN';
  const freqRow=document.createElement('div');freqRow.style.cssText='display:flex;justify-content:center;padding:6px 0;';
  const freqDrag=makeNumDrag({label:'FREQUENCY',unit:' Hz',min:20,max:8000,value:440,step:1,
    tip:'Frequency — drag up/down to tune the oscillator. Dbl-click to type.',
    onChange:v=>{params.freq=v;if(osc)osc.frequency.value=v;}});
  freqRow.appendChild(freqDrag);
  sec1.append(l1,freqRow);
  // Level fader + detune slider
  const sec2=document.createElement('div');sec2.className='acid-section';
  const levelRow=document.createElement('div');levelRow.style.cssText='display:flex;gap:12px;align-items:flex-start;padding:4px 0 8px;';
  const levelFader=makeVertFader({label:'LEVEL',min:0,max:100,value:70,unit:'%',height:80,tip:'Output level.',onChange:v=>{params.vol=v;if(gainNode)gainNode.gain.value=v/100;}});
  const detuneSlider=makeSlider({label:'DETUNE',min:-50,max:50,value:0,unit:' ct',tip:'Fine pitch offset in cents (100 cents = 1 semitone).',onChange:v=>{params.detune=v;if(osc)osc.detune.value=v;}});
  const rightCol=document.createElement('div');rightCol.style.cssText='flex:1;display:flex;flex-direction:column;gap:8px;';rightCol.appendChild(detuneSlider);
  levelRow.append(levelFader,rightCol);sec2.appendChild(levelRow);
  // Waveform + play button
  const sec3=document.createElement('div');sec3.className='app-section';
  const l3=document.createElement('span');l3.className='app-section-lbl';l3.textContent='WAVEFORM';
  const wPicker=makeWavePicker({waves:['sine','square','sawtooth','triangle'],value:'sine',tip:'Waveform shape.',onChange:w=>{params.wave=w;if(osc)osc.type=w;}});
  const playBtn=document.createElement('button');playBtn.className='seg-btn';playBtn.textContent='START';playBtn.style.cssText='width:100%;padding:9px;font-size:11px;margin-top:8px;';
  sec3.append(l3,wPicker,playBtn);
  ui.append(sec1,sec2,sec3);wb.appendChild(ui);
  playBtn.addEventListener('click',()=>{
    ensureAudio();
    if(osc){try{osc.stop();}catch(_){}osc=null;gainNode=null;playBtn.textContent='START';playBtn.classList.remove('active');return;}
    gainNode=ac.createGain();gainNode.gain.value=params.vol/100;
    osc=ac.createOscillator();osc.type=params.wave;osc.frequency.value=params.freq;osc.detune.value=params.detune;
    const b=getB();osc.connect(gainNode);gainNode.connect(b?b.output:drySum);osc.start();
    playBtn.textContent='STOP';playBtn.classList.add('active');
    osc.onended=()=>{playBtn.textContent='START';playBtn.classList.remove('active');osc=null;gainNode=null;};
  });
};

// --- LFO factory
APP_FACTORIES['win-lfo'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec1=document.createElement('div');sec1.className='acid-section';
  const l1=document.createElement('span');l1.className='app-section-lbl';l1.textContent='LFO';
  let osc=null,gainNode=null;
  const getB=()=>APP_BUSES[winId];
  let p={rate:2,depth:0.5,wave:'sine'};
  function startLFO(rate,depth,wave){
    ensureAudio();const b=getB();if(!b)return;
    if(osc){try{osc.stop();}catch(_){}osc=null;}
    if(gainNode){try{gainNode.disconnect();}catch(_){}gainNode=null;}
    osc=ac.createOscillator();osc.type=wave;osc.frequency.value=rate;
    gainNode=ac.createGain();gainNode.gain.value=depth;
    osc.connect(gainNode);gainNode.connect(b.output);osc.start();
  }
  // Live LFO display canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:rgba(0,0,0,.25);border-radius:6px;padding:4px;margin-bottom:8px;';
  const cv=document.createElement('canvas');cv.height=36;cv.style.cssText='width:100%;display:block;border-radius:4px;';cvWrap.appendChild(cv);
  let animPhase=0;
  (function drawLFO(){
    requestAnimationFrame(drawLFO);
    if(!win.classList.contains('open'))return;
    const {ctx,W,H}=setupCanvas(cv,200,36);
    ctx.fillStyle='rgba(0,0,0,.75)';ctx.fillRect(0,0,W,H);
    animPhase=(animPhase+p.rate*0.03)%(Math.PI*2);
    ctx.beginPath();ctx.strokeStyle=acidColor(.75);ctx.lineWidth=1.5;
    for(let x=0;x<W;x++){
      const t=x/W*Math.PI*4+animPhase;
      let y;
      if(p.wave==='sine')y=Math.sin(t);
      else if(p.wave==='square')y=Math.sign(Math.sin(t));
      else if(p.wave==='sawtooth')y=((t%(Math.PI*2))/(Math.PI))-1;
      else y=Math.abs(((t%(Math.PI*2))/(Math.PI))-1)*2-1;
      const py=H/2-y*p.depth*(H/2-3);
      if(x===0)ctx.moveTo(x,py);else ctx.lineTo(x,py);
    }
    ctx.stroke();
  })();
  // Rate num-drag (big, draggable Hz display)
  const rateRow=document.createElement('div');rateRow.style.cssText='display:flex;gap:12px;align-items:flex-start;justify-content:center;padding:4px 0 6px;';
  const rateDrag=makeNumDrag({label:'RATE',unit:' Hz',min:0.01,max:30,value:2,step:0.1,decimals:2,tip:'LFO rate — drag up to go faster.',onChange:v=>{p.rate=v;startLFO(p.rate,p.depth,p.wave);}});
  const depthFader=makeVertFader({label:'DEPTH',min:0,max:100,value:50,unit:'%',height:80,tip:'LFO depth — how strong the modulation output signal is.',onChange:v=>{p.depth=v/100;startLFO(p.rate,p.depth,p.wave);}});
  rateRow.append(rateDrag,depthFader);
  const sec2=document.createElement('div');sec2.className='acid-section';
  const l2=document.createElement('span');l2.className='app-section-lbl';l2.textContent='SHAPE';
  const wPicker=makeWavePicker({waves:['sine','square','sawtooth','triangle'],value:'sine',tip:'LFO waveform shape.',onChange:w=>{p.wave=w;startLFO(p.rate,p.depth,p.wave);}});
  sec2.append(l2,wPicker);
  sec1.append(l1,cvWrap,rateRow);ui.append(sec1,sec2);wb.appendChild(ui);
  startLFO(p.rate,p.depth,p.wave);
};

// --- SCOPE factory
APP_FACTORIES['win-scope'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  wb.innerHTML=`<div class="app-ui"><canvas class="scope-cv" height="120" style="width:100%;display:block;border-radius:6px;background:#020812"></canvas></div>`;
  const canvas=wb.querySelector('.scope-cv');
  const getB=()=>APP_BUSES[winId];
  (function draw(){
    requestAnimationFrame(draw);const b=getB();if(!b?._scopeAnalyser)return;
    const a=b._scopeAnalyser,buf=new Float32Array(a.fftSize);a.getFloatTimeDomainData(buf);
    const {ctx:ctx2,W,H}=setupCanvas(canvas,380,120);
    ctx2.fillStyle='rgba(2,8,18,.85)';ctx2.fillRect(0,0,W,H);
    ctx2.beginPath();ctx2.strokeStyle='rgba(50,220,255,.9)';ctx2.lineWidth=1.5;
    for(let i=0;i<buf.length;i++){const x=i/buf.length*W,y=(1-buf[i])*.5*H;if(i===0)ctx2.moveTo(x,y);else ctx2.lineTo(x,y);}ctx2.stroke();
  })();
};

// --- SPECTRUM factory
APP_FACTORIES['win-spectrum'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  wb.innerHTML=`<div class="app-ui"><canvas class="spec-cv" height="120" style="width:100%;display:block;border-radius:6px;background:#040210"></canvas></div>`;
  const canvas=wb.querySelector('.spec-cv');
  const BARS=48;const peaks=Array.from({length:BARS},()=>0);
  const getB=()=>APP_BUSES[winId];
  (function draw(){
    requestAnimationFrame(draw);const b=getB();if(!b?._analyser)return;
    const a=b._analyser;const fd=new Uint8Array(a.frequencyBinCount);a.getByteFrequencyData(fd);
    const {ctx:ctx2,W,H}=setupCanvas(canvas,380,120);
    ctx2.fillStyle='rgba(4,2,16,.85)';ctx2.fillRect(0,0,W,H);
    const bw=W/BARS-1;
    for(let i=0;i<BARS;i++){
      const idx=Math.floor(i/BARS*fd.length),val=fd[idx]/255;
      peaks[i]=Math.max(peaks[i]*.97,val);
      const bh=val*H;const ph=peaks[i]*H;
      ctx2.fillStyle=`rgba(${100+Math.round(val*132)},${Math.round(val*104+32)},32,.9)`;
      ctx2.fillRect(i*(bw+1),H-bh,bw,bh);
      ctx2.fillStyle='rgba(255,200,80,.85)';ctx2.fillRect(i*(bw+1),H-ph-2,bw,2);
    }
  })();
};

// --- MERGE factory
APP_FACTORIES['win-merge'] = function(win){
  const wb=win.querySelector('.wbody');
  wb.innerHTML=`<div class="app-ui"><div class="app-section"><span class="app-section-lbl">4-TO-1 MERGE</span></div>
  <div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;padding:8px 0">
    <div style="text-align:center;font-size:9px;color:var(--acid-a88);letter-spacing:1px">IN 1</div>
    <div style="text-align:center;font-size:9px;color:var(--acid-a88);letter-spacing:1px">IN 2</div>
    <div style="text-align:center;font-size:9px;color:var(--acid-a88);letter-spacing:1px">IN 3</div>
    <div style="text-align:center;font-size:9px;color:var(--acid-a88);letter-spacing:1px">IN 4</div>
  </div>
  <div style="text-align:center;padding:6px;font-size:9px;color:rgba(255,255,255,.25);letter-spacing:1px">→ MIX OUT</div></div>`;
};

// --- CHORD GEN factory
APP_FACTORIES['win-chordgen'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const ROOTS=['C','C#','D','D#','E','F','F#','G','G#','A','A#','B'];
  const TYPES=['maj','min','dim','aug','maj7','min7','dom7','sus4'];
  const SUFFIX={maj:'',min:'m',dim:'°',aug:'+',maj7:'maj7',min7:'m7',dom7:'7',sus4:'sus4'};
  // Chord display section — big name + note bubbles
  const sec1=document.createElement('div');sec1.className='acid-section';
  const s1l=document.createElement('span');s1l.className='app-section-lbl';s1l.textContent='CHORD';
  const chordName=document.createElement('div');
  chordName.style.cssText='font-size:36px;font-weight:700;color:var(--acid);text-align:center;letter-spacing:3px;padding:10px 0 6px;line-height:1;';
  const noteBubbles=document.createElement('div');
  noteBubbles.style.cssText='display:flex;gap:7px;justify-content:center;padding:8px 0 4px;flex-wrap:wrap;';
  sec1.append(s1l,chordName,noteBubbles);
  // Selector section — steppers for root, type, octave
  const sec2=document.createElement('div');sec2.className='acid-section';
  const s2l=document.createElement('span');s2l.className='app-section-lbl';s2l.textContent='SELECTOR';
  const rootStep=makeStepper({label:'ROOT',steps:ROOTS,index:0,tip:'Root note of the chord.',onChange:()=>updateChord()});
  const typeStep=makeStepper({label:'TYPE',steps:TYPES,index:0,tip:'Chord quality and extension.',onChange:()=>updateChord()});
  const octStep=makeStepper({label:'OCTAVE',steps:[2,3,4,5,6],index:2,tip:'Base octave for the chord.'});
  sec2.append(s2l,rootStep,typeStep,octStep);
  // Large strum button
  const strumBtn=document.createElement('button');strumBtn.className='seg-btn';
  strumBtn.textContent='STRUM';
  strumBtn.style.cssText='width:100%;padding:14px;font-size:13px;letter-spacing:5px;margin-top:2px;';
  strumBtn.addEventListener('click',()=>{
    if(typeof CHORDS!=='undefined'&&typeof triggerPoly==='function'){
      const t=ac?.currentTime||0;
      const rn=rootStep._val(),tn=typeStep._val();
      CHORDS[tn]?.forEach(semi=>triggerPoly(`cg-${rn}-${semi}`,rn,semi,t,0.5));
    }
    strumBtn.style.background='var(--acid)';strumBtn.style.color='#0d0a06';
    setTimeout(()=>{strumBtn.style.background='';strumBtn.style.color='';},180);
  });
  function updateChord(){
    const rn=rootStep._val(),tn=typeStep._val();
    chordName.textContent=rn+(SUFFIX[tn]??tn);
    noteBubbles.innerHTML='';
    const ri=ROOTS.indexOf(rn);
    const intervals=typeof CHORDS!=='undefined'?CHORDS[tn]:[0,4,7];
    (intervals||[0,4,7]).forEach(semi=>{
      const ni=(ri+semi)%12;
      const b2=document.createElement('div');
      b2.style.cssText='padding:5px 12px;border-radius:20px;background:var(--acid-a15);border:1px solid var(--acid-a38);color:var(--acid);font-size:11px;letter-spacing:1px;font-weight:700;';
      b2.textContent=ROOTS[ni];noteBubbles.appendChild(b2);
    });
  }
  ui.append(sec1,sec2,strumBtn);wb.appendChild(ui);
  updateChord();
};

// --- GRANULAR factory — XY pad for position+scatter + size stepper + density fader + pitch knob
APP_FACTORIES['win-granular'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec1=document.createElement('div');sec1.className='acid-section';
  const secLbl=document.createElement('span');secLbl.className='app-section-lbl';secLbl.textContent='GRANULAR CLOUD';
  sec1.appendChild(secLbl);
  const getB=()=>APP_BUSES[winId]?._gran;
  // Freeze / Live mode buttons
  const modeRow=document.createElement('div');modeRow.style.cssText='display:flex;gap:6px;margin-bottom:6px;';
  const freezeBtn=document.createElement('button');freezeBtn.className='seg-btn';freezeBtn.textContent='FREEZE';freezeBtn.dataset.tip='Freeze — captures buffer and plays grains from the frozen snapshot.';
  const liveBtn=document.createElement('button');liveBtn.className='seg-btn active';liveBtn.textContent='LIVE';liveBtn.dataset.tip='Live — continuously captures incoming audio into the grain buffer.';
  const revToggle=makeToggle({label:'REVERSE',value:false,tip:'Reverse grains — each grain plays backwards.',onChange:v=>{const b=getB();if(b)b.params.reverse=v;}});
  modeRow.append(freezeBtn,liveBtn);sec1.append(modeRow,revToggle);
  [freezeBtn,liveBtn].forEach(btn=>btn.addEventListener('click',()=>{[freezeBtn,liveBtn].forEach(b=>b.classList.remove('active'));btn.classList.add('active');ensureAudio();const b=getB();if(b)b.params.frozen=(btn===freezeBtn);}));
  // XY pad: X = buffer position, Y = scatter — most expressive way to explore grain space
  const xyPad=makeXYPad({labelX:'POSITION',labelY:'SCATTER',minX:0,maxX:100,minY:0,maxY:100,valueX:50,valueY:25,
    tip:'X axis scrubs through the buffer position. Y axis controls how randomly grains are scattered around that position.',
    onChange:(x,y)=>{const b=getB();if(b){b.params.pos=x/100;b.params.scatter=y/100;}}});
  // Size stepper + density fader + pitch knob
  const SIZES=[{label:'10 ms',value:10},{label:'30 ms',value:30},{label:'80 ms',value:80},{label:'150 ms',value:150},{label:'300 ms',value:300},{label:'500 ms',value:500}];
  const sizeStep=makeStepper({label:'GRAIN SIZE',steps:SIZES,index:2,tip:'Size of each individual grain.',onChange:v=>{const b=getB();if(b)b.params.size=v;}});
  const layout=document.createElement('div');layout.style.cssText='display:flex;gap:12px;align-items:flex-start;justify-content:center;padding:4px 0 4px;';
  const densityFader=makeVertFader({label:'DENSITY',min:1,max:32,value:8,height:80,tip:'Number of simultaneous grains playing.',onChange:v=>{const b=getB();if(b){b.params.density=Math.round(v);}}});
  const kPitch=makeKnob({label:'PITCH',min:25,max:400,value:100,unit:'%',size:'md',tip:'Grain playback speed — above 100% is faster and higher pitched.',onChange:v=>{const b=getB();if(b)b.params.pitch=v/100;}});
  layout.append(densityFader,kPitch);
  // Waveform canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:rgba(0,0,0,.3);border-radius:6px;padding:4px;margin-top:6px;';
  const canvas=document.createElement('canvas');canvas.height=36;canvas.style.cssText='width:100%;display:block;';cvWrap.appendChild(canvas);
  sec1.append(xyPad,sizeStep,layout,cvWrap);ui.appendChild(sec1);wb.appendChild(ui);
  (function drawG(){
    requestAnimationFrame(drawG);const b=getB();if(!b)return;
    const cd=b.capBuf.getChannelData(0),wp=b.writePos();
    const {ctx:ctx2,W,H}=setupCanvas(canvas,320,36);
    ctx2.fillStyle='rgba(0,0,0,.9)';ctx2.fillRect(0,0,W,H);
    ctx2.beginPath();ctx2.strokeStyle=acidColor(.75);ctx2.lineWidth=1;
    for(let i=0;i<W;i++){const idx=Math.floor(i*b.bufLen/W);const v=(cd[idx]||0);const y=(1-v)*.5*H;if(i===0)ctx2.moveTo(i,y);else ctx2.lineTo(i,y);}ctx2.stroke();
    if(!b.params.frozen){ctx2.fillStyle='rgba(255,255,255,.7)';ctx2.fillRect(Math.floor((wp%b.bufLen)/b.bufLen*W),0,2,H);}
    else{ctx2.fillStyle=acidColor(.6);ctx2.fillRect(0,0,W,2);ctx2.fillRect(0,H-2,W,2);}
  })();
};

// --- FLANGER factory
APP_FACTORIES['win-flanger'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='FLANGER';
  const getB=()=>APP_BUSES[winId]?._flanger;
  // Rate stepper (slow sweep values feel more natural than a knob)
  const RATES=[{label:'0.01 Hz',value:0.01},{label:'0.1 Hz',value:0.1},{label:'0.3 Hz',value:0.3},{label:'1 Hz',value:1},{label:'5 Hz',value:5}];
  const rateStep=makeStepper({label:'RATE',steps:RATES,index:2,tip:'LFO sweep rate — how fast the flanger sweeps.',onChange:v=>{const b=getB();if(b)b.lfo.frequency.value=v;}});
  // Large feedback knob is the core tonal shaper
  const kFb=makeKnob({label:'FEEDBACK',min:0,max:95,value:50,unit:'%',size:'lg',tip:'Feedback — higher values create intense, metallic jet-plane sweeps.',onChange:v=>{const b=getB();if(b)b.fb.gain.value=v/100;}});
  const kRow=document.createElement('div');kRow.style.cssText='display:flex;justify-content:center;padding:4px 0 8px;';kRow.appendChild(kFb);
  const sDepth=makeSlider({label:'DEPTH',min:0,max:100,value:40,unit:'%',tip:'LFO depth — how wide the sweep travels.',onChange:v=>{const b=getB();if(b)b.lfoG.gain.value=v*0.0001;}});
  const sMix=makeSlider({label:'MIX',min:0,max:100,value:50,unit:'%',tip:'Dry/wet blend.',onChange:v=>{const b=getB();if(b){b.wet.gain.value=v/100;b.dry.gain.value=1-v/100;}}});
  const secWave=document.createElement('div');secWave.className='app-section';
  const wlbl=document.createElement('span');wlbl.className='acid-section-label';wlbl.textContent='LFO SHAPE';
  const wavePicker=makeWavePicker({waves:['sine','triangle','square','sawtooth'],value:'sine',tip:'LFO waveform shape — changes the character of the sweep.',onChange:w=>{const b=getB();if(b)b.lfo.type=w;}});
  secWave.append(wlbl,wavePicker);
  sec.append(lbl,rateStep,kRow,sDepth,sMix);ui.append(sec,secWave);wb.appendChild(ui);
};

// --- RING MOD factory
APP_FACTORIES['win-ringmod'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getRB=()=>APP_BUSES[winId]?._ring;
  let intOsc=null,carrierFreq=220,carrierWave='sine';
  // Hero canvas — shows live carrier waveform
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#030a06;border-radius:8px;overflow:hidden;margin-bottom:2px;';
  const canvas=document.createElement('canvas');canvas.height=50;canvas.style.cssText='width:100%;display:block;';
  cvWrap.appendChild(canvas);
  // Carrier section
  const sec1=document.createElement('div');sec1.className='acid-section';
  const s1l=document.createElement('span');s1l.className='app-section-lbl';s1l.textContent='CARRIER';
  const hint=document.createElement('div');hint.style.cssText='font-size:9px;color:rgba(255,255,255,.28);margin-bottom:8px;line-height:1.5;';hint.textContent='Wire SRC + MOD ports. Output = SRC × MOD.';
  const ctrlRow=document.createElement('div');ctrlRow.style.cssText='display:flex;gap:12px;align-items:flex-start;justify-content:center;padding:4px 0 8px;';
  const freqND=makeNumDrag({label:'FREQUENCY',unit:' Hz',min:20,max:4000,value:220,step:5,decimals:0,
    tip:'Carrier oscillator frequency — sets the pitch of the ring modulation effect.',
    onChange:v=>{carrierFreq=v;if(intOsc)intOsc.frequency.value=v;}});
  const dryFader=makeVertFader({label:'DRY',min:0,max:100,value:30,unit:'%',height:80,
    tip:'Dry signal amount mixed with the ring-modulated output.',
    onChange:v=>{const rb=getRB();if(rb)rb.dry.gain.value=v/100;}});
  ctrlRow.append(freqND,dryFader);
  // Wave section
  const sec2=document.createElement('div');sec2.className='acid-section';
  const s2l=document.createElement('span');s2l.className='app-section-lbl';s2l.textContent='CARRIER WAVE';
  const wavePicker=makeWavePicker({waves:['sine','square','sawtooth','triangle'],value:'sine',
    tip:'Carrier waveform shape — changes the character of the ring mod effect.',
    onChange:w=>{
      carrierWave=w;ensureAudio();const rb=getRB();if(!rb)return;
      if(intOsc){try{intOsc.stop();}catch(_){}intOsc=null;}
      intOsc=ac.createOscillator();intOsc.type=w;intOsc.frequency.value=carrierFreq;
      intOsc.connect(rb.ringGain.gain);intOsc.start();
    }
  });
  const offBtn=document.createElement('button');offBtn.className='seg-btn';offBtn.textContent='CARRIER OFF';offBtn.style.cssText='width:100%;margin-top:6px;';
  offBtn.addEventListener('click',()=>{
    if(intOsc){try{intOsc.stop();}catch(_){}intOsc=null;}
    const rb=getRB();if(rb){rb.ringGain.gain.cancelScheduledValues(ac.currentTime);rb.ringGain.gain.value=0;}
  });
  sec2.append(s2l,wavePicker,offBtn);
  sec1.append(s1l,hint,ctrlRow);
  ui.append(cvWrap,sec1,sec2);wb.appendChild(ui);
  // Carrier waveform animation
  let rmPhase=0;
  (function drawRM(){
    requestAnimationFrame(drawRM);if(!win.classList.contains('open'))return;
    const {ctx:ctx2,W,H}=setupCanvas(canvas,280,50);
    ctx2.fillStyle='rgba(3,10,6,.9)';ctx2.fillRect(0,0,W,H);
    if(!intOsc){
      ctx2.fillStyle='rgba(255,255,255,.1)';ctx2.font='8px monospace';ctx2.textAlign='center';ctx2.fillText('CARRIER OFF',W/2,H/2+3);return;
    }
    ctx2.beginPath();ctx2.strokeStyle=acidColor(.85);ctx2.lineWidth=1.5;
    const cycles=Math.min(8,Math.max(1,carrierFreq/80));
    for(let i=0;i<W;i++){
      const t=(i/W)*cycles*Math.PI*2+rmPhase;
      let v=carrierWave==='sine'?Math.sin(t):carrierWave==='square'?Math.sign(Math.sin(t)):carrierWave==='sawtooth'?((t/(Math.PI*2))%1)*2-1:Math.asin(Math.sin(t))/(Math.PI/2);
      const y=H/2-v*H*0.38;
      i===0?ctx2.moveTo(i,y):ctx2.lineTo(i,y);
    }
    ctx2.stroke();rmPhase+=0.06;
  })();
  // Start carrier
  setTimeout(()=>{
    ensureAudio();const rb=getRB();if(!rb)return;
    if(intOsc){try{intOsc.stop();}catch(_){}intOsc=null;}
    intOsc=ac.createOscillator();intOsc.type='sine';intOsc.frequency.value=220;
    intOsc.connect(rb.ringGain.gain);intOsc.start();
  },50);
  win._stopAudio=()=>{if(intOsc){try{intOsc.stop();}catch(_){}intOsc=null;}};
};

// --- AUTO-FILTER factory — base freq num-drag + large mod knob + attack/release steppers + Q knob
APP_FACTORIES['win-autofilter'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getB=()=>APP_BUSES[winId]?._af;
  // Canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#020812;border-radius:6px;padding:4px;margin-bottom:6px;';
  const canvas=document.createElement('canvas');canvas.height=50;canvas.style.cssText='width:100%;display:block;border-radius:4px;';cvWrap.appendChild(canvas);
  // Section
  const kSec=document.createElement('div');kSec.className='app-section';
  const kLbl=document.createElement('span');kLbl.className='app-section-lbl';kLbl.textContent='AUTO-FILTER';
  // Base freq num-drag + large mod knob
  const topRow=document.createElement('div');topRow.style.cssText='display:flex;gap:14px;align-items:flex-start;justify-content:center;padding:4px 0 8px;';
  const freqDrag=makeNumDrag({label:'BASE FREQ',unit:' Hz',min:20,max:8000,value:800,step:10,tip:'Base cutoff frequency — the center point the envelope follower sweeps from.',onChange:v=>{const b=getB();if(b)b.baseF(v);}});
  const kMod=makeKnob({label:'MOD',min:0,max:100,value:80,unit:'%',size:'lg',tip:'Modulation amount — how wide the envelope sweeps the filter.',onChange:v=>{const b=getB();if(b)b.modAmt(v*200);}});
  topRow.append(freqDrag,kMod);
  // Attack + release as steppers (musical time values)
  const ATK_STEPS=[{label:'1 ms',value:0.001},{label:'5 ms',value:0.005},{label:'10 ms',value:0.01},{label:'30 ms',value:0.03},{label:'100 ms',value:0.1}];
  const REL_STEPS=[{label:'50 ms',value:0.05},{label:'100 ms',value:0.1},{label:'200 ms',value:0.2},{label:'500 ms',value:0.5},{label:'1 s',value:1}];
  const atkStep=makeStepper({label:'ATTACK',steps:ATK_STEPS,index:2,tip:'How fast the filter opens when signal rises.',onChange:v=>{const b=getB();if(b)b.atk(v);}});
  const relStep=makeStepper({label:'RELEASE',steps:REL_STEPS,index:2,tip:'How fast the filter closes when signal falls.',onChange:v=>{const b=getB();if(b)b.rel(v);}});
  const kQ=makeKnob({label:'Q',min:0.1,max:20,value:2,unit:'',decimals:1,size:'sm',tip:'Resonance — sharpens the filter peak.',onChange:v=>{const b=getB();if(b)b.q(v);}});
  const qRow=document.createElement('div');qRow.style.cssText='display:flex;justify-content:center;padding:4px 0;';qRow.appendChild(kQ);
  // Type buttons
  const tSec=document.createElement('div');tSec.className='app-section';
  const tLbl=document.createElement('span');tLbl.className='app-section-lbl';tLbl.textContent='FILTER TYPE';
  const tBtns=document.createElement('div');tBtns.style.cssText='display:flex;gap:5px;';
  [{t:'lowpass',l:'LP',tip:'Low-pass: lets lows through.'},{t:'highpass',l:'HP',tip:'High-pass: lets highs through.'},{t:'bandpass',l:'BP',tip:'Band-pass: lets a narrow band through.'}].forEach(({t,l,tip},i)=>{
    const btn=document.createElement('button');btn.className='seg-btn'+(i===0?' active':'');btn.textContent=l;btn.dataset.tip=tip;
    btn.addEventListener('click',()=>{tBtns.querySelectorAll('.seg-btn').forEach(b=>b.classList.remove('active'));btn.classList.add('active');const b=getB();if(b)b.type(t);});
    tBtns.appendChild(btn);
  });
  tSec.append(tLbl,tBtns);
  kSec.append(kLbl,topRow,atkStep,relStep,qRow);
  ui.append(cvWrap,kSec,tSec);wb.appendChild(ui);
  (function drawAF(){
    requestAnimationFrame(drawAF);if(!win.classList.contains('open'))return;
    const {ctx:ctx2,W,H}=setupCanvas(canvas,280,50);
    ctx2.fillStyle='rgba(2,8,18,.9)';ctx2.fillRect(0,0,W,H);const b=getB();if(!b)return;
    ctx2.beginPath();ctx2.strokeStyle=acidColor(.8);ctx2.lineWidth=1.5;
    const fq=b.filt.frequency.value||800,q=b.filt.Q.value||2;
    const logMin=Math.log10(20),logMax=Math.log10(20000);
    for(let i=0;i<W;i++){const f=Math.pow(10,logMin+(i/W)*(logMax-logMin));const df=f/fq,response=1/(Math.sqrt(Math.pow(1-df*df,2)+Math.pow(df/q,2)));const db=20*Math.log10(Math.max(0.001,Math.min(response,10)));const y=H/2-db*(H/40);if(i===0)ctx2.moveTo(i,y);else ctx2.lineTo(i,y);}
    ctx2.stroke();
    ctx2.beginPath();ctx2.strokeStyle='rgba(255,255,255,.08)';ctx2.lineWidth=1;ctx2.moveTo(0,H/2);ctx2.lineTo(W,H/2);ctx2.stroke();
  })();
};

// --- NOISE factory
APP_FACTORIES['win-noise'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const getB=()=>APP_BUSES[winId]?._noise;
  let isOn=false,levelVal=30,noiseType='white';
  const TYPE_COLS={white:'rgba(220,220,220,.85)',pink:'rgba(255,160,160,.85)',brown:'rgba(180,90,30,.85)'};
  // Hero section: canvas + power button
  const sec1=document.createElement('div');sec1.className='acid-section';
  const s1l=document.createElement('span');s1l.className='app-section-lbl';s1l.textContent='NOISE SOURCE';
  const topRow=document.createElement('div');topRow.style.cssText='display:flex;gap:10px;align-items:center;padding:4px 0 6px;';
  const cvWrap=document.createElement('div');cvWrap.style.cssText='flex:1;background:#030305;border-radius:6px;overflow:hidden;height:58px;';
  const canvas=document.createElement('canvas');canvas.height=58;canvas.style.cssText='width:100%;display:block;';
  cvWrap.appendChild(canvas);
  const powerBtn=document.createElement('button');powerBtn.className='seg-btn';powerBtn.textContent='OFF';
  powerBtn.style.cssText='font-size:11px;padding:12px 14px;min-width:54px;letter-spacing:2px;flex-shrink:0;';
  topRow.append(cvWrap,powerBtn);sec1.append(s1l,topRow);
  // Output section: level fader + HP/LP filters
  const sec2=document.createElement('div');sec2.className='acid-section';
  const s2l=document.createElement('span');s2l.className='app-section-lbl';s2l.textContent='OUTPUT';
  const outRow=document.createElement('div');outRow.style.cssText='display:flex;gap:12px;align-items:flex-start;';
  const levelFader=makeVertFader({label:'LEVEL',min:0,max:100,value:30,unit:'%',height:88,
    tip:'Output volume of the noise signal.',
    onChange:v=>{levelVal=v;const b=getB();if(b&&b.on)b.out.gain.value=v/100;}});
  const filWrap=document.createElement('div');filWrap.style.cssText='flex:1;display:flex;flex-direction:column;gap:4px;padding-top:2px;';
  const sHP=makeSlider({label:'HIGH-PASS',min:20,max:8000,value:20,unit:' Hz',tip:'Removes low frequencies from the noise.',onChange:v=>{const b=getB();if(b&&b.hp)b.hp.frequency.value=v;}});
  const sLP=makeSlider({label:'LOW-PASS',min:200,max:20000,value:20000,unit:' Hz',tip:'Removes high frequencies from the noise.',onChange:v=>{const b=getB();if(b&&b.lp)b.lp.frequency.value=v;}});
  filWrap.append(sHP,sLP);outRow.append(levelFader,filWrap);sec2.append(s2l,outRow);
  // Color section
  const tSec=document.createElement('div');tSec.className='app-section';
  const tLbl=document.createElement('span');tLbl.className='app-section-lbl';tLbl.textContent='COLOR';
  const tBtns=document.createElement('div');tBtns.style.cssText='display:flex;gap:5px;';
  [{t:'white',tip:'White noise — equal energy at all frequencies. Bright and hissy.'},{t:'pink',tip:'Pink noise — rolls off at 3dB/octave. More balanced, like waterfalls.'},{t:'brown',tip:'Brown noise — rolls off at 6dB/octave. Deep, rumbling sound.'}].forEach(({t,tip},i)=>{
    const btn=document.createElement('button');btn.className='seg-btn'+(i===0?' active':'');
    btn.textContent=t.toUpperCase();btn.dataset.tip=tip;btn.style.color=TYPE_COLS[t];
    btn.addEventListener('click',()=>{
      tBtns.querySelectorAll('.seg-btn').forEach(b=>b.classList.remove('active'));btn.classList.add('active');
      noiseType=t;const b=getB();if(b)b.setType(t);
    });
    tBtns.appendChild(btn);
  });
  tSec.append(tLbl,tBtns);
  ui.append(sec1,sec2,tSec);wb.appendChild(ui);
  powerBtn.addEventListener('click',()=>{
    const b=getB();if(!b)return;
    isOn=!isOn;b.setOn(isOn,levelVal);
    powerBtn.textContent=isOn?'ON':'OFF';
    powerBtn.style.color=isOn?'var(--acid)':'';powerBtn.style.borderColor=isOn?'var(--acid)':'';
  });
  // Animated noise waveform canvas
  (function drawNoise(){
    requestAnimationFrame(drawNoise);if(!win.classList.contains('open'))return;
    const {ctx:ctx2,W,H}=setupCanvas(canvas,180,58);
    if(!isOn){ctx2.fillStyle='rgba(3,3,5,.96)';ctx2.fillRect(0,0,W,H);return;}
    ctx2.fillStyle='rgba(3,3,5,.55)';ctx2.fillRect(0,0,W,H);
    ctx2.beginPath();ctx2.strokeStyle=TYPE_COLS[noiseType]||'rgba(220,220,220,.8)';ctx2.lineWidth=1;
    let pv=0.5;
    for(let i=0;i<W;i++){
      let v;
      if(noiseType==='white')v=Math.random();
      else if(noiseType==='pink')v=pv*0.72+Math.random()*0.28;
      else v=pv*0.96+Math.random()*0.04;
      pv=v;
      const y=H/2+(v-0.5)*(H*0.8*(levelVal/100));
      i===0?ctx2.moveTo(i,y):ctx2.lineTo(i,y);
    }
    ctx2.stroke();
  })();
};

// --- CHORD PAD factory (redesigned — sleek 4×4 chord grid with quality-aware triads)
APP_FACTORIES['win-padboard'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const SCALES={
    Major:      {intervals:[0,2,4,5,7,9,11],quality:['maj','min','min','maj','maj','min','dim']},
    Minor:      {intervals:[0,2,3,5,7,8,10], quality:['min','dim','maj','min','min','maj','maj']},
    Dorian:     {intervals:[0,2,3,5,7,9,10], quality:['min','min','maj','maj','min','dim','maj']},
    Phrygian:   {intervals:[0,1,3,5,7,8,10], quality:['min','maj','maj','min','dim','maj','min']},
    Lydian:     {intervals:[0,2,4,6,7,9,11], quality:['maj','maj','min','dim','maj','min','min']},
    Mixolydian: {intervals:[0,2,4,5,7,9,10], quality:['maj','min','dim','maj','min','min','maj']},
  };
  const QUALITY_IVLS={maj:[0,4,7],min:[0,3,7],dim:[0,3,6]};
  const QUALITY_SUFFIX={maj:'',min:'m',dim:'°'};
  const QUALITY_COLOR={
    maj:'rgba(100,70,255,',
    min:'rgba(60,100,200,',
    dim:'rgba(160,50,80,',
  };
  const NOTES=['C','C#','D','D#','E','F','F#','G','G#','A','A#','B'];
  const ROMAN=['I','II','III','IV','V','VI','VII'];
  let selRoot=0,selScale='Major',octave=4;

  // ── Controls row ──────────────────────────────────────────
  const ctrlSec=document.createElement('div');ctrlSec.className='app-section';
  ctrlSec.style.cssText='padding-bottom:8px;border-bottom:1px solid rgba(255,255,255,.06);margin-bottom:10px;';

  const ctrlRow=document.createElement('div');
  ctrlRow.style.cssText='display:flex;align-items:center;gap:10px;flex-wrap:wrap;';

  // Key label + note pills
  const keyLbl=document.createElement('span');
  keyLbl.style.cssText='font-size:8px;letter-spacing:2px;color:rgba(255,255,255,.3);flex-shrink:0;';
  keyLbl.textContent='KEY';keyLbl.dataset.tip='Root note — sets the tonal centre for all chord pads';
  const noteRow=document.createElement('div');noteRow.style.cssText='display:flex;gap:3px;';
  NOTES.forEach((n,i)=>{
    const b=document.createElement('button');
    b.className='seg-btn'+(i===0?' active':'');
    b.textContent=n;b.style.cssText='font-size:8px;padding:3px 5px;min-width:24px;';
    b.dataset.tip=`Set root key to ${n}`;
    b.addEventListener('click',()=>{noteRow.querySelectorAll('.seg-btn').forEach(x=>x.classList.remove('active'));b.classList.add('active');selRoot=i;renderPads();});
    noteRow.appendChild(b);
  });

  // Scale select
  const scaleLbl=document.createElement('span');
  scaleLbl.style.cssText='font-size:8px;letter-spacing:2px;color:rgba(255,255,255,.3);flex-shrink:0;margin-left:6px;';
  scaleLbl.textContent='MODE';scaleLbl.dataset.tip='Harmonic mode — determines chord quality (major/minor/diminished) for each pad';
  const scaleSel=document.createElement('select');
  scaleSel.style.cssText='font-size:10px;padding:4px 8px;border-radius:8px;background:rgba(255,255,255,.07);border:1px solid rgba(255,255,255,.12);color:rgba(255,255,255,.8);font-family:inherit;cursor:pointer;outline:none;';
  Object.keys(SCALES).forEach(s=>{const o=document.createElement('option');o.value=s;o.textContent=s;scaleSel.appendChild(o);});
  scaleSel.value='Major';
  scaleSel.addEventListener('change',()=>{selScale=scaleSel.value;renderPads();});
  scaleSel.dataset.tip='Harmonic mode — determines chord quality (major/minor/diminished) for each pad';

  // Octave
  const octLbl=document.createElement('span');
  octLbl.style.cssText='font-size:8px;letter-spacing:2px;color:rgba(255,255,255,.3);flex-shrink:0;margin-left:4px;';
  octLbl.textContent='OCT';octLbl.dataset.tip='Base octave — shifts all pads up or down by an octave';
  const octRow=document.createElement('div');octRow.style.cssText='display:flex;gap:3px;';
  [3,4,5].forEach(o=>{
    const b=document.createElement('button');b.className='seg-btn'+(o===4?' active':'');
    b.textContent=String(o);b.style.cssText='font-size:9px;padding:3px 8px;';
    b.dataset.tip=`Set octave to ${o}`;
    b.addEventListener('click',()=>{octRow.querySelectorAll('.seg-btn').forEach(x=>x.classList.remove('active'));b.classList.add('active');octave=o;});
    octRow.appendChild(b);
  });

  ctrlRow.append(keyLbl,noteRow,scaleLbl,scaleSel,octLbl,octRow);
  ctrlSec.appendChild(ctrlRow);

  // ── Pad grid ──────────────────────────────────────────────
  const padSec=document.createElement('div');padSec.className='app-section';
  const padGrid=document.createElement('div');
  padGrid.style.cssText='display:grid;grid-template-columns:repeat(4,1fr);gap:8px;';
  const pads=[];

  function renderPads(){
    const sc=SCALES[selScale]||SCALES.Major;
    pads.forEach((pad,i)=>{
      const deg=i%sc.intervals.length;
      const octOffset=Math.floor(i/sc.intervals.length);
      const semi=sc.intervals[deg]+octOffset*12;
      const qual=sc.quality[deg];
      const noteIdx=(selRoot+semi)%12;
      const noteName=NOTES[noteIdx];
      const suffix=QUALITY_SUFFIX[qual]||'';
      const roman=ROMAN[deg]||'';
      pad.dataset.semi=semi;pad.dataset.root=selRoot;pad.dataset.qual=qual;
      pad.querySelector('.pad-chord').textContent=noteName+suffix;
      pad.querySelector('.pad-deg').textContent=roman+(octOffset?'+'.repeat(octOffset):'');
      // Update color
      const c=QUALITY_COLOR[qual]||QUALITY_COLOR.maj;
      pad.style.background=`linear-gradient(160deg,${c}.18),${c}.06))`;
      pad.style.borderColor=`${c}.22)`;
      pad.style.borderTopColor=`${c}.35)`;
      pad.dataset.tip=`${noteName}${suffix} (${roman}) — click to play this chord`;
    });
  }

  for(let i=0;i<16;i++){
    const pad=document.createElement('button');
    pad.style.cssText='border:1px solid rgba(100,70,255,.22);border-top-color:rgba(140,110,255,.35);border-radius:12px;padding:14px 8px 12px;display:flex;flex-direction:column;align-items:center;gap:4px;cursor:pointer;transition:transform .08s,box-shadow .08s,background .1s;width:100%;';
    const chordEl=document.createElement('span');chordEl.className='pad-chord';
    chordEl.style.cssText='font-size:16px;font-weight:700;color:rgba(200,170,255,.92);letter-spacing:-.5px;font-family:inherit;line-height:1.1;';
    const degEl=document.createElement('span');degEl.className='pad-deg';
    degEl.style.cssText='font-size:8px;color:rgba(140,110,255,.55);letter-spacing:1.5px;font-family:inherit;';
    pad.append(chordEl,degEl);
    pad.addEventListener('mousedown',()=>{
      pad.style.transform='scale(.94)';
      pad.style.boxShadow='0 0 20px rgba(130,90,255,.4)';
      ensureAudio();
      if(typeof triggerPoly==='function'&&ac){
        const semi=parseInt(pad.dataset.semi)||0,root=parseInt(pad.dataset.root)||0;
        const qual=pad.dataset.qual||'maj';
        const midiBase=(octave+1)*12+root+semi;
        const midiArr=(QUALITY_IVLS[qual]||[0,4,7]).map(iv=>midiBase+iv);
        triggerPoly(midiArr,ac.currentTime,0.6);
      }
    });
    const up=()=>{pad.style.transform='';pad.style.boxShadow='';};
    pad.addEventListener('mouseup',up);pad.addEventListener('mouseleave',up);
    pads.push(pad);padGrid.appendChild(pad);
  }
  renderPads();
  padSec.appendChild(padGrid);
  ui.append(ctrlSec,padSec);wb.appendChild(ui);
};

// --- BIT CRUSHER factory — bits stepper (integers only) + crush slider + staircase canvas
APP_FACTORIES['win-bitcrush'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='BIT CRUSHER';
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#050c03;border-radius:6px;padding:4px;margin-bottom:8px;';
  const canvas=document.createElement('canvas');canvas.height=48;canvas.style.cssText='width:100%;display:block;border-radius:4px;';cvWrap.appendChild(canvas);
  let bits=16;
  function drawCrush(){
    const {ctx,W,H}=setupCanvas(canvas,240,48);
    ctx.fillStyle='#050c03';ctx.fillRect(0,0,W,H);
    const steps=Math.pow(2,Math.round(bits))-1;
    ctx.beginPath();ctx.strokeStyle='#50ff80';ctx.lineWidth=2;
    for(let x=0;x<W;x++){const phase=(x/W)*Math.PI*4;const raw=Math.sin(phase);const q=Math.round(raw*steps)/steps;const y=H/2-q*(H/2-4);if(x===0)ctx.moveTo(x,y);else ctx.lineTo(x,y);}
    ctx.stroke();
    ctx.beginPath();ctx.strokeStyle='rgba(80,255,128,.08)';ctx.lineWidth=1;ctx.moveTo(0,H/2);ctx.lineTo(W,H/2);ctx.stroke();
  }
  // Bits stepper — bit depth is inherently discrete, stepper is the right control
  const BIT_STEPS=[{label:'4 bit',value:4},{label:'5 bit',value:5},{label:'6 bit',value:6},{label:'8 bit',value:8},{label:'10 bit',value:10},{label:'12 bit',value:12},{label:'16 bit',value:16}];
  const getB=()=>APP_BUSES[winId]?._bc;
  const bitStep=makeStepper({label:'BIT DEPTH',steps:BIT_STEPS,index:6,tip:'Bit depth — fewer bits creates harsh digital quantisation noise. 4-bit is severe crunch, 16-bit is clean.',onChange:v=>{bits=v;drawCrush();const b=getB();if(b)b.wsh.curve=b.makeBitCurve(v);}});
  const sCrush=makeSlider({label:'CRUSH',min:0,max:100,value:0,unit:'%',tip:'Crush intensity — additional harmonic distortion layered after bit reduction.',onChange:()=>{drawCrush();}});
  sec.append(lbl,cvWrap,bitStep,sCrush);ui.appendChild(sec);wb.appendChild(ui);
  document.addEventListener('workspace-zoom',drawCrush);new ResizeObserver(()=>{if(canvas.offsetWidth>0)drawCrush();}).observe(canvas);
  drawCrush();
};

// --- CABINET SIM factory (mini — type buttons + frequency canvas + 2 sliders)
APP_FACTORIES['win-cabinet'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='CABINET SIM';
  const CABS={Clean:{lo:0,mid:0,hi:0,midF:1000,Q:0.8},Vintage:{lo:2,mid:3,hi:-4,midF:800,Q:1.2},Crunch:{lo:1,mid:6,hi:-8,midF:1200,Q:1.8},Heavy:{lo:4,mid:-2,hi:-12,midF:600,Q:2.2}};
  const CAB_TIPS={Clean:'Flat, transparent response — no cabinet colouring',Vintage:'Warm mid-forward tone, 1960s open-back combo',Crunch:'Aggressive midrange bite, driven closed-back 4×12',Heavy:'Scooped bass-heavy response, high-gain metal cabinet'};
  let selCab='Clean';
  // Type buttons — taller and more prominent
  const typeRow=document.createElement('div');typeRow.style.cssText='display:flex;gap:5px;margin-bottom:10px;';
  Object.keys(CABS).forEach(name=>{
    const b=document.createElement('button');b.className='seg-btn'+(name==='Clean'?' active':'');
    b.textContent=name;b.style.cssText='flex:1;padding:9px 2px;font-size:9px;';b.dataset.tip=CAB_TIPS[name];
    b.addEventListener('click',()=>{typeRow.querySelectorAll('.seg-btn').forEach(x=>x.classList.remove('active'));b.classList.add('active');selCab=name;applyCab();drawResp();});
    typeRow.appendChild(b);
  });
  // Frequency response canvas — uses acid color
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#060604;border-radius:6px;overflow:hidden;margin-bottom:12px;';
  const canvas=document.createElement('canvas');canvas.height=50;canvas.style.cssText='width:100%;display:block;';
  cvWrap.appendChild(canvas);
  // Presence (large knob — the main tonal shaper) + body (vertical fader)
  const ctrlRow=document.createElement('div');ctrlRow.style.cssText='display:flex;gap:14px;align-items:flex-start;justify-content:center;padding:4px 0;';
  const kPresence=makeKnob({label:'PRESENCE',min:-12,max:12,value:0,unit:' dB',size:'lg',
    tip:'High-frequency air — boosts upper-mid sparkle and attack clarity',
    onChange:()=>{applyCab();drawResp();}});
  const bodyFader=makeVertFader({label:'BODY',min:-6,max:6,value:0,unit:' dB',height:80,
    tip:'Low-mid warmth — adds fullness and roundness to the tone',
    onChange:()=>{applyCab();drawResp();}});
  ctrlRow.append(kPresence,bodyFader);
  function applyCab(){
    const b=APP_BUSES[winId]?._cab;if(!b)return;
    const cab=CABS[selCab],pres=kPresence._val(),body=bodyFader._val();
    b.lo.gain.value=cab.lo+body;b.mid.frequency.value=cab.midF;b.mid.Q.value=cab.Q;b.mid.gain.value=cab.mid;b.hi.gain.value=cab.hi+pres;
  }
  function drawResp(){
    const {ctx,W,H}=setupCanvas(canvas,260,50);
    ctx.fillStyle='#060604';ctx.fillRect(0,0,W,H);
    const cab=CABS[selCab],pres=kPresence._val(),body=bodyFader._val();
    ctx.beginPath();ctx.strokeStyle=acidColor(.88);ctx.lineWidth=1.8;
    for(let x=0;x<W;x++){
      const f=Math.pow(10,Math.log10(20)+(x/W)*(Math.log10(20000)-Math.log10(20)));
      let db=0;
      if(f<200)db+=(cab.lo+body)*(1-Math.min(1,f/200));
      const mRatio=f/cab.midF;db+=cab.mid/(Math.pow(mRatio-1/mRatio,2)*cab.Q*cab.Q+1);
      if(f>5000)db+=(cab.hi+pres*0.5)*(Math.min(1,(f-5000)/10000));
      const y=H/2-db*(H/20);
      if(x===0)ctx.moveTo(x,Math.max(2,Math.min(H-2,y)));else ctx.lineTo(x,Math.max(2,Math.min(H-2,y)));
    }
    ctx.stroke();
    ctx.beginPath();ctx.strokeStyle='rgba(255,255,255,.06)';ctx.lineWidth=1;ctx.moveTo(0,H/2);ctx.lineTo(W,H/2);ctx.stroke();
  }
  sec.append(lbl,typeRow,cvWrap,ctrlRow);
  ui.appendChild(sec);wb.appendChild(ui);
  document.addEventListener('workspace-zoom',drawResp);
  new ResizeObserver(()=>{if(canvas.offsetWidth>0)drawResp();}).observe(canvas);
  drawResp();
};

// --- STEREO IMAGER factory — full-width hero slider + L/R spread canvas
APP_FACTORIES['win-stereoimg'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='STEREO IMAGER';
  let widthVal=100;
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#040e06;border-radius:6px;padding:6px 8px;margin-bottom:10px;';
  const canvas=document.createElement('canvas');canvas.height=40;canvas.style.cssText='width:100%;display:block;border-radius:3px;';cvWrap.appendChild(canvas);
  function drawMeter(){
    const {ctx,W,H}=setupCanvas(canvas,240,40);
    ctx.fillStyle='#040e06';ctx.fillRect(0,0,W,H);
    const spread=Math.min(widthVal/200,1);const cx=W/2,bH=12;
    ctx.fillStyle=`rgba(32,192,96,${0.25+spread*0.7})`;
    const lW=spread*cx*0.9;ctx.fillRect(cx-lW-2,H/2-bH-4,lW,bH);ctx.fillRect(cx+2,H/2-bH-4,lW,bH);
    ctx.fillStyle=`rgba(32,192,96,${0.9-spread*0.7})`;
    const cW=Math.max(3,(1-spread)*cx*0.5+6);ctx.fillRect(cx-cW/2,H/2+2,cW,8);
    ctx.font='9px monospace';ctx.fillStyle='rgba(32,192,96,.4)';
    ctx.textAlign='left';ctx.fillText('L',4,H/2-8);
    ctx.textAlign='right';ctx.fillText('R',W-4,H/2-8);
    ctx.textAlign='center';ctx.fillText('M',cx,H-2);
    ctx.textAlign='center';ctx.fillStyle='rgba(32,192,96,.6)';ctx.fillText(Math.round(widthVal)+'%',cx,H/2-bH-10);
  }
  const getB=()=>APP_BUSES[winId]?._si;
  // Wide hero slider — the whole width of the window
  const widthSlider=makeSlider({label:'WIDTH',min:0,max:200,value:100,unit:'%',
    tip:'Stereo width — 0% collapses to mono, 100% is original, 200% is hyper-wide.',
    onChange:v=>{widthVal=v;drawMeter();const b=getB();if(!b)return;const w=v/100;b.lGain.gain.value=0.5+w*0.5;b.rGain.gain.value=0.5+w*0.5;}});
  const monoToggle=makeToggle({label:'BASS MONO',value:false,tip:'Sum low frequencies to mono — prevents bass from going too wide.',onChange:v=>{
    const b=getB();if(!b)return;
    if(v){
      // Build bass-mono chain: lowpass → splitter → merger summing L+R
      if(b._bassLP)return;
      const lp=ac.createBiquadFilter();lp.type='lowpass';lp.frequency.value=250;lp.Q.value=0.7;
      const spl2=ac.createChannelSplitter(2);const mrg2=ac.createChannelMerger(2);
      const sumL=ac.createGain();sumL.gain.value=0.5;const sumR=ac.createGain();sumR.gain.value=0.5;
      b.input.connect(lp);lp.connect(spl2);spl2.connect(sumL,0);spl2.connect(sumL,1);
      spl2.connect(sumR,0);spl2.connect(sumR,1);sumL.connect(mrg2,0,0);sumR.connect(mrg2,0,1);
      mrg2.connect(b.output);
      b._bassLP={lp,spl2,mrg2,sumL,sumR};
    } else {
      if(!b._bassLP)return;
      try{b.input.disconnect(b._bassLP.lp);}catch(_){}
      try{b._bassLP.mrg2.disconnect();}catch(_){}
      b._bassLP=null;
    }
  }});
  sec.append(lbl,cvWrap,widthSlider,monoToggle);ui.appendChild(sec);wb.appendChild(ui);
  document.addEventListener('workspace-zoom',drawMeter);new ResizeObserver(()=>{if(canvas.offsetWidth>0)drawMeter();}).observe(canvas);
  drawMeter();
};

// --- COMB FILTER factory — freq num-drag + large feedback knob + mix slider
APP_FACTORIES['win-comb'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');wb.innerHTML='';
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const lbl=document.createElement('span');lbl.className='acid-section-label';lbl.textContent='COMB FILTER';
  let combFreq=100,combFb=0.5;
  const cvWrap=document.createElement('div');cvWrap.style.cssText='background:#05040e;border-radius:6px;padding:4px;margin-bottom:8px;';
  const canvas=document.createElement('canvas');canvas.height=48;canvas.style.cssText='width:100%;display:block;border-radius:4px;';cvWrap.appendChild(canvas);
  function drawComb(){
    const {ctx,W,H}=setupCanvas(canvas,240,48);
    ctx.fillStyle='#05040e';ctx.fillRect(0,0,W,H);
    ctx.beginPath();ctx.strokeStyle='#7050ff';ctx.lineWidth=1.8;
    const logMin=Math.log10(20),logMax=Math.log10(20000);
    for(let x=0;x<W;x++){const f=Math.pow(10,logMin+(x/W)*(logMax-logMin));const phase=2*Math.PI*f/combFreq;const re=1-combFb*Math.cos(phase),im=combFb*Math.sin(phase);const mag=1/Math.sqrt(re*re+im*im);const db=Math.max(-24,Math.min(12,20*Math.log10(mag)));const y=H/2-db*(H/40);if(x===0)ctx.moveTo(x,y);else ctx.lineTo(x,y);}
    ctx.stroke();ctx.beginPath();ctx.strokeStyle='rgba(112,80,255,.1)';ctx.lineWidth=1;ctx.moveTo(0,H/2);ctx.lineTo(W,H/2);ctx.stroke();
  }
  const getB=()=>APP_BUSES[winId]?._comb;
  // Layout: freq num-drag + large feedback knob
  const layout=document.createElement('div');layout.style.cssText='display:flex;gap:14px;align-items:flex-start;justify-content:center;padding:4px 0 8px;';
  const freqDrag=makeNumDrag({label:'FREQ',unit:' Hz',min:50,max:2000,value:100,step:1,tip:'Comb fundamental — sets the spacing between resonant frequency peaks.',onChange:v=>{combFreq=v;drawComb();const b=getB();if(b)b.dly.delayTime.value=1/v;}});
  const kFb=makeKnob({label:'FEEDBACK',min:0,max:90,value:50,unit:'%',size:'lg',tip:'Resonance — higher values create sharper, more metallic ringing peaks.',onChange:v=>{combFb=v/100;drawComb();const b=getB();if(b)b.fb.gain.value=v/100;}});
  layout.append(freqDrag,kFb);
  const sMix=makeSlider({label:'MIX',min:0,max:100,value:40,unit:'%',tip:'Dry/wet blend.',onChange:v=>{const b=getB();if(b){b.wet.gain.value=v/100;b.dry.gain.value=1-v/100*0.5;}}});
  sec.append(lbl,cvWrap,layout,sMix);ui.appendChild(sec);wb.appendChild(ui);
  document.addEventListener('workspace-zoom',drawComb);new ResizeObserver(()=>{if(canvas.offsetWidth>0)drawComb();}).observe(canvas);drawComb();
};

/* =====================================================
   WIN-DISTORTION — multi-mode analog distortion
   ===================================================== */
APP_FACTORIES['win-distortion'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='DISTORTION';

  // Drive pad: X = tone, Y = drive
  const pad=document.createElement('div');pad.className='acid-drive-pad';
  const padCv=document.createElement('canvas');padCv.style.cssText='position:absolute;inset:0;width:100%;height:100%;pointer-events:none;';
  const padH=document.createElement('div');padH.className='acid-drive-pad-handle';
  const padBL=document.createElement('div');padBL.style.cssText='position:absolute;inset:0;display:flex;justify-content:space-between;align-items:flex-end;padding:4px 8px;pointer-events:none;';
  padBL.innerHTML='<span style="font-size:9px;color:rgba(255,255,255,.3);letter-spacing:1px">BASS</span><span style="font-size:9px;color:rgba(255,255,255,.3);letter-spacing:1px">TREBLE</span>';
  const padTL=document.createElement('div');padTL.style.cssText='position:absolute;top:4px;left:8px;font-size:9px;color:rgba(255,255,255,.3);letter-spacing:1px;pointer-events:none;';padTL.textContent='DRIVE ▲';
  pad.append(padCv,padH,padBL,padTL);

  let driveX=0.5,driveY=0.3;
  function drawPadCv(){
    const {ctx,W,H}=setupCanvas(padCv,200,120);ctx.clearRect(0,0,W,H);
    ctx.strokeStyle='rgba(255,255,255,.06)';ctx.lineWidth=1;
    for(let i=1;i<4;i++){ctx.beginPath();ctx.moveTo(W*i/4,0);ctx.lineTo(W*i/4,H);ctx.stroke();}
    for(let i=1;i<4;i++){ctx.beginPath();ctx.moveTo(0,H*i/4);ctx.lineTo(W,H*i/4);ctx.stroke();}
    ctx.strokeStyle='rgba(255,100,60,.25)';ctx.lineWidth=1;ctx.setLineDash([2,3]);
    ctx.beginPath();ctx.moveTo(driveX*W,0);ctx.lineTo(driveX*W,H);ctx.stroke();
    ctx.beginPath();ctx.moveTo(0,(1-driveY)*H);ctx.lineTo(W,(1-driveY)*H);ctx.stroke();
    ctx.setLineDash([]);
  }
  function applyDist(){
    const b=APP_BUSES[winId]?._dist;if(!b)return;
    b.setDrive(0.05+driveY*0.95);
    b.tone.frequency.value=300+driveX*9000;
    b.tone.gain.value=-10+driveX*22;
    drawWaveCurve();drawPadCv();
  }
  function setPadXY(e){
    const r=pad.getBoundingClientRect();
    driveX=Math.max(0,Math.min(1,(e.clientX-r.left)/r.width));
    driveY=Math.max(0,Math.min(1,1-(e.clientY-r.top)/r.height));
    padH.style.left=(driveX*100)+'%';padH.style.top=((1-driveY)*100)+'%';
    applyDist();
  }
  pad.addEventListener('pointerdown',e=>{pad.setPointerCapture(e.pointerId);setPadXY(e);});
  pad.addEventListener('pointermove',e=>{if(e.buttons)setPadXY(e);});
  padH.style.left='50%';padH.style.top='70%';

  // Waveshaper curve canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='width:100%;height:60px;border-radius:6px;background:rgba(0,0,0,.4);border:1px solid rgba(255,255,255,.06);margin-bottom:8px;overflow:hidden;';
  const cv=document.createElement('canvas');cv.style.cssText='width:100%;height:100%;';
  cvWrap.appendChild(cv);
  function drawWaveCurve(){
    const b=APP_BUSES[winId]?._dist;
    const {ctx,W,H}=setupCanvas(cv,300,60);
    ctx.clearRect(0,0,W,H);
    ctx.strokeStyle='rgba(255,255,255,.06)';ctx.lineWidth=1;
    ctx.beginPath();ctx.moveTo(W/2,0);ctx.lineTo(W/2,H);ctx.stroke();
    ctx.beginPath();ctx.moveTo(0,H/2);ctx.lineTo(W,H/2);ctx.stroke();
    ctx.strokeStyle='rgba(255,255,255,.1)';
    ctx.beginPath();ctx.moveTo(0,H);ctx.lineTo(W,0);ctx.stroke();
    if(b&&b.wsh.curve){
      const curve=b.wsh.curve;
      ctx.strokeStyle=acidColor?acidColor(.9):'rgba(255,100,60,.9)';ctx.lineWidth=2;
      ctx.beginPath();
      for(let i=0;i<W;i++){
        const xi=Math.min(Math.floor(i/W*curve.length),curve.length-1);
        const y=((-curve[xi]+1)/2)*H;
        if(i===0)ctx.moveTo(i,y);else ctx.lineTo(i,y);
      }
      ctx.stroke();
    }
  }

  // Mode buttons
  const MODES=[['TUBE','tube'],['TRANS','transistor'],['FUZZ','fuzz'],['OCT','octave'],['RECT','hard']];
  const modeRow=document.createElement('div');modeRow.style.cssText='display:flex;gap:4px;margin-bottom:10px;';
  MODES.forEach(([lbl,key])=>{
    const btn=document.createElement('button');btn.className='acid-seg-btn';btn.textContent=lbl;btn.style.flex='1';
    if(key==='tube')btn.classList.add('on');
    btn.addEventListener('click',()=>{
      modeRow.querySelectorAll('.acid-seg-btn').forEach(b=>b.classList.remove('on'));btn.classList.add('on');
      const db=APP_BUSES[winId]?._dist;if(db){db.mode=key;db.setDrive(0.05+driveY*0.95);}
      drawWaveCurve();
    });
    modeRow.appendChild(btn);
  });

  const row=document.createElement('div');row.style.cssText='display:flex;gap:12px;align-items:flex-start;';
  const kLevel=makeKnob({label:'OUTPUT',min:0,max:100,value:80,unit:'%',size:'md',tip:'Output gain after distortion.',onChange:v=>{const b=APP_BUSES[winId]?._dist;if(b)b.level.gain.value=v/100;}});
  const sMix=makeSlider({label:'MIX',min:0,max:100,value:100,unit:'%',tip:'Dry/wet blend.',onChange:v=>{const b=APP_BUSES[winId]?._dist;if(b){b.wetMix.gain.value=v/100;b.dryMix.gain.value=1-v/100;}}});
  row.append(kLevel,sMix);
  sec.append(hdr,pad,cvWrap,modeRow,row);
  ui.appendChild(sec);wb.appendChild(ui);
  applyDist();
  new ResizeObserver(drawWaveCurve).observe(cvWrap);
  new ResizeObserver(drawPadCv).observe(pad);
  drawPadCv();
  (function loop(){requestAnimationFrame(loop);if(cv.offsetWidth>0)drawWaveCurve();})();
};

/* =====================================================
   WIN-MULTICOMP — 3-band compressor with draggable crossovers
   ===================================================== */
APP_FACTORIES['win-multicomp'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='MULTI-BAND COMP';

  // Crossover canvas — drag the dividers
  const cvWrap=document.createElement('div');cvWrap.style.cssText='width:100%;height:80px;border-radius:8px;background:rgba(0,0,0,.5);border:1px solid rgba(255,255,255,.07);margin-bottom:10px;position:relative;cursor:ew-resize;user-select:none;overflow:hidden;';
  const cv=document.createElement('canvas');cv.style.cssText='width:100%;height:100%;display:block;';
  cvWrap.appendChild(cv);
  let xo1=400,xo2=4000;
  const LOG_MIN=20,LOG_MAX=20000;
  function freqToX(f,W){return (Math.log10(f)-Math.log10(LOG_MIN))/(Math.log10(LOG_MAX)-Math.log10(LOG_MIN))*W;}
  function xToFreq(x,W){return Math.pow(10,Math.log10(LOG_MIN)+(x/W)*(Math.log10(LOG_MAX)-Math.log10(LOG_MIN)));}
  const BAND_COLS=['rgba(58,160,255,.45)','rgba(80,220,80,.45)','rgba(255,100,50,.45)'];
  const GR_MAX=12,analysers=[];
  function drawXO(){
    const {ctx,W,H}=setupCanvas(cv,400,80);
    ctx.clearRect(0,0,W,H);
    const x1=freqToX(xo1,W),x2=freqToX(xo2,W);
    // Band fills
    ctx.fillStyle=BAND_COLS[0];ctx.fillRect(0,0,x1,H);
    ctx.fillStyle=BAND_COLS[1];ctx.fillRect(x1,0,x2-x1,H);
    ctx.fillStyle=BAND_COLS[2];ctx.fillRect(x2,0,W-x2,H);
    // GR bars
    const b=APP_BUSES[winId]?._mc;
    if(b){
      b.bands.forEach((band,i)=>{
        const x=(i===0?0:(i===1?x1:x2)),w=(i===0?x1:(i===1?x2-x1:W-x2));
        try{const gr=Math.abs(band.comp.reduction||0);const grH=Math.min(H,gr/GR_MAX*H);
          ctx.fillStyle='rgba(255,60,40,.5)';ctx.fillRect(x,0,w,grH);}catch(_){}
      });
    }
    // Crossover lines
    ['#fff','#fff'].forEach((col,i)=>{
      const x=i===0?x1:x2;
      ctx.strokeStyle='rgba(255,255,255,.9)';ctx.lineWidth=2;
      ctx.setLineDash([5,3]);ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,H);ctx.stroke();ctx.setLineDash([]);
      ctx.fillStyle='rgba(255,255,255,.7)';ctx.font='8px monospace';
      ctx.fillText(i===0?(xo1<1000?xo1+'Hz':Math.round(xo1/100)/10+'kHz'):(xo2<1000?xo2+'Hz':Math.round(xo2/100)/10+'kHz'),x+3,H-4);
    });
  }
  let draggingXO=null;
  cvWrap.addEventListener('pointerdown',e=>{
    const W=cv.offsetWidth,r=cvWrap.getBoundingClientRect();
    const mx=e.clientX-r.left;
    const d1=Math.abs(mx-freqToX(xo1,W)),d2=Math.abs(mx-freqToX(xo2,W));
    draggingXO=d1<d2?1:2;cvWrap.setPointerCapture(e.pointerId);
  });
  cvWrap.addEventListener('pointermove',e=>{
    if(!draggingXO)return;
    const W=cv.offsetWidth,r=cvWrap.getBoundingClientRect();
    const f=Math.max(50,Math.min(18000,xToFreq(e.clientX-r.left,W)));
    if(draggingXO===1){xo1=Math.min(f,xo2*0.8);}else{xo2=Math.max(f,xo1*1.2);}
    const b=APP_BUSES[winId]?._mc;if(b)b.setXO(xo1,xo2);
    drawXO();
    // Update labels
    loLabel.textContent='LOW   <'+Math.round(xo1)+'Hz';
    midLabel.textContent=Math.round(xo1)+'Hz–'+Math.round(xo2/1000)+'kHz';
    hiLabel.textContent='>'+Math.round(xo2/1000)+'kHz';
  });
  cvWrap.addEventListener('pointerup',()=>{draggingXO=null;});

  // 3 band cards
  const bands=document.createElement('div');bands.style.cssText='display:flex;gap:6px;margin-bottom:10px;';
  const BAND_NAMES=['LOW','MID','HIGH'];
  const loLabel=document.createElement('div');const midLabel=document.createElement('div');const hiLabel=document.createElement('div');
  const labelEls=[loLabel,midLabel,hiLabel];
  loLabel.textContent='LOW   <400Hz';midLabel.textContent='400Hz–4kHz';hiLabel.textContent='>4kHz';
  const bandCards=BAND_NAMES.map((name,i)=>{
    const card=document.createElement('div');card.style.cssText='flex:1;min-width:0;background:rgba(0,0,0,.35);border-radius:8px;padding:8px;border:1px solid rgba(255,255,255,.07);';
    const lbl=document.createElement('div');lbl.style.cssText='font-size:8px;color:rgba(255,255,255,.4);letter-spacing:1.5px;margin-bottom:6px;text-align:center;';
    lbl.textContent=name;
    const bndLabel=labelEls[i];bndLabel.style.cssText='font-size:7px;color:rgba(255,255,255,.25);text-align:center;margin-bottom:6px;';
    const kThr=makeKnob({label:'THR',min:-60,max:0,value:-18,unit:'dB',size:'sm',tip:`${name} band threshold.`,onChange:v=>{const b=APP_BUSES[winId]?._mc;if(b)b.bands[i].comp.threshold.value=v;}});
    const kRatio=makeKnob({label:'RATIO',min:1,max:20,value:4,unit:':1',size:'sm',tip:`${name} band ratio.`,onChange:v=>{const b=APP_BUSES[winId]?._mc;if(b)b.bands[i].comp.ratio.value=v;}});
    const kMake=makeKnob({label:'MAKEUP',min:0,max:18,value:0,unit:'dB',size:'sm',tip:`${name} band makeup gain.`,onChange:v=>{const b=APP_BUSES[winId]?._mc;if(b)b.bands[i].gain.gain.value=Math.pow(10,v/20);}});
    const kRow=document.createElement('div');kRow.style.cssText='display:flex;gap:4px;justify-content:center;';
    kRow.append(kThr,kRatio,kMake);
    card.append(lbl,bndLabel,kRow);
    return card;
  });
  bands.append(...bandCards);
  const masterRow=document.createElement('div');masterRow.style.cssText='display:flex;gap:10px;align-items:center;';
  const kMaster=makeKnob({label:'OUTPUT',min:0,max:100,value:80,unit:'%',size:'sm',tip:'Master output level.',onChange:v=>{const b=APP_BUSES[winId]?._mc;if(b)b.master.gain.value=v/100;}});
  masterRow.appendChild(kMaster);
  sec.append(hdr,cvWrap,bands,masterRow);
  ui.appendChild(sec);wb.appendChild(ui);
  new ResizeObserver(drawXO).observe(cvWrap);
  (function loop(){requestAnimationFrame(loop);drawXO();})();
};

/* =====================================================
   WIN-WAVETABLE — wavetable synthesizer with morph strip
   ===================================================== */
APP_FACTORIES['win-wavetable'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='WAVETABLE SYNTH';

  // Morph strip — 8 waveform thumbnails + draggable cursor
  const morphSec=document.createElement('div');morphSec.className='acid-section';
  const mhdr=document.createElement('div');mhdr.className='acid-section-label';mhdr.textContent='WAVEFORM MORPH';
  const strip=document.createElement('div');strip.className='acid-morph-strip';
  const cursor=document.createElement('div');cursor.className='acid-morph-cursor';strip.appendChild(cursor);
  const WAVE_SHAPES=[
    x=>Math.sin(x*Math.PI*2),
    x=>Math.sign(Math.sin(x*Math.PI*2)),
    x=>(x%1)*2-1,
    x=>Math.abs((x%1)*4-2)-1,
    x=>Math.sin(x*Math.PI*2)*0.6+Math.sin(x*Math.PI*4)*0.25+Math.sin(x*Math.PI*6)*0.1,
    x=>Math.sin(x*Math.PI*2)+Math.sin(x*Math.PI*6)*.33+Math.sin(x*Math.PI*10)*.2,
    x=>Math.sin(x*Math.PI*2)*0.9,
    x=>{let v=0;for(let h=1;h<=8;h++)v+=Math.sin(x*Math.PI*2*h)/h;return v*0.4;}
  ];
  const thumbs=WAVE_SHAPES.map((shape,i)=>{
    const thumb=document.createElement('div');thumb.className='acid-morph-thumb';
    const cv=document.createElement('canvas');cv.width=60;cv.height=48;
    const ctx=cv.getContext('2d');
    ctx.fillStyle='rgba(0,0,0,.3)';ctx.fillRect(0,0,60,48);
    ctx.strokeStyle=acidColor?acidColor(.7):'rgba(232,104,32,.7)';ctx.lineWidth=1.5;ctx.beginPath();
    for(let x=0;x<60;x++){const y=((-shape(x/60)+1)/2)*46+1;if(x===0)ctx.moveTo(x,y);else ctx.lineTo(x,y);}
    ctx.stroke();
    thumb.appendChild(cv);
    strip.appendChild(thumb);
    return thumb;
  });
  let morphPos=0;
  function setMorph(p){
    morphPos=p;
    cursor.style.left=(p*100)+'%';
    const idx=Math.min(7,Math.floor(p*8));
    thumbs.forEach((t,i)=>t.classList.toggle('selected',i===idx));
    const b=APP_BUSES[winId]?._wt;if(b)b.setMorph(p);
  }
  strip.addEventListener('pointerdown',e=>{strip.setPointerCapture(e.pointerId);});
  strip.addEventListener('pointermove',e=>{
    if(!e.buttons)return;
    const r=strip.getBoundingClientRect();setMorph(Math.max(0,Math.min(1,(e.clientX-r.left)/r.width)));
  });
  setMorph(0);
  morphSec.append(mhdr,strip);

  // OSC + Filter
  const oscSec=document.createElement('div');oscSec.className='acid-section';
  const oscHdr=document.createElement('div');oscHdr.className='acid-section-label';oscHdr.textContent='OSC / FILTER';
  const oscRow=document.createElement('div');oscRow.style.cssText='display:flex;gap:12px;flex-wrap:wrap;';
  const kDet=makeKnob({label:'DETUNE',min:-50,max:50,value:0,unit:'¢',size:'sm',tip:'Detune in cents.',onChange:v=>{const b=APP_BUSES[winId]?._wt;if(b)b.voices.forEach(voice=>voice.osc&&(voice.osc.detune.value=v));}});
  const kCut=makeKnob({label:'CUTOFF',min:100,max:18000,value:4000,unit:'Hz',size:'md',tip:'Filter cutoff frequency.',onChange:v=>{const b=APP_BUSES[winId]?._wt;if(b)b.filt.frequency.value=v;}});
  const kRes=makeKnob({label:'RES',min:0.1,max:20,value:1,unit:'',size:'sm',tip:'Filter resonance.',onChange:v=>{const b=APP_BUSES[winId]?._wt;if(b)b.filt.Q.value=v;}});
  const kLevel=makeKnob({label:'LEVEL',min:0,max:100,value:75,unit:'%',size:'sm',tip:'Master output level.',onChange:v=>{const b=APP_BUSES[winId]?._wt;if(b&&b.masterG&&b.masterG.gain)b.masterG.gain.value=v/100;}});
  oscRow.append(kDet,kCut,kRes,kLevel);

  // ADSR row
  const adsrRow=document.createElement('div');adsrRow.style.cssText='display:flex;gap:8px;margin-top:8px;';
  const kAtk=makeKnob({label:'ATK',min:0.001,max:2,value:0.015,unit:'s',size:'sm',tip:'Envelope attack.',onChange:v=>{const b=APP_BUSES[winId]?._wt;if(b)b.attack=v;}});
  const kRel=makeKnob({label:'REL',min:0.01,max:5,value:0.35,unit:'s',size:'sm',tip:'Envelope release.',onChange:v=>{const b=APP_BUSES[winId]?._wt;if(b)b.release=v;}});
  adsrRow.append(kAtk,kRel);
  oscSec.append(oscHdr,oscRow,adsrRow);

  // Mini keyboard — 2 octaves of chromatic note triggers
  const kbSec=document.createElement('div');kbSec.className='acid-section';
  const kbHdr=document.createElement('div');kbHdr.className='acid-section-label';kbHdr.textContent='KEYBOARD';
  const NOTE_NAMES=['C','C#','D','D#','E','F','F#','G','G#','A','A#','B'];
  let kbOct=4;
  const kbRow=document.createElement('div');kbRow.style.cssText='display:flex;gap:3px;flex-wrap:wrap;margin-top:4px;';
  const octStepper=makeStepper({label:'OCT',steps:[{label:'2',value:2},{label:'3',value:3},{label:'4',value:4},{label:'5',value:5},{label:'6',value:6}],value:4,onChange:v=>{kbOct=v;}});
  const noteButtons=NOTE_NAMES.map((note,i)=>{
    const btn=document.createElement('button');
    btn.className='acid-seg-btn';btn.textContent=note;
    btn.style.cssText='flex:1;min-width:26px;padding:6px 2px;font-size:9px;'+(note.includes('#')?'opacity:.7;':'');
    btn.addEventListener('pointerdown',()=>{
      const midi=kbOct*12+i;const freq=440*Math.pow(2,(midi-69)/12);
      const b=APP_BUSES[winId]?._wt;if(b)b.playNote(freq,0.7);
      btn.classList.add('on');
    });
    btn.addEventListener('pointerup',()=>{
      const midi=kbOct*12+i;const freq=440*Math.pow(2,(midi-69)/12);
      const b=APP_BUSES[winId]?._wt;if(b)b.stopNote(freq);
      btn.classList.remove('on');
    });
    btn.addEventListener('pointerleave',()=>{
      const midi=kbOct*12+i;const freq=440*Math.pow(2,(midi-69)/12);
      const b=APP_BUSES[winId]?._wt;if(b)b.stopNote(freq);
      btn.classList.remove('on');
    });
    kbRow.appendChild(btn);return btn;
  });
  kbSec.append(kbHdr,octStepper,kbRow);

  sec.append(hdr);
  ui.append(sec,morphSec,oscSec,kbSec);
  wb.appendChild(ui);
};

/* =====================================================
   WIN-STEPSEQ — melodic step sequencer with velocity bars
   ===================================================== */
APP_FACTORIES['win-stepseq'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='STEP SEQUENCER';

  const NOTES=['C','C#','D','D#','E','F','F#','G','G#','A','A#','B'];
  const SCALES={
    Chromatic:[0,1,2,3,4,5,6,7,8,9,10,11],
    Major:[0,2,4,5,7,9,11],
    Minor:[0,2,3,5,7,8,10],
    Pentatonic:[0,2,4,7,9],
    Blues:[0,3,5,6,7,10],
    Dorian:[0,2,3,5,7,9,10]
  };
  let rootNote=0,scaleName='Major',seqOct=4,running=false,currentStep=0;
  const stepData=Array.from({length:16},(_,i)=>({active:i<8,note:0,vel:0.7,prob:1.0}));

  // Controls row
  const ctrlRow=document.createElement('div');ctrlRow.style.cssText='display:flex;gap:8px;margin-bottom:8px;align-items:center;';
  const rootStep=makeStepper({label:'ROOT',steps:NOTES.map((n,i)=>({label:n,value:i})),onChange:v=>{rootNote=v;updateStepNotes();}});
  const scaleStep=makeStepper({label:'SCALE',steps:Object.keys(SCALES).map(n=>({label:n,value:n})),onChange:v=>{scaleName=v;updateStepNotes();}});
  const octStep=makeStepper({label:'OCT',steps:[{label:'2',value:2},{label:'3',value:3},{label:'4',value:4},{label:'5',value:5}],value:4,onChange:v=>{seqOct=v;}});
  ctrlRow.append(rootStep,scaleStep,octStep);

  // Velocity bars
  const velWrap=document.createElement('div');velWrap.className='acid-vel-steps';
  const bars=stepData.map((step,i)=>{
    const bar=document.createElement('div');bar.className='acid-vel-bar'+(step.active?'':' off');
    const inner=document.createElement('div');inner.className='acid-vel-bar-inner';
    bar.appendChild(inner);
    inner.style.height=(step.vel*100)+'%';
    bar.style.height='100%';bar.style.flex='1';
    let dragging=false;
    bar.addEventListener('pointerdown',e=>{
      if(e.button===2){step.active=!step.active;bar.classList.toggle('off',!step.active);return;}
      dragging=true;bar.setPointerCapture(e.pointerId);
      const r=bar.getBoundingClientRect();
      step.vel=Math.max(0.02,Math.min(1,1-(e.clientY-r.top)/r.height));
      inner.style.height=(step.vel*100)+'%';
    });
    bar.addEventListener('pointermove',e=>{
      if(!dragging)return;
      const r=bar.getBoundingClientRect();
      step.vel=Math.max(0.02,Math.min(1,1-(e.clientY-r.top)/r.height));
      inner.style.height=(step.vel*100)+'%';
    });
    bar.addEventListener('pointerup',()=>{dragging=false;});
    bar.addEventListener('contextmenu',e=>{e.preventDefault();step.active=!step.active;bar.classList.toggle('off',!step.active);});
    return bar;
  });
  bars.forEach(b=>velWrap.appendChild(b));

  // Note chips row (below velocity bars)
  const noteRow=document.createElement('div');noteRow.style.cssText='display:flex;gap:2px;margin-top:3px;';
  const noteChips=stepData.map((_,i)=>{
    const chip=document.createElement('div');chip.style.cssText='flex:1;font-size:7px;text-align:center;color:rgba(255,255,255,.4);letter-spacing:0;overflow:hidden;white-space:nowrap;';
    chip.textContent='C4';noteRow.appendChild(chip);return chip;
  });
  function updateStepNotes(){
    const scale=SCALES[scaleName]||SCALES.Major;
    stepData.forEach((step,i)=>{
      const scIdx=i%scale.length;const oct=seqOct+Math.floor(i/scale.length);
      const midi=(rootNote+scale[scIdx])+(oct+1)*12;
      step.note=midi;
      const noteName=NOTES[(rootNote+scale[scIdx])%12];
      noteChips[i].textContent=noteName+oct;
    });
  }
  updateStepNotes();

  // Swing + prob knobs
  const paramRow=document.createElement('div');paramRow.style.cssText='display:flex;gap:10px;margin-top:8px;align-items:center;';
  const kSwing=makeKnob({label:'SWING',min:0,max:100,value:0,unit:'%',size:'sm',tip:'Swing/shuffle amount.'});
  const kProb=makeKnob({label:'PROB',min:0,max:100,value:100,unit:'%',size:'sm',tip:'Global trigger probability.',onChange:v=>{stepData.forEach(s=>s.prob=v/100);}});
  const kGate=makeKnob({label:'GATE',min:5,max:200,value:90,unit:'%',size:'sm',tip:'Note gate length as % of step.'});
  paramRow.append(kSwing,kProb,kGate);

  // Transport step hook
  const seqD=APP_BUSES[winId]?._seq;
  if(seqD){
    window.__prScheduleStep=(function(orig){
      return function(step,time){
        if(orig)orig(step,time);
        const s=stepData[step%16];
        // apply swing: delay odd steps by a fraction of the step duration
        const swingMs=(step%2===1)?(60/tempo/4)*1000*(kSwing._val()/100)*0.5:0;
        if(s&&s.active&&Math.random()<s.prob){
          const freq=440*Math.pow(2,(s.note-69)/12);
          const bWT=APP_BUSES['win-wavetable']?._wt;
          if(bWT){
            const gateDur=Math.max(50,(60/tempo/4)*(kGate._val()/100)*1000);
            setTimeout(()=>{bWT.playNote(freq,s.vel);setTimeout(()=>bWT.stopNote(freq),gateDur);},swingMs);
          }
        }
        bars.forEach((b,i)=>b.classList.toggle('active-step',i===step%16));
      };
    })(window.__prScheduleStep);
  }

  sec.append(hdr,ctrlRow,velWrap,noteRow,paramRow);
  ui.append(sec);wb.appendChild(ui);
};

/* =====================================================
   WIN-TAPE — tape machine with wow/flutter and age macro
   ===================================================== */
APP_FACTORIES['win-tape'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='TAPE MACHINE';

  // Reel canvas
  const reelWrap=document.createElement('div');reelWrap.style.cssText='width:100%;height:90px;border-radius:8px;background:rgba(0,0,0,.5);border:1px solid rgba(210,160,60,.15);margin-bottom:10px;overflow:hidden;position:relative;';
  const reelCv=document.createElement('canvas');reelCv.style.cssText='width:100%;height:100%;';
  reelWrap.appendChild(reelCv);
  let reelAngle=0;
  function drawReel(){
    const {ctx,W,H}=setupCanvas(reelCv,300,90);
    ctx.clearRect(0,0,W,H);
    const accentCol=acidColor?acidColor(.8):'rgba(210,160,60,.8)';
    const accentDim=acidColor?acidColor(.25):'rgba(210,160,60,.25)';
    // Left reel
    const lx=W*0.27,ly=H*0.5,r=H*0.38;
    ctx.strokeStyle=accentDim;ctx.lineWidth=2;ctx.beginPath();ctx.arc(lx,ly,r,0,Math.PI*2);ctx.stroke();
    ctx.strokeStyle=accentCol;ctx.lineWidth=1.5;ctx.beginPath();ctx.arc(lx,ly,r*0.5,0,Math.PI*2);ctx.stroke();
    for(let s=0;s<6;s++){
      const a=reelAngle+s*(Math.PI/3);
      ctx.strokeStyle=accentCol;ctx.lineWidth=1.5;ctx.beginPath();
      ctx.moveTo(lx+Math.cos(a)*r*0.2,ly+Math.sin(a)*r*0.2);
      ctx.lineTo(lx+Math.cos(a)*r*0.45,ly+Math.sin(a)*r*0.45);
      ctx.stroke();
    }
    ctx.fillStyle=accentDim;ctx.beginPath();ctx.arc(lx,ly,r*0.12,0,Math.PI*2);ctx.fill();
    // Right reel (faster spin)
    const rx=W*0.73,ry=H*0.5,r2=H*0.33;
    ctx.strokeStyle=accentDim;ctx.lineWidth=2;ctx.beginPath();ctx.arc(rx,ry,r2,0,Math.PI*2);ctx.stroke();
    ctx.strokeStyle=accentCol;ctx.lineWidth=1.5;ctx.beginPath();ctx.arc(rx,ry,r2*0.48,0,Math.PI*2);ctx.stroke();
    for(let s=0;s<6;s++){
      const a=reelAngle*1.3+s*(Math.PI/3);
      ctx.strokeStyle=accentCol;ctx.lineWidth=1.5;ctx.beginPath();
      ctx.moveTo(rx+Math.cos(a)*r2*0.2,ry+Math.sin(a)*r2*0.2);
      ctx.lineTo(rx+Math.cos(a)*r2*0.45,ry+Math.sin(a)*r2*0.45);
      ctx.stroke();
    }
    ctx.fillStyle=accentDim;ctx.beginPath();ctx.arc(rx,ry,r2*0.12,0,Math.PI*2);ctx.fill();
    // Tape path between reels
    ctx.strokeStyle=accentDim;ctx.lineWidth=3;ctx.beginPath();
    ctx.moveTo(lx+r*0.9,ly);ctx.bezierCurveTo(W*0.4,ly-10,W*0.6,ly-10,rx-r2*0.9,ry);
    ctx.stroke();
    reelAngle+=0.008;
  }
  (function loop(){if(!win.isConnected)return;requestAnimationFrame(loop);drawReel();})();

  // AGE macro knob (the hero control — sets wow+flutter+sat simultaneously)
  const ageSec=document.createElement('div');ageSec.style.cssText='display:flex;gap:12px;align-items:flex-start;margin-bottom:8px;';
  const kAge=makeKnob({label:'AGE',min:0,max:100,value:20,unit:'%',size:'lg',tip:'Global tape age: increases wow, flutter, and saturation together.',onChange:v=>{
    const b=APP_BUSES[winId]?._tape;if(!b)return;
    const a=v/100;
    b.setWow(a*0.7);b.setFlutter(a*0.6);b.setSat(a*0.5);
    kWow._update(a*70);kFlutter._update(a*60);kSat._update(a*50);
  }});
  const detailCol=document.createElement('div');detailCol.style.cssText='flex:1;display:flex;flex-direction:column;gap:6px;';
  const kWow=makeKnob({label:'WOW',min:0,max:100,value:14,unit:'%',size:'sm',tip:'Low-frequency pitch wobble.',onChange:v=>{const b=APP_BUSES[winId]?._tape;if(b)b.setWow(v/100);}});
  const kFlutter=makeKnob({label:'FLUTTER',min:0,max:100,value:12,unit:'%',size:'sm',tip:'High-frequency pitch flutter.',onChange:v=>{const b=APP_BUSES[winId]?._tape;if(b)b.setFlutter(v/100);}});
  const kSat=makeKnob({label:'SATURATION',min:0,max:100,value:10,unit:'%',size:'sm',tip:'Tape saturation and warmth.',onChange:v=>{const b=APP_BUSES[winId]?._tape;if(b)b.setSat(v/100);}});
  const detailRow=document.createElement('div');detailRow.style.cssText='display:flex;gap:6px;';
  detailRow.append(kWow,kFlutter,kSat);
  const sBias=makeSlider({label:'BIAS LOSS',min:0,max:100,value:0,unit:'%',tip:'High-frequency roll-off (old tape head).',onChange:v=>{const b=APP_BUSES[winId]?._tape;if(b)b.setBias(v/100);}});
  detailCol.append(detailRow,sBias);
  ageSec.append(kAge,detailCol);

  sec.append(hdr,reelWrap,ageSec);
  ui.appendChild(sec);wb.appendChild(ui);
};

/* =====================================================
   WIN-FORMANT — vowel filter with 2D vowel pad
   ===================================================== */
APP_FACTORIES['win-formant'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='VOWEL FILTER';

  // Vowel positions (normalised 0-1 x,y in the pad)
  const VOWELS={A:{x:.18,y:.82},E:{x:.35,y:.32},I:{x:.72,y:.22},O:{x:.70,y:.72},U:{x:.55,y:.88}};
  const FORMANTS={A:[800,1200,2500],E:[400,2000,2800],I:[300,2500,3200],O:[500,800,2500],U:[300,700,2400]};
  let vowelX=0.18,vowelY=0.82;

  const padWrap=document.createElement('div');padWrap.className='acid-vowel-pad';
  const padCv=document.createElement('canvas');padCv.style.cssText='position:absolute;inset:0;width:100%;height:100%;pointer-events:none;';
  const padCursor=document.createElement('div');padCursor.className='acid-vowel-cursor';
  padWrap.append(padCv,padCursor);

  // Vowel dots
  Object.entries(VOWELS).forEach(([name,pos])=>{
    const dot=document.createElement('div');dot.className='acid-vowel-dot';dot.textContent=name;
    dot.style.left=(pos.x*100)+'%';dot.style.top=(pos.y*100)+'%';
    dot.addEventListener('click',()=>{setVowelXY(pos.x,pos.y);});
    padWrap.appendChild(dot);
  });

  function interpFormants(x,y){
    let totalW=0;const f=[0,0,0];
    Object.entries(VOWELS).forEach(([name,pos])=>{
      const dx=x-pos.x,dy=y-pos.y;
      const dist=Math.sqrt(dx*dx+dy*dy);
      const w=Math.max(0,1-dist*2.5);
      totalW+=w;
      const fm=FORMANTS[name];
      f[0]+=fm[0]*w;f[1]+=fm[1]*w;f[2]+=fm[2]*w;
    });
    if(totalW>0){f[0]/=totalW;f[1]/=totalW;f[2]/=totalW;}
    return f;
  }

  function drawPadBg(){
    const {ctx,W,H}=setupCanvas(padCv,300,160);ctx.clearRect(0,0,W,H);
    // Gradient influence zones
    Object.values(VOWELS).forEach(pos=>{
      const grd=ctx.createRadialGradient(pos.x*W,pos.y*H,0,pos.x*W,pos.y*H,W*0.3);
      grd.addColorStop(0,'rgba(220,80,220,.12)');grd.addColorStop(1,'rgba(0,0,0,0)');
      ctx.fillStyle=grd;ctx.fillRect(0,0,W,H);
    });
  }

  function setVowelXY(x,y){
    vowelX=x;vowelY=y;
    padCursor.style.left=(x*100)+'%';padCursor.style.top=(y*100)+'%';
    const f=interpFormants(x,y);
    const b=APP_BUSES[winId]?._formant;if(b)b.setFormants(f[0],f[1],f[2]);
    // Highlight nearest vowel dot
    let near=null,nearDist=Infinity;
    Object.entries(VOWELS).forEach(([name,pos])=>{
      const d=Math.hypot(x-pos.x,y-pos.y);if(d<nearDist){nearDist=d;near=name;}
    });
    padWrap.querySelectorAll('.acid-vowel-dot').forEach(d=>{d.classList.toggle('near',d.textContent===near);});
  }
  padWrap.addEventListener('pointerdown',e=>{padWrap.setPointerCapture(e.pointerId);const r=padWrap.getBoundingClientRect();setVowelXY((e.clientX-r.left)/r.width,(e.clientY-r.top)/r.height);});
  padWrap.addEventListener('pointermove',e=>{if(e.buttons){const r=padWrap.getBoundingClientRect();setVowelXY(Math.max(0,Math.min(1,(e.clientX-r.left)/r.width)),Math.max(0,Math.min(1,(e.clientY-r.top)/r.height)));}});

  const paramRow=document.createElement('div');paramRow.style.cssText='display:flex;gap:10px;margin-top:8px;';
  const kQ=makeKnob({label:'RESONANCE',min:1,max:20,value:4,unit:'',size:'sm',tip:'Formant filter sharpness.',onChange:v=>{const b=APP_BUSES[winId]?._formant;if(b)b.setQ(v);}});
  const sMix=makeSlider({label:'MIX',min:0,max:100,value:70,unit:'%',tip:'Dry/wet blend.',onChange:v=>{const b=APP_BUSES[winId]?._formant;if(b)b.setMix(v/100);}});
  paramRow.append(kQ,sMix);

  sec.append(hdr,padWrap,paramRow);
  ui.appendChild(sec);wb.appendChild(ui);
  new ResizeObserver(drawPadBg).observe(padWrap);
  drawPadBg();
  setVowelXY(0.18,0.82);
};

/* =====================================================
   WIN-SIDECHAIN — sidechain compressor with pumping visualizer
   ===================================================== */
APP_FACTORIES['win-sidechain'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='SIDECHAIN COMP';

  // Pumping visualizer canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='width:100%;height:70px;border-radius:8px;background:rgba(0,0,0,.5);border:1px solid rgba(50,220,130,.15);margin-bottom:10px;overflow:hidden;position:relative;';
  const cv=document.createElement('canvas');cv.style.cssText='width:100%;height:100%;';
  cvWrap.appendChild(cv);
  const grHistory=new Array(120).fill(0);
  function drawPump(){
    const {ctx,W,H}=setupCanvas(cv,300,70);ctx.clearRect(0,0,W,H);
    const b=APP_BUSES[winId]?._sc;
    if(b){grHistory.push(b.grNow||0);grHistory.shift();}
    // GR history waveform
    ctx.strokeStyle=acidColor?acidColor(.7):'rgba(50,220,130,.7)';ctx.lineWidth=2;ctx.beginPath();
    const maxGR=24;
    grHistory.forEach((gr,i)=>{
      const x=i/grHistory.length*W;
      const y=(gr/maxGR)*H;
      if(i===0)ctx.moveTo(x,H-y);else ctx.lineTo(x,H-y);
    });
    ctx.stroke();
    // Fill under
    ctx.lineTo(W,H);ctx.lineTo(0,H);ctx.closePath();
    ctx.fillStyle=acidColor?acidColor(.12):'rgba(50,220,130,.12)';ctx.fill();
    // GR value text
    const curGR=grHistory[grHistory.length-1];
    ctx.fillStyle='rgba(255,255,255,.5)';ctx.font='9px monospace';
    ctx.fillText('GR: -'+curGR.toFixed(1)+'dB',6,14);
  }
  (function loop(){if(!win.isConnected)return;requestAnimationFrame(loop);drawPump();})();

  const ATK_STEPS=[{label:'0.1ms',value:.0001},{label:'1ms',value:.001},{label:'5ms',value:.005},{label:'10ms',value:.01},{label:'20ms',value:.02},{label:'50ms',value:.05}];
  const REL_STEPS=[{label:'50ms',value:.05},{label:'100ms',value:.1},{label:'200ms',value:.2},{label:'400ms',value:.4},{label:'800ms',value:.8},{label:'2s',value:2}];

  const thrND=makeNumDrag({label:'THRESHOLD',unit:' dB',min:-60,max:0,value:-20,step:1,tip:'Sidechain trigger threshold.',onChange:v=>{const b=APP_BUSES[winId]?._sc;if(b)b.setThr(v);}});
  const ratioStep=makeStepper({label:'RATIO',steps:[{label:'2:1',value:2},{label:'4:1',value:4},{label:'8:1',value:8},{label:'20:1',value:20},{label:'∞:1',value:100}],value:8,onChange:v=>{const b=APP_BUSES[winId]?._sc;if(b)b.setRatio(v);}});
  const atkStep=makeStepper({label:'ATTACK',steps:ATK_STEPS,value:.005,onChange:v=>{const b=APP_BUSES[winId]?._sc;if(b)b.setAtk(v);}});
  const relStep=makeStepper({label:'RELEASE',steps:REL_STEPS,value:.12,onChange:v=>{const b=APP_BUSES[winId]?._sc;if(b)b.setRel(v);}});
  const kDepth=makeKnob({label:'DEPTH',min:0,max:100,value:100,unit:'%',size:'md',tip:'Maximum gain reduction depth.',onChange:v=>{const b=APP_BUSES[winId]?._sc;if(b)b.setDepth(v/100);}});

  const row=document.createElement('div');row.style.cssText='display:flex;gap:10px;align-items:flex-start;';
  const paramCol=document.createElement('div');paramCol.style.cssText='flex:1;display:flex;flex-direction:column;gap:6px;';
  paramCol.append(thrND,ratioStep,atkStep,relStep);
  row.append(paramCol,kDepth);

  sec.append(hdr,cvWrap,row);
  ui.appendChild(sec);wb.appendChild(ui);
};

/* =====================================================
   WIN-GLITCH — glitch/stutter with pattern grid
   ===================================================== */
APP_FACTORIES['win-glitch'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='GLITCH';

  // Pattern grid — 2 rows × 8 columns
  const gridWrap=document.createElement('div');gridWrap.style.cssText='margin-bottom:8px;';
  const rowLabels=['A','B'];
  const patterns=[Array(8).fill(false),Array(8).fill(false)];
  patterns[0][0]=true;patterns[0][4]=true;
  const grid=document.createElement('div');grid.className='acid-glitch-grid';grid.style.gridTemplateColumns='repeat(8,1fr)';
  const cells=[];
  for(let row=0;row<2;row++){
    for(let col=0;col<8;col++){
      const cell=document.createElement('div');cell.className='acid-glitch-cell'+(patterns[row][col]?' on':'');
      cell.addEventListener('click',()=>{
        patterns[row][col]=!patterns[row][col];
        cell.classList.toggle('on',patterns[row][col]);
        const bg=APP_BUSES[winId]?._glitch;if(bg)bg.pat2d[row][col]=patterns[row][col];
      });
      cells.push(cell);grid.appendChild(cell);
    }
  }
  gridWrap.appendChild(grid);

  // Controls
  const ctrlRow=document.createElement('div');ctrlRow.style.cssText='display:flex;gap:10px;align-items:flex-start;';
  const RATE_STEPS=[{label:'1/16',value:0.0625},{label:'1/8',value:0.125},{label:'1/4',value:0.25},{label:'1/2',value:0.5},{label:'1 BAR',value:1}];
  const SLICE_STEPS=[{label:'1/64',value:0.015},{label:'1/32',value:0.031},{label:'1/16',value:0.0625},{label:'1/8',value:0.125},{label:'1/4',value:0.25}];
  const rateStep=makeStepper({label:'FIRE RATE',steps:RATE_STEPS,value:0.125,onChange:v=>{const b=APP_BUSES[winId]?._glitch;if(b)b.setFireRate(v);}});
  const sliceStep=makeStepper({label:'SLICE',steps:SLICE_STEPS,value:0.0625,onChange:v=>{const b=APP_BUSES[winId]?._glitch;if(b)b.setDly(v);}});
  const kProb=makeKnob({label:'PROB',min:0,max:100,value:60,unit:'%',size:'sm',tip:'Trigger probability per beat.'});
  const kFB=makeKnob({label:'REPEAT',min:0,max:100,value:30,unit:'%',size:'sm',tip:'Feedback — how many times the slice repeats.',onChange:v=>{const b=APP_BUSES[winId]?._glitch;if(b)b.setFB(v/100);}});
  const kCol=document.createElement('div');kCol.style.cssText='display:flex;flex-direction:column;gap:6px;';
  kCol.append(rateStep,sliceStep);
  const kRow=document.createElement('div');kRow.style.cssText='display:flex;gap:8px;';
  kRow.append(kProb,kFB);
  ctrlRow.append(kCol,kRow);

  // Waveform preview canvas
  const wvWrap=document.createElement('div');wvWrap.style.cssText='width:100%;height:50px;border-radius:6px;background:rgba(0,0,0,.4);border:1px solid rgba(255,220,0,.1);margin-bottom:8px;overflow:hidden;';
  const wvCv=document.createElement('canvas');wvCv.style.cssText='width:100%;height:100%;';
  wvWrap.appendChild(wvCv);
  let glitchPhase=0;
  function drawGlitch(){
    const {ctx,W,H}=setupCanvas(wvCv,360,50);ctx.clearRect(0,0,W,H);
    const ac2=acidColor?acidColor(.7):'rgba(255,220,0,.7)';
    ctx.strokeStyle=ac2;ctx.lineWidth=1.5;ctx.beginPath();
    for(let x=0;x<W;x++){
      const t=x/W+glitchPhase;
      const glitchZone=patterns[0][Math.floor(t*8)%8]||patterns[1][Math.floor(t*8)%8];
      let y;
      if(glitchZone){
        y=(Math.sin(t*Math.PI*60)*(0.4+Math.random()*0.2))*H*0.45+H/2;
      } else {
        y=Math.sin(t*Math.PI*8)*H*0.15+H/2;
      }
      if(x===0)ctx.moveTo(x,y);else ctx.lineTo(x,y);
    }
    ctx.stroke();glitchPhase+=0.002;
  }
  (function loop(){if(!win.isConnected)return;requestAnimationFrame(loop);drawGlitch();})();

  sec.append(hdr,wvWrap,gridWrap,ctrlRow);
  ui.appendChild(sec);wb.appendChild(ui);
};

/* =====================================================
   WIN-OSC-BANK — additive synthesis oscillator bank
   ===================================================== */
APP_FACTORIES['win-osc-bank'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='OSCILLATOR BANK';

  // Waveform preview canvas
  const wvWrap=document.createElement('div');wvWrap.style.cssText='width:100%;height:60px;border-radius:8px;background:rgba(0,0,0,.5);border:1px solid rgba(40,200,200,.15);margin-bottom:8px;overflow:hidden;';
  const wvCv=document.createElement('canvas');wvCv.style.cssText='width:100%;height:100%;';
  wvWrap.appendChild(wvCv);
  let drawbarVals=new Array(8).fill(0);drawbarVals[0]=0.8;
  function drawWavePreview(){
    const {ctx,W,H}=setupCanvas(wvCv,380,60);ctx.clearRect(0,0,W,H);
    ctx.strokeStyle=acidColor?acidColor(.8):'rgba(40,200,200,.8)';ctx.lineWidth=2;ctx.beginPath();
    for(let px=0;px<W;px++){
      const t=px/W;
      let y=0;
      drawbarVals.forEach((v,h)=>{y+=Math.sin(t*Math.PI*2*(h+1))*v;});
      const norm=(y/(drawbarVals.reduce((s,v)=>s+v,0)||1)+1)/2;
      const yp=norm*(H-8)+4;
      if(px===0)ctx.moveTo(px,yp);else ctx.lineTo(px,yp);
    }
    ctx.stroke();
  }

  // Drawbar controls
  const drawbarSec=document.createElement('div');drawbarSec.className='acid-section';
  const dbHdr=document.createElement('div');dbHdr.className='acid-section-label';dbHdr.textContent='HARMONICS';
  const dbRow=document.createElement('div');dbRow.className='acid-drawbar-row';
  const HARM_LABELS=["1'","2'","4'","8'","16'","3'","5⅓'","10⅔'"];
  const dbEls=drawbarVals.map((v,i)=>{
    const wrap=document.createElement('div');wrap.className='acid-drawbar';
    const track=document.createElement('div');track.className='acid-drawbar-track';
    const fill=document.createElement('div');fill.className='acid-drawbar-fill';
    fill.style.height=(v*100)+'%';
    track.appendChild(fill);
    const label=document.createElement('div');label.className='acid-drawbar-label';label.textContent=HARM_LABELS[i];
    let dragging=false;
    track.addEventListener('pointerdown',e=>{dragging=true;track.setPointerCapture(e.pointerId);});
    track.addEventListener('pointermove',e=>{
      if(!dragging)return;
      const r=track.getBoundingClientRect();
      const val=Math.max(0,Math.min(1,1-(e.clientY-r.top)/r.height));
      drawbarVals[i]=val;fill.style.height=(val*100)+'%';
      const b=APP_BUSES[winId]?._bank;if(b)b.setHarmonic(i,val);
      drawWavePreview();
    });
    track.addEventListener('pointerup',()=>{dragging=false;});
    wrap.append(track,label);dbRow.appendChild(wrap);return {fill,track};
  });
  drawbarSec.append(dbHdr,dbRow);

  // Fundamental frequency + master
  const paramSec=document.createElement('div');paramSec.className='acid-section';
  const pHdr=document.createElement('div');pHdr.className='acid-section-label';pHdr.textContent='MASTER';
  const pRow=document.createElement('div');pRow.style.cssText='display:flex;gap:10px;align-items:center;';
  const fundND=makeNumDrag({label:'FUNDAMENTAL',unit:' Hz',min:20,max:2000,value:220,step:1,tip:'Base frequency — all harmonics scale from this.',onChange:v=>{const b=APP_BUSES[winId]?._bank;if(b)b.setFundamental(v);}});
  const kMaster=makeKnob({label:'MASTER',min:0,max:100,value:50,unit:'%',size:'md',tip:'Overall output level.',onChange:v=>{const b=APP_BUSES[winId]?._bank;if(b)b.setMaster(v/100);}});
  pRow.append(fundND,kMaster);
  paramSec.append(pHdr,pRow);

  sec.append(hdr,wvWrap);
  ui.append(sec,drawbarSec,paramSec);
  wb.appendChild(ui);
  // Sync visual defaults to audio on first open
  const _b=APP_BUSES[winId]?._bank;
  if(_b){drawbarVals.forEach((v,i)=>_b.setHarmonic(i,v));_b.setMaster(kMaster._val()/100);}
  new ResizeObserver(drawWavePreview).observe(wvWrap);
  (function loop(){if(!win.isConnected)return;requestAnimationFrame(loop);drawWavePreview();})();
};

/* =====================================================
   WIN-FREQSHIFT — frequency shifter with sideband canvas
   ===================================================== */
APP_FACTORIES['win-freqshift'] = function(win){
  const winId=win.id,wb=win.querySelector('.wbody');
  const ui=document.createElement('div');ui.className='acid-app-ui';
  const sec=document.createElement('div');sec.className='acid-section';
  const hdr=document.createElement('div');hdr.className='acid-section-label';hdr.textContent='FREQ SHIFTER';

  // Sideband visualizer canvas
  const cvWrap=document.createElement('div');cvWrap.style.cssText='width:100%;height:90px;border-radius:8px;background:rgba(0,0,0,.5);border:1px solid rgba(0,220,180,.15);margin-bottom:10px;overflow:hidden;';
  const cv=document.createElement('canvas');cv.style.cssText='width:100%;height:100%;';
  cvWrap.appendChild(cv);
  let shiftHz=100;
  function drawSidebands(){
    const {ctx,W,H}=setupCanvas(cv,280,90);ctx.clearRect(0,0,W,H);
    const acol=acidColor?acidColor(.7):'rgba(0,220,180,.7)';
    // Frequency grid (log scale 20Hz–20kHz)
    ctx.strokeStyle='rgba(255,255,255,.05)';ctx.lineWidth=1;
    [100,200,500,1000,2000,5000,10000].forEach(f=>{
      const x=(Math.log10(f)-Math.log10(20))/(Math.log10(20000)-Math.log10(20))*W;
      ctx.beginPath();ctx.moveTo(x,0);ctx.lineTo(x,H);ctx.stroke();
      ctx.fillStyle='rgba(255,255,255,.2)';ctx.font='7px monospace';
      ctx.fillText(f>=1000?Math.round(f/100)/10+'k':f,x+2,H-2);
    });
    // Input partials (simulated 3 harmonics)
    const partials=[220,440,880,1320,1760];
    partials.forEach(f=>{
      if(f<20||f>20000)return;
      const x=(Math.log10(f)-Math.log10(20))/(Math.log10(20000)-Math.log10(20))*W;
      ctx.strokeStyle='rgba(255,255,255,.25)';ctx.lineWidth=1.5;ctx.beginPath();ctx.moveTo(x,H);ctx.lineTo(x,H*0.2);ctx.stroke();
      // Shifted versions
      const sf=f+shiftHz;
      if(sf>20&&sf<20000){
        const sx=(Math.log10(sf)-Math.log10(20))/(Math.log10(20000)-Math.log10(20))*W;
        ctx.strokeStyle=acol;ctx.lineWidth=2;ctx.beginPath();ctx.moveTo(sx,H);ctx.lineTo(sx,H*0.25);ctx.stroke();
        // Arrow showing shift
        ctx.strokeStyle='rgba(255,255,255,.15)';ctx.lineWidth=1;ctx.setLineDash([2,3]);
        ctx.beginPath();ctx.moveTo(x,H*0.5);ctx.lineTo(sx,H*0.5);ctx.stroke();ctx.setLineDash([]);
      }
    });
  }
  (function loop(){if(!win.isConnected)return;requestAnimationFrame(loop);drawSidebands();})();

  // Main control: large shift num-drag (the hero)
  const shiftND=makeNumDrag({label:'SHIFT',unit:' Hz',min:-2000,max:2000,value:100,step:1,tip:'Frequency shift in Hz — positive shifts up, negative shifts down.',onChange:v=>{
    shiftHz=v;
    const b=APP_BUSES[winId]?._fs;if(b)b.setShift(v);
  }});
  shiftND.style.cssText=(shiftND.style.cssText||'')+'font-size:14px;padding:8px;';

  // Fine tune + mix
  const paramRow=document.createElement('div');paramRow.style.cssText='display:flex;gap:10px;margin-top:8px;align-items:center;';
  const kFine=makeKnob({label:'FINE',min:-100,max:100,value:0,unit:'Hz',size:'sm',tip:'Fine-tune ±100 Hz on top of the main shift.',onChange:v=>{const b=APP_BUSES[winId]?._fs;const base=shiftHz;if(b)b.setShift(base+v);}});
  const sMix=makeSlider({label:'MIX',min:0,max:100,value:100,unit:'%',tip:'Dry/wet blend.',onChange:v=>{const b=APP_BUSES[winId]?._fs;if(b)b.setMix(v/100);}});
  paramRow.append(kFine,sMix);

  sec.append(hdr,cvWrap,shiftND,paramRow);
  ui.appendChild(sec);wb.appendChild(ui);
  new ResizeObserver(drawSidebands).observe(cvWrap);
};

/* =====================================================
   MULTI-INSTANCE — audio bus init for spawned windows
   ===================================================== */
function initInstanceBus(winId,baseId){
  if(!ac)return;
  if(!APP_BUSES[winId]){
    const input=ac.createGain();
    const output=ac.createGain();
    output.connect(drySum);
    APP_BUSES[winId]={input,output};
  }
  const b=APP_BUSES[winId];
  switch(baseId){
    case 'win-compressor':{
      const node=ac.createDynamicsCompressor();
      node.threshold.value=-18;node.ratio.value=4;
      node.attack.value=0.01;node.release.value=0.1;node.knee.value=3;
      const makeup=ac.createGain();makeup.gain.value=Math.pow(10,4/20);
      b.input.connect(node);node.connect(makeup);makeup.connect(b.output);
      b._comp={node,makeup};break;
    }
    case 'win-reverb':{
      const pre=ac.createDelay(0.1);pre.delayTime.value=0.015;
      const conv=ac.createConvolver();conv.buffer=makeImpulse(ac,1.8,2.2);
      const wet=ac.createGain();wet.gain.value=0.35;
      const dry=ac.createGain();dry.gain.value=0.65;
      const damp=ac.createBiquadFilter();damp.type='lowpass';damp.frequency.value=8000;
      b.input.connect(dry);dry.connect(b.output);
      b.input.connect(pre);pre.connect(conv);conv.connect(damp);damp.connect(wet);wet.connect(b.output);
      b._rev={pre,conv,wet,dry,damp};break;
    }
    case 'win-eq':{
      const freqs=[80,250,1000,4000,12000];
      const types=['lowshelf','peaking','peaking','peaking','highshelf'];
      const bands=freqs.map((f,i)=>{const n=ac.createBiquadFilter();n.type=types[i];n.frequency.value=f;if(types[i]==='peaking')n.Q.value=0.8;return n;});
      b.input.connect(bands[0]);
      bands.forEach((bn,i)=>{if(bands[i+1])bn.connect(bands[i+1]);});
      bands[bands.length-1].connect(b.output);
      b._bands=bands;break;
    }
    case 'win-delay':{
      const dly=ac.createDelay(2.0);dly.delayTime.value=0.5;
      const fb=ac.createGain();fb.gain.value=0.35;
      const dry=ac.createGain();dry.gain.value=0.7;
      const wet=ac.createGain();wet.gain.value=0.4;
      const panner=ac.createStereoPanner();panner.pan.value=0;
      b.input.connect(dry);dry.connect(b.output);
      b.input.connect(dly);dly.connect(fb);fb.connect(dly);dly.connect(wet);wet.connect(panner);panner.connect(b.output);
      b._dly={dly,fb,dry,wet,panner};break;
    }
    case 'win-lofi':{
      const crusher=ac.createWaveShaper();crusher.oversample='4x';
      const warmth=ac.createBiquadFilter();warmth.type='lowpass';warmth.frequency.value=20000;
      b.input.connect(crusher);crusher.connect(warmth);warmth.connect(b.output);
      function makeCrushCurve(bits){const steps=Math.pow(2,bits),n=4096,c=new Float32Array(n);for(let i=0;i<n;i++){const x=(i*2/n)-1;c[i]=Math.round(x*steps)/steps;}return c;}
      b._lofi={crusher,warmth,makeCrushCurve};
      crusher.curve=makeCrushCurve(16);break;
    }
    case 'win-gate':{
      const gateGain=ac.createGain();gateGain.gain.value=1;
      const analyser=ac.createAnalyser();analyser.fftSize=512;
      b.input.connect(analyser);b.input.connect(gateGain);gateGain.connect(b.output);
      b._gate={gateGain,analyser,open:false};break;
    }
    case 'win-vol':{
      const vol=ac.createGain();vol.gain.value=0.8;
      b.input.connect(vol);vol.connect(b.output);
      b._vol=vol;break;
    }
    case 'win-pan':{
      const panner=ac.createStereoPanner();panner.pan.value=0;
      b.input.connect(panner);panner.connect(b.output);
      b._panner=panner;break;
    }
    case 'win-chorus':{
      const d1=ac.createDelay(0.05);d1.delayTime.value=0.02;
      const d2=ac.createDelay(0.05);d2.delayTime.value=0.025;
      const l1=ac.createOscillator();l1.frequency.value=0.8;l1.start();
      const l2=ac.createOscillator();l2.frequency.value=1.1;l2.start();
      const lg1=ac.createGain();lg1.gain.value=0.005;const lg2=ac.createGain();lg2.gain.value=0.005;
      l1.connect(lg1);lg1.connect(d1.delayTime);l2.connect(lg2);lg2.connect(d2.delayTime);
      const dry=ac.createGain();dry.gain.value=0.6;
      const w1=ac.createGain();w1.gain.value=0.35;const w2=ac.createGain();w2.gain.value=0.35;
      b.input.connect(dry);dry.connect(b.output);
      b.input.connect(d1);d1.connect(w1);w1.connect(b.output);
      b.input.connect(d2);d2.connect(w2);w2.connect(b.output);
      b._chorus={d1,d2,l1,l2,lg1,lg2,dry,w1,w2};break;
    }
    case 'win-tremolo':{
      const lfo=ac.createOscillator();lfo.type='sine';lfo.frequency.value=4;lfo.start();
      const lg=ac.createGain();lg.gain.value=0.5;
      const tg=ac.createGain();tg.gain.value=1;
      const dc=ac.createConstantSource();dc.offset.value=0.5;dc.start();
      const dcg=ac.createGain();dcg.gain.value=1;
      dc.connect(dcg);dcg.connect(tg.gain);lfo.connect(lg);lg.connect(tg.gain);
      b.input.connect(tg);tg.connect(b.output);
      b._tremolo={lfo,lg,tg,dcg};break;
    }
    case 'win-phaser':{
      const ap=Array.from({length:4},()=>{const f=ac.createBiquadFilter();f.type='allpass';f.frequency.value=800;f.Q.value=0.35;return f;});
      const lfo=ac.createOscillator();lfo.type='sine';lfo.frequency.value=0.5;lfo.start();
      const lg=ac.createGain();lg.gain.value=600;
      const dc=ac.createConstantSource();dc.offset.value=800;dc.start();
      lfo.connect(lg);ap.forEach(f=>{lg.connect(f.frequency);dc.connect(f.frequency);});
      const dry=ac.createGain();dry.gain.value=0.7;const wet=ac.createGain();wet.gain.value=0.5;
      b.input.connect(dry);dry.connect(b.output);
      b.input.connect(ap[0]);for(let i=0;i<3;i++)ap[i].connect(ap[i+1]);
      ap[3].connect(wet);wet.connect(b.output);
      b._phaser={ap,lfo,lg,dc,dry,wet};break;
    }
    case 'win-granular':{
      const SR=ac.sampleRate,bufLen=SR*3;const capBuf=ac.createBuffer(1,bufLen,SR);let wp=0;
      const sp=ac.createScriptProcessor(2048,1,1);
      sp.onaudioprocess=ev=>{const id=ev.inputBuffer.getChannelData(0);const cd=capBuf.getChannelData(0);for(let i=0;i<id.length;i++)cd[(wp++)%bufLen]=id[i];ev.outputBuffer.getChannelData(0).set(id);};
      b.input.connect(sp);sp.connect(b.output);
      const gOut=ac.createGain();gOut.gain.value=0.8;gOut.connect(b.output);
      const params={size:120,scatter:0.25,pitch:1.0,density:8,pos:0.5};
      function tick(){const SR2=ac.sampleRate,gsz=Math.max(64,Math.floor(params.size*SR2/1000));const scat=Math.floor(params.scatter*bufLen);const cent=Math.floor(params.pos*bufLen);const start=(cent+Math.floor((Math.random()-.5)*scat*2)+bufLen)%bufLen;const gb=ac.createBuffer(1,gsz,SR2);const gd=gb.getChannelData(0);const cd=capBuf.getChannelData(0);for(let i=0;i<gsz;i++){const w=0.5*(1-Math.cos(2*Math.PI*i/gsz));gd[i]=(cd[(start+i)%bufLen]||0)*w;}const src=ac.createBufferSource();src.buffer=gb;src.playbackRate.value=params.pitch;const eg=ac.createGain();eg.gain.value=1;src.connect(eg);eg.connect(gOut);src.start();src.onended=()=>{try{src.disconnect();eg.disconnect();}catch(_){};};}
      let timer=setInterval(tick,125);
      b._gran={capBuf,bufLen,params,gOut,writePos:()=>wp,setTimer:d=>{clearInterval(timer);timer=setInterval(tick,1000/Math.max(1,d));}};
      b._stop=()=>{clearInterval(timer);};break;
    }
    case 'win-flanger':{
      const dly=ac.createDelay(0.025);dly.delayTime.value=0.005;
      const fb=ac.createGain();fb.gain.value=0.5;const dry=ac.createGain();dry.gain.value=0.7;const wet=ac.createGain();wet.gain.value=0.5;
      const lfo=ac.createOscillator();lfo.type='sine';lfo.frequency.value=0.3;lfo.start();
      const lfoG=ac.createGain();lfoG.gain.value=0.004;const dcS=ac.createConstantSource();dcS.offset.value=0.005;dcS.start();
      lfo.connect(lfoG);lfoG.connect(dly.delayTime);dcS.connect(dly.delayTime);
      b.input.connect(dry);dry.connect(b.output);b.input.connect(dly);dly.connect(fb);fb.connect(dly);dly.connect(wet);wet.connect(b.output);
      b._flanger={dly,fb,dry,wet,lfo,lfoG,dcS};break;
    }
    case 'win-ringmod':{
      const ringGain=ac.createGain();ringGain.gain.value=0;const modBus=ac.createGain();modBus.gain.value=1;const dry=ac.createGain();dry.gain.value=0.3;
      b.input.connect(ringGain);modBus.connect(ringGain.gain);ringGain.connect(b.output);b.input.connect(dry);dry.connect(b.output);
      b._ring={ringGain,modBus,dry};b._modBus=modBus;break;
    }
    case 'win-autofilter':{
      const filt=ac.createBiquadFilter();filt.type='lowpass';filt.frequency.value=800;filt.Q.value=2;
      const env=ac.createAnalyser();env.fftSize=256;const buf2=new Float32Array(env.frequencyBinCount);
      b.input.connect(filt);filt.connect(b.output);b.input.connect(env);
      let baseF=800,modAmt=4000,atk=0.01,rel=0.2,envVal=0;
      const follow=()=>{env.getFloatTimeDomainData(buf2);let rms=0;for(let i=0;i<buf2.length;i++)rms+=buf2[i]*buf2[i];rms=Math.sqrt(rms/buf2.length);const target=Math.min(1,rms*8);const coef=target>envVal?atk:rel;envVal+=(target-envVal)*coef;filt.frequency.value=Math.min(20000,baseF+envVal*modAmt);};
      b._af={filt,baseF:v=>{baseF=v;},modAmt:v=>{modAmt=v;},atk:v=>{atk=v;},rel:v=>{rel=v;},type:t=>{filt.type=t;},q:v=>{filt.Q.value=v;}};
      (function loop(){requestAnimationFrame(loop);follow();})();break;
    }
    case 'win-noise':{
      const nsHp=ac.createBiquadFilter();nsHp.type='highpass';nsHp.frequency.value=20;nsHp.Q.value=0.7;
      const nsLp=ac.createBiquadFilter();nsLp.type='lowpass';nsLp.frequency.value=20000;nsLp.Q.value=0.7;
      const out=ac.createGain();out.gain.value=0;
      nsHp.connect(nsLp);nsLp.connect(out);out.connect(b.output);
      try{b.output.disconnect(drySum);}catch(e){}b.output.connect(drySum);
      let nsNode=null,nsType='white',nsOn=false;
      function mkNoise(type){if(nsNode){try{nsNode.stop();}catch(_){}nsNode=null;}if(!nsOn)return;const bSz=2*ac.sampleRate;const buf3=ac.createBuffer(1,bSz,ac.sampleRate);const d=buf3.getChannelData(0);if(type==='white'){for(let i=0;i<bSz;i++)d[i]=Math.random()*2-1;}else if(type==='pink'){let b0=0,b1=0,b2=0,b3=0,b4=0,b5=0,b6=0;for(let i=0;i<bSz;i++){const w=Math.random()*2-1;b0=.99886*b0+w*.0555179;b1=.99332*b1+w*.0750759;b2=.96900*b2+w*.1538520;b3=.86650*b3+w*.3104856;b4=.55000*b4+w*.5329522;b5=-.7616*b5-w*.0168980;d[i]=(b0+b1+b2+b3+b4+b5+b6+w*.5362)*0.11;b6=w*0.115926;}}else{let last=0;for(let i=0;i<bSz;i++){d[i]=(last+.02*(Math.random()*2-1))/1.02;last=d[i];d[i]*=3.5;}}const src=ac.createBufferSource();src.buffer=buf3;src.loop=true;src.connect(nsHp);src.start();nsNode=src;}
      function setNsOn(v,level){nsOn=v;out.gain.setTargetAtTime(v?((level??30)/100):0,ac.currentTime,0.008);if(v)mkNoise(nsType);else if(nsNode){try{nsNode.stop();}catch(_){}nsNode=null;}}
      b._noise={out,hp:nsHp,lp:nsLp,makeNoise:mkNoise,setType:t=>{nsType=t;mkNoise(t);},setOn:setNsOn,get on(){return nsOn;}};
      b._stop=()=>setNsOn(false);break;
    }
    case 'win-padboard':{try{b.input.connect(b.output);}catch(_){}break;}
    case 'win-bitcrush':{
      const wsh=ac.createWaveShaper();wsh.oversample='4x';
      function makeBitCurve(bits){const steps=Math.pow(2,Math.round(bits))-1,n=4096,c=new Float32Array(n+1);for(let i=0;i<=n;i++){const x=i*2/n-1;c[i]=Math.round(x*steps)/steps;}return c;}
      b.input.connect(wsh);wsh.connect(b.output);wsh.curve=makeBitCurve(16);b._bc={wsh,makeBitCurve};break;
    }
    case 'win-cabinet':{
      const lo=ac.createBiquadFilter();lo.type='lowshelf';lo.frequency.value=200;lo.gain.value=0;
      const mid=ac.createBiquadFilter();mid.type='peaking';mid.frequency.value=1000;mid.Q.value=0.8;mid.gain.value=0;
      const hi=ac.createBiquadFilter();hi.type='highshelf';hi.frequency.value=5000;hi.gain.value=0;
      b.input.connect(lo);lo.connect(mid);mid.connect(hi);hi.connect(b.output);b._cab={lo,mid,hi};break;
    }
    case 'win-stereoimg':{
      const spl=ac.createChannelSplitter(2);
      const mrgr=ac.createChannelMerger(2);
      const lGain=ac.createGain();lGain.gain.value=1;
      const rGain=ac.createGain();rGain.gain.value=1;
      b.input.connect(spl);spl.connect(lGain,0);spl.connect(rGain,1);
      lGain.connect(mrgr,0,0);rGain.connect(mrgr,0,1);mrgr.connect(b.output);
      b._si={spl,mrgr,lGain,rGain};break;
    }
    case 'win-comb':{
      const dly=ac.createDelay(0.1);dly.delayTime.value=0.01;
      const fb=ac.createGain();fb.gain.value=0.5;
      const dry=ac.createGain();dry.gain.value=0.6;
      const wet=ac.createGain();wet.gain.value=0.4;
      b.input.connect(dry);dry.connect(b.output);
      b.input.connect(dly);dly.connect(fb);fb.connect(dly);dly.connect(wet);wet.connect(b.output);
      b._comb={dly,fb,dry,wet};break;
    }
    default:
      try{b.input.connect(b.output);}catch(_){}
  }
}

function spawnWindow(baseId,wx,wy){
  const factory=APP_FACTORIES[baseId];
  if(!factory){openWindow(baseId,wx,wy);return;}
  const baseWin=document.getElementById(baseId);
  if(!baseWin)return;
  const instanceId=baseId+'-i'+(++_spawnCounter);
  // Clone base window's structure
  const win=baseWin.cloneNode(true);
  win.id=instanceId;
  ['open','closing','maxd','focused','win-selected','dragging'].forEach(c=>win.classList.remove(c));
  ['left','top','transform','transformOrigin','height','zIndex'].forEach(p=>win.style.removeProperty(p));
  // Remove port sides and resize grip (will be re-added)
  win.querySelector('.port-side-in')?.remove();
  win.querySelector('.port-side-out')?.remove();
  win.querySelector('.resize-grip')?.remove();
  // Clear wbody
  const wbody=win.querySelector('.wbody');
  if(wbody)wbody.innerHTML='';
  document.getElementById('workspace').appendChild(win);
  // Init audio
  if(ac)initInstanceBus(instanceId,baseId);
  // Copy port definitions
  const baseDefs=PORT_DEFS[baseId];
  if(baseDefs)PORT_DEFS[instanceId]=JSON.parse(JSON.stringify(baseDefs));
  // Set up UI
  factory(win);
  // Set up window frame (drag, resize, traffic lights)
  initWindowFrame(win);
  // Render port jacks
  renderPorts(instanceId);
  // Set up resize observer
  setTimeout(()=>{
    attachResizeScale(win);
    if(window._resizeClassObs)window._resizeClassObs.observe(win,{attributes:true,attributeFilter:['class']});
  },100);
  // Init sliders
  setTimeout(()=>initSliders(),50);
  // Assign a unique accent colour so spawned instances are visually distinct
  const _spawnHues=[200,140,280,40,320,170,60,240];
  const hue=_spawnHues[(_spawnCounter-1)%_spawnHues.length];
  win.style.setProperty('--acid',`hsl(${hue},85%,58%)`);
  win.style.setProperty('--acid-rgb',`${Math.round(Math.cos((hue-30)*Math.PI/180)*100+128)},${Math.round(Math.cos((hue-150)*Math.PI/180)*100+128)},${Math.round(Math.cos((hue+90)*Math.PI/180)*100+128)}`);
  // Open it
  openWindow(instanceId,wx,wy);
}

/* =====================================================
   NEW APP UIs
   ===================================================== */
function setupAppUIs() {

  // --- SPECTRUM ---
  const specWin = document.getElementById('win-spectrum');
  if (specWin) {
    const wb = specWin.querySelector('.wbody');
    wb.innerHTML = `<div class="app-ui">
      <canvas id="spec-canvas" height="140" style="width:100%;display:block;border-radius:6px;background:#040210"></canvas>
      <div class="app-section"><span class="app-section-lbl" data-s="VIEW" data-p="DISPLAY">VIEW</span>
        <div class="app-row" style="gap:6px;flex-wrap:wrap">
          <button class="seg-btn active" data-mode="bars">BARS</button>
          <button class="seg-btn" data-mode="line">LINE</button>
          <button class="seg-btn" data-mode="radial">RADIAL</button>
          <span style="flex:1"></span>
          <button class="seg-btn" id="spec-peak-btn">PEAK</button>
        </div>
      </div>
    </div>`;
    const specCanvas = document.getElementById('spec-canvas');
    specCanvas.width = specCanvas.offsetWidth > 0 ? specCanvas.offsetWidth : 520;
    new ResizeObserver(() => { if(specCanvas.offsetWidth > 0) specCanvas.width = specCanvas.offsetWidth; }).observe(specCanvas);
    const specCtx = specCanvas.getContext('2d');
    const BARS = 52;
    const peaks = Array.from({length:BARS}, () => 0);
    let showPeak = false, specMode = 'bars';
    wb.querySelector('#spec-peak-btn').addEventListener('click', function(){showPeak = !showPeak; this.classList.toggle('active',showPeak);});
    wb.querySelectorAll('.seg-btn[data-mode]').forEach(b => b.addEventListener('click', () => {
      wb.querySelectorAll('.seg-btn[data-mode]').forEach(x => x.classList.remove('active')); b.classList.add('active'); specMode = b.dataset.mode;
    }));
    function drawSpec() {
      const W = specCanvas.width, H = specCanvas.height;
      specCtx.fillStyle = '#040210'; specCtx.fillRect(0, 0, W, H);
      // Use real FFT if analyser is available, else idle display
      const analyser = APP_BUSES['win-spectrum']?._analyser || wmAnalyser;
      const heights = new Array(BARS).fill(0);
      if (analyser) {
        const buf = new Uint8Array(analyser.frequencyBinCount);
        analyser.getByteFrequencyData(buf);
        for (let i = 0; i < BARS; i++) {
          const idx = Math.floor(Math.pow(i / BARS, 1.6) * buf.length);
          heights[i] = buf[idx] / 255;
        }
      }
      heights.forEach((h, i) => {
        if(h > peaks[i]) peaks[i] = h; else peaks[i] = Math.max(0, peaks[i] - 0.004);
      });
      if(specMode === 'bars') {
        const bw = (W - BARS * 2) / BARS;
        heights.forEach((h, i) => {
          const bh = h * H, x = i * (bw + 2) + 1, y = H - bh;
          const g = specCtx.createLinearGradient(0, y, 0, H);
          const hue = 260 + i * 1.8;
          g.addColorStop(0, `hsl(${hue},80%,65%)`); g.addColorStop(1, `hsl(${hue+20},60%,25%)`);
          specCtx.fillStyle = g; specCtx.fillRect(x, y, bw, bh);
          if(showPeak) { specCtx.fillStyle = `hsl(${hue},100%,80%)`; specCtx.fillRect(x, H - peaks[i]*H - 2, bw, 2); }
        });
      } else if(specMode === 'line') {
        specCtx.strokeStyle = '#c060ff'; specCtx.lineWidth = 2;
        specCtx.shadowBlur = 6; specCtx.shadowColor = '#c060ff';
        specCtx.beginPath();
        heights.forEach((h, i) => { const x = (i/BARS)*W, y = H - h*H; i===0?specCtx.moveTo(x,y):specCtx.lineTo(x,y); });
        specCtx.stroke(); specCtx.shadowBlur = 0;
        specCtx.fillStyle = 'rgba(160,60,255,0.1)'; specCtx.lineTo(W,H); specCtx.lineTo(0,H); specCtx.fill();
      } else {
        const cx = W/2, cy = H/2, r0 = Math.min(cx,cy)*0.28;
        heights.forEach((h, i) => {
          const angle = (i/BARS)*Math.PI*2 - Math.PI/2;
          const r = r0 + h * (Math.min(cx,cy) - r0) * 0.88;
          specCtx.strokeStyle = `hsl(${260+i*3},80%,60%)`; specCtx.lineWidth = 2.5;
          specCtx.beginPath(); specCtx.moveTo(cx+Math.cos(angle)*r0, cy+Math.sin(angle)*r0); specCtx.lineTo(cx+Math.cos(angle)*r, cy+Math.sin(angle)*r); specCtx.stroke();
        });
      }
      requestAnimationFrame(drawSpec);
    }
    drawSpec();
  }

  // --- REVERB STUDIO ---
  const reverbWin = document.getElementById('win-reverb');
  if (reverbWin) APP_FACTORIES['win-reverb'](reverbWin);

  // --- COMPRESSOR ---
  const compWin = document.getElementById('win-compressor');
  if (compWin) APP_FACTORIES['win-compressor'](compWin);

  // --- ARPEGGIATOR ---
  const arpWin = document.getElementById('win-arp');
  if (arpWin) {
    const wb = arpWin.querySelector('.wbody');
    const modeMap = {up:'UP',down:'DOWN',updown:'UP/DN',random:'RANDOM'};
    const rateMap = [{v:4,l:'1/32'},{v:2,l:'1/16'},{v:1,l:'1/8'},{v:0.5,l:'1/4'}];
    function arpHtml(){
      return `<div class="app-ui">
      <div class="app-section" style="display:flex;align-items:center;justify-content:space-between">
        <span class="app-section-lbl">ARPEGGIATOR</span>
        <button class="arp-pwr-btn tbtn small${arp.on?' on':''}" style="min-width:44px">${arp.on?'ON':'OFF'}</button>
      </div>
      <div class="app-section"><span class="app-section-lbl">MODE</span>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          ${Object.entries(modeMap).map(([k,l])=>`<button class="seg-btn arp-mode-btn${arp.mode===k?' active':''}" data-mode="${k}">${l}</button>`).join('')}
        </div>
      </div>
      <div class="app-section"><span class="app-section-lbl">RATE</span>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          ${rateMap.map(r=>`<button class="seg-btn arp-rate-btn${arp.rate===r.v?' active':''}" data-rate="${r.v}">${r.l}</button>`).join('')}
        </div>
      </div>
      <div class="app-section"><span class="app-section-lbl">OCTAVES</span>
        <div class="app-row"><input type="range" class="app-slider arp-oct-sl" min="1" max="4" value="${arp.oct}"><span class="app-val arp-oct-v">${arp.oct}</span></div>
      </div>
    </div>`;
    }
    wb.innerHTML = arpHtml();
    function bindArpWin(){
      const pwrBtn = wb.querySelector('.arp-pwr-btn');
      pwrBtn.addEventListener('click', () => {
        arp.on = !arp.on; arpCounter = 0;
        pwrBtn.textContent = arp.on ? 'ON' : 'OFF';
        pwrBtn.classList.toggle('on', arp.on);
        const l = document.getElementById('arpOn');
        if(l){l.classList.toggle('on',arp.on);l.textContent=arp.on?'on':'off';}
      });
      wb.querySelectorAll('.arp-mode-btn').forEach(b => b.addEventListener('click', () => {
        wb.querySelectorAll('.arp-mode-btn').forEach(x => x.classList.remove('active'));
        b.classList.add('active'); arp.mode = b.dataset.mode;
        const l = document.getElementById('arpMode'); if(l)l.value = arp.mode;
      }));
      wb.querySelectorAll('.arp-rate-btn').forEach(b => b.addEventListener('click', () => {
        wb.querySelectorAll('.arp-rate-btn').forEach(x => x.classList.remove('active'));
        b.classList.add('active'); arp.rate = parseFloat(b.dataset.rate);
        const l = document.getElementById('arpRate'); if(l)l.value = arp.rate;
      }));
      const octSl = wb.querySelector('.arp-oct-sl');
      const octV = wb.querySelector('.arp-oct-v');
      octSl.addEventListener('input', () => {
        arp.oct = parseInt(octSl.value); octV.textContent = arp.oct;
        const l = document.getElementById('arpOct'); if(l)l.value = arp.oct;
      });
    }
    bindArpWin();
  }

  // --- LFO ---
  const lfoWin = document.getElementById('win-lfo');
  if (lfoWin) {
    const wb = lfoWin.querySelector('.wbody');
    wb.innerHTML = `<div class="app-ui">
      <canvas id="lfo-display" height="64" style="width:100%;display:block;border-radius:6px;background:#060210;margin-bottom:2px"></canvas>
      <div class="app-section"><span class="app-section-lbl" data-s="SHAPE" data-p="WAVEFORM">SHAPE</span>
        <div style="display:flex;gap:6px;flex-wrap:wrap">
          <button class="seg-btn active" data-wave="sine">SINE</button>
          <button class="seg-btn" data-wave="tri">TRI</button>
          <button class="seg-btn" data-wave="saw">SAW</button>
          <button class="seg-btn" data-wave="rsaw">RSAW</button>
          <button class="seg-btn" data-wave="sqr">SQR</button>
          <button class="seg-btn" data-wave="rnd">S&amp;H</button>
        </div>
      </div>
      <div class="app-section"><span class="app-section-lbl" data-s="LFO" data-p="PARAMETERS">LFO</span>
        <div class="app-row"><span class="app-lbl" data-s="SPEED" data-p="RATE">SPEED</span><input type="range" class="app-slider" id="lfo-rate" min="1" max="100" value="20"><span class="app-val" id="lfo-rate-val">0.50Hz</span></div>
        <div class="app-row" style="margin-top:8px"><span class="app-lbl" data-s="AMOUNT" data-p="DEPTH">AMOUNT</span><input type="range" class="app-slider" id="lfo-depth" min="0" max="100" value="50" oninput="this.nextElementSibling.textContent=this.value+'%'"><span class="app-val">50%</span></div>
      </div>
    </div>`;
    const lfoCanvas = document.getElementById('lfo-display');
    lfoCanvas.width = lfoCanvas.offsetWidth > 0 ? lfoCanvas.offsetWidth : 280;
    new ResizeObserver(() => { if(lfoCanvas.offsetWidth > 0) lfoCanvas.width = lfoCanvas.offsetWidth; }).observe(lfoCanvas);
    const lfoCtx = lfoCanvas.getContext('2d');
    let lfoPhase = 0, lfoWave = 'sine', lfoShVal = 0;
    function lfoRateToHz(v) { return Math.pow(10, (v/100) * 3.3 - 2); }
    const rateEl = document.getElementById('lfo-rate');
    const rateValEl = document.getElementById('lfo-rate-val');
    rateEl.addEventListener('input', () => { rateValEl.textContent = lfoRateToHz(+rateEl.value).toFixed(2) + ' Hz'; });
    rateValEl.textContent = lfoRateToHz(+rateEl.value).toFixed(2) + ' Hz';
    wb.querySelectorAll('.seg-btn[data-wave]').forEach(b => b.addEventListener('click', () => {
      wb.querySelectorAll('.seg-btn[data-wave]').forEach(x => x.classList.remove('active')); b.classList.add('active'); lfoWave = b.dataset.wave;
    }));
    function lfoSample(ph) {
      switch(lfoWave) {
        case 'tri': return ph < 0.5 ? ph*4-1 : 3-ph*4;
        case 'saw': return ph*2-1;
        case 'rsaw': return 1-ph*2;
        case 'sqr': return ph < 0.5 ? 1 : -1;
        case 'rnd': return lfoShVal;
        default: return Math.sin(ph * Math.PI * 2);
      }
    }
    let lfoLastT = 0;
    function lfoTick(now) {
      const dt = Math.min((now - lfoLastT) / 1000, 0.1);
      lfoLastT = now;
      const rate = lfoRateToHz(+rateEl.value);
      const depth = +document.getElementById('lfo-depth').value / 100;
      const prevPhase = lfoPhase;
      lfoPhase = (lfoPhase + rate * dt) % 1;
      if(lfoWave === 'rnd' && lfoPhase < prevPhase) lfoShVal = Math.random() * 2 - 1;
      const v = lfoSample(lfoPhase) * depth;
      const W = lfoCanvas.width, H = lfoCanvas.height;
      lfoCtx.fillStyle = '#060210'; lfoCtx.fillRect(0, 0, W, H);
      lfoCtx.strokeStyle = '#c060ff'; lfoCtx.lineWidth = 2;
      lfoCtx.shadowBlur = 8; lfoCtx.shadowColor = '#9030cc';
      lfoCtx.beginPath();
      for(let i = 0; i < W; i++) { const s = lfoSample(i/W)*0.42; const y = H/2 - s*H; i===0?lfoCtx.moveTo(0,y):lfoCtx.lineTo(i,y); }
      lfoCtx.stroke(); lfoCtx.shadowBlur = 0;
      lfoCtx.strokeStyle = 'rgba(255,255,255,0.5)'; lfoCtx.lineWidth = 1.5;
      lfoCtx.beginPath(); lfoCtx.moveTo(lfoPhase*W, 0); lfoCtx.lineTo(lfoPhase*W, H); lfoCtx.stroke();
      connections.forEach(c => {
        if(c.from.win !== 'win-lfo' || c.from.port !== 'out') return;
        const pm = CV_PARAM_MAP[c.to.win];
        if(!pm || !pm[c.to.port]) return;
        const sl = document.getElementById(pm[c.to.port].sliderId);
        if(!sl) return;
        if(c.lfoBase === undefined) c.lfoBase = +sl.value;
        const range = (+sl.max - +sl.min);
        const newVal = Math.max(+sl.min, Math.min(+sl.max, c.lfoBase + v * range * 0.35));
        sl.value = newVal;
        sl.dispatchEvent(new Event('input'));
      });
      requestAnimationFrame(lfoTick);
    }
    requestAnimationFrame(lfoTick);
  }

  // --- UNIVERSAL MIXER ---
  const mixerWin = document.getElementById('win-mixer');
  if (mixerWin) {
    const wb = mixerWin.querySelector('.wbody');
    wb.innerHTML = `<div class="app-ui">
      <div class="app-section"><span class="app-section-lbl" data-s="OUTPUT" data-p="MASTER OUTPUT">OUTPUT</span>
        <div class="app-row"><span class="app-lbl">VOLUME</span><input type="range" class="app-slider" id="mix-vol" min="0" max="150" value="85"><span class="app-val" id="mix-vol-v">85%</span></div>
        <div class="app-row" style="margin-top:8px"><span class="app-lbl" data-s="BASS" data-p="LOW">BASS</span><input type="range" class="app-slider" id="mix-low" min="-12" max="12" value="0"><span class="app-val" id="mix-low-v">0dB</span></div>
        <div class="app-row" style="margin-top:8px"><span class="app-lbl" data-s="MIDS" data-p="MID">MIDS</span><input type="range" class="app-slider" id="mix-mid" min="-12" max="12" value="0"><span class="app-val" id="mix-mid-v">0dB</span></div>
        <div class="app-row" style="margin-top:8px"><span class="app-lbl" data-s="TREBLE" data-p="HIGH">TREBLE</span><input type="range" class="app-slider" id="mix-high" min="-12" max="12" value="0"><span class="app-val" id="mix-high-v">0dB</span></div>
      </div>
      <div class="app-section">
        <canvas id="mix-meter" height="24" style="width:100%;display:block;border-radius:4px;background:#0a0a0a"></canvas>
        <div style="display:flex;justify-content:space-between;margin-top:4px">
          <span style="font-size:9px;color:var(--mute);letter-spacing:.5px">-∞</span>
          <span style="font-size:9px;color:var(--mute);letter-spacing:.5px">-18</span>
          <span style="font-size:9px;color:var(--mute);letter-spacing:.5px">-12</span>
          <span style="font-size:9px;color:var(--mute);letter-spacing:.5px">-6</span>
          <span style="font-size:9px;color:var(--mute);letter-spacing:.5px">0dB</span>
        </div>
        <div style="margin-top:10px;font-size:9px;color:var(--mute);letter-spacing:.5px;text-align:center">
          CONNECT ANY APP OUTPUT → MIXER INPUT
        </div>
      </div>
    </div>`;
    document.getElementById('mix-vol').addEventListener('input', function() {
      document.getElementById('mix-vol-v').textContent = this.value + '%';
      if (APP_BUSES['win-mixer']?._vol) APP_BUSES['win-mixer']._vol.gain.value = +this.value / 100;
    });
    [['mix-low',()=>eqLow],['mix-mid',()=>eqMid],['mix-high',()=>eqHigh]].forEach(([id, getNode]) => {
      document.getElementById(id).addEventListener('input', function() {
        const v = +this.value;
        document.getElementById(id + '-v').textContent = (v >= 0 ? '+' : '') + v + ' dB';
        const node = getNode(); if (node) node.gain.value = v;
      });
    });
    // VU meter using master analyser
    const meterCanvas = document.getElementById('mix-meter');
    function drawMeter() {
      const {ctx:meterCtx,W,H}=setupCanvas(meterCanvas,300,8);
      meterCtx.fillStyle = '#0a0a0a'; meterCtx.fillRect(0, 0, W, H);
      const analyser = wmAnalyser;
      if (analyser) {
        const buf = new Uint8Array(analyser.frequencyBinCount);
        analyser.getByteFrequencyData(buf);
        let rms = 0; for (let i = 0; i < buf.length; i++) rms += (buf[i]/255) ** 2;
        rms = Math.sqrt(rms / buf.length);
        const level = Math.min(rms * 3, 1);
        const grd = meterCtx.createLinearGradient(0, 0, W, 0);
        grd.addColorStop(0, 'var(--acid)'); grd.addColorStop(0.7, '#ffaa00'); grd.addColorStop(1, '#ff3b30');
        meterCtx.fillStyle = grd;
        meterCtx.fillRect(0, 0, W * level, H);
      }
      requestAnimationFrame(drawMeter);
    }
    drawMeter();
  }

  // --- EQ 5-BAND ---
  ;(function(){const w=document.getElementById('win-eq');if(w)APP_FACTORIES['win-eq'](w);})();

  // --- DELAY ---
  ;(function(){const w=document.getElementById('win-delay');if(w)APP_FACTORIES['win-delay'](w);})();

  // --- OSCILLOSCOPE ---
  ;(function(){
    const canvas=document.getElementById('scope-canvas');
    if(!canvas)return;
    canvas.width=310;canvas.height=120;
    const ctx2=canvas.getContext('2d');
    function drawScope(){
      requestAnimationFrame(drawScope);
      const analyser=APP_BUSES['win-scope']?._scopeAnalyser;
      if(!analyser||!document.getElementById('win-scope')?.classList.contains('open'))return;
      const data=new Float32Array(analyser.fftSize);
      analyser.getFloatTimeDomainData(data);
      ctx2.fillStyle='#040814';ctx2.fillRect(0,0,canvas.width,canvas.height);
      ctx2.strokeStyle='#4df0b0';ctx2.lineWidth=1.5;ctx2.beginPath();
      const sw=canvas.width/data.length;
      for(let i=0;i<data.length;i++){
        const y=(1-(data[i]+1)/2)*canvas.height;
        if(i===0)ctx2.moveTo(0,y);else ctx2.lineTo(i*sw,y);
      }
      ctx2.stroke();
    }
    drawScope();
  })();

  // --- LO-FI ---
  ;(function(){const w=document.getElementById('win-lofi');if(w)APP_FACTORIES['win-lofi'](w);})();

  // --- GATE ---
  ;(function(){const w=document.getElementById('win-gate');if(w)APP_FACTORIES['win-gate'](w);})();

  // --- CHORD GENERATOR ---
  ;(function(){
    const rootsEl=document.getElementById('chg-roots');
    const typesEl=document.getElementById('chg-types');
    if(!rootsEl||!typesEl)return;
    let chgRoot=60,chgType='maj';
    NOTE_NAMES.forEach((n,i)=>{
      const btn=document.createElement('button');
      btn.className='root-btn'+(i===0?' active':'');btn.textContent=n;
      btn.addEventListener('click',()=>{chgRoot=60+i;rootsEl.querySelectorAll('.root-btn').forEach(b=>b.classList.remove('active'));btn.classList.add('active');});
      rootsEl.appendChild(btn);
    });
    Object.keys(CHORDS).forEach(t=>{
      const btn=document.createElement('button');
      btn.className='type-btn'+(t==='maj'?' active':'');btn.textContent=t.toUpperCase();
      btn.addEventListener('click',()=>{chgType=t;typesEl.querySelectorAll('.type-btn').forEach(b=>b.classList.remove('active'));btn.classList.add('active');});
      typesEl.appendChild(btn);
    });
    document.getElementById('chg-play')?.addEventListener('click',()=>{
      ensureAudio();
      const intervals=CHORDS[chgType]||[0];
      triggerPoly(intervals.map(i=>chgRoot+i),ac.currentTime,0.8);
    });
  })();

  // --- TONE GENERATOR ---
  ;(function(){
    let toneOsc=null,toneGainNode=null,toneOn=false;
    function startTone(){
      ensureAudio();
      if(!toneOsc){
        toneGainNode=ac.createGain();toneGainNode.gain.value=0;
        toneOsc=ac.createOscillator();toneOsc.type='sine';
        toneOsc.frequency.value=+(document.getElementById('tone-freq')?.value||440);
        toneOsc.connect(toneGainNode);
        const b=APP_BUSES['win-tone'];
        if(b){toneGainNode.connect(b.output);}else{toneGainNode.connect(drySum);}
        toneOsc.start();
      }
      toneOn=true;
      toneGainNode.gain.setTargetAtTime(+(document.getElementById('tone-vol')?.value||50)/100,ac.currentTime,0.01);
      const btn=document.getElementById('tone-toggle');if(btn){btn.textContent='STOP';btn.style.background='#c02020';btn.style.color='#fff';}
    }
    function stopTone(){
      if(toneGainNode)toneGainNode.gain.setTargetAtTime(0,ac.currentTime,0.01);
      toneOn=false;
      const btn=document.getElementById('tone-toggle');if(btn){btn.textContent='PLAY';btn.style.background='';btn.style.color='';}
    }
    document.getElementById('tone-toggle')?.addEventListener('click',()=>{if(toneOn)stopTone();else startTone();});
    document.getElementById('tone-freq')?.addEventListener('input',function(){
      const f=+this.value;
      if(toneOsc)toneOsc.frequency.setTargetAtTime(f,ac.currentTime,0.01);
      const lbl=document.getElementById('tone-fv');
      if(lbl)lbl.textContent=f>=1000?(f/1000).toFixed(2)+' kHz':f+' Hz';
    });
    document.getElementById('tone-vol')?.addEventListener('input',function(){
      if(toneGainNode&&toneOn)toneGainNode.gain.setTargetAtTime(+this.value/100,ac.currentTime,0.01);
      const lbl=document.getElementById('tone-vv');if(lbl)lbl.textContent=this.value+'%';
    });
    const waves=['sine','square','sawtooth','triangle'];
    ['tone-w-sine','tone-w-sq','tone-w-saw','tone-w-tri'].forEach((id,i)=>{
      document.getElementById(id)?.addEventListener('click',()=>{
        if(toneOsc)toneOsc.type=waves[i];
        document.querySelectorAll('[id^=tone-w-]').forEach(b=>{b.style.background='';b.style.color='';});
        const btn=document.getElementById(id);if(btn){btn.style.background='var(--acid)';btn.style.color='#1a0a04';}
      });
    });
  })();

  // --- VOLUME ---
  ;(function(){const w=document.getElementById('win-vol');if(w)APP_FACTORIES['win-vol'](w);})();

  // --- PAN ---
  ;(function(){const w=document.getElementById('win-pan');if(w)APP_FACTORIES['win-pan'](w);})();

  // --- CHORUS / TREMOLO / PHASER ---
  ;(function(){const w=document.getElementById('win-chorus');if(w)APP_FACTORIES['win-chorus'](w);})();
  ;(function(){const w=document.getElementById('win-tremolo');if(w)APP_FACTORIES['win-tremolo'](w);})();
  ;(function(){const w=document.getElementById('win-phaser');if(w)APP_FACTORIES['win-phaser'](w);})();

  // --- TONE / LFO / SCOPE / SPECTRUM / MERGE / CHORDGEN ---
  ;(function(){const w=document.getElementById('win-tone');if(w)APP_FACTORIES['win-tone'](w);})();
  ;(function(){const w=document.getElementById('win-lfo');if(w&&!w.querySelector('.app-knobs'))APP_FACTORIES['win-lfo'](w);})();
  ;(function(){const w=document.getElementById('win-scope');if(w&&!w.querySelector('.scope-cv'))APP_FACTORIES['win-scope'](w);})();
  ;(function(){const w=document.getElementById('win-spectrum');if(w&&!w.querySelector('.spec-cv'))APP_FACTORIES['win-spectrum'](w);})();
  ;(function(){const w=document.getElementById('win-merge');if(w&&!w.querySelector('.app-section'))APP_FACTORIES['win-merge'](w);})();
  ;(function(){const w=document.getElementById('win-chordgen');if(w&&!w.querySelector('.seg-btn'))APP_FACTORIES['win-chordgen'](w);})();

  // --- JUNE 2026 BATCH: GRANULAR / FLANGER / RING MOD / AUTO-FILTER / NOISE ---
  ;(function(){const w=document.getElementById('win-granular');if(w)APP_FACTORIES['win-granular'](w);})();
  ;(function(){const w=document.getElementById('win-flanger');if(w)APP_FACTORIES['win-flanger'](w);})();
  ;(function(){const w=document.getElementById('win-ringmod');if(w)APP_FACTORIES['win-ringmod'](w);})();
  ;(function(){const w=document.getElementById('win-autofilter');if(w)APP_FACTORIES['win-autofilter'](w);})();
  ;(function(){const w=document.getElementById('win-noise');if(w)APP_FACTORIES['win-noise'](w);})();

  // --- NEW APPS: CHORD PAD / BIT CRUSHER / CABINET / STEREO IMAGER / COMB FILTER ---
  ;(function(){const w=document.getElementById('win-padboard');if(w)APP_FACTORIES['win-padboard'](w);})();
  ;(function(){const w=document.getElementById('win-bitcrush');if(w)APP_FACTORIES['win-bitcrush'](w);})();
  ;(function(){const w=document.getElementById('win-cabinet');if(w)APP_FACTORIES['win-cabinet'](w);})();
  ;(function(){const w=document.getElementById('win-stereoimg');if(w)APP_FACTORIES['win-stereoimg'](w);})();
  ;(function(){const w=document.getElementById('win-comb');if(w)APP_FACTORIES['win-comb'](w);})();

  // --- RESIZE = SCALE INNER UI (ResizeObserver on all windows) ---
  ;(function(){
    if(typeof ResizeObserver==='undefined')return;
    // Attach to all existing windows
    document.querySelectorAll('.window').forEach(w=>{
      setTimeout(()=>attachResizeScale(w),100);
    });
    // Hook via MutationObserver on class changes to catch newly opened windows
    const classObs=new MutationObserver(muts=>{
      muts.forEach(m=>{
        if(m.attributeName==='class'){
          const w=m.target;
          if(w.classList.contains('open')&&!w._resObs)attachResizeScale(w);
        }
      });
    });
    document.querySelectorAll('.window').forEach(w=>classObs.observe(w,{attributes:true,attributeFilter:['class']}));
    // Expose so new spawned windows can be observed
    window._resizeClassObs = classObs;
  })();
}

setupAppUIs();
setTimeout(() => { initSliders(); Object.keys(PORT_DEFS).forEach(id => renderPorts(id)); }, 80);

/* =====================================================
   SLIDER INIT — fill gradient, scroll, dblclick edit
===================================================== */
function sliderFill(el) {
  const mn = parseFloat(el.min)||0, mx = parseFloat(el.max)||100;
  const raw = Math.max(0, Math.min(1, ((parseFloat(el.value)||mn) - mn) / (mx - mn)));
  // pill thumb is 28px wide — 14px half-width offset tracks thumb center accurately
  el.style.setProperty('--fill', `calc(${raw.toFixed(4)} * (100% - 28px) + 14px)`);
}
function initSliders() {
  document.querySelectorAll('input[type=range]').forEach(el => {
    if (el._sliderInited) return;
    el._sliderInited = true;
    sliderFill(el);
    el.addEventListener('input', () => sliderFill(el));
    el.addEventListener('wheel', e => {
      e.preventDefault();
      e.stopPropagation(); // prevent workspace zoom
      clearTimeout(el._wheelTimer);
      el._wheelVel = Math.min((el._wheelVel||0) + 0.7, 8);
      el._wheelTimer = setTimeout(() => { el._wheelVel = 0; }, 180);
      const mn=parseFloat(el.min)||0, mx=parseFloat(el.max)||100;
      const range=mx-mn, baseStep=parseFloat(el.step)||(range/100);
      const step = baseStep * (1 + (el._wheelVel||0) * 0.5);
      el.value = Math.max(mn, Math.min(mx, parseFloat(el.value) + (e.deltaY<0?step:-step)));
      el.dispatchEvent(new Event('input',{bubbles:true}));
    }, {passive:false});
    el.addEventListener('dblclick', () => {
      const cur = el.value;
      const inp = document.createElement('input');
      inp.type = 'text'; inp.value = cur;
      inp.style.cssText = 'position:fixed;z-index:9999;font:inherit;font-size:12px;padding:3px 7px;border-radius:6px;border:1px solid var(--acid);background:#0f0d09;color:var(--acid);width:70px;text-align:center;outline:none';
      const r = el.getBoundingClientRect();
      inp.style.left = (r.left + r.width/2 - 35)+'px';
      inp.style.top = (r.top - 30)+'px';
      document.body.appendChild(inp);
      inp.select();
      const commit = () => {
        const v = parseFloat(inp.value);
        if (!isNaN(v)) {
          el.value = Math.max(parseFloat(el.min)||0, Math.min(parseFloat(el.max)||100, v));
          el.dispatchEvent(new Event('input',{bubbles:true}));
        }
        inp.remove();
      };
      inp.addEventListener('keydown', e => { if(e.key==='Enter')commit(); if(e.key==='Escape')inp.remove(); e.stopPropagation(); });
      inp.addEventListener('blur', commit);
    });
  });
}
setTimeout(initSliders, 200);

/* =====================================================
   UI AUTO-SCALE — keeps the UI proportional to the monitor
   Reference size is 1440×810. Smaller screens scale down;
   larger screens stay at 1:1 (no upscaling).
===================================================== */
(function autoScale(){
  const REF_W=1440,REF_H=810;
  function apply(){
    const s=Math.max(0.5,Math.min(1,window.innerWidth/REF_W,window.innerHeight/REF_H));
    document.body.style.zoom=s;
  }
  apply();
  window.addEventListener('resize',apply);
})();