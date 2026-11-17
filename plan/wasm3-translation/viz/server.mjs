#!/usr/bin/env node
// Live progress visualizer for plan/wasm3-translation/plan.md
// Usage: node viz/server.mjs [port]   -> http://localhost:8765
// Re-parses plan.md on every request; the page refreshes itself when the file changes.
import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const here = path.dirname(fileURLToPath(import.meta.url));
const PLAN = path.resolve(here, '..', 'plan.md');
const PORT = Number(process.argv[2] || 8765);

// Edges from "Order and dependencies" in plan.md
const DEPS = { M0: [], M0b: ['M0'], M1: ['M0'], M2: ['M1'], M3: ['M2'], M4: ['M3'],
  M5: ['M1'], M6: ['M5'], M7: ['M6'], M8: ['M4', 'M7', 'M0b'], M9: ['M8'] };

function parse(text) {
  const lines = text.split('\n');
  const state = {};
  let sec = '', ms = [], cur = null, mode = null;
  let lastKey = null;
  for (const ln of lines) {
    if (/^## /.test(ln)) { sec = ln; cur = null; lastKey = null; continue; }
    if (sec.startsWith('## Current state')) {
      const m = ln.match(/^- \*\*(.+?)\*\*:? ?(.*)/);
      if (m) { lastKey = m[1].replace(/:$/, ''); state[lastKey] = m[2]; }
      else if (lastKey && /^  \S/.test(ln)) state[lastKey] += ' ' + ln.trim();
      continue;
    }
    if (!sec.startsWith('## 5.')) continue;
    const h = ln.match(/^### (M\d+b?): (.*)/);
    if (h) { cur = { id: h[1], title: h[2], items: [], exit: '', met: '' }; ms.push(cur); mode = null; continue; }
    if (/^### (Order|Deferred)/.test(ln)) { cur = null; continue; }
    if (!cur) continue;
    const it = ln.match(/^- \[( |x)\] (.*)/);
    if (it) { cur.items.push({ done: it[1] === 'x', text: it[2] }); mode = 'item'; continue; }
    const ex = ln.match(/^\*\*Exit\*\*:? ?(.*)/);
    if (ex) { cur.exit = ex[1]; mode = 'exit'; continue; }
    if (ln.trim() === '') { mode = mode === 'met' ? null : (mode === 'exit' ? 'afterexit' : null); continue; }
    if (mode === 'item' && /^\s+\S/.test(ln)) cur.items.at(-1).text += ' ' + ln.trim();
    else if (mode === 'exit') cur.exit += ' ' + ln.trim();
    else if (/^\*\*Met/.test(ln)) { cur.met = ln.replace(/^\*\*Met\*\*:? ?/, '').trim(); mode = 'met'; }
    else if (mode === 'met') cur.met += ' ' + ln.trim();
  }
  const byId = Object.fromEntries(ms.map(m => [m.id, m]));
  for (const m of ms) {
    m.total = m.items.length; m.done = m.items.filter(i => i.done).length;
    m.deps = DEPS[m.id] || [];
    m.complete = m.total > 0 && m.done === m.total;
  }
  for (const m of ms) {
    const ready = m.deps.every(d => byId[d]?.complete);
    m.status = m.complete ? 'done' : m.done > 0 ? 'progress' : ready ? 'ready' : 'blocked';
  }
  const total = ms.reduce((a, m) => a + m.total, 0), done = ms.reduce((a, m) => a + m.done, 0);
  return { state, milestones: ms, total, done, mtime: fs.statSync(PLAN).mtimeMs };
}

const PAGE = String.raw`<!doctype html><html lang="en"><head><meta charset="utf-8">
<meta name="viewport" content="width=device-width,initial-scale=1"><title>WASM 3.0 Plan Progress</title>
<style>
:root{--bg:#fafaf8;--fg:#1d1d1b;--mut:#6b6b66;--card:#fff;--bd:#e2e1dc;--done:#2f8f5b;--prog:#d98a1c;--ready:#3b6fd4;--block:#9a9a94;--code:#efeee9}
@media(prefers-color-scheme:dark){:root{--bg:#161615;--fg:#ecebe6;--mut:#9a9992;--card:#1f1f1d;--bd:#34332f;--done:#4cc183;--prog:#f0a847;--ready:#6d9bf0;--block:#77776f;--code:#2a2a27}}
*{box-sizing:border-box}body{margin:0;background:var(--bg);color:var(--fg);font:15px/1.5 system-ui,sans-serif}
main{max-width:1000px;margin:0 auto;padding:24px 16px 64px}
h1{font-size:22px;margin:0 0 4px}.sub{color:var(--mut);font-size:13px;display:flex;gap:8px;align-items:center}
.dot{width:8px;height:8px;border-radius:50%;background:var(--done);animation:p 2s infinite}.dot.off{background:var(--block);animation:none}
@keyframes p{50%{opacity:.3}}
.bar{height:14px;border-radius:7px;background:var(--bd);overflow:hidden;margin:16px 0 4px}.bar>i{display:block;height:100%;background:var(--done);transition:width .6s}
.big{display:flex;justify-content:space-between;font-size:13px;color:var(--mut)}
.note{background:var(--card);border:1px solid var(--bd);border-radius:10px;padding:10px 14px;margin:12px 0;font-size:14px}
.note b{display:block;font-size:12px;text-transform:uppercase;letter-spacing:.04em;color:var(--mut);margin-bottom:2px}
.flow{display:flex;flex-wrap:wrap;gap:6px;margin:20px 0}
.chip{border:2px solid var(--c);color:var(--c);border-radius:8px;padding:4px 10px;font-weight:600;font-size:13px;cursor:pointer;background:var(--card);text-decoration:none}
.chip.done{background:var(--c);color:var(--bg)}
.done{--c:var(--done)}.progress{--c:var(--prog)}.ready{--c:var(--ready)}.blocked{--c:var(--block)}
.legend{font-size:12px;color:var(--mut);display:flex;gap:14px;flex-wrap:wrap}.legend span:before{content:"";display:inline-block;width:10px;height:10px;border-radius:3px;background:var(--c);margin-right:5px}
.card{background:var(--card);border:1px solid var(--bd);border-left:5px solid var(--c);border-radius:10px;padding:12px 16px;margin:12px 0}
.card h2{font-size:16px;margin:0;display:flex;gap:10px;align-items:baseline;flex-wrap:wrap}
.tag{font-size:11px;font-weight:700;text-transform:uppercase;color:var(--c)}.cnt{margin-left:auto;font-size:13px;color:var(--mut);font-weight:400}
.mini{height:5px;background:var(--bd);border-radius:3px;margin:8px 0}.mini>i{display:block;height:100%;background:var(--c);border-radius:3px}
ul{list-style:none;padding:0;margin:6px 0}li{display:flex;gap:8px;padding:3px 0;font-size:14px}
li .bx{flex:none;width:16px;height:16px;margin-top:3px;border:2px solid var(--bd);border-radius:4px;text-align:center;font-size:11px;line-height:12px}
li.d .bx{background:var(--done);border-color:var(--done);color:var(--bg)}li.d span{color:var(--mut)}
.meta{font-size:13px;color:var(--mut);margin-top:6px}.meta b{color:var(--fg)}.deps{font-size:12px;color:var(--mut)}
code{background:var(--code);padding:0 4px;border-radius:4px;font-size:.9em}
details summary{cursor:pointer;font-size:13px;color:var(--mut)}
</style></head><body><main>
<h1>WASM 3.0 translation</h1>
<div class="sub"><span class="dot" id="dot"></span><span id="upd">loading…</span></div>
<div class="bar"><i id="bar" style="width:0"></i></div><div class="big"><span id="pct"></span><span id="cnt"></span></div>
<div class="flow" id="flow"></div>
<div class="legend"><span class="done">done</span><span class="progress">in progress</span><span class="ready">ready to start</span><span class="blocked">blocked</span></div>
<div id="notes"></div><div id="ms"></div>
</main><script>
const esc=s=>s.replace(/[&<>]/g,c=>({'&':'&amp;','<':'&lt;','>':'&gt;'}[c]));
const md=s=>esc(s).replace(/\[([^\]]+)\]\([^)]*\)/g,'$1').replace(/\x60([^\x60]+)\x60/g,'<code>$1</code>').replace(/\*\*([^*]+)\*\*/g,'<b>$1</b>');
const LAB={ready:'ready',progress:'in progress',done:'done',blocked:'blocked'};
let last=0;
function render(d){
  document.getElementById('bar').style.width=(100*d.done/d.total)+'%';
  document.getElementById('pct').textContent=Math.round(100*d.done/d.total)+'% of checklist items';
  document.getElementById('cnt').textContent=d.done+' / '+d.total+' items · '+d.milestones.filter(m=>m.complete).length+' / '+d.milestones.length+' milestones';
  document.getElementById('flow').innerHTML=d.milestones.map(m=>'<a class="chip '+m.status+'" href="#'+m.id+'" title="'+esc(m.title)+'">'+m.id+'</a>').join('');
  const S=d.state, n=[];
  for(const k of ['Next action','Waiting for the user','Last updated']) if(S[k]) n.push('<div class="note"><b>'+k+'</b>'+md(S[k])+'</div>');
  document.getElementById('notes').innerHTML=n.join('');
  document.getElementById('ms').innerHTML=d.milestones.map(m=>{
    const p=m.total?100*m.done/m.total:0;
    return '<section class="card '+m.status+'" id="'+m.id+'"><h2>'+m.id+' · '+md(m.title)+' <span class="tag">'+LAB[m.status]+'</span><span class="cnt">'+m.done+'/'+m.total+'</span></h2>'
    +'<div class="mini"><i style="width:'+p+'%"></i></div>'
    +(m.deps.length?'<div class="deps">needs '+m.deps.join(', ')+'</div>':'')
    +'<ul>'+m.items.map(i=>'<li class="'+(i.done?'d':'')+'"><div class="bx">'+(i.done?'✓':'')+'</div><span>'+md(i.text.length>260?i.text.slice(0,260)+'…':i.text)+'</span></li>').join('')+'</ul>'
    +(m.exit?'<div class="meta"><b>Exit:</b> '+md(m.exit)+'</div>':'')
    +(m.met?'<div class="meta"><b>Met:</b> '+md(m.met)+'</div>':'')+'</section>';
  }).join('');
}
async function tick(){
  try{
    const d=await (await fetch('/api/plan',{cache:'no-store'})).json();
    document.getElementById('dot').className='dot';
    if(d.mtime!==last){last=d.mtime;render(d);}
    document.getElementById('upd').textContent='live · plan.md modified '+new Date(d.mtime).toLocaleTimeString();
  }catch(e){document.getElementById('dot').className='dot off';document.getElementById('upd').textContent='server unreachable, retrying…';}
}
tick();setInterval(tick,30000);
</script></body></html>`;

http.createServer((req, res) => {
  try {
    if (req.url.startsWith('/api/plan')) {
      res.writeHead(200, { 'content-type': 'application/json', 'cache-control': 'no-store' });
      res.end(JSON.stringify(parse(fs.readFileSync(PLAN, 'utf8'))));
    } else {
      res.writeHead(200, { 'content-type': 'text/html; charset=utf-8' });
      res.end(PAGE);
    }
  } catch (e) { res.writeHead(500); res.end(String(e)); }
}).listen(PORT, '127.0.0.1', () => console.log(`http://localhost:${PORT}  (watching ${PLAN})`));
