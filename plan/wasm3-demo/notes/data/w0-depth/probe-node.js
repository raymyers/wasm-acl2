// W0 item 4: run the probes in node: main thread (stack set by node's
// --stack-size), and in worker threads with resourceLimits.stackSizeMb.
// Usage: node [--stack-size=N] probe-node.js BUILD_DIR [worker-MB...]
const path = require('path');
const { Worker, isMainThread, workerData, parentPort } = require('worker_threads');
const w0Probe = require('./probe-core.js');
function run(dir) {
  const jscl = require(path.join(dir, 'jscl.js'));
  require(path.join(dir, 'probe.js'));
  return w0Probe(jscl);
}
if (isMainThread) {
  const dir = path.resolve(process.argv[2]);
  const flag = process.execArgv.join(' ') || 'default stack';
  console.log(`W0-PROBE node main (${flag}): ${JSON.stringify(run(dir))}`);
  for (const mb of process.argv.slice(3)) {
    const w = new Worker(__filename, { workerData: dir, resourceLimits: { stackSizeMb: +mb } });
    w.on('message', r => console.log(`W0-PROBE node worker stackSizeMb=${mb}: ${JSON.stringify(r)}`));
  }
} else {
  parentPort.postMessage(run(workerData));
}
