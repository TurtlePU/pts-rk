#!/usr/bin/env node
// A credential handoff via a dedicated, browser-owned persistent session.
// This launcher does not inspect credentials or implement Grazie collection.
const fs = require('fs');
const path = require('path');
const net = require('net');
const {spawn} = require('child_process');
const MARKER = '.prose-review-browser.json';
const EXTENSION = 'https://chromewebstore.google.com/detail/jetbrains-grazie-writing/fonaoompfjljjllgccccgjnhnoghohgc';

function options(args) {
  const action = args.shift();
  if (!['init', 'start'].includes(action)) throw Error('Usage: grazie-session.cjs init|start --profile-dir ABSOLUTE_PATH --browser CHROME_EXECUTABLE [--port 9229]');
  const result = {action, port: 9229};
  while (args.length) {
    const flag = args.shift(), value = args.shift();
    if (!value || !['--profile-dir', '--browser', '--port'].includes(flag)) throw Error('Invalid launcher options');
    result[flag.slice(2)] = value;
  }
  if (!result['profile-dir'] || !path.isAbsolute(result['profile-dir'])) throw Error('Supply an absolute dedicated profile directory outside repositories');
  if (!result.browser || !path.isAbsolute(result.browser)) throw Error('Supply an absolute Chrome executable path');
  result.port = Number(result.port);
  if (!Number.isInteger(result.port) || result.port < 1024 || result.port > 65535) throw Error('Invalid debugging port');
  return result;
}

function profileDirectory(directory, initialize) {
  // Resolve existing ancestors first so symlinks cannot hide a repository.
  let ancestor = path.resolve(directory), suffix = [];
  while (!fs.existsSync(ancestor)) {
    suffix.unshift(path.basename(ancestor));
    ancestor = path.dirname(ancestor);
  }
  const real = path.join(fs.realpathSync(ancestor), ...suffix);
  for (let parent = real; ; parent = path.dirname(parent)) {
    if (fs.existsSync(path.join(parent, '.git'))) throw Error('Browser credentials must live outside Git repositories');
    if (path.dirname(parent) === parent) break;
  }
  const marker = path.join(real, MARKER);
  if (initialize) {
    if (fs.existsSync(real) && fs.readdirSync(real).length) throw Error('Initialization requires a new or empty directory, never a personal browser profile');
    fs.mkdirSync(real, {recursive: true, mode: 0o700});
  } else if (!fs.existsSync(marker)) {
    throw Error('Not a dedicated prose-review profile; run init first');
  }
  const stat = fs.statSync(real);
  if (!stat.isDirectory() || (stat.mode & 0o077) ||
      (process.getuid && stat.uid !== process.getuid())) throw Error('Profile must be owned by you and accessible only to you (mode 700)');
  if (initialize) fs.writeFileSync(marker, JSON.stringify({purpose: 'prose-review-grazie', version: 1}) + '\n', {mode: 0o600, flag: 'wx'});
  else if (JSON.parse(fs.readFileSync(marker)).purpose !== 'prose-review-grazie') throw Error('Invalid dedicated profile marker');
  return real;
}

async function main(args) {
  const config = options(args);
  fs.accessSync(config.browser, fs.constants.X_OK);
  const profile = profileDirectory(config['profile-dir'], config.action === 'init');
  // Do not attach to an unrelated existing debugging session.
  await new Promise((resolve, reject) => {
    const server = net.createServer();
    server.once('error', () => reject(Error('Debugging port is already in use; close the dedicated browser or choose another port')));
    server.listen(config.port, '127.0.0.1', () => server.close(resolve));
  });
  const child = spawn(config.browser, [
    '--user-data-dir=' + profile,
    '--remote-debugging-address=127.0.0.1',
    '--remote-debugging-port=' + config.port,
    '--no-first-run', '--no-default-browser-check',
    config.action === 'init' ? EXTENSION : 'about:blank',
  ], {detached: true, stdio: 'ignore'});
  await new Promise((resolve, reject) => {child.once('spawn', resolve); child.once('error', reject)});
  child.unref();
  console.log('Started the dedicated browser. Keep the debugging port local and close it when finished.');
  if (config.action === 'init') console.log('Install the official Grazie extension, sign in with your JetBrains Account, and open an empty Text Playground. Do not enable Chrome Sync or use other accounts in this profile.');
  console.log('This is session setup only; authenticated cloud collection still needs a verified UI adapter.');
}
module.exports = {options, profileDirectory};
if (require.main === module) main(process.argv.slice(2)).catch(error => {console.error(error.message); process.exitCode = 1});
