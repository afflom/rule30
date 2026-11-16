// Exercise the actual reusable workflow code; no proof tooling or network needed.
const {test} = require('node:test');
const assert = require('node:assert/strict');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');
const crypto = require('node:crypto');
const {spawnSync} = require('node:child_process');
const workflow = fs.readFileSync(path.join(__dirname, '../workflows/download-check.yml'), 'utf8');
const shell = workflow.split('        run: |\n')[1].split('\n      - name:')[0]
  .split('\n').map(line => line.slice(10)).join('\n');
const binding = workflow.split('// BEGIN CANDIDATE BINDING\n')[1].split('// END CANDIDATE BINDING')[0];
const expected = {schema: 'rule30/release-candidate/1', accepted_commit: 'a'.repeat(40),
  tree: 'b'.repeat(40), repository: 'afflom/rule30', run_id: '123', run_attempt: '2'};
function checkBinding(candidate, tree=expected.tree) {
  new Function('require', 'context', 'process', binding)(
    () => ({readFileSync: () => JSON.stringify(candidate)}),
    {sha: expected.accepted_commit, repo: {owner: 'afflom', repo: 'rule30'}},
    {env: {ACCEPTED_TREE: tree, GITHUB_RUN_ID: '123', GITHUB_RUN_ATTEMPT: '2'}});
}
test('candidate binding cannot silently skip when tree output is missing', () => {
  assert.match(workflow, /if: inputs\.require-candidate-binding/);
  assert.doesNotMatch(workflow, /if: inputs\.accepted-tree/);
  const main = fs.readFileSync(path.join(__dirname, '../workflows/main-ci.yml'), 'utf8');
  assert.match(main, /require-candidate-binding: true/);
});
test('exact accepted candidate identity' , () => checkBinding(expected));
for (const key of Object.keys(expected)) {
  test('reject mismatched ' + key, () => assert.throws(() => checkBinding({...expected, [key]: 'wrong'})));
  test('reject missing ' + key, () => {const candidate = {...expected}; delete candidate[key]; assert.throws(() => checkBinding(candidate));});
}
test('reject malformed expected tree', () => assert.throws(() => checkBinding(expected, '')));
function sums(dir) {
  fs.writeFileSync(path.join(dir, 'SHA256SUMS'), fs.readdirSync(dir).filter(n => n !== 'SHA256SUMS').sort()
    .map(n => crypto.createHash('sha256').update(fs.readFileSync(path.join(dir, n))).digest('hex') + '  ' + n + '\n').join(''));
}
function fixture(mutate) {
  const root = fs.mkdtempSync(path.join(os.tmpdir(), 'r30-consumer-'));
  const dir = path.join(root, 'dist'); fs.mkdirSync(dir);
  try {
    for (const name of ['Rule30-Paper.pdf','Paper.pdf','Rule30-Core.pdf','Core.pdf','Paper.lean','Paper.tex',
      'Core.lean','Core.tex','Observations.pdf','Observations.lean','Observations.tex','paper-lexlean.lock',
      'core-lexlean.lock','paper-attestation-a.json','core-attestation-b.json']) fs.writeFileSync(path.join(dir,name), 'fixture\n');
    fs.writeFileSync(path.join(dir,'candidate.json'), JSON.stringify(expected));
    for (const name of ['lexlean-paper-verified-a.tar.gz','lexlean-core-verified-b.tar.gz']) {
      assert.equal(spawnSync('tar', ['-czf', path.join(dir,name), '-C',dir,'Paper.lean']).status, 0);
    }
    sums(dir); if (mutate) mutate(dir);
    return spawnSync('bash', ['-c',shell], {cwd:dir,env:{...process.env,RUNNER_TEMP:root},encoding:'utf8'});
  } finally {fs.rmSync(root,{recursive:true,force:true});}
}
test('complete downloaded fixture passes', () => {const r=fixture(); assert.equal(r.status,0,r.stderr);});
const bad = {
  'changed bytes': d => fs.appendFileSync(path.join(d,'Paper.lean'),'bad'),
  'missing required asset': d => {fs.unlinkSync(path.join(d,'Paper.tex')); sums(d);},
  'unlisted extra': d => fs.writeFileSync(path.join(d,'extra'),'bad'),
  'duplicate checksum': d => {const p=path.join(d,'SHA256SUMS'); fs.appendFileSync(p,fs.readFileSync(p,'utf8').split('\n')[0]+'\n');},
  'traversal checksum': d => fs.appendFileSync(path.join(d,'SHA256SUMS'),'0'.repeat(64)+'  ../outside\n'),
  'absolute checksum': d => fs.appendFileSync(path.join(d,'SHA256SUMS'),'0'.repeat(64)+'  /outside\n'),
  'hidden extra': d => fs.writeFileSync(path.join(d,'.extra'),'bad'),
  'symlink': d => fs.symlinkSync('Paper.pdf',path.join(d,'link')),
  'directory': d => fs.mkdirSync(path.join(d,'extra')),
  'unequal aliases': d => {fs.writeFileSync(path.join(d,'Paper.pdf'),'other'); sums(d);},
  'invalid archive': d => {fs.writeFileSync(path.join(d,'lexlean-core-verified-b.tar.gz'),'bad'); sums(d);},
  'ambiguous attestation': d => {fs.writeFileSync(path.join(d,'core-attestation-c.json'),'{}'); sums(d);},
};
for (const [name,mutate] of Object.entries(bad)) test('reject '+name, () => assert.notEqual(fixture(mutate).status,0));
