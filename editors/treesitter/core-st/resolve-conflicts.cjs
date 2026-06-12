#!/usr/bin/env node
// AUTO-GENERATED conflict resolver for the Strata tree-sitter grammar.
// Iteratively runs `tree-sitter generate`, scrapes the reported conflicting
// rules, and accumulates them into conflicts.json (which grammar.js reads).
// Re-run after editing grammar.js:  node resolve-conflicts.cjs
const fs = require('fs');
const { execSync } = require('child_process');
const grammar = fs.readFileSync('grammar.js', 'utf8');
const defined = new Set([...grammar.matchAll(/^    ([a-z_][a-z0-9_]*): \$ =>/gm)].map(m => m[1]));
const seen = new Set();
let conflicts = [];
function write() { fs.writeFileSync('conflicts.json', JSON.stringify(conflicts) + '\n'); }
for (let i = 0; i < 500; i++) {
  write();
  let out;
  try { out = execSync('tree-sitter generate 2>&1', { encoding: 'utf8' }); }
  catch (e) { out = (e.stdout || '') + (e.stderr || ''); }
  if (!/Unresolved conflict|Caused by/.test(out)) {
    console.log(`Resolved ${conflicts.length} conflict group(s).`);
    write();
    process.exit(0);
  }
  let cand = null;
  const hint = out.match(/Add a conflict for these rules: (.+)/);
  if (hint) cand = hint[1].split(',').map(s => s.trim().replace(/`/g, '')).filter(r => defined.has(r));
  if (!cand || cand.length === 0) {
    const rules = [];
    for (const line of out.match(/^\s+\d+:\s+.*$/gm) || []) {
      const m = [...line.matchAll(/\(([a-z_][a-z0-9_]*)\b/g)].map(x => x[1]).find(r => defined.has(r));
      if (m) rules.push(m);
    }
    cand = [...new Set(rules)].sort();
  }
  cand = [...new Set(cand)].sort();
  const key = cand.join(',');
  if (cand.length === 0 || seen.has(key)) {
    console.error('Could not auto-resolve conflicts. Last tree-sitter output:\n' + out);
    process.exit(1);
  }
  seen.add(key);
  conflicts.push(cand);
}
console.error('Conflict resolution did not converge after 500 iterations.');
process.exit(1);
