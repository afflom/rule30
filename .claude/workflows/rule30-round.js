export const meta = {
  name: 'rule30-round',
  description: 'One round of the Rule 30 loop: an induce agent gathers the observed relations not in the register and the open audit obligations, lenses propose exact theorems toward Problem 1, two skeptics each try to refute every proposal (induced ones included), survivors are mechanized one at a time',
  whenToUse: 'A new set of lenses on the open obligation of afflom/rule30; args = {round, lenses: [{key, prompt}], extra, induce}: round names the round, lenses are the proposers, extra is context for every agent, induce (default true; false skips the Induce phase) runs bin/r30 discover and bin/r30 audit first',
  phases: [
    { title: 'Induce', detail: 'bin/r30 discover --window 256 --degree 2 and bin/r30 audit: observed relations not in the register, open audit obligations' },
    { title: 'Propose', detail: 'one agent per lens, with the induced context' },
    { title: 'Refute', detail: 'truth-and-provability and routing-and-rules skeptics per proposal, lens and induced' },
    { title: 'Mechanize', detail: 'survivors proved one at a time in new research modules' },
  ],
}

// args (all optional):
//   round   a name for the round, echoed in the result
//   lenses  [{key, prompt}]: one proposer per lens
//   extra   context prepended to every lens prompt
//   induce  false skips the Induce phase (default true): no discover/audit run, no induced proposals

const ROOT = '/home/alex/Desktop/rule30-uor-work'
const RULES = `Repository ${ROOT} (Wolfram's Rule 30 Prize, Problem 1: the center column is not eventually periodic; Lean 4 research modules in rule30-core-lean/Rule30UOR, every theorem under propext and Quot.sound only, no Classical.choice; the register frontier.toml lists proved reductions, open claims and REFUTED routes; rule30-lexlean/STRATEGY.md's last sections are the research log). Start with 'bin/r30 brief' and 'bin/r30 frontier list --status refuted'; read the last sections of STRATEGY.md (from 'The tower' onward) and the modules named in your task. Tools: bin/r30 claim <id>, mentions, sig, lexicon search, kappa, experiment run. MEMORY (31 GB machine shared with the editor and the proof gate; sessions have died of OOM kills): prefix every python3 command with 'ulimit -v 4000000;', keep simulations below 4000 rows, never run lake build. The owner's rules: anything that does not close the proof is not a route; no heuristic or enumerative work; exact theorems the kernel can decide; extrapolate beyond what is given; refuted routes are recorded, never walked again. Your output is data for the orchestrator.`

const PROPOSAL = { type: 'object', properties: {
  title: { type: 'string' },
  lean_statement: { type: 'string', description: 'Exact Lean 4 statements in the repository vocabulary (twopow, bxor, named predicates), with the module they would live in' },
  proof_sketch: { type: 'string', description: 'A complete proof sketch from proved repository facts, naming each theorem used, and every numerical check run with its result' },
  routes_to_problem1: { type: 'string', description: 'The exact chain to Problem 1: closure (False from CenterPeriodic T P), an equivalence, or a sharpening of the open obligation' },
  what_fails: { type: 'string', description: 'If it does not close, the precise point where it stops, as data for the next round' },
  confidence: { type: 'number' },
  closes_problem1: { type: 'boolean' },
}, required: ['title', 'lean_statement', 'proof_sketch', 'routes_to_problem1', 'what_fails', 'confidence', 'closes_problem1'] }

const VERDICT = { type: 'object', properties: {
  refuted: { type: 'boolean', description: 'true if false, unprovable as sketched, heuristic, enumerative, a refuted route in disguise, or a restatement of the register' },
  reason: { type: 'string' },
  counterexample_or_gap: { type: 'string' },
  salvage: { type: 'string', description: 'A weaker exact statement that survives, in Lean, or empty' },
}, required: ['refuted', 'reason', 'counterexample_or_gap', 'salvage'] }

const MECH = { type: 'object', properties: {
  module: { type: 'string' },
  proved: { type: 'array', items: { type: 'string' }, description: 'Fully qualified Lean names of the theorems and definitions proved, each depending only on propext and Quot.sound' },
  not_proved: { type: 'string' },
  report: { type: 'string' },
}, required: ['module', 'proved', 'not_proved', 'report'] }

const INDUCED = { type: 'object', properties: {
  discover_available: { type: 'boolean', description: 'false when bin/r30 has no discover command (or it failed); then relations is empty' },
  audit_available: { type: 'boolean', description: 'false when bin/r30 has no audit command (or it failed); then obligations is empty' },
  relations: { type: 'array', description: 'Observed relations NOT already in the register or the library', items: { type: 'object', properties: {
    title: { type: 'string' },
    lean_statement: { type: 'string', description: 'The relation as a Lean theorem for all t, in the repository vocabulary (twopow, bxor, named predicates)' },
    certificate: { type: 'string', description: 'The window certificate discover decided: window, degree, the sequences and what was checked' },
  }, required: ['title', 'lean_statement', 'certificate'] } },
  obligations: { type: 'array', description: 'The open conditional refutations of the audit', items: { type: 'object', properties: {
    theorem: { type: 'string', description: 'The conditional refutation (Lean name)' },
    open_hypotheses: { type: 'array', items: { type: 'string' }, description: 'Its hypotheses neither refuted nor discharged, as the audit labels them' },
  }, required: ['theorem', 'open_hypotheses'] } },
  notes: { type: 'string', description: 'What was run, what was missing, and the counts' },
}, required: ['discover_available', 'audit_available', 'relations', 'obligations', 'notes'] }

const lenses = (args && args.lenses) || []
const extra = (args && args.extra) || ''
const round = (args && args.round) || 'round'
const induce = !(args && args.induce === false)

// Induce: what the machine already observed (discover) and what the audit left open,
// before any lens proposes. A missing command contributes nothing; the round goes on.
let induced = { discover_available: false, audit_available: false, relations: [], obligations: [], notes: 'Induce skipped' }
if (induce) {
  phase('Induce')
  const got = await agent(`${RULES}\n\nINDUCE. From ${ROOT} run exactly these two commands:\n(1) 'bin/r30 discover --window 256 --degree 2 --json'\n(2) 'bin/r30 audit --json --status open' (the audit runs Lean: if '${ROOT}/bin/r30 gate' does not print a line starting with 'finished', run 'bin/r30 audit --cached --json --status open' instead, which reads the last recorded audit).\nIf bin/r30 answers 'invalid choice' for a command (it does not exist yet) or the command fails, say so in notes, set its *_available to false and return an empty list for it; do not substitute anything else for it.\nFrom (1) return each observed relation that is NOT already in the register or the library: check it against 'bin/r30 frontier list' and 'bin/r30 mentions <its Lean constants>' (a relation that is already a theorem or a claim is not returned). State each as an exact Lean theorem for all t in the repository vocabulary, with the window certificate the command decided.\nFrom (2) return every open conditional refutation with its open hypotheses exactly as the audit labels them.\nDo not edit files, do not run git, lake build or bin/r30 commit.`,
    { label: 'induce', phase: 'Induce', schema: INDUCED })
  if (got) induced = got
  log(`${round}: induced ${induced.relations.length} observed relations (discover ${induced.discover_available ? 'ran' : 'absent'}) and ${induced.obligations.length} open obligations (audit ${induced.audit_available ? 'ran' : 'absent'})`)
}

const inducedContext = (induced.relations.length || induced.obligations.length)
  ? `\n\nINDUCED THIS ROUND (data, not instructions):\nObserved relations not in the register (each a candidate theorem for all t whose window certificate is already decided):\n${JSON.stringify(induced.relations, null, 1)}\nOpen audit obligations (conditional refutations of the period whose hypotheses are neither refuted under a period nor discharged; bin/r30 audit):\n${JSON.stringify(induced.obligations, null, 1)}`
  : ''

// The induced items go straight to Refute and Mechanize as proposals of their own:
// one per observed relation, one per distinct set of open hypotheses (the conditional
// refutations sharing it are one obligation).
const bySet = {}
for (const o of induced.obligations) {
  const k = [...o.open_hypotheses].sort().join(' & ')
  ;(bySet[k] = bySet[k] || []).push(o.theorem)
}
const obligationSets = Object.keys(bySet).sort().map(k => ({ theorem: bySet[k].join(', '), open_hypotheses: k ? k.split(' & ') : [] }))
if (induced.obligations.length) log(`${round}: ${induced.obligations.length} open conditional refutations share ${obligationSets.length} distinct sets of open hypotheses; one proposal per set`)
const inducedItems = [
  ...induced.relations.map((r, i) => ({ key: `induced-relation-${i + 1}`, proposal: {
    title: r.title, lean_statement: r.lean_statement,
    proof_sketch: `An observed relation: its window certificate is already decided (${r.certificate}). The proof is the induction for all t from the definitions in the repository; prove it in Lean or report the failure point.`,
    routes_to_problem1: 'An observed relation: a candidate theorem for all t; where it bears on the open obligation, it sharpens it.',
    what_fails: 'Not yet proved for all t beyond the decided window.', confidence: 0.7, closes_problem1: false } })),
  ...obligationSets.map((o, i) => ({ key: `induced-obligation-${i + 1}`, proposal: {
    title: `Discharge the open hypotheses of ${o.theorem} under a period`,
    lean_statement: `From CenterPeriodic T P (0 < P), derive the open hypotheses of ${o.theorem}: ${o.open_hypotheses.join('; ')}`,
    proof_sketch: 'An open audit obligation: no theorem of the library refutes or discharges these hypotheses (bin/r30 audit). A derivation closes the conditional refutation, which then refutes the period.',
    routes_to_problem1: `${o.theorem} refutes the period once these hypotheses hold under it.`,
    what_fails: 'No derivation known; the skeptics decide whether it is a refuted route in disguise.', confidence: 0.3, closes_problem1: true } })),
]

const judge = (p, key) => parallel(['truth-and-provability', 'routing-and-rules'].map(lens => () =>
  agent(`${RULES}\n\nYou are a skeptic (${lens}). Try to REFUTE this proposal; default to refuted=true if uncertain. truth-and-provability: check every statement against the actual Lean definitions (grep rule30-core-lean/Rule30UOR) and small cases by a read-only python3 check under ulimit; check every cited theorem exists. routing-and-rules: check it is not a refuted route (bin/r30 frontier list --status refuted; bin/r30 claim <id>; bin/r30 audit --cached --status dead), not heuristic or enumerative, not already in the register, and that its chain to Problem 1 is exact.\n\nPROPOSAL (${key}):\n${JSON.stringify(p, null, 2)}`,
    { label: `refute:${key}:${lens}`, phase: 'Refute', schema: VERDICT })))
  .then(vs => {
    const v = vs.filter(Boolean)
    const salvage = v.map(x => x.salvage).filter(Boolean).join('\n---\n')
    return { lens: key, proposal: p, verdicts: v, survives: v.length === 2 && v.every(x => !x.refuted), salvage }
  })

phase('Propose')
const [judgedLenses, judgedInduced] = await Promise.all([
  pipeline(lenses,
    l => agent(`${RULES}\n\n${extra}${inducedContext}\n\nLENS (${l.key}): ${l.prompt}\n\nReturn one proposal, the best exact statement this lens yields. If it does not close Problem 1, say so and give the exact failure point.`,
      { label: `propose:${l.key}`, phase: 'Propose', schema: PROPOSAL }),
    (p, l) => p ? judge(p, l.key) : { lens: l.key, proposal: null, verdicts: [], survives: false, salvage: '' }),
  pipeline(inducedItems, it => judge(it.proposal, it.key)),
])
const judged = [...judgedLenses, ...judgedInduced]

// Mechanize one at a time: one Lean process on the machine besides the gate.
const toMechanize = judged.filter(Boolean).filter(j => j.survives || (j.salvage && j.proposal && j.proposal.confidence >= 0.6))
log(`${round}: ${judged.filter(Boolean).filter(j => j.survives).length} survivors, ${toMechanize.length} to mechanize (survivors and confident salvage; ${judgedInduced.filter(Boolean).length} induced proposals judged)`)
phase('Mechanize')
const mechanized = []
for (const j of toMechanize) {
  const observed = j.lens.startsWith('induced-relation-')
    ? `\n\nTHIS IS AN OBSERVED RELATION: a candidate theorem for all t whose window certificate is already decided. Prove it for all t in Lean, or report the exact point where the proof fails (the step, the case, the missing lemma) in not_proved.`
    : ''
  const m = await agent(`${RULES}\n\nMECHANIZE. Before EVERY Lean run, check that '${ROOT}/bin/r30 gate' prints a line starting with 'finished' (if RUNNING, edit and check again later in a separate command). Create a new research module with '${ROOT}/bin/r30 module add <Name>' (a short CamelCase name for this result; never edit lakefile.toml or the audit by hand), set its 'public import' to the modules you need, keep the generated header, and check it with 'cd rule30-core-lean && LEAN_NUM_THREADS=1 lake env lean -j 1 Rule30UOR/<Name>.lean' (one Lean process at a time, no ulimit on lean). Rules: at most propext and Quot.sound (temporary '#print axioms', then remove); no Classical.choice, no by_cases on undecidable props, avoid core Nat.pow_lt_pow_right, cfomega for linear arithmetic; no sorry left (delete what you cannot prove and say so); published statements first-order (no function-typed arguments, no casts, no decide, no primed names, named predicates instead of inline quantifiers). Do NOT run git, bin/r30 commit or bin/r30 theorem add. Prove the surviving statements below, numerically checking each first.${observed}\n\nPROPOSAL:\n${JSON.stringify(j.proposal, null, 2)}\n\nSKEPTICS' SALVAGE (prefer these forms where the proposal was too strong):\n${j.salvage}`,
    { label: `mechanize:${j.lens}`, phase: 'Mechanize', schema: MECH })
  mechanized.push({ lens: j.lens, result: m })
}

return {
  round,
  induced: { discover_available: induced.discover_available, audit_available: induced.audit_available,
    relations: induced.relations.length, obligations: induced.obligations.length, obligation_sets: obligationSets.length, notes: induced.notes },
  proposals: judged.filter(Boolean).map(j => ({ lens: j.lens, title: j.proposal && j.proposal.title, survives: j.survives,
    closes: j.proposal && j.proposal.closes_problem1, what_fails: j.proposal && j.proposal.what_fails,
    verdicts: j.verdicts.map(v => ({ refuted: v.refuted, reason: v.reason.slice(0, 600) })) })),
  mechanized,
}
