import Rule30UOR.Interfaces
open Lean Meta Elab Command

/-!
Conservative proof-term audit of the existing refutation engines. Run from rule30-core-lean:
  lake build
  lake env lean scripts/AuditVacuous.lean
The report is generated under .lake/build. NOT_CERTIFIED means unclassified, not nonvacuous.
The initial certificate is the independently proved lhBandAgree_engine_hypotheses_unsat.
-/

/-- Conclusion of `ty` (after all binders) is `¬ CenterPeriodic _ _`. -/
def concludesNotCP (ty : Expr) : MetaM Bool :=
  forallTelescope ty fun _ concl => do
    let concl := concl.consumeMData
    if concl.isAppOfArity ``Not 1 then
      return concl.appArg!.consumeMData.isAppOf ``Rule30UOR.Scale.CenterPeriodic
    return false

/-- Strip mdata and `id`-style wrappers. -/
partial def stripWrap (e : Expr) : Expr :=
  let e := e.consumeMData.headBeta
  if e.isAppOfArity ``id 2 then stripWrap e.appArg!
  else if e.isAppOfArity ``letFun 4 then
    stripWrap (e.appArg!.beta #[e.appFn!.appArg!])
  else match e with
    | .letE _ _ v b _ => stripWrap (b.instantiate1 v)
    | _ => e

inductive Verdict | cpUnused | routes (via : Name) | uses
  deriving Inhabited

/-- Classify a `¬ CP` theorem's proof term relative to a set of certified-vacuous constants. -/
def classify (v : Expr) (cert : NameSet) : MetaM Verdict :=
  lambdaTelescope v fun xs body => do
    -- find a CenterPeriodic binder among xs
    let mut cpVar : Option Expr := none
    for x in xs do
      let t ← inferType x
      if t.consumeMData.isAppOf ``Rule30UOR.Scale.CenterPeriodic then cpVar := some x
    let body := stripWrap body
    match cpVar with
    | some h =>
      if !(body.containsFVar h.fvarId!) then return .cpUnused
      -- body may be `E args h` where `E` is certified
      let fn := body.getAppFn.consumeMData
      if let some n := fn.constName? then
        if cert.contains n then
          let args := body.getAppArgs
          -- only the final argument may mention h, and it must be exactly h
          let init := args.pop
          if args.back? == some h && init.all (fun a => !a.containsFVar h.fvarId!) then
            return .routes n
      return .uses
    | none =>
      let fn := body.getAppFn.consumeMData
      if let some n := fn.constName? then
        if cert.contains n then return .routes n
      return .uses

elab "#audit_vacuous" : command => liftTermElabM do
  let env ← getEnv
  let some modIdx := env.getModuleIdx? `Rule30UOR.Interfaces | throwError "module not found"
  let names := (env.header.moduleData[modIdx.toNat]!).constNames
  let mut cands : Array (Name × Expr) := #[]
  for n in names do
    if let some (.thmInfo ti) := env.find? n then
      if ← concludesNotCP ti.type then cands := cands.push (n, ti.value)
  -- base: the left-band engine whose bundle 9.1582 proves unsatisfiable
  let mut cert : NameSet := NameSet.empty.insert
    `Rule30UOR.Interfaces.not_centerPeriodic_of_lhBandAgree_one_at_zero_diag_doubles
  let mut changed := true
  while changed do
    changed := false
    for (n, v) in cands do
      if cert.contains n then continue
      match ← classify v cert with
      | .cpUnused | .routes _ => cert := cert.insert n; changed := true
      | .uses => pure ()
  let vac := cands.filter (fun (n, _) => cert.contains n)
  let nonvac := cands.filter (fun (n, _) => !cert.contains n)
  logInfo m!"¬CenterPeriodic theorems: {cands.size}; certified vacuous: {vac.size}; not certified: {nonvac.size}"
  let mut out := "VACUOUS\n"
  for (n, _) in vac do out := out ++ s!"{n}\n"
  out := out ++ "NOT_CERTIFIED\n"
  for (n, _) in nonvac do out := out ++ s!"{n}\n"
  IO.FS.createDirAll ".lake/build"
  IO.FS.writeFile ".lake/build/vacuity-audit.txt" out

#audit_vacuous

#print axioms Rule30UOR.Interfaces.lhBandAgree_engine_hypotheses_unsat
#print axioms Rule30UOR.Interfaces.prefix_tail_engine_hypotheses_unsat
#print axioms Rule30UOR.Interfaces.late_scale_engine_hypotheses_unsat
#print axioms Rule30UOR.Interfaces.single_row_zero_diag_succ_engine_hypotheses_unsat
#print axioms Rule30UOR.Interfaces.engine_input_iff_not_centerPeriodic
#print axioms Rule30UOR.Interfaces.problem1_iff_engine_input

