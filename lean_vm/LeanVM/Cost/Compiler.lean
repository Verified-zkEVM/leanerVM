module

public import LeanVM.Cost.Rules
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Match.MatcherApp.Basic
public meta import LeanVM.Cost.Rules

/-!
# The compiler

`translate` takes a Lean expression `e` (its free variables bound in the machine's environment)
and returns machine code `t`, a price `c` (a Lean expression of `ℕ` in the same variables) and a
proof of `Runs P env t (enc e) c`, built from the rules of `Cost/Rules.lean`:

* a variable of the environment: `Rule.var`, at its position;
* `let`: `Rule.letE`, the body translated with the bound value in front of the environment;
* a `match`: unfolded to its `casesOn`, then the rule of that type's `casesOn`;
* an application whose head has a rule (`rules`): the rule whose conclusion's value unifies with
  `enc e`, its premises solved in turn: a run of a part (under the binders and hypotheses the
  premise states, as for the alternatives of a `match`) by translating it, an equation by `rfl`;
* a definition without a rule: unfolded, then translated.

Nothing here is trusted: the kernel checks every proof the compiler builds.
-/

public meta section

namespace LeanVM.Cost.Compiler

open Lean Meta Elab

/-- The rules, by the head constant of the Lean expressions they translate. -/
def rules : List (Name × Name) := [
  (``Option.none, ``Rule.none),
  (``Option.some, ``Rule.some),
  (``List.nil, ``Rule.nil),
  (``List.cons, ``Rule.cons),
  (``Prod.mk, ``Rule.pair),
  (``Prod.fst, ``Rule.fst),
  (``Prod.snd, ``Rule.snd),
  (``Option.casesOn, ``Rule.caseOption),
  (``List.casesOn, ``Rule.caseList),
  (``Prod.casesOn, ``Rule.casePair),
  (``Nat.casesOn, ``Rule.caseNat),
  (``ite, ``Rule.ite),
  (``dite, ``Rule.dite),
  (``cond, ``Rule.cond),
  (``HAdd.hAdd, ``Rule.natAdd),
  (``HAdd.hAdd, ``Rule.kAdd),
  (``HSub.hSub, ``Rule.natSub),
  (``HMul.hMul, ``Rule.natMul),
  (``HMul.hMul, ``Rule.kMul),
  (``HDiv.hDiv, ``Rule.natDiv),
  (``HMod.hMod, ``Rule.natMod),
  (``Decidable.decide, ``Rule.natLt),
  (``Decidable.decide, ``Rule.natLe),
  (``Decidable.decide, ``Rule.natEq)
]

/-- A compiled function: its index in the program, the constant of its body, its spec, and the
bodies its spec needs (its own first). -/
structure CompiledFn where
  fn : Name
  index : Nat
  body : Name
  spec : Name
  deps : Array (Nat × Name)
  deriving Inhabited

/-- The compiled functions. -/
initialize compiledExt : SimplePersistentEnvExtension CompiledFn (NameMap CompiledFn) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e ↦ m.insert e.fn e
    addImportedFn := fun as ↦ as.foldl (fun m a ↦ a.foldl (fun m e ↦ m.insert e.fn e) m) {} }

/-- The function being compiled, when it is recursive: its constant, its index, the induction
hypothesis, the measure, and its arguments. -/
structure SelfInfo where
  fn : Name
  index : Nat
  ih : Expr
  measure : Expr
  args : Array Expr

/-- The translation's context: the program, the environment (a list of values) and, for each
position, the Lean expression whose encoding it holds; the function being compiled, if it is
recursive; and the callees' spec premises still to be proved (`Includes P deps`). -/
structure Ctx where
  P : Expr
  env : Expr
  vals : Array Expr
  self : Option SelfInfo := none
  pending : IO.Ref (Array (MVarId × Array (Nat × Name)))

/-- The context with `x`'s encoding in front. -/
def Ctx.push (ctx : Ctx) (x : Expr) : MetaM Ctx := do
  let v ← mkAppM ``Enc.enc #[x]
  return { ctx with env := ← mkAppM ``List.cons #[v, ctx.env], vals := #[x] ++ ctx.vals }

/-- `Runs P env t v c`. -/
def runsType (ctx : Ctx) (t v c : Expr) : Expr :=
  mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, t, v, c]

/-- The parts of `Runs P env t v c`. -/
def runsParts? (ty : Expr) : Option (Expr × Expr × Expr × Expr × Expr) :=
  if ty.isAppOfArity ``Runs 5 then
    let a := ty.getAppArgs
    some (a[0]!, a[1]!, a[2]!, a[3]!, a[4]!)
  else none

/-- The Lean expression `x` of `enc x`. -/
def encArg? (v : Expr) : Option Expr :=
  if v.isAppOfArity ``Enc.enc 3 then some v.appArg! else none

/-- The natural number a literal denotes, if `e` is one. -/
def natLit? (e : Expr) : MetaM (Option Nat) := do
  let e ← instantiateMVars e
  if let some n := e.rawNatLit? then return some n
  if e.isAppOfArity ``OfNat.ofNat 3 then
    if (← isDefEq (← inferType e) (mkConst ``Nat)) then
      return e.appFn!.appArg!.rawNatLit?
  return none

/-- The arguments as one value: `(x₁, (x₂, …))`, or `x₁` alone. -/
def mkTuple (xs : Array Expr) : MetaM Expr := do
  if xs.size == 0 then return mkConst ``Unit.unit
  let mut t := xs[xs.size - 1]!
  for i in (List.range (xs.size - 1)).reverse do
    t ← mkAppM ``Prod.mk #[xs[i]!, t]
  return t

/-- The type of `mkTuple`. -/
def mkTupleType (tys : Array Expr) : MetaM Expr := do
  if tys.size == 0 then return mkConst ``Unit
  let mut t := tys[tys.size - 1]!
  for i in (List.range (tys.size - 1)).reverse do
    t ← mkAppM ``Prod #[tys[i]!, t]
  return t

/-- The components of a tuple `x` of `n` values. -/
def tupleComponents (x : Expr) (n : Nat) : MetaM (Array Expr) := do
  let mut out := #[]
  let mut t := x
  for _ in [0:n - 1] do
    out := out.push (← mkAppM ``Prod.fst #[t])
    t ← mkAppM ``Prod.snd #[t]
  return out.push t

/-- The list `[(i, body), …]` of a spec's needed bodies. -/
def depsExpr (deps : Array (Nat × Name)) : MetaM Expr := do
  let pairTy ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Term]
  let mut l ← mkAppOptM ``List.nil #[pairTy]
  for (i, b) in deps.reverse do
    l ← mkAppM ``List.cons #[← mkAppM ``Prod.mk #[mkNatLit i, mkConst b], l]
  return l

/-- A proof of `goal` (a decrease, a membership) by a tactic. -/
def proveByTactic (goal : Expr) : MetaM Expr := do
  let mvar ← mkFreshExprSyntheticOpaqueMVar goal
  let tac ← `(tactic| first | omega | (simp_all; done) | (simp_all; omega) | decreasing_tactic)
  let remaining ← Term.TermElabM.run' (Tactic.run mvar.mvarId! (Tactic.evalTactic tac))
  unless remaining.isEmpty do throwError "could not prove {goal}"
  instantiateMVars mvar

mutual

/-- **The translation** of `e`: its code, its price, and a proof of
`Runs P env code (enc e) price`. -/
partial def translate (ctx : Ctx) (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let e ← instantiateMVars e
  let e := e.headBeta
  -- a variable of the environment
  for h : i in [0:ctx.vals.size] do
    if ctx.vals[i] == e then
      let enc ← mkAppM ``Enc.enc #[e]
      let ty := mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, mkApp (mkConst ``Term.var) (mkNatLit i),
        enc, mkNatLit 1]
      let hget ← mkEqRefl (← mkAppM ``Option.some #[enc])
      let pf ← mkAppOptM ``Rule.var #[ctx.P, ctx.env, none, none, mkNatLit i, e, hget]
      check pf
      return (mkApp (mkConst ``Term.var) (mkNatLit i), mkNatLit 1, ← mkExpectedTypeHint pf ty)
  -- a natural number literal
  if let some n ← natLit? e then
    let pf ← mkAppOptM ``Rule.natLit #[ctx.P, ctx.env, mkNatLit n]
    let code ← mkAppM ``Term.val #[← mkAppM ``Val.nat #[mkNatLit n]]
    return (code, mkNatLit 1, pf)
  -- `let`
  if let .letE n ty v b _ := e then
    let (tv, cv, pv) ← translate ctx v
    return ← withLocalDeclD n ty fun x ↦ do
      let ctx' ← ctx.push x
      let (tb, cb, pb) ← translate ctx' (b.instantiate1 x)
      if tb.hasFVar then throwError "translate: the code of a `let` body depends on its variable"
      withLocalDeclD `hx (← mkEq x v) fun hx ↦ do
        let f ← mkLambdaFVars #[x] (b.instantiate1 x)
        let d ← mkLambdaFVars #[x] cb
        let hb ← mkLambdaFVars #[x, hx] pb
        let pf ← mkAppOptM ``Rule.letE #[ctx.P, ctx.env, none, none, none, none, tv, tb, v, f, cv,
          d, pv, hb]
        let c ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[cv, d.beta #[v]], mkNatLit 1]
        return (← mkAppM ``Term.letE #[tv, tb], c, pf)
  -- a call of the function being compiled, or of a compiled function
  if let .const f _ := e.getAppFn then
    if let some self := ctx.self then
      if f == self.fn then return ← translateSelfCall ctx self e
    if let some cf := (compiledExt.getState (← getEnv)).find? f then
      return ← translateCall ctx cf e
  -- a `match`: its `casesOn`
  if let .const f _ := e.getAppFn then
    if (← Meta.isMatcher f) then
      match ← delta? e (· == f) with
      | some e' => return ← translate ctx (← Core.betaReduce e')
      | none => throwError "translate: cannot unfold the match {e}"
  -- a rule
  let fn := e.getAppFn
  if let .const f _ := fn then
    for (key, rule) in rules do
      if key == f then
        if let some r ← tryRule ctx rule e then return r
    -- a definition: unfolded
    if let some e' ← unfoldDefinition? e then
      return ← translate ctx e'.headBeta
  throwError "translate: no rule for {e}"

/-- The translations of `es`, as a run of the list: the codes, the values, the price, the proof. -/
partial def translateList (ctx : Ctx) (es : List Expr) : MetaM (Expr × Expr × Expr × Expr) := do
  match es with
  | [] =>
    let ts ← mkAppOptM ``List.nil #[mkConst ``Term]
    let vs ← mkAppOptM ``List.nil #[mkConst ``Val]
    return (ts, vs, mkNatLit 0, ← mkAppOptM ``RunsList.nil #[ctx.P, ctx.env])
  | e :: es =>
    let (t, c, p) ← translate ctx e
    let (ts, vs, cs, ps) ← translateList ctx es
    let v ← mkAppM ``Enc.enc #[e]
    let pf ← mkAppOptM ``RunsList.cons #[ctx.P, ctx.env, t, ts, v, vs, c, cs, p, ps]
    return (← mkAppM ``List.cons #[t, ts], ← mkAppM ``List.cons #[v, vs],
      ← mkAppM ``HAdd.hAdd #[c, cs], pf)

/-- A call of a compiled function: its spec at the arguments, the premise `Includes P deps`
left to the end. -/
partial def translateCall (ctx : Ctx) (cf : CompiledFn) (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let args := e.getAppArgs
  let (_, _, _, pl) ← translateList ctx args.toList
  let depsE ← depsExpr cf.deps
  let hInc ← mkFreshExprMVar (mkAppN (mkConst ``Includes) #[ctx.P, depsE])
  ctx.pending.modify (·.push (hInc.mvarId!, cf.deps))
  let spec := mkAppN (mkConst cf.spec) (#[ctx.P, hInc] ++ args)
  let pf ← mkAppM ``Rule.call #[pl, spec]
  let ty ← inferType pf
  let some (_, _, t, _, cost) := runsParts? ty | throwError "call: not a run"
  return (t, ← instantiateMVars cost, pf)

/-- A recursive call: the induction hypothesis at the arguments, the decrease by a tactic. -/
partial def translateSelfCall (ctx : Ctx) (self : SelfInfo) (e : Expr) :
    MetaM (Expr × Expr × Expr) := do
  let args := e.getAppArgs
  let (_, _, c, pl) ← translateList ctx args.toList
  let y ← mkTuple args
  let x ← mkTuple self.args
  let dec ← mkAppM ``LT.lt #[self.measure.beta #[y], self.measure.beta #[x]]
  let dec ← Core.betaReduce dec
  let decPf ← proveByTactic dec
  let spec := mkAppN self.ih #[y, decPf]
  let pf ← mkAppM ``Rule.call #[pl, spec]
  let ty ← inferType pf
  let some (_, _, t, _, cost) := runsParts? ty | throwError "call: not a run"
  let _ := c
  return (t, ← instantiateMVars cost, pf)

/-- The rule `rule` applied to `e`, if its conclusion's value unifies with `enc e` and its
premises are solved. -/
partial def tryRule (ctx : Ctx) (rule : Name) (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let s ← saveState
  let info ← getConstInfo rule
  let lvls ← info.levelParams.mapM fun _ ↦ mkFreshLevelMVar
  let ty := info.type.instantiateLevelParams info.levelParams lvls
  let (args, _, concl) ← forallMetaTelescopeReducing ty
  let some (P, env, t, v, c) := runsParts? concl | throwError "rule {rule} does not conclude a run"
  let target ← mkAppM ``Enc.enc #[e]
  unless (← isDefEq P ctx.P) && (← isDefEq env ctx.env) && (← withReducible (isDefEq v target)) do
    s.restore
    return none
  -- the premises, in order
  for a in args do
    if (← a.mvarId!.isAssigned) then continue
    let aty ← instantiateMVars (← inferType a)
    if (← isProp aty) then
      unless ← solvePremise ctx a.mvarId! aty do
        s.restore
        return none
  -- instance arguments not fixed by unification
  for a in args do
    unless (← a.mvarId!.isAssigned) do
      let aty ← instantiateMVars (← inferType a)
      if (← isClass? aty).isSome then
        a.mvarId!.assign (← synthInstance aty)
  let pf ← instantiateMVars (mkAppN (mkConst rule lvls) args)
  if pf.hasMVar then
    s.restore
    throwError "translate: rule {rule} left {pf} unsolved"
  return some (← instantiateMVars t, ← instantiateMVars c, pf)

/-- A premise of a rule: a run (under binders and hypotheses), solved by translating its value;
anything else by `rfl`. -/
partial def solvePremise (ctx : Ctx) (g : MVarId) (ty : Expr) : MetaM Bool := do
  forallTelescopeReducing ty fun xs body ↦ do
    match runsParts? body with
    | some (_, env, t, v, c) =>
      let some x := encArg? v | throwError "a premise's value is not an encoding: {v}"
      -- the environment of the premise: the binders' encodings in front of the context's
      let mut ctx' := ctx
      let mut pushed : Array Expr := #[]
      let envI ← instantiateMVars env
      -- binders whose encodings the premise's environment holds, innermost first
      let mut e := envI
      let mut front : Array Expr := #[]
      while e.isAppOfArity ``List.cons 3 do
        if (← instantiateMVars e) == (← instantiateMVars ctx.env) then break
        let hd := e.appFn!.appArg!
        match encArg? hd with
        | some y => front := front.push y
        | none => throwError "an environment entry is not an encoding: {hd}"
        e := e.appArg!
      for y in front.reverse do
        ctx' ← ctx'.push y
        pushed := pushed.push y
      let (t', c', p') ← translate ctx' (← instantiateMVars x)
      if t'.hasFVar then throwError "translate: code depends on a bound variable: {t'}"
      unless ← isDefEq t t' do return false
      unless ← isDefEq c c' do return false
      g.assign (← mkLambdaFVars xs p')
      return true
    | none =>
      -- an equation: by `rfl`
      try
        g.assign (← mkLambdaFVars xs (← mkEqRefl (body.appFn!.appArg!)))
        return true
      catch _ => return false

end

/-- `Prod.fst (a, b)` to `a` and `Prod.snd (a, b)` to `b`, everywhere in `e`, after `β`. -/
def cleanTuples (e : Expr) : MetaM Expr := do
  let e ← Core.betaReduce (← instantiateMVars e)
  return e.replace fun s ↦
    if s.isAppOfArity ``Prod.fst 3 && s.appArg!.isAppOfArity ``Prod.mk 4 then
      some s.appArg!.appFn!.appArg!
    else if s.isAppOfArity ``Prod.snd 3 && s.appArg!.isAppOfArity ``Prod.mk 4 then
      some s.appArg!.appArg!
    else none

/-- Every `match` in `e` replaced by its `casesOn` (definitionally equal). -/
def unfoldMatchers (e : Expr) : MetaM Expr :=
  Meta.transform e (post := fun s ↦ do
    if let .const f _ := s.getAppFn then
      if (← Meta.isMatcher f) then
        if let some s' ← delta? s (· == f) then
          return .visit (← Core.betaReduce s')
    return .done s)

/-- The callees' spec premises, from `hP : Includes P deps`. -/
def solvePending (pending : Array (MVarId × Array (Nat × Name))) (hP deps : Expr) :
    MetaM Unit := do
  for (m, depsH) in pending do
    let sub ← proveByTactic (← mkSubset (← depsExpr depsH) deps)
    m.assign (← mkAppM ``Includes.mono #[hP, sub])
where
  mkSubset (l l' : Expr) : MetaM Expr := do
    let ty ← inferType l
    withLocalDeclD `p (ty.appArg!) fun p ↦ do
      withLocalDeclD `hp (← mkAppM ``Membership.mem #[l, p]) fun hp ↦ do
        mkForallFVars #[p, hp] (← mkAppM ``Membership.mem #[l', p])

/-- The bodies a spec needs: its own, then its callees', each once. -/
def mergeDeps (own : Nat × Name) (callees : Array (Array (Nat × Name))) : Array (Nat × Name) :=
  callees.foldl (fun acc ds ↦ ds.foldl (fun acc d ↦
    if acc.any (·.1 == d.1) then acc else acc.push d) acc) #[own]

/-- `cost_compile f at i [measure m]`: compile `f` to the body of function `i`, and add
`f.costBody` (the code), `f.costSpec` (`f`'s run on every argument, at the machine's price) and
`f.costEq` (the price's recurrence). A recursive `f` needs a measure of its arguments that its
recursive calls decrease. -/
syntax (name := costCompile) "cost_compile " ident " at " num (&" measure " term)? : command

@[command_elab costCompile] def elabCostCompile : Command.CommandElab := fun stx ↦
  Command.liftTermElabM do
    let f : Ident := ⟨stx[1]⟩
    let i : NumLit := ⟨stx[3]⟩
    let m? : Option Syntax := if stx[4].isNone then none else some stx[4][1]
    let fn ← realizeGlobalConstNoOverloadWithInfo f
    let idx := i.getNat
    let info ← getConstInfo fn
    let lvls := info.levelParams.map Level.param
    let eqn? ← getUnfoldEqnFor? fn
    forallTelescopeReducing info.type fun xs _ ↦ do
    withLocalDeclD `P (mkConst ``Program) fun P ↦ do
      let pending ← IO.mkRef #[]
      let lhs := mkAppN (mkConst fn lvls) xs
      -- the body: `f`'s unfolding at its arguments
      let (rhs, eqPf) ← match eqn? with
        | some eqn =>
          let pf := mkAppN (mkConst eqn lvls) xs
          let ty ← inferType pf
          let some (_, l, r) := ty.eq? | throwError "{eqn} is not an equation"
          let r' ← unfoldMatchers r
          pure (r', ← mkExpectedTypeHint pf (← mkEq l r'))
          
        | none =>
          let some r ← delta? lhs (· == fn) | throwError "cannot unfold {fn}"
          let r' ← unfoldMatchers r.headBeta
          pure (r', ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs r'))
      let mut ctx : Ctx := { P, env := ← mkAppOptM ``List.nil #[mkConst ``Val], vals := #[], pending }
      for x in xs.reverse do
        ctx ← ctx.push x
      let tys ← xs.mapM fun x ↦ inferType x
      let tupleTy ← mkTupleType tys
      -- the arguments and the value, as functions of the tuple
      let (argsF, valF) ← withLocalDeclD `y tupleTy fun y ↦ do
        let comps ← tupleComponents y xs.size
        let env ← comps.foldrM (fun c l ↦ do mkAppM ``List.cons #[← mkAppM ``Enc.enc #[c], l])
          (← mkAppOptM ``List.nil #[mkConst ``Val])
        let v ← mkAppM ``Enc.enc #[mkAppN (mkConst fn lvls) comps]
        return (← mkLambdaFVars #[y] env, ← mkLambdaFVars #[y] v)
      let mkRunsBodyAt (y : Expr) : MetaM Expr := do
        let args := argsF.beta #[y]
        return mkAppN (mkConst ``RunsBody) #[P, mkNatLit idx, args, valF.beta #[y],
          mkAppN (mkConst ``machineCost) #[P, mkNatLit idx, args]]
      -- the measure, as a function of the tuple
      let measure? ← m?.mapM fun m ↦ do
        let mf ← Term.elabTerm m (some (← mkForallFVars xs (mkConst ``Nat)))
        Term.synthesizeSyntheticMVarsNoPostponing
        withLocalDeclD `y tupleTy fun y ↦ do
          mkLambdaFVars #[y] ((← instantiateMVars mf).beta (← tupleComponents y xs.size))
      let x ← mkTuple xs
      let finish (ih? : Option Expr) : MetaM Unit := do
        let ctx := match ih?, measure? with
          | some ih, some mf => { ctx with self := some { fn := fn, index := idx, ih := ih, measure := mf, args := xs } }
          | _, _ => ctx
        let (t, c, pf) ← translate ctx rhs
        let t ← instantiateMVars t
        if t.hasFVar || t.hasMVar then throwError "the code is not closed: {t}"
        -- the code, as a constant
        let bodyName := fn.str "costBody"
        let bodyTy := mkConst ``LeanVM.Cost.Term
        addAndCompile <| .defnDecl (mkDefinitionValEx bodyName [] bodyTy t .abbrev .safe [])
        let pendingNow ← pending.get
        let calleeDeps ← pendingNow.mapM fun (_, d) ↦ pure d
        let deps := mergeDeps (idx, bodyName) calleeDeps
        let depsE ← depsExpr deps
        withLocalDeclD `hP (mkAppN (mkConst ``Includes) #[P, depsE]) fun hP ↦ do
          solvePending pendingNow hP depsE
          let mem ← proveByTactic (← mkAppM ``Membership.mem
            #[depsE, ← mkAppM ``Prod.mk #[mkNatLit idx, mkConst bodyName]])
          let hb ← mkAppM ``Includes.get #[hP, mem]
          -- the run at `f`'s value
          let env := ctx.env
          let motive ← withLocalDeclD `z (← inferType lhs) fun z ↦ do
            mkLambdaFVars #[z] (mkAppN (mkConst ``Runs) #[P, env, mkConst bodyName,
              ← mkAppM ``Enc.enc #[z], c])
          let pf' ← mkEqMPR (← mkCongrArg motive eqPf) pf
          let runBody ← mkAppM ``RunsBody.intro #[hb, pf']
          let specTy ← mkForallFVars (#[P, hP] ++ xs) (← mkRunsBodyAt x)
          let (specVal, costPf) ← match ih?, measure? with
            | some ih, some mf =>
              let ex ← mkAppM ``Exists.intro #[c, runBody]
              let stepXs ← mkLambdaFVars (xs.push ih) ex
              let step ← withLocalDeclD `x tupleTy fun x' ↦ do
                let ihTy ← withLocalDeclD `y tupleTy fun y ↦ do
                  let lt ← mkAppM ``LT.lt #[mf.beta #[y], mf.beta #[x']]
                  mkForallFVars #[y] (← mkArrow lt (← mkRunsBodyAt y))
                withLocalDeclD `ih ihTy fun ih' ↦ do
                  mkLambdaFVars #[x', ih'] (mkAppN stepXs ((← tupleComponents x' xs.size).push ih'))
              let specT ← mkAppM ``RunsBody.induction #[argsF, valF, mf, step]
              let ihVal ← withLocalDeclD `y tupleTy fun y ↦ do
                let lt ← mkAppM ``LT.lt #[mf.beta #[y], mf.beta #[x]]
                withLocalDeclD `h lt fun h ↦ do mkLambdaFVars #[y, h] (mkApp specT y)
              let runBody' := (← mkLambdaFVars #[ih] runBody).beta #[ihVal]
              pure (← mkLambdaFVars (#[P, hP] ++ xs) (mkApp specT x),
                ← mkAppM ``machineCost_eq #[runBody'])
            | _, _ =>
              pure (← mkLambdaFVars (#[P, hP] ++ xs) (← mkAppM ``RunsBody.withMachineCost #[runBody]),
                ← mkAppM ``machineCost_eq #[runBody])
          let specName := fn.str "costSpec"
          let specVal ← instantiateMVars specVal
          let specTy ← instantiateMVars specTy
          addDecl <| .thmDecl
            { name := specName, levelParams := info.levelParams, type := specTy, value := specVal }
          let costTy ← cleanTuples (← inferType costPf)
          let costTy ← mkForallFVars (#[P, hP] ++ xs) costTy
          let costTy ← instantiateMVars costTy
          let costVal ← instantiateMVars (← mkLambdaFVars (#[P, hP] ++ xs) costPf)
          addDecl <| .thmDecl
            { name := fn.str "costEq", levelParams := info.levelParams, type := costTy,
              value := costVal }
          let entry : CompiledFn :=
            { fn := fn, index := idx, body := bodyName, spec := specName, deps := deps }
          modifyEnv (compiledExt.addEntry · entry)
          logInfo m!"{fn}: function {idx}, code {t}"
      match measure? with
      | some mf =>
        let ihTy ← withLocalDeclD `y tupleTy fun y ↦ do
          let lt ← mkAppM ``LT.lt #[mf.beta #[y], mf.beta #[x]]
          mkForallFVars #[y] (← mkArrow lt (← mkRunsBodyAt y))
        withLocalDeclD `ih ihTy fun ih ↦ finish (some ih)
      | none => finish none

/-- `#translate fun xs ↦ e`: the code and price of `e` with `xs` in the environment. -/
elab "#translate " t:term : command => Command.liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  lambdaTelescope e fun xs body ↦ do
    withLocalDeclD `P (mkConst ``Program) fun P ↦ do
      let pending ← IO.mkRef #[]
      let mut ctx : Ctx := { P, env := ← mkAppOptM ``List.nil #[mkConst ``Val], vals := #[], pending }
      for x in xs.reverse do
        ctx ← ctx.push x
      let (t, c, pf) ← translate ctx body
      check pf
      logInfo m!"code: {t}\nprice: {c}"

end LeanVM.Cost.Compiler
