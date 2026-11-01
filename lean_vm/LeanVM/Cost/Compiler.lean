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

/-- What a data parameter is: an encoded value, or a function of `arity` arguments (the machine
holds a closure, the spec assumes the closure computes the function). -/
inductive ParamKind where
  | enc
  | fn (arity : Nat)
  deriving Inhabited, BEq

/-- A compiled function: the term compiled (a head constant applied to fixed arguments), its data
parameters, its index, the constant of its body, its spec, and the bodies its spec needs (its own
first). -/
structure CompiledFn where
  head : Name
  static : Array Expr
  params : Array ParamKind
  index : Nat
  body : Name
  spec : Name
  deps : Array (Nat × Name)
  deriving Inhabited

/-- The compiled functions, by head constant. -/
initialize compiledExt :
    SimplePersistentEnvExtension CompiledFn (NameMap (Array CompiledFn)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e ↦ m.insert e.head (((m.find? e.head).getD #[]).push e)
    addImportedFn := fun as ↦ as.foldl (fun m a ↦ a.foldl
      (fun m e ↦ m.insert e.head (((m.find? e.head).getD #[]).push e)) m) {} }

/-- The next free index of the program, past the `reserved` ones. -/
def nextIndex (reserved : Array Nat := #[]) : MetaM Nat := do
  let m := compiledExt.getState (← getEnv)
  let n := m.foldl (fun acc _ fs ↦ fs.foldl (fun acc f ↦ max acc (f.index + 1)) acc) 1
  return reserved.foldl (fun acc r ↦ max acc (r + 1)) n

/-- An entry of the environment: the encoding of a Lean expression, or a closure `v` computing
the Lean function `f` (`hf : ∀ a…, RunsApp P v [enc a…] (enc (f a…))`). -/
inductive Entry where
  | enc (x : Expr)
  | fn (f v hf : Expr) (arity : Nat)

/-- The function being compiled, when it is recursive: its term, the induction hypothesis, the
measure (of the tuple of its encoded parameters), its parameters and their kinds. -/
structure SelfInfo where
  term : Expr
  ih : Expr
  measure : Expr
  args : Array Expr
  kinds : Array ParamKind

/-- The translation's context: the program, the environment (a list of values) and its entries;
the function being compiled, if it is recursive; the callees' premises `Includes P deps` still to
be proved; the name lifted closures are named after, and their counter. -/
structure Ctx where
  P : Expr
  env : Expr
  vals : Array Entry
  self : Option SelfInfo := none
  pending : IO.Ref (Array (MVarId × Array (Nat × Name)))
  base : Name
  lams : IO.Ref Nat
  /-- The indices of the functions being compiled, not yet registered. -/
  reserved : Array Nat := #[]

/-- The context with `x`'s encoding in front. -/
def Ctx.push (ctx : Ctx) (x : Expr) : MetaM Ctx := do
  let v ← mkAppM ``Enc.enc #[x]
  return { ctx with env := ← mkAppM ``List.cons #[v, ctx.env], vals := #[.enc x] ++ ctx.vals }

/-- The context with a closure `v` of `f` in front. -/
def Ctx.pushFn (ctx : Ctx) (f v hf : Expr) (arity : Nat) : MetaM Ctx := do
  let env ← mkAppM ``List.cons #[v, ctx.env]
  return { ctx with env, vals := #[.fn f v hf arity] ++ ctx.vals }

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

/-- The arguments as one value: `(x₁, (x₂, …))`, or `x₁` alone, or `()`. -/
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
  if n == 0 then return #[]
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

/-- `∀ a…, p a…`: `RunsApp P v [enc a…] (enc (f a…))` for a function type `ty`. -/
def runsAppType (P f v ty : Expr) : MetaM Expr :=
  forallTelescopeReducing ty fun as _ ↦ do
    let vs ← as.foldrM (fun a l ↦ do mkAppM ``List.cons #[← mkAppM ``Enc.enc #[a], l])
      (← mkAppOptM ``List.nil #[mkConst ``Val])
    let w ← mkAppM ``Enc.enc #[mkAppN f as]
    mkForallFVars as (mkAppN (mkConst ``RunsApp) #[P, v, vs, w])

/-- The kind of a parameter of type `ty`: a function (not a proof, not a type), or a value. -/
def paramKind (ty : Expr) : MetaM ParamKind := do
  let ty ← whnfR ty
  if ty.isForall then
    let n ← forallTelescopeReducing ty fun as _ ↦ pure as.size
    return .fn n
  return .enc

/-- The compiled function `e` is a call of, and the call's data arguments. -/
def findCompiled? (e : Expr) : MetaM (Option (CompiledFn × Array Expr)) := do
  let .const h _ := e.getAppFn | return none
  let some cands := (compiledExt.getState (← getEnv)).find? h | return none
  let args := e.getAppArgs
  for cf in cands do
    if args.size == cf.static.size + cf.params.size then
      let mut ok := true
      for i in [0:cf.static.size] do
        unless ← isDefEq args[i]! cf.static[i]! do
          ok := false
          break
      if ok then return some (cf, args.extract cf.static.size args.size)
  return none

/-- The bodies a spec needs: its own, then its callees', each once. -/
def mergeDeps (own : Nat × Name) (callees : Array (Array (Nat × Name))) : Array (Nat × Name) :=
  callees.foldl (fun acc ds ↦ ds.foldl (fun acc d ↦
    if acc.any (·.1 == d.1) then acc else acc.push d) acc) #[own]

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

mutual

/-- **The translation** of `e`: its code, its price, and a proof of
`Runs P env code (enc e) price`. -/
partial def translate (ctx : Ctx) (e : Expr) : MetaM (Expr × Expr × Expr) := do
  let e ← instantiateMVars e
  let e := e.headBeta
  -- a variable of the environment
  for h : i in [0:ctx.vals.size] do
    if let .enc x := ctx.vals[i] then
      if x == e then
        let enc ← mkAppM ``Enc.enc #[e]
        let hget ← mkEqRefl (← mkAppM ``Option.some #[enc])
        let pf ← mkAppOptM ``Rule.var #[ctx.P, ctx.env, none, none, mkNatLit i, e, hget]
        return (mkApp (mkConst ``Term.var) (mkNatLit i), mkNatLit 1, pf)
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
  -- an application of a closure of the environment
  if let .fvar _ := e.getAppFn then
    for h : i in [0:ctx.vals.size] do
      if let .fn f v hf arity := ctx.vals[i] then
        if f == e.getAppFn && e.getAppNumArgs == arity then
          let args := e.getAppArgs
          let (_, _, _, pl) ← translateList ctx (args.toList.map .inl)
          let hget ← mkEqRefl (← mkAppM ``Option.some #[v])
          let pv ← mkAppOptM ``Rule.rawVar #[ctx.P, ctx.env, mkNatLit i, v, hget]
          let pf ← mkAppM ``Rule.app #[pv, pl, mkAppN hf args]
          return ← parts pf
  -- a call of the function being compiled, or of a compiled function
  if let some self := ctx.self then
    if e.getAppFn == self.term.getAppFn && e.getAppNumArgs == self.term.getAppNumArgs + self.args.size then
      if ← (self.term.getAppArgs.zip (e.getAppArgs.extract 0 self.term.getAppNumArgs)).allM
          fun (a, b) ↦ isDefEq a b then
        return ← translateSelfCall ctx self e
  if let some (cf, args) ← findCompiled? e then
    return ← translateCall ctx cf args e
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
      return ← translate ctx (← unfoldMatchers e'.headBeta)
  throwError "translate: no rule for {e}"

/-- The code and price a run's proof states. -/
partial def parts (pf : Expr) : MetaM (Expr × Expr × Expr) := do
  let ty ← instantiateMVars (← inferType pf)
  let some (_, _, t, _, cost) := runsParts? ty | throwError "not a run: {ty}"
  return (t, cost, pf)

/-- The translations of the arguments (an encoded value, or a closure: its code, value and proof
already built), as a run of the list: the codes, the values, the price, the proof. -/
partial def translateList (ctx : Ctx) (es : List (Expr ⊕ (Expr × Expr × Expr × Expr))) :
    MetaM (Expr × Expr × Expr × Expr) := do
  match es with
  | [] =>
    let ts ← mkAppOptM ``List.nil #[mkConst ``Term]
    let vs ← mkAppOptM ``List.nil #[mkConst ``Val]
    return (ts, vs, mkNatLit 0, ← mkAppOptM ``RunsList.nil #[ctx.P, ctx.env])
  | a :: es =>
    let (t, v, c, p) ← match a with
      | .inl e => do
        let (t, c, p) ← translate ctx e
        pure (t, ← mkAppM ``Enc.enc #[e], c, p)
      | .inr r => pure r
    let (ts, vs, cs, ps) ← translateList ctx es
    let pf ← mkAppOptM ``RunsList.cons #[ctx.P, ctx.env, t, ts, v, vs, c, cs, p, ps]
    return (← mkAppM ``List.cons #[t, ts], ← mkAppM ``List.cons #[v, vs],
      ← mkAppM ``HAdd.hAdd #[c, cs], pf)

/-- A function argument as a closure: a closure of the environment passed on, or a lambda (its
free variables captured) compiled to a function of its own. Returns the code, the value, the price,
the run's proof, and the hypothesis `∀ a…, RunsApp P v [enc a…] (enc (f a…))`. -/
partial def closureOf (ctx : Ctx) (f : Expr) (arity : Nat) :
    MetaM (Expr × Expr × Expr × Expr × Expr) := do
  -- a closure of the environment
  for h : i in [0:ctx.vals.size] do
    if let .fn g v hf _ := ctx.vals[i] then
      if g == f then
        let hget ← mkEqRefl (← mkAppM ``Option.some #[v])
        let pv ← mkAppOptM ``Rule.rawVar #[ctx.P, ctx.env, mkNatLit i, v, hget]
        return (mkApp (mkConst ``Term.var) (mkNatLit i), v, mkNatLit 1, pv, hf)
  -- a lambda: lifted
  let fty ← inferType f
  forallBoundedTelescope fty arity fun ps _ ↦ do
    let body ← Core.betaReduce (mkAppN f ps)
    let fvs := (← body.collectFVars.run {}).2.fvarIds.filter fun x ↦ !ps.contains (.fvar x)
    let caps := ctx.vals.filter fun en ↦ match en with
      | .enc x => x.isFVar && fvs.contains x.fvarId!
      | .fn g _ _ _ => g.isFVar && fvs.contains g.fvarId!
    let capFvs : Array Expr := caps.map fun en ↦ match en with
      | .enc x => x
      | .fn g _ _ _ => g
    for x in fvs do
      unless capFvs.contains (.fvar x) do
        throwError "closure: free variable {Expr.fvar x} of {f} is not in the environment"
    let lam ← mkLambdaFVars (capFvs ++ ps) body
    let k ← ctx.lams.modifyGet fun n ↦ (n, n + 1)
    let name := ctx.base.str s!"lam{k}"
    let cf ← compileFn name lam (← nextIndex ctx.reserved) none ctx.reserved
    -- the closure: function `cf.index` with the captures' values
    let mut capArgs : Array (Expr ⊕ (Expr × Expr × Expr × Expr)) := #[]
    for en in caps do
      match en with
      | .enc x => capArgs := capArgs.push (.inl x)
      | .fn g _ _ arity =>
        let (t, v, c, p, _) ← closureOf ctx g arity
        capArgs := capArgs.push (.inr (t, v, c, p))
    let (ts, us, c, pl) ← translateList ctx capArgs.toList
    let pf ← mkAppOptM ``Rule.closure #[ctx.P, ctx.env, mkNatLit cf.index, ts, us, c, pl]
    let (t, cost, _) ← parts pf
    let v ← mkAppM ``Val.fn #[mkNatLit cf.index, us]
    -- the hypothesis, from the lifted function's spec
    let hInc ← mkFreshExprMVar (mkAppN (mkConst ``Includes) #[ctx.P, ← depsExpr cf.deps])
    ctx.pending.modify (·.push (hInc.mvarId!, cf.deps))
    let mut specArgs := #[ctx.P, hInc]
    for en in caps do
      match en with
      | .enc x => specArgs := specArgs.push x
      | .fn g v hf _ => specArgs := specArgs ++ #[g, v, hf]
    let hf ← withLocalDeclsD (← ps.mapM fun p ↦ do
        pure ((← p.fvarId!.getUserName), fun _ ↦ inferType p)) fun qs ↦ do
      let spec := mkAppN (mkConst cf.spec) (specArgs ++ qs)
      let vs ← qs.foldrM (fun q l ↦ do mkAppM ``List.cons #[← mkAppM ``Enc.enc #[q], l])
        (← mkAppOptM ``List.nil #[mkConst ``Val])
      let w ← mkAppM ``Enc.enc #[← Core.betaReduce (mkAppN f qs)]
      mkLambdaFVars qs (← mkAppOptM ``RunsApp.of_spec #[ctx.P, mkNatLit cf.index, us, vs, w, spec])
    let hfTy ← runsAppType ctx.P f v fty
    return (t, v, cost, pf, ← mkExpectedTypeHint hf hfTy)

/-- A call of a compiled function: its spec at the arguments, the premise `Includes P deps`
left to the end. -/
partial def translateCall (ctx : Ctx) (cf : CompiledFn) (args : Array Expr) (e : Expr) :
    MetaM (Expr × Expr × Expr) := do
  let mut items : Array (Expr ⊕ (Expr × Expr × Expr × Expr)) := #[]
  let mut specArgs : Array Expr := #[]
  for (a, k) in args.zip cf.params do
    match k with
    | .enc =>
      items := items.push (.inl a)
      specArgs := specArgs.push a
    | .fn arity =>
      let (t, v, c, p, hf) ← closureOf ctx a arity
      items := items.push (.inr (t, v, c, p))
      specArgs := specArgs ++ #[a, v, hf]
  let (_, _, _, pl) ← translateList ctx items.toList
  let hInc ← mkFreshExprMVar (mkAppN (mkConst ``Includes) #[ctx.P, ← depsExpr cf.deps])
  ctx.pending.modify (·.push (hInc.mvarId!, cf.deps))
  let spec := mkAppN (mkConst cf.spec) (#[ctx.P, hInc] ++ specArgs)
  let _ := e
  parts (← mkAppM ``Rule.call #[pl, spec])

/-- A recursive call: the induction hypothesis at the arguments, the decrease by a tactic. The
function arguments must be the function's own. -/
partial def translateSelfCall (ctx : Ctx) (self : SelfInfo) (e : Expr) :
    MetaM (Expr × Expr × Expr) := do
  let args := e.getAppArgs.extract self.term.getAppNumArgs e.getAppNumArgs
  let mut items : Array (Expr ⊕ (Expr × Expr × Expr × Expr)) := #[]
  let mut encArgs : Array Expr := #[]
  for ((a, x), k) in (args.zip self.args).zip self.kinds do
    match k with
    | .enc =>
      items := items.push (.inl a)
      encArgs := encArgs.push a
    | .fn arity =>
      unless a == x do throwError "a recursive call changes the function argument {x}"
      let (t, v, c, p, _) ← closureOf ctx a arity
      items := items.push (.inr (t, v, c, p))
  let (_, _, _, pl) ← translateList ctx items.toList
  let encSelf := (self.args.zip self.kinds).filterMap fun (x, k) ↦ if k == .enc then some x else none
  let y ← mkTuple encArgs
  let x ← mkTuple encSelf
  let dec ← Core.betaReduce (← mkAppM ``LT.lt #[self.measure.beta #[y], self.measure.beta #[x]])
  let decPf ← proveByTactic dec
  parts (← mkAppM ``Rule.call #[pl, mkAppN self.ih #[y, decPf]])

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
  for a in args do
    if (← a.mvarId!.isAssigned) then continue
    let aty ← instantiateMVars (← inferType a)
    if (← isProp aty) then
      unless ← solvePremise ctx a.mvarId! aty do
        s.restore
        return none
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
      let mut ctx' := ctx
      let mut e ← instantiateMVars env
      let mut front : Array Expr := #[]
      let base ← instantiateMVars ctx.env
      while e.isAppOfArity ``List.cons 3 do
        if e == base then break
        let hd := e.appFn!.appArg!
        match encArg? hd with
        | some y => front := front.push y
        | none => throwError "an environment entry is not an encoding: {hd}"
        e := e.appArg!
      for y in front.reverse do
        ctx' ← ctx'.push y
      let (t', c', p') ← translate ctx' (← instantiateMVars x)
      if t'.hasFVar then throwError "translate: code depends on a bound variable: {t'}"
      unless ← isDefEq t t' do return false
      unless ← isDefEq c c' do return false
      g.assign (← mkLambdaFVars xs p')
      return true
    | none =>
      try
        g.assign (← mkLambdaFVars xs (← mkEqRefl (body.appFn!.appArg!)))
        return true
      catch _ => return false

/-- **Compile** the function `term` (closed) to the body of function `idx`: add `name.costBody`,
`name.costSpec`, `name.costEq`, and register it. A recursive term needs `measure?`, a function of
its encoded parameters (as a tuple) that its recursive calls decrease. -/
partial def compileFn (name : Name) (term : Expr) (idx : Nat) (measure? : Option Expr)
    (reserved : Array Nat := #[]) : MetaM CompiledFn := do
  let term ← instantiateMVars term
  let ty ← inferType term
  forallTelescopeReducing ty fun xs _ ↦ do
  withLocalDeclD `P (mkConst ``Program) fun P ↦ do
    let kinds ← xs.mapM fun x ↦ do paramKind (← inferType x)
    -- the closures' hypotheses
    let fnInfo ← (xs.zip kinds).filterMapM fun (x, k) ↦ match k with
      | .fn _ => pure (some x)
      | .enc => pure none
    withFnHyps P fnInfo #[] fun fnHyps ↦ do
    let pending ← IO.mkRef #[]
    let lams ← IO.mkRef 0
    let lhs ← Core.betaReduce (mkAppN term xs)
    let (rhs, eqPf) ← if term.isLambda then
        -- a lifted lambda: its body as it is
        let r' ← unfoldMatchers lhs
        pure (r', ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs r'))
      else
        let head := lhs.getAppFn
        let some headName := head.constName? | throwError "compile: {lhs} has no head constant"
        let lvls := head.constLevels!
        match ← getUnfoldEqnFor? headName with
        | some eqn =>
          let pf := mkAppN (mkConst eqn lvls) lhs.getAppArgs
          let pty ← inferType pf
          let some (_, l, r) := pty.eq? | throwError "{eqn} is not an equation"
          let r' ← unfoldMatchers r
          pure (r', ← mkExpectedTypeHint pf (← mkEq l r'))
        | none =>
          let some r ← delta? lhs (· == headName) | throwError "cannot unfold {headName}"
          let r' ← unfoldMatchers r.headBeta
          pure (r', ← mkExpectedTypeHint (← mkEqRefl lhs) (← mkEq lhs r'))
    let env0 ← mkAppOptM ``List.nil #[mkConst ``Val]
    let mut ctx : Ctx := { P := P, env := env0, vals := #[], pending := pending, base := name,
                           lams := lams, reserved := reserved.push idx }
    for (x, k) in (xs.zip kinds).reverse do
      match k with
      | .enc => ctx ← ctx.push x
      | .fn arity =>
        let some (_, v, hf) := fnHyps.find? (·.1 == x) | throwError "no closure for {x}"
        ctx ← ctx.pushFn x v hf arity
    let encXs := (xs.zip kinds).filterMap fun (x, k) ↦ if k == .enc then some x else none
    let tupleTy ← mkTupleType (← encXs.mapM fun x ↦ inferType x)
    -- the environment as a function of the tuple of the encoded parameters
    let argsF ← withLocalDeclD `y tupleTy fun y ↦ do
      let comps ← tupleComponents y encXs.size
      let mut l ← mkAppOptM ``List.nil #[mkConst ``Val]
      let mut j := encXs.size
      for (x, k) in (xs.zip kinds).reverse do
        match k with
        | .enc =>
          j := j - 1
          l ← mkAppM ``List.cons #[← mkAppM ``Enc.enc #[comps[j]!], l]
        | .fn _ =>
          let some (_, v, _) := fnHyps.find? (·.1 == x) | throwError "no closure for {x}"
          l ← mkAppM ``List.cons #[v, l]
      mkLambdaFVars #[y] l
    let valF ← withLocalDeclD `y tupleTy fun y ↦ do
      let comps ← tupleComponents y encXs.size
      let mut j := 0
      let mut args := #[]
      for (x, k) in xs.zip kinds do
        match k with
        | .enc =>
          args := args.push comps[j]!
          j := j + 1
        | .fn _ => args := args.push x
      mkLambdaFVars #[y] (← mkAppM ``Enc.enc #[← Core.betaReduce (mkAppN term args)])
    let runsBodyAt (y : Expr) : MetaM Expr := do
      let args ← Core.betaReduce (argsF.beta #[y])
      return mkAppN (mkConst ``RunsBody) #[P, mkNatLit idx, args, valF.beta #[y],
        mkAppN (mkConst ``machineCost) #[P, mkNatLit idx, args]]
    let x ← mkTuple encXs
    let mf? ← measure?.mapM fun m ↦ withLocalDeclD `y tupleTy fun y ↦ do
      mkLambdaFVars #[y] (m.beta (← tupleComponents y encXs.size))
    let finish (ih? : Option Expr) : MetaM CompiledFn := do
      let ctx := match ih?, mf? with
        | some ih, some mf =>
          let si : SelfInfo := { term := term, ih := ih, measure := mf, args := xs, kinds := kinds }
          { ctx with self := some si }
        | _, _ => ctx
      let (t, c, pf) ← translate ctx rhs
      let t ← instantiateMVars t
      if t.hasFVar || t.hasMVar then throwError "the code is not closed: {t}"
      let bodyName := name.str "costBody"
      let bodyTy := mkConst ``LeanVM.Cost.Term
      addAndCompile <| .defnDecl (mkDefinitionValEx bodyName [] bodyTy t .abbrev .safe [])
      let pendingNow ← pending.get
      let deps := mergeDeps (idx, bodyName) (pendingNow.map (·.2))
      let depsE ← depsExpr deps
      withLocalDeclD `hP (mkAppN (mkConst ``Includes) #[P, depsE]) fun hP ↦ do
        solvePending pendingNow hP depsE
        let mem ← proveByTactic (← mkAppM ``Membership.mem
          #[depsE, ← mkAppM ``Prod.mk #[mkNatLit idx, mkConst bodyName]])
        let hb ← mkAppM ``Includes.get #[hP, mem]
        let motive ← withLocalDeclD `z (← inferType lhs) fun z ↦ do
          mkLambdaFVars #[z] (mkAppN (mkConst ``Runs) #[P, ctx.env, mkConst bodyName,
            ← mkAppM ``Enc.enc #[z], c])
        let pf' ← mkEqMPR (← mkCongrArg motive eqPf) pf
        let runBody ← mkAppM ``RunsBody.intro #[hb, pf']
        -- the spec's binders: `P`, `hP`, each parameter (a function with its closure and hypothesis)
        let mut binders := #[P, hP]
        for (x, k) in xs.zip kinds do
          match k with
          | .enc => binders := binders.push x
          | .fn _ =>
            let some (_, v, hf) := fnHyps.find? (·.1 == x) | throwError "no closure for {x}"
            binders := binders ++ #[x, v, hf]
        let (specVal, costPf) ← match ih?, mf? with
          | some ih, some mf =>
            let ex ← mkAppM ``Exists.intro #[c, runBody]
            let stepXs ← mkLambdaFVars (encXs.push ih) ex
            let step ← withLocalDeclD `x tupleTy fun x' ↦ do
              let ihTy ← withLocalDeclD `y tupleTy fun y ↦ do
                let lt ← mkAppM ``LT.lt #[mf.beta #[y], mf.beta #[x']]
                mkForallFVars #[y] (← mkArrow lt (← runsBodyAt y))
              withLocalDeclD `ih ihTy fun ih' ↦ do
                mkLambdaFVars #[x', ih'] (mkAppN stepXs ((← tupleComponents x' encXs.size).push ih'))
            let specT ← mkAppM ``RunsBody.induction #[argsF, valF, mf, step]
            let ihVal ← withLocalDeclD `y tupleTy fun y ↦ do
              let lt ← mkAppM ``LT.lt #[mf.beta #[y], mf.beta #[x]]
              withLocalDeclD `h lt fun h ↦ do mkLambdaFVars #[y, h] (mkApp specT y)
            let runBody' := (← mkLambdaFVars #[ih] runBody).beta #[ihVal]
            pure (← mkLambdaFVars binders (mkApp specT x), ← mkAppM ``machineCost_eq #[runBody'])
          | _, _ =>
            pure (← mkLambdaFVars binders (← mkAppM ``RunsBody.withMachineCost #[runBody]),
              ← mkAppM ``machineCost_eq #[runBody])
        let specTy ← instantiateMVars (← mkForallFVars binders (← cleanTuples (← runsBodyAt x)))
        let specName := name.str "costSpec"
        let specVal ← instantiateMVars specVal
        addDecl <| .thmDecl
          { name := specName, levelParams := [], type := specTy, value := specVal }
        let costTy ← mkForallFVars binders (← cleanTuples (← inferType costPf))
        let costTy ← instantiateMVars costTy
        let costVal ← instantiateMVars (← mkLambdaFVars binders costPf)
        addDecl <| .thmDecl
          { name := name.str "costEq", levelParams := [], type := costTy, value := costVal }
        let headC := if term.isLambda then name else term.getAppFn.constName!
        let entry : CompiledFn :=
          { head := headC, static := term.getAppArgs, params := kinds, index := idx,
            body := bodyName, spec := specName, deps := deps }
        modifyEnv (compiledExt.addEntry · entry)
        logInfo m!"{name}: function {idx}, code {t}"
        return entry
    match mf? with
    | some mf =>
      let ihTy ← withLocalDeclD `y tupleTy fun y ↦ do
        let lt ← mkAppM ``LT.lt #[mf.beta #[y], mf.beta #[x]]
        mkForallFVars #[y] (← mkArrow lt (← runsBodyAt y))
      withLocalDeclD `ih ihTy fun ih ↦ finish (some ih)
    | none => finish none

/-- Local closures `v` and hypotheses for the function parameters `fs`. -/
partial def withFnHyps {α : Type} (P : Expr) (fs : Array Expr) (acc : Array (Expr × Expr × Expr))
    (k : Array (Expr × Expr × Expr) → MetaM α) : MetaM α := do
  if h : acc.size < fs.size then
    let f := fs[acc.size]
    withLocalDeclD ((← f.fvarId!.getUserName).appendAfter "Val") (mkConst ``Val) fun v ↦ do
      let hty ← runsAppType P f v (← inferType f)
      withLocalDeclD ((← f.fvarId!.getUserName).appendAfter "Spec") hty fun hf ↦
        withFnHyps P fs (acc.push (f, v, hf)) k
  else k acc

end

/-- `cost_compile name := term [at i] [measure m]`: compile `term` (a function: a constant applied
to its fixed arguments, such as types and instances) to the body of function `i` (the next free
index by default), and add `name.costBody` (the code), `name.costSpec` (the run on every argument,
at the machine's price, in every program holding the bodies it needs) and `name.costEq` (the
price's recurrence). A recursive term needs a measure of its encoded parameters that its recursive
calls decrease; its function parameters stay fixed. -/
syntax (name := costCompile) "cost_compile " ident " := " term (" at " num)? (&" measure " term)? :
  command

@[command_elab costCompile] def elabCostCompile : Command.CommandElab := fun stx ↦
  Command.liftTermElabM do
    let name := (Lean.TSyntax.getId ⟨stx[1]⟩ : Name)
    let name := (← getCurrNamespace) ++ name
    let term ← Term.elabTerm stx[3] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let term ← instantiateMVars term
    let idx ← if stx[4].isNone then nextIndex else pure (TSyntax.getNat ⟨stx[4][1]⟩)
    let measure? ← if stx[5].isNone then pure none else do
      let ty ← inferType term
      -- the measure takes the encoded parameters
      let mty ← forallTelescopeReducing ty fun xs _ ↦ do
        let encXs ← xs.filterM fun x ↦ do pure ((← paramKind (← inferType x)) == .enc)
        mkForallFVars encXs (mkConst ``Nat)
      let m ← Term.elabTerm stx[5][1] (some mty)
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (some (← instantiateMVars m))
    discard <| compileFn name term idx measure?

/-- `#translate fun xs ↦ e`: the code and price of `e` with `xs` in the environment. -/
elab "#translate " t:term : command => Command.liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  lambdaTelescope e fun xs body ↦ do
    withLocalDeclD `P (mkConst ``Program) fun P ↦ do
      let pending ← IO.mkRef #[]
      let lams ← IO.mkRef 0
      let env0 ← mkAppOptM ``List.nil #[mkConst ``Val]
      let mut ctx : Ctx := { P := P, env := env0, vals := #[], pending := pending,
                             base := `translate, lams := lams }
      for x in xs.reverse do
        ctx ← ctx.push x
      let (t, c, pf) ← translate ctx body
      check pf
      logInfo m!"code: {t}\nprice: {c}"

end LeanVM.Cost.Compiler
