module

public import LeanVM.Cost.Rules
public meta import Lean.Elab.Command
public meta import Lean.Meta.Basic
public meta import Lean.Meta.Match.MatcherApp.Basic
public meta import Lean.Meta.Constructions.SparseCasesOn
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
  (``Bool.or, ``Rule.boolOr),
  (``Bool.and, ``Rule.boolAnd),
  (``Bool.not, ``Rule.boolNot),
  (``HAdd.hAdd, ``Rule.natAdd),
  (``HAdd.hAdd, ``Rule.kAdd),
  (``HSub.hSub, ``Rule.natSub),
  (``HMul.hMul, ``Rule.natMul),
  (``HMul.hMul, ``Rule.kMul),
  (``HDiv.hDiv, ``Rule.natDiv),
  (``HMod.hMod, ``Rule.natMod),
  (``Decidable.decide, ``Rule.natLt),
  (``Decidable.decide, ``Rule.natLe),
  (``Decidable.decide, ``Rule.natEq),
  (``Decidable.decide, ``Rule.wordLt),
  (``Decidable.decide, ``Rule.wordLe),
  (``Decidable.decide, ``Rule.wordEq),
  (``Decidable.decide, ``Rule.kEq),
  (``Decidable.decide, ``Rule.decideEqTrue),
  (``Decidable.decide, ``Rule.uint8Eq),
  (``Decidable.decide, ``Rule.decideAnd),
  (``Decidable.decide, ``Rule.decideNot),
  (``HXor.hXor, ``Rule.wXor),
  (``HXor.hXor, ``Rule.u8Xor),
  (``HAnd.hAnd, ``Rule.wAnd),
  (``HAnd.hAnd, ``Rule.u8And),
  (``HAnd.hAnd, ``Rule.natAnd),
  (``HOr.hOr, ``Rule.wOr),
  (``HOr.hOr, ``Rule.u8Or),
  (``Complement.complement, ``Rule.wNot),
  (``HShiftLeft.hShiftLeft, ``Rule.wShl),
  (``HShiftRight.hShiftRight, ``Rule.wShr),
  (``HShiftRight.hShiftRight, ``Rule.natShiftRight),
  (``HAdd.hAdd, ``Rule.wAdd),
  (``HSub.hSub, ``Rule.wSub),
  (``HMul.hMul, ``Rule.wMul),
  (``UInt64.toNat, ``Rule.wToNat),
  (``Nat.toUInt64, ``Rule.natToUInt64),
  (``LeanVM.Parameters.K.lane, ``Rule.kLane),
  (``UInt8.toUInt64, ``Rule.u8ToUInt64),
  (``UInt64.toUInt8, ``Rule.u64ToUInt8),
  (``BEq.beq, ``Rule.natBEq),
  (``BEq.beq, ``Rule.wordBEq),
  (``BEq.beq, ``Rule.kBEq),
  (``Array.size, ``Rule.arrSize),
  (``HAppend.hAppend, ``Rule.arrAppend),
  (``Array.replicate, ``Rule.arrReplicate),
  (``Array.toList, ``Rule.arrToList),
  (``List.toArray, ``Rule.listToArray),
  (``Array.getD, ``Rule.arrGetD),
  (``GetElem?.getElem?, ``Rule.arrGetElem?),
  (``GetElem.getElem, ``Rule.arrGetElem),
  (``LeanVM.Parameters.K.ofLane, ``Rule.kOfLane),
  (``UInt8.toNat, ``Rule.uint8ToNat),
  (``UInt64.ofNat, ``Rule.uint64OfNat),
  (``HShiftLeft.hShiftLeft, ``Rule.natShiftLeft),
  (``Vector.toList, ``Rule.vecToList),
  (``Vector.mk, ``Rule.vecMk),
  (``Subtype.val, ``Rule.subtypeVal),
  (``Subtype.mk, ``Rule.subtypeMk),
  (``Array.setIfInBounds, ``Rule.arrSetIfInBounds),
  (``Array.extract, ``Rule.arrExtract),
  (``Fin.val, ``Rule.finVal),
  (``Fin.mk, ``Rule.finMk),
  (``HSub.hSub, ``Rule.kSub)
]

/-- Rewrites: a library function compiled through an equal form (`lhs = rhs`). -/
def rewrites : List (Name × Name) := [
  (``Array.zipWith, ``Rewrite.arrayZipWith),
  (``HPow.hPow, ``Rewrite.natTwoPow),
  (``Decidable.decide, ``Rewrite.decideEqList)
]

/-- Measures registered by `cost_measure`, by function: over all its parameters. -/
initialize measureExt : SimplePersistentEnvExtension (Name × Expr) (NameMap Expr) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e ↦ m.insert e.1 e.2
    addImportedFn := fun as ↦ as.foldl (fun m a ↦ a.foldl (fun m e ↦ m.insert e.1 e.2) m) {} }

/-- Rewrites registered by `cost_rewrite`, by the head constant of their left side. -/
initialize rewriteExt : SimplePersistentEnvExtension (Name × Name) (List (Name × Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun l e ↦ l ++ [e]
    addImportedFn := fun as ↦ as.foldl (fun l a ↦ l ++ a.toList) [] }

/-- All rewrites. -/
def allRewrites : MetaM (List (Name × Name)) := do
  return rewrites ++ rewriteExt.getState (← getEnv)

/-- What a data parameter is: an encoded value, or a function of `arity` arguments (the machine
holds a closure, the spec assumes the closure computes the function). -/
inductive ParamKind where
  | enc
  | fn (arity : Nat)
  | type
  /-- A proof: no data, not in the machine's environment. -/
  | proof
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
  /-- The definitions unfolded into the body. -/
  inlined : Array Name := #[]
  /-- A lifted lambda: the closed term compiled. -/
  lam? : Option Expr := none
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
  /-- The type parameters in scope (each with an `Enc` instance in the local context). -/
  types : Array Expr := #[]
  /-- The function's own local context: the callees' premises are created there, outside the
  binders of matches and `let`s. -/
  baseLCtx : LocalContext := {}
  baseInsts : LocalInstances := #[]
  /-- The definitions unfolded so far. -/
  inlined : IO.Ref (Array Name)

/-- The context with `x`'s encoding in front. -/
def Ctx.push (ctx : Ctx) (x : Expr) : MetaM Ctx := do
  let v ← mkAppM ``Enc.enc #[x]
  return { ctx with env := ← mkAppM ``List.cons #[v, ctx.env], vals := #[.enc x] ++ ctx.vals }

/-- The context with a closure `v` of `f` in front. -/
def Ctx.pushFn (ctx : Ctx) (f v hf : Expr) (arity : Nat) : MetaM Ctx := do
  let env ← mkAppM ``List.cons #[v, ctx.env]
  return { ctx with env, vals := #[.fn f v hf arity] ++ ctx.vals }

/-- `Runs P env t v c` in the context's program and environment. -/
def runsAt (ctx : Ctx) (t v c : Expr) : Expr := mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, t, v, c]

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

/-- A callee's premise `Includes P deps`, open until the end, in the function's own context. -/
def Ctx.premise (ctx : Ctx) (deps : Array (Nat × Name)) : MetaM Expr := do
  let ty := mkAppN (mkConst ``Includes) #[ctx.P, ← depsExpr deps]
  let m ← withLCtx ctx.baseLCtx ctx.baseInsts (mkFreshExprMVar ty)
  ctx.pending.modify (·.push (m.mvarId!, deps))
  return m

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

/-- The occurrences of the loose bound variable `i` in `e`. -/
partial def bvarCount (e : Expr) (i : Nat) : Nat :=
  match e with
  | .bvar j => if j == i then 1 else 0
  | .app f a => bvarCount f i + bvarCount a i
  | .lam _ t b _ | .forallE _ t b _ => bvarCount t i + bvarCount b (i + 1)
  | .letE _ t v b _ => bvarCount t i + bvarCount v i + bvarCount b (i + 1)
  | .mdata _ b | .proj _ _ b => bvarCount b i
  | _ => 0

/-- `f` applied to `args`, β-reduced, a compound data argument used more than once bound by a
`let` (definitionally equal: it is evaluated once). -/
partial def betaWithLets (f : Expr) (args : List Expr) (all : List Expr := args) :
    MetaM Expr := do
  match f, args with
  | .lam n t b bi, a :: as =>
    -- an argument another argument mentions (an instance or a proof about it) is substituted
    let mentioned := all.any fun o ↦ o != a && (o.find? (· == a)).isSome
    let simple := a.isFVar || a.isConst || a.isLit || a.isLambda || bvarCount b 0 ≤ 1 ||
      mentioned || (← isProp t) || (← isType a) || (← whnfR t).isForall || (← isClass? t).isSome
    if simple then betaWithLets (b.instantiate1 a) as all
    else
      let _ := bi
      return .letE n t a (← betaWithLets b as all) false
  | f, as => return mkAppN f as.toArray

/-- Every `match` in `e` replaced by its `casesOn` (definitionally equal). -/
def unfoldMatchers (e : Expr) : MetaM Expr := do
  let e ← Meta.transform e (post := fun s ↦ do
    if let .const f _ := s.getAppFn then
      if (← Meta.isMatcher f) && s.getAppNumArgs > 0 then
        if let some s' ← delta? s (· == f) then
          return .visit (← Core.betaReduce s')
    return .done s)
  Core.betaReduce e

/-- `∀ a…, p a…`: `RunsApp P v [enc a…] (enc (f a…))` for a function type `ty`. -/
def runsAppType (P f v ty : Expr) : MetaM Expr :=
  forallTelescopeReducing ty fun as _ ↦ do
    let vs ← as.foldrM (fun a l ↦ do mkAppM ``List.cons #[← mkAppM ``Enc.enc #[a], l])
      (← mkAppOptM ``List.nil #[mkConst ``Val])
    let w ← mkAppM ``Enc.enc #[mkAppN f as]
    mkForallFVars as (mkAppN (mkConst ``RunsApp) #[P, v, vs, w])

/-- The kind of a parameter of type `ty`: a function (not a proof, not a type), or a value. -/
def paramKind (ty : Expr) : MetaM ParamKind := do
  if ← isProp ty then return .proof
  let ty ← whnfR ty
  if ty.isSort then return .type
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
  let e := e.consumeMData.headBeta
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
  -- a literal of `K` or `UInt64`
  if e.isAppOfArity ``OfNat.ofNat 3 && !e.hasFVar then
    let ty ← inferType e
    if ← isDefEq ty (mkConst ``LeanVM.Parameters.K) then
      let pf ← mkAppOptM ``Rule.kLit #[ctx.P, ctx.env, e]
      return ← parts pf
    if ← isDefEq ty (mkConst ``UInt64) then
      let pf ← mkAppOptM ``Rule.wordLit #[ctx.P, ctx.env, e]
      return ← parts pf
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
  -- a constructor, a `casesOn`, a projection of a type encoded as constructors
  if let .const f _ := e.getAppFn then
    let env ← getEnv
    if let some (.ctorInfo ci) := env.find? f then
      if e.getAppNumArgs == ci.numParams + ci.numFields then
        if let some r ← translateCtor ctx ci e then return r
    if isCasesOnRecursor env f then
      if let some r ← translateCases ctx f e then return r
    if isSparseCasesOn env f then
      if let some r ← translateSparse ctx f e then return r
    if let some pinfo ← getProjectionFnInfo? f then
      if e.getAppNumArgs == pinfo.numParams + 1 then
        if let some r ← translateProj ctx pinfo.ctorName pinfo.i (e.getArg! pinfo.numParams) e then
          return r
  -- a method of an instance: the instance's field
  if let .proj _ i s := e.getAppFn then
    let s' ← whnf s
    if let .const c _ := s'.getAppFn then
      if let some (.ctorInfo ci) := (← getEnv).find? c then
        let field := s'.getArg! (ci.numParams + i)
        return ← translate ctx (mkAppN field e.getAppArgs).headBeta
  if let .proj _ i s := e then
    let s' ← whnfCore s
    if let .const c _ := s'.getAppFn then
      if let some (.ctorInfo ci) := (← getEnv).find? c then
        if s'.getAppNumArgs == ci.numParams + ci.numFields then
          return ← translate ctx (s'.getArg! (ci.numParams + i))
  if let .proj sName i s := e then
    let env ← getEnv
    if (getStructureInfo? env sName).isSome then
      let ctorName := (getStructureCtor env sName).name
      if let some r ← translateProj ctx ctorName i s e then return r
  -- a `match`: its `casesOn`
  if let .const f _ := e.getAppFn then
    if (← Meta.isMatcher f) then
      match ← delta? e (· == f) with
      | some e' =>
        let (t, c, p) ← translate ctx (← Core.betaReduce e')
        return (t, c, ← mkExpectedTypeHint p (runsAt ctx t (← mkAppM ``Enc.enc #[e]) c))
      | none => throwError "translate: cannot unfold the match {e}"
  -- a rule
  let fn := e.getAppFn
  if let .const f _ := fn then
    for (key, rule) in rules do
      if key == f then
        if let some r ← tryRule ctx rule e then return r
    -- a rewrite
    for (key, rw) in ← allRewrites do
      if key == f then
        if let some r ← tryRewrite ctx rw e then
          ctx.inlined.modify fun a ↦ if a.contains f then a else a.push f
          return r
    -- a recursive definition: compiled on demand, then called
    if let some cf ← compileOnDemand ctx f e then
      if let some (cf', args) ← findCompiled? e then
        let _ := cf
        return ← translateCall ctx cf' args e
    -- a definition: unfolded (the run stated at `e`, definitionally equal), its compound
    -- arguments used more than once bound by `let`s
    let unfolded? ← match (← getEnv).find? f with
      | some (.defnInfo info) =>
        if e.getAppNumArgs > 0 && info.value.isLambda then
          let v := info.value.instantiateLevelParams info.levelParams fn.constLevels!
          pure (some (← betaWithLets v e.getAppArgs.toList))
        else unfoldDefinition? e
      | _ => unfoldDefinition? e
    if let some e' := unfolded? then
      ctx.inlined.modify fun a ↦ if a.contains f then a else a.push f
      let (t, c, p) ← try translate ctx (← unfoldMatchers e'.headBeta)
        catch ex => throwError "{ex.toMessageData}\n  in the unfolding of {f}"
      return (t, c, ← mkExpectedTypeHint p (runsAt ctx t (← mkAppM ``Enc.enc #[e]) c))
  throwError "translate: no rule for {e} (head {e.getAppFn})"

/-- Unify a rule's value `enc pat` with `enc e`: argument by argument when `pat` and `e` have the
same head constant (so that a `casesOn` is not unfolded first, structure eta turning it into
projections), as a whole otherwise. -/
partial def matchValue (v target : Expr) : MetaM Bool := do
  unless v.isAppOfArity ``Enc.enc 3 && target.isAppOfArity ``Enc.enc 3 do return ← isDefEq v target
  unless ← isDefEq (v.getArg! 0) (target.getArg! 0) do return false
  unless ← isDefEq (v.getArg! 1) (target.getArg! 1) do return false
  let pat ← instantiateMVars (v.getArg! 2)
  let e := target.getArg! 2
  if pat.getAppFn.isConst && pat.getAppFn.constName? == e.getAppFn.constName? &&
      pat.getAppNumArgs == e.getAppNumArgs then
    for (a, b) in pat.getAppArgs.zip e.getAppArgs do
      unless ← withTransparency .instances (isDefEq a b) do return false
    return true
  withTransparency .instances (isDefEq pat e)

/-- `e` translated through the equation `rw : lhs = rhs` whose `lhs` unifies with `e`. -/
partial def tryRewrite (ctx : Ctx) (rw : Name) (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let s ← saveState
  let info ← getConstInfo rw
  let lvls ← info.levelParams.mapM fun _ ↦ mkFreshLevelMVar
  let (args, _, concl) ← forallMetaTelescopeReducing (info.type.instantiateLevelParams info.levelParams lvls)
  let some (_, lhs, rhs) := concl.eq? | throwError "{rw} is not an equation"
  unless ← isDefEq lhs e do
    s.restore
    return none
  -- instance arguments not fixed by unification
  for a in args do
    unless (← a.mvarId!.isAssigned) do
      let aty ← instantiateMVars (← inferType a)
      if (← isClass? aty).isSome then
        a.mvarId!.assign (← synthInstance aty)
  let eqPf ← instantiateMVars (mkAppN (mkConst rw lvls) args)
  if eqPf.hasMVar then
    s.restore
    return none
  let rhs ← instantiateMVars rhs
  let (t, c, pf) ← translate ctx rhs
  let motive ← withLocalDeclD `z (← inferType e) fun z ↦ do
    mkLambdaFVars #[z] (mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, t, ← mkAppM ``Enc.enc #[z], c])
  return some (t, c, ← mkEqMPR (← mkCongrArg motive eqPf) pf)

/-- Whether `enc x` is a constructor of tag `j` (the type's encoding is the constructors'). -/
partial def encodesAsCtor (x : Expr) (j : Nat) : MetaM Bool := do
  try
    let v ← whnfD (← mkAppM ``Enc.enc #[x])
    unless v.isAppOfArity ``Val.ctor 2 do return false
    let tag ← whnfD (← instantiateMVars v.appFn!.appArg!)
    return tag.nat? == some j || tag.rawNatLit? == some j
  catch _ => return false

/-- Which of the fields `fs` hold data (not proofs). -/
partial def dataMask (fs : Array Expr) : MetaM (Array Bool) :=
  fs.mapM fun f ↦ do return !(← isProp (← inferType f))

/-- The list `[enc x₀, …]` of the data fields. -/
partial def encList (xs : Array Expr) : MetaM Expr := do
  xs.foldrM (fun x l ↦ do mkAppM ``List.cons #[← mkAppM ``Enc.enc #[x], l])
    (← mkAppOptM ``List.nil #[mkConst ``Val])

/-- A constructor application: `.ctor j` of its data fields. -/
partial def translateCtor (ctx : Ctx) (ci : ConstructorVal) (e : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  unless ← encodesAsCtor e ci.cidx do return none
  let fields := e.getAppArgs.extract ci.numParams e.getAppNumArgs
  let mask ← dataMask fields
  let dataFs := (fields.zip mask).filterMap fun (f, m) ↦ if m then some f else none
  let (ts, vs, c, pl) ← translateList ctx (dataFs.toList.map .inl)
  let pf := mkAppN (mkConst ``Runs.ctor) #[ctx.P, ctx.env, mkNatLit ci.cidx, ts, vs, c, pl]
  let code := mkApp2 (mkConst ``Term.ctor) (mkNatLit ci.cidx) ts
  let cost ← mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[c, mkNatLit dataFs.size], mkNatLit 1]
  let ty := mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, code, ← mkAppM ``Enc.enc #[e], cost]
  return some (code, cost, ← mkExpectedTypeHint pf ty)

/-- A projection: `.proj k` of the structure's code, `k` the field's position among the data
fields. -/
partial def translateProj (ctx : Ctx) (ctorName : Name) (i : Nat) (s e : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let sTy ← whnf (← inferType s)
  let .const sTyName lvls := sTy.getAppFn | return none
  let ci ← getConstInfoCtor ctorName
  unless sTyName == ci.induct do return none
  let params := sTy.getAppArgs
  let ctorTy ← instantiateForall (← instantiateTypeLevelParams ci.toConstantVal lvls) params
  let fieldsOf ← forallTelescopeReducing ctorTy fun fs _ ↦ dataMask fs
  unless fieldsOf[i]?.getD false do return none
  -- the data fields of `s`, as projections
  let structName := sTy.getAppFn.constName!
  let mut projs := #[]
  let mut k := 0
  for j in [0:fieldsOf.size] do
    if fieldsOf[j]! then
      if j == i then k := projs.size
      projs := projs.push (Expr.proj structName j s)
  unless ← encodesAsCtor (mkAppN (mkAppN (mkConst ctorName lvls) params)
      (← (List.range fieldsOf.size).toArray.mapM fun j ↦ pure (Expr.proj structName j s))) 0 do
    return none
  let (t, c, p) ← translate ctx s
  let fs ← encList projs
  let hCtor ← mkExpectedTypeHint p
    (mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, t, mkApp2 (mkConst ``Val.ctor) (mkNatLit 0) fs, c])
  let v ← mkAppM ``Enc.enc #[e]
  let hi ← mkEqRefl (← mkAppM ``Option.some #[v])
  let pf := mkAppN (mkConst ``Runs.proj) #[ctx.P, ctx.env, mkNatLit k, mkNatLit 0, t, fs, v, c,
    hCtor, hi]
  return some (mkApp2 (mkConst ``Term.proj) (mkNatLit k) t, ← mkAppM ``HAdd.hAdd #[c, mkNatLit 1], pf)

/-- A case split on `major` (of an inductive type encoded as constructors, without indices),
its result of type `β` not depending on the value: `.case` of the branches, each run with the
constructor's data fields in front. `bodyOf j fields` is branch `j`'s Lean expression, `valOf x`
the split's value at `x` (reducing to `bodyOf j fields` at `x = C_j fields`). -/
partial def translateCasesCore (ctx : Ctx) (major : Expr) (bodyOf : Nat → Array Expr → MetaM Expr)
    (valOf : Expr → MetaM Expr) (e : Expr) : MetaM (Option (Expr × Expr × Expr)) := do
  let majTy ← whnf (← inferType major)
  let .const indName lvls := majTy.getAppFn | return none
  let indVal ← getConstInfoInduct indName
  unless indVal.numIndices == 0 do return none
  let params := majTy.getAppArgs
  let nc := indVal.ctors.length
  let casesOn := mkCasesOnName indName
  let (t0, c0, p0) ← translate ctx major
  -- the branches: code, price and proof, abstracted over the fields and `major = C fields`
  let mut alts : Array Expr := #[]
  let mut costLams : Array Expr := #[]
  let mut pfLams : Array Expr := #[]
  for ctorName in indVal.ctors, j in [0:nc] do
    let ctorTy ← instantiateForall (← inferType (mkConst ctorName lvls)) params
    let r ← forallTelescopeReducing ctorTy fun fields _ ↦ do
      let ctorApp := mkAppN (mkAppN (mkConst ctorName lvls) params) fields
      unless ← encodesAsCtor ctorApp j do return none
      let mask ← dataMask fields
      let dataFs := (fields.zip mask).filterMap fun (f, m) ↦ if m then some f else none
      withLocalDeclD `hx (← mkEq major ctorApp) fun hx ↦ do
        let mut ctx' := ctx
        for f in dataFs.reverse do ctx' ← ctx'.push f
        let body ← Core.betaReduce (← bodyOf j fields)
        let (tj, cj, pj) ← translate ctx' body
        if tj.hasFVar then throwError "translate: code depends on a field: {tj}"
        if cj.containsFVar hx.fvarId! then throwError "translate: a price depends on a match"
        return some (tj, ← mkLambdaFVars fields cj, ← mkLambdaFVars (fields.push hx) pj)
    let some (tj, cj, pj) := r | return none
    alts := alts.push tj
    costLams := costLams.push cj
    pfLams := pfLams.push pj
  let altsE ← alts.foldrM (fun a l ↦ mkAppM ``List.cons #[a, l]) (← mkAppOptM ``List.nil #[mkConst ``Term])
  let code := mkApp2 (mkConst ``Term.case) t0 altsE
  let costCases (x : Expr) : MetaM Expr := do
    let m ← withLocalDeclD `x (← inferType major) fun y ↦ mkLambdaFVars #[y] (mkConst ``Nat)
    return mkAppN (mkConst casesOn (Level.one :: lvls)) (params ++ #[m, x] ++ costLams)
  let costOf (x : Expr) : MetaM Expr := do
    mkAppM ``HAdd.hAdd #[← mkAppM ``HAdd.hAdd #[c0, ← costCases x], mkNatLit 1]
  let encOf (x : Expr) : MetaM Expr := do mkAppM ``Enc.enc #[← valOf x]
  -- the proof, by cases on the value
  let pmotive ← withLocalDeclD `x (← inferType major) fun x ↦ do
    mkLambdaFVars #[x] (← mkArrow (← mkEq major x)
      (mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, code, ← encOf x, ← costOf x]))
  let mut minorPfs : Array Expr := #[]
  for ctorName in indVal.ctors, j in [0:nc] do
    let ctorTy ← instantiateForall (← inferType (mkConst ctorName lvls)) params
    let mp ← forallTelescopeReducing ctorTy fun fields _ ↦ do
      let ctorApp := mkAppN (mkAppN (mkConst ctorName lvls) params) fields
      let mask ← dataMask fields
      let dataFs := (fields.zip mask).filterMap fun (f, m) ↦ if m then some f else none
      withLocalDeclD `hx (← mkEq major ctorApp) fun hx ↦ do
        let fs ← encList dataFs
        let rmotive ← withLocalDeclD `z (← inferType major) fun z ↦ do
          mkLambdaFVars #[z] (mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, t0, ← mkAppM ``Enc.enc #[z], c0])
        let h0 ← mkEqNDRec rmotive p0 hx
        let h0 ← mkExpectedTypeHint h0
          (mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, t0, mkApp2 (mkConst ``Val.ctor) (mkNatLit j) fs, c0])
        let ha ← mkEqRefl (← mkAppM ``Option.some #[alts[j]!])
        let pj := pfLams[j]!.beta (fields.push hx)
        let pjTy ← inferType pj
        let some (_, _, _, w, d) := runsParts? pjTy | throwError "alternative: not a run"
        let env' ← mkAppM ``HAppend.hAppend #[fs, ctx.env]
        let pj ← mkExpectedTypeHint pj (mkAppN (mkConst ``Runs) #[ctx.P, env', alts[j]!, w, d])
        let pf := mkAppN (mkConst ``Runs.case) #[ctx.P, ctx.env, t0, altsE, mkNatLit j, fs, alts[j]!,
          w, c0, d, h0, ha, pj]
        mkLambdaFVars (fields.push hx) pf
    minorPfs := minorPfs.push mp
  let pf := mkApp (mkAppN (mkConst casesOn (Level.zero :: lvls)) (params ++ #[pmotive, major] ++ minorPfs))
    (← mkEqRefl major)
  let cost ← costOf major
  let ty := mkAppN (mkConst ``Runs) #[ctx.P, ctx.env, code, ← mkAppM ``Enc.enc #[e], cost]
  return some (code, cost, ← mkExpectedTypeHint pf ty)

/-- A `casesOn` with a constant motive. -/
partial def translateCases (ctx : Ctx) (casesOn : Name) (e : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let indVal ← getConstInfoInduct casesOn.getPrefix
  let np := indVal.numParams
  let nc := indVal.ctors.length
  let args := e.getAppArgs
  unless indVal.numIndices == 0 && args.size == np + 2 + nc do return none
  let motive ← Core.betaReduce args[np]!
  let constMotive ← lambdaTelescope motive fun xs b ↦ pure !(b.hasAnyFVar (xs.contains <| .fvar ·))
  unless constMotive do return none
  let major := args[np + 1]!
  let minors := args.extract (np + 2) (np + 2 + nc)
  translateCasesCore ctx major (fun j fields ↦ pure (mkAppN minors[j]! fields))
    (fun x ↦ pure (mkAppN e.getAppFn (args.set! (np + 1) x))) e

/-- A sparse `casesOn` (arms for some constructors, a catch-all with a proof that the value is
none of them), as a full case split: the catch-all at each other constructor, its proof by
`decide`. -/
partial def translateSparse (ctx : Ctx) (f : Name) (e : Expr) :
    MetaM (Option (Expr × Expr × Expr)) := do
  let some info ← getSparseCasesOnInfo f | return none
  let args := e.getAppArgs
  unless args.size == info.arity do return none
  let major := args[info.majorPos]!
  let indVal ← getConstInfoInduct info.indName
  let np := indVal.numParams
  let motive ← Core.betaReduce args[np]!
  let constMotive ← lambdaTelescope motive fun xs b ↦ pure !(b.hasAnyFVar (xs.contains <| .fvar ·))
  unless constMotive do return none
  let nArms := info.insterestingCtors.size
  -- the catch-all's hypothesis names the value: every occurrence of `major` is replaced, in the
  -- value at `x` and in each branch (where `major` is that constructor)
  let at_ (x : Expr) : Array Expr := args.map fun a ↦ a.replace fun s ↦ if s == major then some x else none
  let bodyOf (j : Nat) (fields : Array Expr) : MetaM Expr := do
    let ctorName := indVal.ctors[j]!
    let majTy ← whnf (← inferType major)
    let ctorApp := mkAppN (mkAppN (mkConst ctorName majTy.getAppFn.constLevels!) majTy.getAppArgs) fields
    let argsC := at_ ctorApp
    let arms := argsC.extract (info.majorPos + 1) (info.majorPos + 1 + nArms)
    let catchAll := argsC[info.majorPos + 1 + nArms]!
    match info.insterestingCtors.idxOf? ctorName with
    | some k => pure (mkAppN arms[k]! fields)
    | none =>
      let hTy ← whnfR (← inferType catchAll)
      let .forallE _ hyp _ _ := hTy | throwError "sparse casesOn: unexpected catch-all {hTy}"
      -- `Nat.hasNotBit mask (C fields).ctorIdx`, unfolded to a decidable equation
      let hyp' ← deltaExpand hyp (· == ``Nat.hasNotBit)
      let pf ← mkExpectedTypeHint (← mkDecideProof hyp') hyp
      pure (mkApp catchAll pf)
  translateCasesCore ctx major bodyOf (fun x ↦ pure (mkAppN e.getAppFn (at_ x))) e

/-- Whether the non-recursive definition `f` (applied in `e` to all its parameters) is compiled to
a function of its own rather than unfolded: a large body (more than `outlineSize` nodes), not an
instance, a projection, a matcher or a reducible definition. -/
partial def shouldOutline (f : Name) (e : Expr) : MetaM Bool := do
  let env ← getEnv
  let some (.defnInfo info) := env.find? f | return false
  if (← isInstance f) || (← getProjectionFnInfo? f).isSome || (← Meta.isMatcher f) then return false
  if (← getReducibilityStatus f) == .reducible then return false
  let arity ← forallTelescopeReducing info.type fun xs _ ↦ pure xs.size
  unless e.getAppNumArgs == arity do return false
  return info.value.approxDepth.toNat > 0 && exprSize info.value > outlineSize
where
  outlineSize : Nat := 120
  exprSize (e : Expr) : Nat := Id.run do
    let mut n := 0
    let mut stack := [e]
    while !stack.isEmpty && n ≤ outlineSize do
      match stack with
      | [] => break
      | x :: rest =>
        stack := rest
        n := n + 1
        match x with
        | .app f a => stack := f :: a :: stack
        | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
        | .letE _ t v b _ => stack := t :: v :: b :: stack
        | .mdata _ b => stack := b :: stack
        | .proj _ _ b => stack := b :: stack
        | _ => pure ()
    return n

/-- Whether `f`'s unfolding mentions `f`. -/
partial def isRecursive (f : Name) : MetaM Bool := do
  let some eqn ← getUnfoldEqnFor? f | return false
  let ty := (← getConstInfo eqn).type
  return (ty.getForallBody.eq?.map fun (_, _, r) ↦ r.containsConst (· == f)).getD false

/-- Compile the recursive `f` of the call `e`: at its types and instances fixed up to its last
instance argument (its types otherwise parameters), with the first measure among the sizes of
its encoded parameters (a natural number itself) that its recursive calls decrease. -/
partial def compileOnDemand (ctx : Ctx) (f : Name) (e : Expr) : MetaM (Option CompiledFn) := do
  let recursive ← isRecursive f
  unless recursive || (← shouldOutline f e) do return none
  let info ← getConstInfo f
  let args := e.getAppArgs
  -- the static prefix: up to the last instance argument
  let bis ← forallTelescopeReducing info.type fun xs _ ↦ xs.mapM fun x ↦ x.fvarId!.getBinderInfo
  let lastInst := (bis.toList.zipIdx.filter (·.1.isInstImplicit)).getLast?.map (·.2 + 1) |>.getD 0
  let static := args.extract 0 lastInst
  if static.any (·.hasFVar) then throwError "compile {f}: its types or instances are not closed"
  let term := mkAppN e.getAppFn static
  let ty ← inferType term
  let measures ← forallTelescopeReducing ty fun xs _ ↦ do
    let mut out := #[]
    for (x, j) in xs.zipIdx do
      let k ← paramKind (← inferType x)
      if k == .enc then
        let xty ← whnfR (← inferType x)
        let m ← if ← isDefEq xty (mkConst ``Nat) then pure x
          else if xty.isAppOf ``List then mkAppM ``List.length #[x]
          else if xty.isAppOf ``Array then mkAppM ``Array.size #[x]
          else mkAppM ``SizeOf.sizeOf #[x]
        out := out.push (← mkLambdaFVars xs m)
        let _ := j
    return out
  -- a registered measure first
  let measures ← match (measureExt.getState (← getEnv)).find? f with
    | some mReg => do
      let m ← forallTelescopeReducing ty fun xs _ ↦ do
        mkLambdaFVars xs (← Core.betaReduce (mkAppN mReg (static ++ xs)))
      pure (#[m] ++ measures)
    | none => pure measures
  let name := (`LeanVM.Cost.Auto ++ f).str s!"c{← nextIndex ctx.reserved}"
  unless recursive do
    let idx ← nextIndex ctx.reserved
    return some (← withLCtx {} {} (compileFn name term idx none ctx.reserved))
  let mut errs : Array MessageData := #[]
  for m in measures do
    let st ← saveState
    try
      let idx ← nextIndex ctx.reserved
      return some (← withLCtx {} {} (compileFn name term idx (some m) ctx.reserved))
    catch ex =>
      st.restore
      errs := errs.push ex.toMessageData
  throwError "compile {f}: no measure its recursive calls decrease: {errs}"

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
      unless capFvs.contains (.fvar x) || ctx.types.contains (.fvar x) do
        throwError "closure: free variable {Expr.fvar x} of {f} is not in the environment"
    let lam ← instantiateMVars (← mkLambdaFVars (ctx.types ++ capFvs ++ ps) body)
    -- the same lambda compiled before: reused
    let reg := compiledExt.getState (← getEnv)
    let prior := reg.foldl (fun acc _ fs ↦ acc <|> fs.find? (·.lam? == some lam)) none
    let cf ← match prior with
      | some cf => pure cf
      | none => do
        let k ← ctx.lams.modifyGet fun n ↦ (n, n + 1)
        let name := ctx.base.str s!"lam{k}"
        let idx ← nextIndex ctx.reserved
        withLCtx {} {} (compileFn name lam idx none ctx.reserved)
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
    let hInc ← ctx.premise cf.deps
    let mut specArgs := #[ctx.P, hInc]
    for ty in ctx.types do
      specArgs := specArgs ++ #[ty, ← synthInstance (← mkAppM ``Enc #[ty])]
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
    | .type =>
      specArgs := specArgs ++ #[a, ← synthInstance (← mkAppM ``Enc #[a])]
    | .proof => specArgs := specArgs.push a
  let (_, _, _, pl) ← translateList ctx items.toList
  let hInc ← ctx.premise cf.deps
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
    | .type =>
      unless a == x do throwError "a recursive call changes the type argument {x}"
    | .proof => throwError "a recursive function with a proof parameter {x}: not supported"
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
  unless (← isDefEq P ctx.P) && (← isDefEq env ctx.env) && (← matchValue v target) do
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
  let t ← instantiateMVars t
  let c ← instantiateMVars c
  -- the callees' `Includes` premises stay open until the end; nothing else may
  if t.hasMVar || c.hasMVar then
    s.restore
    throwError "translate: rule {rule} left the code or the price open: {t}, {c}"
  return some (t, c, pf)

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
      unless ← isDefEq t t' do throwError "premise: code mismatch {t} vs {t'}"
      unless ← isDefEq c c' do throwError "premise: price mismatch {c} vs {c'}"
      g.assign (← mkLambdaFVars xs p')
      return true
    | none =>
      let some (_, a, _) := body.eq? | return false
      try
        g.assign (← mkLambdaFVars xs (← mkEqRefl a))
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
    let fnInfo := (xs.zip kinds).filterMap fun (x, k) ↦ match k with
      | .fn _ => some x
      | _ => none
    let typeXs := (xs.zip kinds).filterMap fun (x, k) ↦ if k == .type then some x else none
    withEncInsts typeXs #[] fun insts ↦ do
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
    let inlined ← IO.mkRef #[]
    let mut ctx : Ctx := { P := P, env := env0, vals := #[], pending := pending, base := name,
                           lams := lams, reserved := reserved.push idx, types := typeXs, inlined,
                           baseLCtx := ← getLCtx, baseInsts := ← getLocalInstances }
    for (x, k) in (xs.zip kinds).reverse do
      match k with
      | .enc => ctx ← ctx.push x
      | .fn arity =>
        let some (_, v, hf) := fnHyps.find? (·.1 == x) | throwError "no closure for {x}"
        ctx ← ctx.pushFn x v hf arity
      | .type | .proof => pure ()
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
        | .type | .proof => pure ()
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
        | _ => args := args.push x
      mkLambdaFVars #[y] (← mkAppM ``Enc.enc #[← Core.betaReduce (mkAppN term args)])
    let runsBodyAt (y : Expr) : MetaM Expr := do
      let args ← Core.betaReduce (argsF.beta #[y])
      return mkAppN (mkConst ``RunsBody) #[P, mkNatLit idx, args, valF.beta #[y],
        mkAppN (mkConst ``machineCost) #[P, mkNatLit idx, args]]
    let x ← mkTuple encXs
    let mf? ← measure?.mapM fun m ↦ withLocalDeclD `y tupleTy fun y ↦ do
      -- the measure takes every parameter; the encoded ones from the tuple
      let comps ← tupleComponents y encXs.size
      let mut j := 0
      let mut args := #[]
      for (x, k) in xs.zip kinds do
        if k == .enc then
          args := args.push comps[j]!
          j := j + 1
        else args := args.push x
      mkLambdaFVars #[y] (← Core.betaReduce (m.beta args))
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
      let depsTy ← mkAppM ``List #[← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Term]]
      addAndCompile <| .defnDecl (mkDefinitionValEx (name.str "costDeps") [] depsTy depsE .abbrev .safe [])
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
          | .type =>
            let some (_, inst) := insts.find? (·.1 == x) | throwError "no instance for {x}"
            binders := binders ++ #[x, inst]
          | .proof => binders := binders.push x
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
        let specBody ← if ih?.isSome then cleanTuples (← runsBodyAt x) else
          -- stated at the parameters themselves (a proof parameter may depend on them)
          pure (mkAppN (mkConst ``RunsBody) #[P, mkNatLit idx, ctx.env, ← mkAppM ``Enc.enc #[lhs],
            mkAppN (mkConst ``machineCost) #[P, mkNatLit idx, ctx.env]])
        let specTy ← instantiateMVars (← mkForallFVars binders specBody)
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
            body := bodyName, spec := specName, deps := deps, inlined := ← inlined.get,
            lam? := if term.isLambda then some term else none }
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

/-- Local `Enc` instances for the type parameters `ts`. -/
partial def withEncInsts {α : Type} (ts : Array Expr) (acc : Array (Expr × Expr))
    (k : Array (Expr × Expr) → MetaM α) : MetaM α := do
  if h : acc.size < ts.size then
    let t := ts[acc.size]
    withLocalDecl `inst .instImplicit (← mkAppM ``Enc #[t]) fun i ↦
      withEncInsts ts (acc.push (t, i)) k
  else k acc

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

/-- `cost_compile name [at i] [measure m] := term`: compile `term` (a function: a constant applied
to its fixed arguments, such as types and instances) to the body of function `i` (the next free
index by default), and add `name.costBody` (the code), `name.costSpec` (the run on every argument,
at the machine's price, in every program holding the bodies it needs) and `name.costEq` (the
price's recurrence). A recursive term needs a measure of its encoded parameters that its recursive
calls decrease; its function parameters stay fixed. -/
syntax (name := costCompile) "cost_compile " ident (" at " num)? (&" measure " term)? " := " term :
  command

@[command_elab costCompile] def elabCostCompile : Command.CommandElab := fun stx ↦
  Command.liftTermElabM do
    let name := (Lean.TSyntax.getId ⟨stx[1]⟩ : Name)
    let name := (← getCurrNamespace) ++ name
    let term ← Term.elabTerm stx[5] none
    Term.synthesizeSyntheticMVarsNoPostponing
    let term ← instantiateMVars term
    let idx ← if stx[2].isNone then nextIndex else pure (TSyntax.getNat ⟨stx[2][1]⟩)
    let measure? ← if stx[3].isNone then pure none else do
      let ty ← inferType term
      -- the measure takes the encoded parameters
      let mty ← forallTelescopeReducing ty fun xs _ ↦ do
        let t ← mkForallFVars xs (mkConst ``Nat)
        -- every binder explicit: the measure names all its parameters
        let rec explicit : Expr → Expr
          | .forallE n d b _ => .forallE n d (explicit b) .default
          | e => e
        pure (explicit t)
      let m ← Term.elabTerm stx[3][1] (some mty)
      Term.synthesizeSyntheticMVarsNoPostponing
      pure (some (← instantiateMVars m))
    discard <| compileFn name term idx measure?

/-- `cost_measure f := m`: the measure (of all `f`'s parameters) that `f`'s recursive calls
decrease, used when `f` is compiled on demand. -/
syntax (name := costMeasure) "cost_measure " ident " := " term : command

@[command_elab costMeasure] def elabCostMeasure : Command.CommandElab := fun stx ↦
  Command.liftTermElabM do
    let f ← realizeGlobalConstNoOverloadWithInfo (⟨stx[1]⟩ : Ident)
    let info ← getConstInfo f
    let mty ← forallTelescopeReducing info.type fun xs _ ↦ do
      let t ← mkForallFVars xs (mkConst ``Nat)
      let rec explicit : Expr → Expr
        | .forallE n d b _ => .forallE n d (explicit b) .default
        | e => e
      pure (explicit t)
    let mty := mty.instantiateLevelParams info.levelParams (info.levelParams.map fun _ ↦ Level.zero)
    let m ← Term.elabTerm stx[3] (some mty)
    Term.synthesizeSyntheticMVarsNoPostponing
    let m ← instantiateMVars m
    modifyEnv (measureExt.addEntry · (f, m))

/-- `cost_rewrite thm`: compile the left side of the equation `thm` through its right side. -/
elab "cost_rewrite " id:ident : command => Command.liftTermElabM do
  let thm ← realizeGlobalConstNoOverloadWithInfo id
  let ty := (← getConstInfo thm).type
  let key ← forallTelescopeReducing ty fun _ b ↦ do
    let some (_, l, _) := b.eq? | throwError "{thm} is not an equation"
    let some k := l.getAppFn.constName? | throwError "{thm}: the left side has no head constant"
    pure k
  modifyEnv (rewriteExt.addEntry · (key, thm))

/-- `#cost_stats f`: the functions `f`'s spec needs, each with the lines of its code (printed at
width 100) and of its Lean source (lifted lambdas: part of their parent's source), and the totals:
the measure of the gate G2. -/
elab "#cost_stats " id:ident : command => Command.liftTermElabM do
  let depsName ← realizeGlobalConstNoOverloadWithInfo (mkIdent (id.getId.str "costDeps"))
  let mut l := (← getConstInfo depsName).value!
  let reg := compiledExt.getState (← getEnv)
  let mut rows : Array MessageData := #[]
  let mut codeTotal := 0
  let mut srcTotal := 0
  let mut inlinedAll : Array Name := #[]
  while l.isAppOfArity ``List.cons 3 do
    let pair := l.appFn!.appArg!
    let some body := pair.appArg!.constName? | throwError "not a body constant: {pair}"
    let code := (← getConstInfo body).value!
    let codeLines := ((← ppExpr code).pretty 100).splitOn "\n" |>.length
    let entry := reg.foldl (fun acc _ fs ↦ acc <|> fs.find? (·.body == body)) none
    let head := (entry.map (·.head)).getD body
    for n in (entry.map (·.inlined)).getD #[] do
      unless inlinedAll.contains n do inlinedAll := inlinedAll.push n
    let srcLines ← match ← findDeclarationRanges? head with
      | some r => pure (r.range.endPos.line - r.range.pos.line + 1)
      | none => pure 0
    codeTotal := codeTotal + codeLines
    srcTotal := srcTotal + srcLines
    rows := rows.push m!"{head}: code {codeLines}, source {srcLines}"
    l := l.appArg!
  let mut inl : Array MessageData := #[]
  let mut inlTotal := 0
  for n in inlinedAll do
    if let some r ← findDeclarationRanges? n then
      let k := r.range.endPos.line - r.range.pos.line + 1
      inlTotal := inlTotal + k
      inl := inl.push m!"{n} {k}"
  logInfo m!"{MessageData.joinSep rows.toList "\n"}\ninlined: {MessageData.joinSep inl.toList ", "}\n\
    total: code {codeTotal}, source {srcTotal} compiled + {inlTotal} inlined"

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
      let inlined ← IO.mkRef #[]
      let mut ctx : Ctx := { P := P, env := env0, vals := #[], pending := pending,
                             base := `translate, lams := lams, inlined }
      for x in xs.reverse do
        ctx ← ctx.push x
      let (t, c, pf) ← translate ctx body
      check pf
      logInfo m!"code: {t}\nprice: {c}"

end LeanVM.Cost.Compiler
