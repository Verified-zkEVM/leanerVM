/-
  LeanVM.E2E.Rel

  The monotonicity of V_I's `Option` runs in the lookup, from the relation of V_I's runs in two
  monads (`LeanVM.E2E.Natural`), and the relational lemmas for the parts of V_I the end theorems
  read.
-/

module

public import LeanVM.E2E.Natural

/-!
# V_I's `Option` runs are monotone in the lookup

`LeanVM.E2E.Natural` relates V_I's runs in two monads (`rel_idealVerify`): a relation closed under
`pure` and `bind` and relating the two hashes' queries relates the runs. Here the same for the
parts T4 reads off an accepting run (`rel_treeRootM`, `rel_verifyBlindWith`,
`rel_fiatShamirIvWith`, `rel_statementDigestWith`), and the main `Option` instance.

**Monotonicity** (`idealVerify_mono` and the lemmas for V_I's parts). The `Option` runs of a
computation answered by a lookup `H` are answered by every lookup `H'` extending it
(`LookSub H H'`: every answer of `H` is one of `H'`), with the same result: the relation "if the
first run returns `some a`, so does the second" is closed. The table check's semantic form is
monotone too (`TableOK.mono`).
-/

namespace LeanVM.E2E

open LeanVM.Parameters LeanVM.Semantics LeanVM.Node LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile.Rom

@[expose] public section

/-! ## The relational closure, for V_I's parts the end theorems read -/

section Rel

variable {m m' : Type → Type} [Monad m] [Monad m'] [LawfulMonad m] [LawfulMonad m']
  (R : ∀ {α : Type}, m α → m' α → Prop)
  (hpure : ∀ {α : Type} (a : α), R (pure a) (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (x' : m' α) (f : α → m β) (f' : α → m' β), R x x' →
    (∀ a, R (f a) (f' a)) → R (x >>= f) (x' >>= f'))
  (H : Bytes → m Digest) (H' : Bytes → m' Digest) (hH : ∀ x, R (H x) (H' x))
include hpure hbind hH

/-- A closed relation holds of two Merkle roots of a word. -/
theorem rel_treeRootM (height : ℕ) (word : Word) :
    R (treeRootM H height word) (treeRootM H' height word) :=
  hbind _ _ _ _ (rel_mapM R hpure hbind _ _ (fun _ ↦ hH _) _) fun _ ↦
    rel_rootOfLevelM R hpure hbind H H' hH _ _

omit [LawfulMonad m] [LawfulMonad m'] in
/-- A closed relation holds of two runs of the Flock-blind verifier V°. -/
theorem rel_verifyBlindWith (bytecode : List K) (pi : Digest) (π : Proof) :
    R (verifyBlindWith H bytecode pi π) (verifyBlindWith H' bytecode pi π) := by
  unfold verifyBlindWith seedWith
  exact hbind _ _ _ _ (hbind _ _ _ _ (hH _) fun _ ↦ hbind _ _ _ _ (hH _) fun _ ↦ hH _)
    fun _ ↦ rel_runProof R hpure hbind H H' hH _ _ _

omit [LawfulMonad m] [LawfulMonad m'] hpure in
/-- A closed relation holds of two runs of the Fiat-Shamir IV. -/
theorem rel_fiatShamirIvWith (bytecode : List K) :
    R (fiatShamirIvWith H bytecode) (fiatShamirIvWith H' bytecode) :=
  hbind _ _ _ _ (hH _) fun _ ↦ hH _

omit [LawfulMonad m] [LawfulMonad m'] hpure in
/-- A closed relation holds of two runs of a statement digest. -/
theorem rel_statementDigestWith (seed : Digest) (s : NodeStatement) :
    R (statementDigestWith H seed s) (statementDigestWith H' seed s) :=
  hbind _ _ _ _ (hbind _ _ _ _ (hH _) fun _ ↦ hbind _ _ _ _ (hH _) fun _ ↦ hH _) fun _ ↦
    hbind _ _ _ _ (hH _) fun _ ↦ hH _

end Rel

/-! ## Monotonicity in the lookup -/

/-- **`H'` extends `H`**: every answer of `H` is one of `H'`. -/
def LookSub (H H' : Bytes → Option Digest) : Prop := ∀ x d, H x = some d → H' x = some d

/-- `LookSub` is reflexive. -/
theorem LookSub.refl (H : Bytes → Option Digest) : LookSub H H := fun _ _ h ↦ h

/-- `LookSub` is transitive. -/
theorem LookSub.trans {H H' H'' : Bytes → Option Digest} (h₁ : LookSub H H') (h₂ : LookSub H' H'') :
    LookSub H H'' := fun x d h ↦ h₂ x d (h₁ x d h)

/-- A log's lookup is extended by the lookup of every log it is a prefix of. -/
theorem lookSub_of_prefix {ℓ ℓ' : Log} (h : ℓ <+: ℓ') : LookSub (look ℓ) (look ℓ') :=
  fun _ _ hx ↦ look_of_prefix h hx

/-- The relation of two `Option` runs: if the first returns `some a`, so does the second. -/
def OptLE {α : Type} (x x' : Option α) : Prop := ∀ a, x = some a → x' = some a

/-- `OptLE` holds of `pure`. -/
theorem optLE_pure {α : Type} (a : α) : OptLE (pure a : Option α) (pure a) := fun _ h ↦ h

/-- `OptLE` is closed under `bind`. -/
theorem optLE_bind {α β : Type} (x x' : Option α) (f : α → Option β) (f' : α → Option β)
    (hx : OptLE x x') (hf : ∀ a, OptLE (f a) (f' a)) : OptLE (x >>= f) (x' >>= f') := by
  intro b h
  obtain ⟨a, ha, hb⟩ := Option.bind_eq_some_iff.mp h
  exact Option.bind_eq_some_iff.mpr ⟨a, hx a ha, hf a b hb⟩

section Mono

variable {H H' : Bytes → Option Digest} (h : LookSub H H')
include h

/-- An answered query is answered alike by an extension. -/
theorem optLE_of_lookSub (x : Bytes) : OptLE (H x) (H' x) := fun d hd ↦ h x d hd

/-- **V_I's `Option` run is monotone in the lookup.** -/
theorem idealVerify_mono {prog : Program} {ip : IdealProof} {fuel : ℕ} {s : NodeStatement} {b : Bool}
    (hv : idealVerify H prog ip fuel s = some b) : idealVerify H' prog ip fuel s = some b :=
  rel_idealVerify (fun x x' ↦ OptLE x x') optLE_pure optLE_bind H H' (optLE_of_lookSub h)
    prog ip fuel s b hv

/-- One node's `Option` run is monotone in the lookup. -/
theorem nodeStep_mono {prog : Program} {seed : Digest} {ip : IdealProof} {ν : Node}
    {o : Option (List Node)} (hv : nodeStep H prog seed ip ν = some o) :
    nodeStep H' prog seed ip ν = some o :=
  rel_nodeStep (fun x x' ↦ OptLE x x') optLE_pure optLE_bind H H' (optLE_of_lookSub h)
    prog seed ip ν o hv

/-- A Merkle root's `Option` run is monotone in the lookup. -/
theorem treeRootM_mono {ht : ℕ} {W : Word} {root : Digest} (hv : treeRootM H ht W = some root) :
    treeRootM H' ht W = some root :=
  rel_treeRootM (fun x x' ↦ OptLE x x') optLE_pure optLE_bind H H' (optLE_of_lookSub h) ht W
    root hv

/-- V°'s `Option` run is monotone in the lookup. -/
theorem verifyBlindWith_mono {bytecode : List K} {pi : Digest} {π : Proof} {b : Bool}
    (hv : verifyBlindWith H bytecode pi π = some b) : verifyBlindWith H' bytecode pi π = some b :=
  rel_verifyBlindWith (fun x x' ↦ OptLE x x') optLE_pure optLE_bind H H' (optLE_of_lookSub h)
    bytecode pi π b hv

/-- The Fiat-Shamir IV's `Option` run is monotone in the lookup. -/
theorem fiatShamirIvWith_mono {bytecode : List K} {seed : Digest}
    (hv : fiatShamirIvWith H bytecode = some seed) : fiatShamirIvWith H' bytecode = some seed :=
  rel_fiatShamirIvWith (fun x x' ↦ OptLE x x') optLE_bind H H' (optLE_of_lookSub h)
    bytecode seed hv

/-- A statement digest's `Option` run is monotone in the lookup. -/
theorem statementDigestWith_mono {seed pi : Digest} {s : NodeStatement}
    (hv : statementDigestWith H seed s = some pi) : statementDigestWith H' seed s = some pi :=
  rel_statementDigestWith (fun x x' ↦ OptLE x x') optLE_bind H H'
    (optLE_of_lookSub h) seed s pi hv

/-- The outer checks' `Option` run is monotone in the lookup. -/
theorem outerChecksWith_mono {prog : Program} {s : NodeStatement} {b : Bool}
    (hv : outerChecksWith H prog s = some b) : outerChecksWith H' prog s = some b :=
  rel_outerChecksWith (fun x x' ↦ OptLE x x') optLE_pure optLE_bind H H' (optLE_of_lookSub h)
    prog s b hv

/-- The table check's `Option` run is monotone in the lookup. -/
theorem tableOKWith_mono {rows : List BlakeRow} {b : Bool} (hv : tableOKWith H rows = some b) :
    tableOKWith H' rows = some b :=
  rel_tableOKWith (fun x x' ↦ OptLE x x') optLE_pure optLE_bind H H' (optLE_of_lookSub h) rows
    b hv

/-- **The table check is monotone in the lookup**: a table whose chains end at answers of `H`
ends them at answers of every extension. -/
theorem TableOK.mono {rows : List BlakeRow} (hok : TableOK H rows) : TableOK H' rows :=
  fun x c hc hrows hs ↦ h _ _ (hok x c hc hrows hs)

end Mono

end
end LeanVM.E2E
