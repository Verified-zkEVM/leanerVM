/-
  LeanVM.E2E.Complete.NodeLog

  The strings a node's checks hash (L17's support): the checks run in a logging monad give a
  list `nodeLog H s w`; answered by `H` on that list alone, the statement's digest and the node
  relation hold as they hold with every string answered.
-/

module

public import LeanVM.E2E.Complete.NonVacuity
public import LeanVM.E2E.Runs
public import LeanVM.E2E.Rel

/-!
# The node's hashed strings

`NodeSupport H s w` (L17, `NonVacuity.lean`) asks for a list `D` of strings with fewer than
`2^64` block prefixes on which, answered by `H`, the node's checks hold as they hold with every
string answered. Here `D` is built: every check is written with its hash a parameter in any
monad (`…With`), so it runs in the **logging monad** `LogM` (a log of the strings hashed and the
value), with `LogM.hash H x = ⟨[x], H x⟩`. `nodeLog H s w` is the concatenated log of the
statement's digest, every child's digest and deferring verifier, every held signature's
verification and DA opening, the children's claims, and the batching.

The relation `Logs P a b` ("if every logged string satisfies `P`, the `Option` run `b` returns
`a`'s value") is closed under `pure` and `bind` and holds of the hash queries when `H'` answers
every string of `P` with `H`. By the relational lemmas of `LeanVM.E2E.Natural` and
`LeanVM.E2E.Rel` and those added here (`rel_simulateQ`, the DA commitment, the batching over a
state), it holds of every check, at `P := True, H' := some ∘ H` and at `P := (· ∈ D),
H' := answeredOn D H`. So with the log within `D` the two runs agree
(`statementDigestWith_answeredOn`, `nodeRelWith_answeredOn`), and the count of the log's block
prefixes is all `NodeSupport` still asks (`nodeSupport_of_count`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest

@[expose] public section

/-! ## The logging monad -/

/-- **A logged computation**: the strings hashed, in order, and the value. -/
structure LogM (α : Type) where
  /-- The strings hashed. -/
  log : List Bytes
  /-- The value. -/
  val : α

namespace LogM

instance : Monad LogM where
  pure a := ⟨[], a⟩
  bind x f := ⟨x.log ++ (f x.val).log, (f x.val).val⟩

instance : LawfulMonad LogM := LawfulMonad.mk'
  (id_map := fun ⟨l, a⟩ ↦ by
    show (⟨l ++ [], a⟩ : LogM _) = ⟨l, a⟩
    rw [List.append_nil])
  (pure_bind := fun _ _ ↦ rfl)
  (bind_assoc := fun _ _ _ ↦ by
    show (⟨_ ++ _ ++ _, _⟩ : LogM _) = ⟨_ ++ (_ ++ _), _⟩
    rw [List.append_assoc]
    rfl)

/-- **The logged hash**: `x` logged, answered by `H`. -/
def hash (H : Bytes → Digest) (x : Bytes) : LogM Digest := ⟨[x], H x⟩

end LogM

/-! ## The relation of a logged run and an `Option` run -/

/-- **`b` answers what `a` logs**: if every string `a` logs satisfies `P`, the `Option` run `b`
returns `a`'s value. -/
def Logs (P : Bytes → Prop) {α : Type} (a : LogM α) (b : Option α) : Prop :=
  (∀ x ∈ a.log, P x) → b = some a.val

theorem logs_pure (P : Bytes → Prop) {α : Type} (a : α) : Logs P (pure a) (pure a) :=
  fun _ ↦ rfl

theorem logs_bind (P : Bytes → Prop) {α β : Type} (x : LogM α) (y : Option α) (f : α → LogM β)
    (g : α → Option β) (hx : Logs P x y) (hf : ∀ a, Logs P (f a) (g a)) :
    Logs P (x >>= f) (y >>= g) := by
  intro h
  have h1 : ∀ z ∈ x.log, P z := fun z hz ↦ h z (List.mem_append_left _ hz)
  have h2 : ∀ z ∈ (f x.val).log, P z := fun z hz ↦ h z (List.mem_append_right _ hz)
  rw [hx h1]
  exact hf _ h2

/-- The logged hash and an `Option` hash answering every string of `P` with `H`. -/
theorem logs_hash (P : Bytes → Prop) (H : Bytes → Digest) (H' : Bytes → Option Digest)
    (hP : ∀ x, P x → H' x = some (H x)) (x : Bytes) : Logs P (LogM.hash H x) (H' x) :=
  fun h ↦ hP x (h x (List.mem_singleton.mpr rfl))

/-- `answeredOn D H` answers every string of `D` with `H`. -/
theorem answeredOn_of_mem {D : List Bytes} {H : Bytes → Digest} {x : Bytes} (hx : x ∈ D) :
    answeredOn D H x = some (H x) := by
  unfold answeredOn
  simp only [hx, ↓reduceIte]

/-- **Transfer**: a check whose logged run is within `D` returns, answered on `D`, what it
returns with every string answered. -/
theorem logs_transfer {α : Type} {D : List Bytes} {a : LogM α} {b b' : Option α} {v : α}
    (hfull : Logs (fun _ ↦ True) a b) (hD : Logs (· ∈ D) a b') (hsub : ∀ x ∈ a.log, x ∈ D)
    (hb : b = some v) : b' = some v := by
  have h1 := hfull fun _ _ ↦ trivial
  rw [hb, Option.some.injEq] at h1
  rw [hD hsub, h1]

/-! ## Relational lemmas for the remaining checks -/

section Rel

variable {m n : Type → Type} [Monad m] [Monad n] [LawfulMonad m] [LawfulMonad n]
  (R : ∀ {α : Type}, m α → n α → Prop)
  (hpure : ∀ {α : Type} (a : α), R (pure a) (pure a))
  (hbind : ∀ {α β : Type} (x : m α) (y : n α) (f : α → m β) (g : α → n β), R x y →
    (∀ a, R (f a) (g a)) → R (x >>= f) (y >>= g))
include hpure hbind

/-- A closed relation relates two simulations of a free computation by related oracles. -/
theorem rel_simulateQ {ι : Type} {spec : OracleSpec.{0, 0} ι} (impl : QueryImpl spec m)
    (impl' : QueryImpl spec n) (hq : ∀ t, R (impl t) (impl' t)) {α : Type} :
    ∀ oa : OracleComp spec α, R (simulateQ impl oa) (simulateQ impl' oa) := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
    simp only [simulateQ_pure]
    exact hpure x
  | query_bind t k ih =>
    simp only [simulateQ_bind, simulateQ_spec_query]
    exact hbind _ _ _ _ (hq t) ih

variable (H : Bytes → m Digest) (H' : Bytes → n Digest) (hH : ∀ x, R (H x) (H' x))
include hH

/-- A closed relation relates two leanXMSS verifications with related hashes. -/
theorem rel_xmssVerifyWith (pk : LeanXmss.PublicKey) (msg : LeanXmss.Message)
    (σ : LeanXmss.Signature) : R (xmssVerifyWith H pk msg σ) (xmssVerifyWith H' pk msg σ) := by
  rw [xmssVerifyWith_eq_simulateQ, xmssVerifyWith_eq_simulateQ]
  exact rel_simulateQ R hpure hbind _ _ (fun t ↦ rel_map R hpure hbind _ _ _ (hH t)) _

/-- A closed relation relates two leanSPHINCS verifications with related hashes. -/
theorem rel_sphincsVerifyWith (pk : _root_.Sphincs.PublicKey) (msg : _root_.Sphincs.Message)
    (σ : _root_.Sphincs.Signature) :
    R (sphincsVerifyWith H pk msg σ) (sphincsVerifyWith H' pk msg σ) := by
  rw [sphincsVerifyWith_eq_simulateQ, sphincsVerifyWith_eq_simulateQ]
  exact rel_simulateQ R hpure hbind _ _ (fun t ↦ rel_map R hpure hbind _ _ _ (hH t)) _

omit [LawfulMonad m] [LawfulMonad n] in
/-- A closed relation relates two deferring verifications with related hashes. -/
theorem rel_verifyDeferredWith (bytecode : List K) (iv pi : Digest) (c : FixedClaims)
    (π : Proof) :
    R (verifyDeferredWith H bytecode iv pi c π) (verifyDeferredWith H' bytecode iv pi c π) :=
  hbind _ _ _ _ (hH _) fun _ ↦ rel_runProof R hpure hbind H H' hH _ _ _

omit hH

/-- A closed relation relates two levels of a DA tree with related hashes. -/
theorem rel_treeLevelWith (HD : List UInt8 → m LeanDa.Digest) (HD' : List UInt8 → n LeanDa.Digest)
    (hHD : ∀ x, R (HD x) (HD' x)) (nodes : List LeanDa.Digest) :
    R (Da.treeLevelWith HD nodes) (Da.treeLevelWith HD' nodes) :=
  rel_mapM R hpure hbind _ _ (fun _ ↦ hHD _) _

/-- A closed relation relates two DA tree roots with related hashes. -/
theorem rel_treeRootFuel (HD : List UInt8 → m LeanDa.Digest) (HD' : List UInt8 → n LeanDa.Digest)
    (hHD : ∀ x, R (HD x) (HD' x)) :
    ∀ (fuel : ℕ) (nodes : List LeanDa.Digest),
      R (Da.treeRootFuel HD fuel nodes) (Da.treeRootFuel HD' fuel nodes)
  | 0, _ => hpure _
  | fuel + 1, nodes => by
    simp only [Da.treeRootFuel]
    split
    · exact hpure _
    · exact hbind _ _ _ _ (rel_treeLevelWith R hpure hbind HD HD' hHD nodes) fun _ ↦
        rel_treeRootFuel HD HD' hHD fuel _

/-- A closed relation relates two DA row digests with related hashes. -/
theorem rel_rowDigestWith (HD : List UInt8 → m LeanDa.Digest) (HD' : List UInt8 → n LeanDa.Digest)
    (hHD : ∀ x, R (HD x) (HD' x)) (row : List K) :
    R (Da.rowDigestWith HD row) (Da.rowDigestWith HD' row) :=
  hbind _ _ _ _ (rel_mapM R hpure hbind _ _ (fun _ ↦ hHD _) _) fun _ ↦ hHD _

/-- A closed relation relates two DA commitments with related hashes. -/
theorem rel_commitCodewordsWith (HD : List UInt8 → m LeanDa.Digest)
    (HD' : List UInt8 → n LeanDa.Digest) (hHD : ∀ x, R (HD x) (HD' x)) (pc pr : LeanDa.Digest)
    (rows : List (List K)) :
    R (Da.commitCodewordsWith HD pc pr rows) (Da.commitCodewordsWith HD' pc pr rows) := by
  unfold Da.commitCodewordsWith
  refine hbind _ _ _ _ (rel_mapM R hpure hbind _ _
    (rel_rowDigestWith R hpure hbind HD HD' hHD) _) fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_treeRootFuel R hpure hbind HD HD' hHD _ _) fun _ ↦ ?_
  refine hbind _ _ _ _ (rel_mapM R hpure hbind _ _ (fun ij ↦ ?_) _) fun _ ↦ ?_
  · split
    · exact hHD _
    · exact hpure _
  · exact hbind _ _ _ _ (rel_treeRootFuel R hpure hbind HD HD' hHD _ _) fun _ ↦ hHD _

/-! ### Over a state -/

/-- The relation lifted to computations over a state: related from every state. -/
def RelS {σ α : Type} (x : StateT σ m α) (y : StateT σ n α) : Prop := ∀ s, R (x.run s) (y.run s)

omit [LawfulMonad m] [LawfulMonad n] hbind in
theorem relS_pure {σ α : Type} (a : α) : RelS R (pure a : StateT σ m α) (pure a) :=
  fun s ↦ hpure (a, s)

omit [LawfulMonad m] [LawfulMonad n] hpure in
theorem relS_bind {σ α β : Type} (x : StateT σ m α) (y : StateT σ n α) (f : α → StateT σ m β)
    (g : α → StateT σ n β) (hx : RelS R x y) (hf : ∀ a, RelS R (f a) (g a)) :
    RelS R (x >>= f) (y >>= g) := fun s ↦ by
  simp only [StateT.run_bind]
  exact hbind _ _ _ _ (hx s) fun p ↦ hf p.1 p.2

include hH

/-- Two observations with related hashes. -/
theorem relS_observeWith (x : E) : RelS R (observeWith (m := m) H x) (observeWith (m := n) H' x) := fun s ↦ by
  simp only [observeWith, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_set, Functor.map_map]
  exact rel_map R hpure hbind _ _ _ (hH _)

/-- Two squeezes with related hashes. -/
theorem relS_squeezeWith : RelS R (squeezeWith (m := m) H) (squeezeWith (m := n) H') := fun s ↦ by
  simp only [squeezeWith, bind_pure_comp, StateT.run_bind, StateT.run_get, pure_bind,
    StateT.run_monadLift, monadLift_self, StateT.run_set, StateT.run_map, map_pure,
    Functor.map_map]
  exact rel_map R hpure hbind _ _ _ (hH _)

/-- Two batching sumchecks with related hashes. -/
theorem relS_batchRoundsWith : ∀ (claim : E) (rounds : List (E × E)),
    RelS R (batchRoundsWith (m := m) H claim rounds) (batchRoundsWith (m := n) H' claim rounds)
  | _, [] => relS_pure R hpure _
  | claim, (g1, gInf) :: rest => by
    simp only [batchRoundsWith]
    repeat' first
      | exact relS_pure R hpure _
      | exact relS_observeWith R hpure hbind H H' hH _
      | exact relS_squeezeWith R hpure hbind H H' hH
      | exact relS_batchRoundsWith _ _
      | (refine relS_bind R hbind _ _ _ _ ?_ fun ⟨_, _⟩ ↦ ?_)
      | (refine relS_bind R hbind _ _ _ _ ?_ fun _ ↦ ?_)

/-- **Two batchings with related hashes.** -/
theorem rel_batchWith (s0 : Digest) (children : List ChildClaims) (h : BatchHints) :
    R (batchWith H s0 children h) (batchWith H' s0 children h) := by
  unfold batchWith
  refine rel_map R hpure hbind _ _ _ ?_
  unfold batchWith.go
  revert s0
  show RelS R _ _
  repeat' first
    | exact relS_pure R hpure _
    | exact relS_observeWith R hpure hbind H H' hH _
    | exact relS_squeezeWith R hpure hbind H H' hH
    | exact relS_batchRoundsWith R hpure hbind H H' hH _ _
    | (refine rel_forIn (fun x y ↦ RelS R x y) (fun a ↦ relS_pure R hpure a)
        (relS_bind R hbind) _ _ (fun _ _ ↦ ?_) _ _)
    | (refine relS_bind R hbind _ _ _ _ ?_ fun ⟨_, _⟩ ↦ ?_)
    | (refine relS_bind R hbind _ _ _ _ ?_ fun _ ↦ ?_)
    | split
    | dsimp only

end Rel

/-! ## The node's log -/

section Log

variable (H : Bytes → Digest)

/-- `childClaimsWith` in any monad. -/
def childClaimsM {m : Type → Type} [Monad m] (H : Bytes → m Digest) (seed : Digest)
    (children : List Child) : m (List ChildClaims) :=
  children.mapM fun c ↦ (fun pi ↦ ⟨pi, c.fresh, c.statement.defer⟩) <$>
    statementDigestWith H seed c.statement

/-- The strings a child's checks hash: its statement's digest and its deferring verifier. -/
def childLog (bytecode : List K) (seed : Digest) (c : Child) : List Bytes :=
  (statementDigestWith (LogM.hash H) seed c.statement).log ++
    (verifyDeferredWith (LogM.hash H) bytecode seed
      (statementDigestWith (LogM.hash H) seed c.statement).val c.fresh c.proof).log

/-- The strings a holder's check hashes: `f` of the claim and the witness, if held directly. -/
def holderLog {α W : Type} (f : α → W → List Bytes) (a : α) : Holder W → List Bytes
  | .direct w => f a w
  | .child _ => []

/-- The strings the holders' checks hash: `f` of every claim held directly. -/
def holdersLog {α W : Type} (f : α → W → List Bytes) (claims : List α) (hs : List (Holder W)) :
    List Bytes :=
  (List.zipWith (holderLog f) claims hs).flatten

/-- The strings a DA opening hashes: the commitment and the vector digest. -/
def daLog (pc pr : LeanDa.Digest) (w : Da.Witness) : List Bytes :=
  (Da.commitCodewordsWith (Da.daHash (LogM.hash H)) pc pr w.rows).log ++
    (Da.vectorDigestWith (Da.daHash (LogM.hash H)) w.vector).log

/-- **The strings a node's checks hash**, at the batching's chain state `s0`, the DA padding
digests `pc`, `pr`, the bytecode and the seed: the statement's digest, the children's digests
and deferring verifiers, the signatures' verifications, the DA openings, the children's claims
and the batching. -/
def nodeLogWith (s0 : Digest) (pc pr : LeanDa.Digest) (bytecode : List K) (seed : Digest)
    (s : NodeStatement) (w : NodeWitness) : List Bytes :=
  (statementDigestWith (LogM.hash H) seed s).log ++ w.children.flatMap (childLog H bytecode seed) ++
    holdersLog (fun c σ ↦ (xmssVerifyWith (LogM.hash H) c.1 c.2 σ).log) s.claims.xmss w.xmss ++
    holdersLog (fun c σ ↦ (sphincsVerifyWith (LogM.hash H) c.1 c.2 σ).log) s.claims.sphincs
      w.sphincs ++
    holdersLog (fun (_ : DaClaim) ↦ daLog H pc pr) s.claims.da w.da ++
    (childClaimsM (LogM.hash H) seed w.children).log ++
    (batchWith (LogM.hash H) s0 (childClaimsM (LogM.hash H) seed w.children).val w.hints).log

/-- **The strings a node's checks hash**, at the deployed parameters `NodeSupport` reads. -/
noncomputable def nodeLog (s : NodeStatement) (w : NodeWitness) : List Bytes :=
  nodeLogWith H B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow End.bytecode (seedOf H) s w

end Log

/-! ## Answered on the log -/

section Answered

variable {H : Bytes → Digest} {P : Bytes → Prop} {H' : Bytes → Option Digest}
  (hP : ∀ x, P x → H' x = some (H x))
include hP

theorem logs_hashH (x : Bytes) : Logs P (LogM.hash H x) (H' x) := logs_hash P H H' hP x

theorem logs_statementDigestWith (seed : Digest) (s : NodeStatement) :
    Logs P (statementDigestWith (LogM.hash H) seed s) (statementDigestWith H' seed s) :=
  rel_statementDigestWith (fun x y ↦ Logs P x y) (logs_bind P) _ _ (logs_hashH hP) seed s

theorem logs_verifyDeferredWith (bytecode : List K) (iv pi : Digest) (c : FixedClaims)
    (π : Proof) :
    Logs P (verifyDeferredWith (LogM.hash H) bytecode iv pi c π)
      (verifyDeferredWith H' bytecode iv pi c π) :=
  rel_verifyDeferredWith (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _ (logs_hashH hP)
    bytecode iv pi c π

theorem logs_xmssVerifyWith (pk : LeanXmss.PublicKey) (msg : LeanXmss.Message)
    (σ : LeanXmss.Signature) :
    Logs P (xmssVerifyWith (LogM.hash H) pk msg σ) (xmssVerifyWith H' pk msg σ) :=
  rel_xmssVerifyWith (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _ (logs_hashH hP)
    pk msg σ

theorem logs_sphincsVerifyWith (pk : _root_.Sphincs.PublicKey) (msg : _root_.Sphincs.Message)
    (σ : _root_.Sphincs.Signature) :
    Logs P (sphincsVerifyWith (LogM.hash H) pk msg σ) (sphincsVerifyWith H' pk msg σ) :=
  rel_sphincsVerifyWith (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _ (logs_hashH hP)
    pk msg σ

theorem logs_daHash (x : List UInt8) : Logs P (Da.daHash (LogM.hash H) x) (Da.daHash H' x) :=
  rel_map (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _ _ (logs_hashH hP x)

theorem logs_commitCodewordsWith (pc pr : LeanDa.Digest) (rows : List (List K)) :
    Logs P (Da.commitCodewordsWith (Da.daHash (LogM.hash H)) pc pr rows)
      (Da.commitCodewordsWith (Da.daHash H') pc pr rows) :=
  rel_commitCodewordsWith (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _
    (logs_daHash hP) pc pr rows

theorem logs_vectorDigestWith (v : List E) :
    Logs P (Da.vectorDigestWith (Da.daHash (LogM.hash H)) v) (Da.vectorDigestWith (Da.daHash H') v) :=
  logs_daHash hP _

theorem logs_childClaimsM (seed : Digest) (children : List Child) :
    Logs P (childClaimsM (LogM.hash H) seed children) (childClaimsWith H' seed children) :=
  rel_mapM (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _
    (fun _ ↦ rel_map (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _ _
      (logs_statementDigestWith hP _ _)) children

theorem logs_batchWith (s0 : Digest) (cs : List ChildClaims) (h : BatchHints) :
    Logs P (batchWith (LogM.hash H) s0 cs h) (batchWith H' s0 cs h) :=
  rel_batchWith (fun x y ↦ Logs P x y) (logs_pure P) (logs_bind P) _ _ (logs_hashH hP) s0 cs h

end Answered

/-! ## The node's checks, answered on the log -/

section Main

variable {H : Bytes → Digest} {D : List Bytes}

theorem full_answers : ∀ x, (fun _ ↦ True) x → (fun x ↦ some (H x)) x = some (H x) :=
  fun _ _ ↦ rfl

theorem on_answers : ∀ x, (· ∈ D) x → answeredOn D H x = some (H x) :=
  fun _ hx ↦ answeredOn_of_mem hx

theorem all_true (l : List Bytes) : ∀ x ∈ l, (fun _ ↦ True) x := fun _ _ ↦ trivial

/-- Holders' checks within `D` transfer. -/
theorem forall₂_holdersLog {α W : Type} {f : α → W → List Bytes} {Q Q' : α → Holder W → Prop}
    (himp : ∀ a h, Q a h → (∀ x ∈ holderLog f a h, x ∈ D) → Q' a h) :
    ∀ {as : List α} {hs : List (Holder W)}, List.Forall₂ Q as hs →
      (∀ x ∈ holdersLog f as hs, x ∈ D) → List.Forall₂ Q' as hs
  | _, _, .nil, _ => .nil
  | a :: _, h :: _, .cons hq hrest, hD => by
    simp only [holdersLog, List.zipWith_cons_cons, List.flatten_cons, List.mem_append] at hD
    exact .cons (himp a h hq fun x hx ↦ hD x (Or.inl hx))
      (forall₂_holdersLog himp hrest fun x hx ↦ hD x (Or.inr (by simpa only [holdersLog] using hx)))

/-- **The statement's digest, answered on its log**, is the digest with every string answered. -/
theorem statementDigestWith_answeredOn (seed : Digest) (s : NodeStatement)
    (hD : ∀ x ∈ (statementDigestWith (LogM.hash H) seed s).log, x ∈ D) :
    statementDigestWith (answeredOn D H) seed s =
      statementDigestWith (fun x ↦ some (H x)) seed s := by
  rw [logs_statementDigestWith full_answers seed s (all_true _)]
  exact logs_statementDigestWith on_answers seed s hD

/-- **The node relation, answered on the node's log**, holds when it holds with every string
answered. -/
theorem nodeRelWith_answeredOn {s0 : Digest} {pc pr : LeanDa.Digest} {bytecode : List K}
    {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hD : ∀ x ∈ nodeLogWith H s0 pc pr bytecode seed s w, x ∈ D)
    (h : NodeRelWith (fun x ↦ some (H x)) s0 pc pr bytecode seed s w) :
    NodeRelWith (answeredOn D H) s0 pc pr bytecode seed s w := by
  obtain ⟨hsh, hch, hx, hs, hda, hb⟩ := h
  simp only [nodeLogWith, List.mem_append] at hD
  refine ⟨hsh, fun c hc ↦ ?_, ?_, ?_, ?_, ?_⟩
  · obtain ⟨hcs, pi, hpi, hv⟩ := hch c hc
    have hcl : ∀ x ∈ childLog H bytecode seed c, x ∈ D := fun x hx ↦
      hD x (.inl (.inl (.inl (.inl (.inl (.inr (List.mem_flatMap.mpr ⟨c, hc, hx⟩)))))))
    simp only [childLog, List.mem_append] at hcl
    rw [logs_statementDigestWith full_answers seed c.statement (all_true _),
      Option.some.injEq] at hpi
    subst hpi
    exact ⟨hcs, _, logs_statementDigestWith on_answers _ _ fun x hx ↦ hcl x (Or.inl hx),
      logs_transfer (logs_verifyDeferredWith full_answers _ _ _ _ _)
        (logs_verifyDeferredWith on_answers _ _ _ _ _) (fun x hx ↦ hcl x (Or.inr hx)) hv⟩
  · refine forall₂_holdersLog (fun a h hq hsub ↦ ?_) hx fun x hx ↦
      hD x (.inl (.inl (.inl (.inl (.inr hx)))))
    cases h with
    | direct σ =>
      exact logs_transfer (logs_xmssVerifyWith full_answers _ _ _)
        (logs_xmssVerifyWith on_answers _ _ _) hsub hq
    | child i => exact hq
  · refine forall₂_holdersLog (fun a h hq hsub ↦ ?_) hs fun x hx ↦
      hD x (.inl (.inl (.inl (.inr hx))))
    cases h with
    | direct σ =>
      exact logs_transfer (logs_sphincsVerifyWith full_answers _ _ _)
        (logs_sphincsVerifyWith on_answers _ _ _) hsub hq
    | child i => exact hq
  · refine forall₂_holdersLog (fun a h hq hsub ↦ ?_) hda fun x hx ↦
      hD x (.inl (.inl (.inr hx)))
    cases h with
    | direct dw =>
      obtain ⟨h1, h2, h3, hc, h5, hv, h7⟩ := hq
      simp only [holderLog, daLog, List.mem_append] at hsub
      exact ⟨h1, h2, h3, logs_transfer (logs_commitCodewordsWith full_answers _ _ _)
        (logs_commitCodewordsWith on_answers _ _ _) (fun x hx ↦ hsub x (Or.inl hx)) hc, h5,
        logs_transfer (logs_vectorDigestWith full_answers _) (logs_vectorDigestWith on_answers _)
          (fun x hx ↦ hsub x (Or.inr hx)) hv, h7⟩
    | child i => exact hq
  · by_cases hc : w.children = []
    · simp only [hc, ↓reduceIte] at hb ⊢
      exact hb
    · simp only [hc, ↓reduceIte] at hb ⊢
      obtain ⟨cs, hcs, hbt⟩ := hb
      rw [logs_childClaimsM full_answers seed w.children (all_true _), Option.some.injEq] at hcs
      subst hcs
      exact ⟨_, logs_childClaimsM on_answers _ _ fun x hx ↦ hD x (.inl (.inr hx)),
        logs_transfer (logs_batchWith full_answers _ _ _) (logs_batchWith on_answers _ _ _)
          (fun x hx ↦ hD x (.inr hx)) hbt⟩

/-- **L17's support, from the count**: when the node's log has fewer than `2^64` block
prefixes, it supports the statement's digest and the node relation. -/
theorem nodeSupport_of_count {s : NodeStatement} {w : NodeWitness}
    (h : (prefixesOf (nodeLog H s w)).length < 2 ^ 64) : NodeSupport H s w := by
  refine ⟨nodeLog H s w, h, ?_, nodeRelWith_answeredOn fun _ hx ↦ hx⟩
  rw [statementDigestWith_answeredOn _ _ fun x hx ↦ by
    simp only [nodeLog, nodeLogWith, List.mem_append]
    exact .inl (.inl (.inl (.inl (.inl (.inl hx)))))]
  exact statementDigestWith_someH H s

end Main

end
end LeanVM.E2E.Complete
