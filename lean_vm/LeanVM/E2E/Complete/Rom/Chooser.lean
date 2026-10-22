/-
  LeanVM.E2E.Complete.Rom.Chooser

  T6-prob: the honest prover's choice of a node's execution, made from the answers of the node's
  log alone (H-oblivious), and transported to every hash agreeing with the log.
-/

module

public import LeanVM.E2E.Complete.Count.Final
public import LeanVM.Protocol.Compile.Rom.Log

/-!
# The node's execution, between hashes agreeing on its strings

`docs/roadmap/t6-prob.md` §1.2, §3. The honest table's semantics `chainSem I H` reads `H` only
at the strings `D` (`ChainRow`), so two hashes agreeing on `D` give one semantics
(`chainSem_congr`), and a node's execution (`NodeExec`) whose strings are `D` is one for either
hash (`NodeExec.transport`). So the honest prover chooses it from a log `L` of answers alone
(`execOf L pi w`, in `NodeExecOn` of `L`'s strings at the hash `fillLog L`), and at every hash
agreeing with `L` the choice is an execution of that hash (`execOf_exec`). At the node's log
(`logOf H (nodeLog H s w)`), the choice exists (`execOf_isSome`): L2 (`guestCompleteModel`) at the
honest table of the node's strings, whose count is L17 (`nodeLog_count_lt`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Compile
open LeanVM.Protocol.Verifier LeanVM.Protocol.Blake2sHash LeanVM.Node LeanVM.Guest
open LeanVM.Protocol.Compile.Rom LeanVM.Protocol.Rom LeanVM.Arithmetization

@[expose] public section

/-- Two `BLAKE2S` semantics with one relation are one semantics (decidability is a
subsingleton). -/
theorem BlakeSem.ext_check {S S' : BlakeSem} (h : S.check = S'.check) : S = S' := by
  obtain ⟨c, d⟩ := S
  obtain ⟨c', d'⟩ := S'
  cases h
  congr
  funext m cv0 cv1 out0 out1 md
  exact Subsingleton.elim _ _

/-- **The honest table reads the hash only on its strings.** -/
theorem chainSem_congr {D : List Bytes} (I : Intermediates D) {H H' : Bytes → Digest}
    (h : ∀ x ∈ D, H x = H' x) : chainSem I H = chainSem I H' := by
  refine BlakeSem.ext_check ?_
  funext m cv0 cv1 out0 out1 md
  refine propext (and_congr_right fun _ ↦ ?_)
  unfold ChainRow
  constructor <;> rintro ⟨x, hx, hr⟩ <;> refine ⟨x, hx, ?_⟩ <;> simpa [h x hx] using hr

/-- **A node's execution transports** to every hash agreeing on its strings. -/
noncomputable def NodeExec.transport {H H' : Bytes → Digest} {pi : Digest} {w : NodeWitness}
    (e : NodeExec H pi w) (h : ∀ x ∈ e.D, H x = H' x) : NodeExec H' pi w where
  D := e.D
  I := e.I
  t := e.t
  fr := e.fr
  sz := e.sz
  q := e.q
  valid := by
    have hv := e.valid
    change ValidExecutionB (chainSem e.I H) _ _ _ at hv
    change ValidExecutionB (chainSem e.I H') _ _ _
    rwa [← chainSem_congr e.I h]
  decode := e.decode
  adm := e.adm
  rel := e.rel
  run := e.run


/-! ## Logs of answers -/

/-- The log of the strings `D` answered by `H`. -/
def logOf (H : Bytes → Digest) (D : List Bytes) : Log := D.map fun x ↦ (x, H x)

/-- The hash a log answers, `0` off it. -/
def fillLog (L : Log) (x : Bytes) : Digest := (look L x).getD 0

theorem look_logOf (H : Bytes → Digest) :
    ∀ (D : List Bytes) {x : Bytes}, x ∈ D → look (logOf H D) x = some (H x)
  | [], _, hx => absurd hx (by simp)
  | y :: D, x, hx => by
    simp only [logOf, List.map_cons, look, logLookup_cons]
    by_cases hy : y = x
    · subst hy; simp
    · simp only [hy, ↓reduceIte]
      exact look_logOf H D (List.mem_of_ne_of_mem (Ne.symm hy) hx)

theorem strings_logOf (H : Bytes → Digest) (D : List Bytes) : (logOf H D).map Prod.fst = D := by
  simp [logOf, Function.comp_def]

/-- A hash agrees with a log where the log answers. -/
def Agrees (L : Log) (H : Bytes → Digest) : Prop := ∀ x u, look L x = some u → H x = u

theorem agrees_logOf (H : Bytes → Digest) (D : List Bytes) : Agrees (logOf H D) H := by
  intro x u hu
  have hx : x ∈ D := by
    by_contra hx
    have : look (logOf H D) x = none := by
      rw [look, logLookup_eq_none_iff, strings_logOf]; exact hx
    rw [this] at hu; cases hu
  rw [look_logOf H D hx] at hu
  exact Option.some.inj hu

/-- On the log's strings the filled hash is every agreeing hash. -/
theorem fillLog_eq {L : Log} {H : Bytes → Digest} (h : Agrees L H) {x : Bytes}
    (hx : x ∈ L.map Prod.fst) : fillLog L x = H x := by
  cases hl : look L x with
  | none =>
    rw [look, logLookup_eq_none_iff] at hl
    exact absurd hx hl
  | some u => simp only [fillLog, hl, Option.getD_some, h x u hl]

/-! ## The oblivious choice -/

/-- **A node's execution on exactly the strings `D`.** -/
def NodeExecOn (D : List Bytes) (H : Bytes → Digest) (pi : Digest) (w : NodeWitness) : Type :=
  {e : NodeExec H pi w // e.D = D}

open Classical in
/-- **The oblivious execution**: an execution on the log's strings at the hash the log answers,
if any; a function of the log alone. -/
noncomputable def execOf (L : Log) (pi : Digest) (w : NodeWitness) :
    Option (NodeExecOn (L.map Prod.fst) (fillLog L) pi w) :=
  if h : Nonempty (NodeExecOn (L.map Prod.fst) (fillLog L) pi w) then some (Classical.choice h)
  else none

/-- **The choice is an execution of every hash agreeing with the log.** -/
noncomputable def NodeExecOn.at {L : Log} {pi : Digest} {w : NodeWitness}
    (e : NodeExecOn (L.map Prod.fst) (fillLog L) pi w) {H : Bytes → Digest} (h : Agrees L H) :
    NodeExec H pi w :=
  e.1.transport fun _ hx ↦ fillLog_eq h (e.2 ▸ hx)

@[simp] theorem NodeExecOn.at_sz {L : Log} {pi : Digest} {w : NodeWitness}
    (e : NodeExecOn (L.map Prod.fst) (fillLog L) pi w) {H : Bytes → Digest} (h : Agrees L H) :
    (e.at h).sz = e.1.sz := rfl

@[simp] theorem NodeExecOn.at_fr {L : Log} {pi : Digest} {w : NodeWitness}
    (e : NodeExecOn (L.map Prod.fst) (fillLog L) pi w) {H : Bytes → Digest} (h : Agrees L H) :
    (e.at h).fr = e.1.fr := rfl

/-- The stack is the choice's; its type depends on the sizes only. -/
theorem NodeExecOn.at_q {L : Log} {pi : Digest} {w : NodeWitness}
    (e : NodeExecOn (L.map Prod.fst) (fillLog L) pi w) {H : Bytes → Digest} (h : Agrees L H) :
    (e.at h).q = e.1.q := rfl

/-- **A node has an execution on its own log's strings** (L2 at the honest table of `nodeLog`,
its count L17). -/
theorem nodeExec_nodeLog (H : Bytes → Digest) {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) :
    Nonempty (NodeExecOn (nodeLog H s w) H (digestOf H s) w) := by
  have hD := nodeLog_count_lt hlim hrel
  have hpi : statementDigestWith (answeredOn (nodeLog H s w) H) (seedOf H) s =
      some (digestOf H s) := by
    rw [statementDigestWith_answeredOn _ _ fun x hx ↦ by
      simp only [nodeLog, nodeLogWith, List.mem_append]
      exact .inl (.inl (.inl (.inl (.inl (.inl hx)))))]
    exact statementDigestWith_someH H s
  have hrel' := nodeRelWith_answeredOn (D := nodeLog H s w) (fun _ hx ↦ hx) hrel
  let I := intermediatesOf (nodeLog H s w) hD
  obtain ⟨t, fr, hv, hsize, hdec⟩ := guestCompleteModel (CompModel.chain I H) H
    (fun _ _ h ↦ (answeredOn_some h).2) (seedOf H) s w (digestOf H s) hpi hrel' hlim hcaps hbud
  obtain ⟨sz, q, hadm, hrel'', hpad, hrun⟩ :=
    exists_stack_of_validB chainSem_le_free hv hsize
  exact ⟨⟨⟨nodeLog H s w, I, t, fr, sz, q, hv, hdec, hadm, ⟨hrel'', hpad⟩, hrun⟩, rfl⟩⟩

/-- **The oblivious choice exists at the node's log.** -/
theorem execOf_isSome (H : Bytes → Digest) {s : NodeStatement} {w : NodeWitness}
    (hrel : NodeRelWith (fun x ↦ some (H x)) B1.Main.aggSeedD B1.Main.daPadCell B1.Main.daPadRow
      End.bytecode (seedOf H) s w) (hlim : End.Limits s w) (hcaps : CapsAgreeWith H (seedOf H) w)
    (hbud : B2C.b2cBudget'.size (End.work s w) ≤ 2 ^ 28) :
    (execOf (logOf H (nodeLog H s w)) (digestOf H s) w).isSome := by
  obtain ⟨e⟩ := nodeExec_nodeLog H hrel hlim hcaps hbud
  have hag := agrees_logOf H (nodeLog H s w)
  have hne : Nonempty (NodeExecOn ((logOf H (nodeLog H s w)).map Prod.fst)
      (fillLog (logOf H (nodeLog H s w))) (digestOf H s) w) := by
    rw [strings_logOf]
    exact ⟨⟨e.1.transport fun _ hx ↦ (fillLog_eq hag (by rw [strings_logOf]; exact e.2 ▸ hx)).symm,
      e.2⟩⟩
  simp [execOf, hne]

end
end LeanVM.E2E.Complete
