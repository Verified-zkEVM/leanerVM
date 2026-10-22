/-
  LeanVM.E2E.Complete.Count.Basic

  Counting the block prefixes of logged strings (L17): only strings longer than one block have
  any, the count adds up along a logged computation, and a scheme's run logs at most its query
  bound times the blocks of its longest query.
-/

module

public import LeanVM.E2E.Complete.NodeLog

/-!
# The count of a log's block prefixes

`NodeSupport` (L17) asks `(prefixesOf D).length < 2^64` of the node's log `D = nodeLog H s w`.
`prefixesOf D` has `nBlocks x = (|x| − 1)/64` entries per string `x` of `D`, so:

* `prefixCount D := (prefixesOf D).length` adds up over appends (`prefixCount_append`) and a string
  of at most `64` bytes adds nothing (`nBlocks_eq_zero_of_length_le`): every Fiat–Shamir step,
  Merkle node and batching step hashes exactly `64` bytes;
* along a logged computation (`LogM`) the count of a `bind` is the sum (`LogM.bind_log`), of a
  `mapM` the sum over the list (`prefixCount_mapM_le`);
* `LogShort x`: every string `x` logs is at most `64` bytes, so its count is `0`; closed under
  `pure`, `bind`, `map`, `mapM`, and over a state (`LogShortS`);
* a scheme's computation `oa : OracleComp (Bytes →ₒ β) α` with at most `n` queries
  (`IsTotalQueryBound`), each of at most `c` blocks (`AllQueriesSatisfy`), logs at most `n * c`
  prefixes when its queries are answered by the logged hash (`prefixCount_simulateQ_le`).
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash OracleSpec OracleComp

@[expose] public section

/-! ## The count -/

/-- **The count of block prefixes** of the strings `D`: what `NodeSupport` bounds. -/
def prefixCount (D : List Bytes) : ℕ := (prefixesOf D).length

theorem prefixCount_nil : prefixCount [] = 0 := rfl

theorem prefixCount_cons (x : Bytes) (D : List Bytes) :
    prefixCount (x :: D) = nBlocks x + prefixCount D := by
  simp [prefixCount, prefixesOf]

theorem prefixCount_singleton (x : Bytes) : prefixCount [x] = nBlocks x := by
  rw [prefixCount_cons, prefixCount_nil, Nat.add_zero]

theorem prefixCount_append (A B : List Bytes) :
    prefixCount (A ++ B) = prefixCount A + prefixCount B := by
  simp [prefixCount, prefixesOf, List.flatMap_append]

/-- The count of a flattening, bounded string by string. -/
theorem prefixCount_flatMap_le {α : Type} (f : α → List Bytes) (g : α → ℕ) :
    ∀ l : List α, (∀ a ∈ l, prefixCount (f a) ≤ g a) →
      prefixCount (l.flatMap f) ≤ (l.map g).sum
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    rw [List.flatMap_cons, prefixCount_append, List.map_cons, List.sum_cons]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (prefixCount_flatMap_le f g l fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- The count of a flattening, each part bounded by `c`. -/
theorem prefixCount_flatMap_le_mul {α : Type} (f : α → List Bytes) (c : ℕ) (l : List α)
    (h : ∀ a ∈ l, prefixCount (f a) ≤ c) : prefixCount (l.flatMap f) ≤ l.length * c := by
  have := prefixCount_flatMap_le f (fun _ ↦ c) l h
  rwa [List.map_const', List.sum_replicate, smul_eq_mul] at this

/-- A string of at most `64 (k + 1)` bytes has at most `k` block prefixes. -/
theorem nBlocks_le_of_length_le {x : Bytes} {k : ℕ} (h : x.length ≤ 64 * (k + 1)) :
    nBlocks x ≤ k := by
  unfold nBlocks
  omega

/-- **A string of at most one block has no block prefix.** -/
theorem nBlocks_eq_zero_of_length_le {x : Bytes} (h : x.length ≤ 64) : nBlocks x = 0 := by
  unfold nBlocks
  omega

/-- The count of strings of at most one block is `0`. -/
theorem prefixCount_eq_zero_of_short {D : List Bytes} (h : ∀ x ∈ D, x.length ≤ 64) :
    prefixCount D = 0 := by
  induction D with
  | nil => rfl
  | cons x D ih =>
    rw [prefixCount_cons, nBlocks_eq_zero_of_length_le (h x List.mem_cons_self),
      ih fun y hy ↦ h y (List.mem_cons_of_mem _ hy)]

/-! ## Along a logged computation -/

namespace LogM

variable {α β : Type}

theorem pure_log (a : α) : (pure a : LogM α).log = [] := rfl

theorem pure_val (a : α) : (pure a : LogM α).val = a := rfl

theorem bind_log (x : LogM α) (f : α → LogM β) : (x >>= f).log = x.log ++ (f x.val).log := rfl

theorem bind_val (x : LogM α) (f : α → LogM β) : (x >>= f).val = (f x.val).val := rfl

theorem map_log (f : α → β) (x : LogM α) : (f <$> x).log = x.log := by
  show (x >>= fun a ↦ pure (f a)).log = x.log
  rw [bind_log, pure_log, List.append_nil]

theorem map_val (f : α → β) (x : LogM α) : (f <$> x).val = f x.val := rfl

theorem hash_log (H : Bytes → Digest) (x : Bytes) : (hash H x).log = [x] := rfl

theorem hash_val (H : Bytes → Digest) (x : Bytes) : (hash H x).val = H x := rfl

end LogM

/-- The count of a `bind`. -/
theorem prefixCount_bind {α β : Type} (x : LogM α) (f : α → LogM β) :
    prefixCount (x >>= f).log = prefixCount x.log + prefixCount (f x.val).log := by
  rw [LogM.bind_log, prefixCount_append]

/-- The count of a logged hash. -/
theorem prefixCount_hash (H : Bytes → Digest) (x : Bytes) :
    prefixCount (LogM.hash H x).log = nBlocks x := by
  rw [LogM.hash_log, prefixCount_singleton]

/-- **The count of a `mapM`**, bounded element by element. -/
theorem prefixCount_mapM_le {α β : Type} (f : α → LogM β) (g : α → ℕ) :
    ∀ l : List α, (∀ a ∈ l, prefixCount (f a).log ≤ g a) →
      prefixCount (l.mapM f).log ≤ (l.map g).sum
  | [], _ => Nat.zero_le _
  | a :: l, h => by
    rw [List.mapM_cons, prefixCount_bind, prefixCount_bind, List.map_cons, List.sum_cons]
    simp only [LogM.pure_log, prefixCount_nil, Nat.add_zero]
    exact Nat.add_le_add (h a List.mem_cons_self)
      (prefixCount_mapM_le f g l fun b hb ↦ h b (List.mem_cons_of_mem _ hb))

/-- The count of a `mapM`, each element bounded by `c`. -/
theorem prefixCount_mapM_le_mul {α β : Type} (f : α → LogM β) (c : ℕ) (l : List α)
    (h : ∀ a ∈ l, prefixCount (f a).log ≤ c) : prefixCount (l.mapM f).log ≤ l.length * c := by
  have := prefixCount_mapM_le f (fun _ ↦ c) l h
  rwa [List.map_const', List.sum_replicate, smul_eq_mul] at this

/-! ## Short logs -/

/-- **Every string `x` logs is at most one block.** -/
def LogShort {α : Type} (x : LogM α) : Prop := ∀ s ∈ x.log, s.length ≤ 64

namespace LogShort

variable {α β : Type}

/-- A short log has no block prefix. -/
theorem prefixCount_eq {x : LogM α} (h : LogShort x) : prefixCount x.log = 0 :=
  prefixCount_eq_zero_of_short h

theorem pure (a : α) : LogShort (Pure.pure a : LogM α) := fun _ h ↦ nomatch h

theorem bind {x : LogM α} {f : α → LogM β} (hx : LogShort x) (hf : ∀ a, LogShort (f a)) :
    LogShort (x >>= f) := by
  intro s hs
  rw [LogM.bind_log, List.mem_append] at hs
  exact hs.elim (hx s) (hf _ s)

theorem map (f : α → β) {x : LogM α} (hx : LogShort x) : LogShort (f <$> x) := by
  intro s hs
  rw [LogM.map_log] at hs
  exact hx s hs

theorem hash (H : Bytes → Digest) {x : Bytes} (hx : x.length ≤ 64) :
    LogShort (LogM.hash H x) := by
  intro s hs
  rw [LogM.hash_log, List.mem_singleton] at hs
  exact hs ▸ hx

theorem mapM (f : α → LogM β) : ∀ (l : List α), (∀ a ∈ l, LogShort (f a)) →
    LogShort (l.mapM f)
  | [], _ => pure _
  | a :: l, h => by
    rw [List.mapM_cons]
    exact bind (h a List.mem_cons_self) fun _ ↦
      bind (mapM f l fun b hb ↦ h b (List.mem_cons_of_mem _ hb)) fun _ ↦ pure _

end LogShort

/-- **Every string a computation over a state logs, from every state, is at most one block.** -/
def LogShortS {σ α : Type} (x : StateT σ LogM α) : Prop := ∀ s, LogShort (x.run s)

namespace LogShortS

variable {σ α β : Type}

theorem pure (a : α) : LogShortS (Pure.pure a : StateT σ LogM α) := fun _ ↦ LogShort.pure _

theorem bind {x : StateT σ LogM α} {f : α → StateT σ LogM β} (hx : LogShortS x)
    (hf : ∀ a, LogShortS (f a)) : LogShortS (x >>= f) := fun s ↦ by
  rw [StateT.run_bind]
  exact LogShort.bind (hx s) fun p ↦ hf p.1 p.2

theorem get : LogShortS (MonadState.get : StateT σ LogM σ) := fun _ ↦ LogShort.pure _

theorem set (s' : σ) : LogShortS (MonadStateOf.set s' : StateT σ LogM PUnit) :=
  fun _ ↦ LogShort.pure _

theorem lift {x : LogM α} (hx : LogShort x) : LogShortS (StateT.lift x : StateT σ LogM α) :=
  fun s ↦ by
    rw [StateT.run_lift]
    exact LogShort.bind hx fun _ ↦ LogShort.pure _

/-- A loop over a list, each step short. -/
theorem forIn {γ : Type} (f : γ → β → StateT σ LogM (ForInStep β))
    (hf : ∀ a b, LogShortS (f a b)) : ∀ (l : List γ) (b : β), LogShortS (ForIn.forIn l b f)
  | [], b => by
    rw [List.forIn_nil]
    exact pure b
  | a :: l, b => by
    rw [List.forIn_cons]
    refine bind (hf a b) fun r ↦ ?_
    cases r with
    | done b' => exact pure b'
    | yield b' => exact forIn f hf l b'

end LogShortS

/-! ## A scheme's logged run -/

/-- **A scheme's computation answered by the logged hash** logs at most its query bound times the
blocks of its longest query. -/
theorem prefixCount_simulateQ_le {α β : Type} (H : Bytes → Digest) (f : Digest → β) {c : ℕ} :
    ∀ (oa : OracleComp (Bytes →ₒ β) α) (n : ℕ), IsTotalQueryBound oa n →
      AllQueriesSatisfy oa (fun t ↦ nBlocks t ≤ c) →
      prefixCount (simulateQ (fun x ↦ f <$> LogM.hash H x : QueryImpl (Bytes →ₒ β) LogM) oa).log ≤
        n * c := by
  intro oa
  induction oa using OracleComp.inductionOn with
  | pure x =>
    intro n _ _
    rw [simulateQ_pure]
    exact Nat.zero_le _
  | query_bind t k ih =>
    intro n hn hq
    rw [isTotalQueryBound_query_bind_iff] at hn
    rw [allQueriesSatisfy_query_bind_iff] at hq
    simp only [simulateQ_bind, simulateQ_spec_query]
    rw [prefixCount_bind, LogM.map_log, prefixCount_hash]
    obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
    refine (Nat.add_le_add hq.1 (ih _ n' (by simpa using hn.2 _) (hq.2 _))).trans ?_
    rw [Nat.succ_mul, Nat.add_comm]

end
end LeanVM.E2E.Complete
