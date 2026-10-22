/-
  LeanVM.E2E.Complete.Count.Prog

  The leaves a verifier program opens (L17): a cost predicate on the verifier language, and the
  count of the block prefixes its compiled run logs.
-/

module

public import LeanVM.E2E.Complete.Count.Basic
public import LeanVM.E2E.Complete.CapsRange

/-!
# The leaves a program opens

The compiled run of a program (`Compile.run`) hashes `64`-byte strings at every read, sample,
proof of work, commitment and Merkle node; the only longer strings are the opened leaves, `8`
bytes a word, hashed only when the leaf has the committed width (`openOne`). So the count of its
log's block prefixes is bounded by the number of leaves it opens times the blocks of the widest
committed leaf:

* `LeafBound W p n`: every commitment of `p` has width at most `W`, and along every path `p`
  opens at most `n` leaves (positions); closed under `bind` (`LeafBound.bind`, the costs adding),
  through `AllRet` (`LeafBound.bind_allRet`), and free for programs without commitments or
  queries (`LeafBound.of_noCQ`);
* `prefixCount_run_le`: the run's log has at most `n * leafBlocks W` block prefixes, from a state
  whose roots are at most `W` wide; `prefixCount_runProof_le`, `prefixCount_verifyDeferredWith_le`
  (the seed hashes `64` bytes).

`whirLeafWidth` and `whirLeaves` are the deployed deferring verifier's: WHIR's commitments are at
most `3 · 2^6` words wide, and its levels query at most `368` positions in all.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Protocol LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.Blake2sHash

@[expose] public section

variable {α β : Type}

/-! ## The cost predicate -/

/-- **Every commitment of `p` has width at most `W`, and `p` opens at most `n` leaves**, along
every path. -/
def LeafBound (W : ℕ) : Prog α → ℕ → Prop
  | .ret _, _ => True
  | .fail, _ => True
  | .read k, n => ∀ x, LeafBound W (k x) n
  | .sample k, n => ∀ x, LeafBound W (k x) n
  | .grind _ k, n => LeafBound W k n
  | .commit _ w k, n => w ≤ W ∧ LeafBound W k n
  | .query _ ps k, n => ps.length ≤ n ∧ ∀ rows, LeafBound W (k rows) (n - ps.length)

namespace LeafBound

variable {W : ℕ}

/-- A larger bound. -/
theorem mono {p : Prog α} {n m : ℕ} (hp : LeafBound W p n) (h : n ≤ m) : LeafBound W p m := by
  induction p generalizing n m with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x) h
  | sample k ih => exact fun x ↦ ih x (hp x) h
  | grind b k ih => exact ih hp h
  | commit ht w k ih => exact ⟨hp.1, ih hp.2 h⟩
  | query i ps k ih => exact ⟨hp.1.trans h, fun rows ↦ ih rows (hp.2 rows) (by omega)⟩

/-- **Sequencing through what `p` returns**: the costs add. -/
theorem bind_allRet {Q : α → Prop} {p : Prog α} {f : α → Prog β} {n₁ n₂ : ℕ}
    (hp : LeafBound W p n₁) (hq : AllRet Q p) (hf : ∀ a, Q a → LeafBound W (f a) n₂) :
    LeafBound W (p.bind f) (n₁ + n₂) := by
  induction p generalizing n₁ with
  | ret a => exact mono (hf a hq) (Nat.le_add_left _ _)
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x) (hq x)
  | sample k ih => exact fun x ↦ ih x (hp x) (hq x)
  | grind b k ih => exact ih hp hq
  | commit ht w k ih => exact ⟨hp.1, ih hp.2 hq⟩
  | query i ps k ih =>
    refine ⟨by have := hp.1; omega, fun rows ↦ ?_⟩
    have := ih rows (hp.2 rows) (hq rows)
    show LeafBound W ((k rows).bind f) (n₁ + n₂ - ps.length)
    rwa [Nat.sub_add_comm hp.1]

/-- **Sequencing**: the costs add. -/
theorem bind {p : Prog α} {f : α → Prog β} {n₁ n₂ : ℕ} (hp : LeafBound W p n₁)
    (hf : ∀ a, LeafBound W (f a) n₂) : LeafBound W (p.bind f) (n₁ + n₂) :=
  bind_allRet hp (allRet_true p) fun a _ ↦ hf a

/-- Sequencing in `do` notation. -/
theorem seq {p : Prog α} {f : α → Prog β} {n₁ n₂ : ℕ} (hp : LeafBound W p n₁)
    (hf : ∀ a, LeafBound W (f a) n₂) : LeafBound W (p >>= f) (n₁ + n₂) :=
  bind hp hf

/-- A program without commitments or queries opens nothing. -/
theorem of_noCQ {p : Prog α} {n : ℕ} (hp : NoCQ p) : LeafBound W p n := by
  induction p with
  | ret a => trivial
  | fail => trivial
  | read k ih => exact fun x ↦ ih x (hp x)
  | sample k ih => exact fun x ↦ ih x (hp x)
  | grind b k ih => exact ih hp
  | commit ht w k ih => exact hp.elim
  | query i ps k ih => exact hp.elim

/-- **Through a program without commitments or queries**, keeping what it returns. -/
theorem bind_noCQ_allRet {Q : α → Prop} {p : Prog α} {f : α → Prog β} {n : ℕ} (hp : NoCQ p)
    (hq : AllRet Q p) (hf : ∀ a, Q a → LeafBound W (f a) n) : LeafBound W (p.bind f) n := by
  have := bind_allRet (n₁ := 0) (of_noCQ hp) hq hf
  rwa [Nat.zero_add] at this

/-- **Through a program without commitments or queries.** -/
theorem bind_noCQ {p : Prog α} {f : α → Prog β} {n : ℕ} (hp : NoCQ p)
    (hf : ∀ a, LeafBound W (f a) n) : LeafBound W (p.bind f) n :=
  bind_noCQ_allRet hp (allRet_true p) fun a _ ↦ hf a

end LeafBound

/-! ## The deployed constants -/

/-- The widest leaf WHIR commits to, in words: `3 · 2^fold`, `fold ≤ 6`. -/
def whirLeafWidth : ℕ := 192

/-- The most positions WHIR's levels query in all: the largest sum of a row of `queryTable`. -/
def whirLeaves : ℕ := 368

/-! ## The count of a run -/

/-- The block prefixes of a leaf of at most `W` words. -/
def leafBlocks (W : ℕ) : ℕ := (8 * W - 1) / 64

theorem leafBlocks_mono {W W' : ℕ} (h : W ≤ W') : leafBlocks W ≤ leafBlocks W' :=
  Nat.div_le_div_right (by omega)

theorem length_flatMap_kBytes (ws : List K) : (ws.flatMap kBytes).length = 8 * ws.length := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.flatMap_cons, List.length_append, ih, List.length_cons]
    show 8 + 8 * ws.length = _
    omega

theorem length_digestBytes_count (d : Digest) : (digestBytes d).length = 32 := by
  simp [digestBytes, List.length_flatMap, wordBytes]

theorem length_blockOf_count (x : E) (tag : ℕ) : (blockOf x tag).length = 32 := rfl

/-- A chain step hashes one block. -/
theorem prefixCount_absorbBlock (H : Bytes → Digest) (cv : Digest) (x : E) (tag : ℕ) :
    prefixCount (absorbBlock (LogM.hash H) cv (blockOf x tag)).log = 0 := by
  show prefixCount (LogM.hash H (digestBytes cv ++ blockOf x tag)).log = 0
  rw [prefixCount_hash]
  exact nBlocks_eq_zero_of_length_le (by
    rw [List.length_append, length_digestBytes_count, length_blockOf_count])

/-- A Merkle climb hashes blocks. -/
theorem logShort_climb (H : Bytes → Digest) :
    ∀ (node : Digest) (q : ℕ) (path : List Digest), LogShort (climb (LogM.hash H) node q path)
  | _, _, [] => LogShort.pure _
  | node, q, s :: ss => by
    simp only [climb]
    split <;> exact LogShort.bind (LogShort.hash H (by
      rw [List.length_append, length_digestBytes_count, length_digestBytes_count]))
      fun _ ↦ logShort_climb H _ _ ss

/-- One opening hashes at most one leaf of its committed width. -/
theorem prefixCount_openOne_le (H : Bytes → Digest) {W : ℕ} (root : Digest) (height : ℕ)
    {width : ℕ} (hw : width ≤ W) (q : ℕ) (o : Opening) :
    prefixCount (openOne (LogM.hash H) root height width q o).log ≤ leafBlocks W := by
  unfold openOne
  split
  · rename_i h
    rw [prefixCount_bind, prefixCount_bind, prefixCount_hash, (logShort_climb H _ _ _).prefixCount_eq]
    simp only [LogM.pure_log, prefixCount_nil, Nat.add_zero]
    refine (Nat.div_le_div_right ?_).trans (leafBlocks_mono hw)
    rw [length_flatMap_kBytes, h.1]
  · exact Nat.zero_le _

/-- Opening the positions `ps` hashes at most one leaf each. -/
theorem prefixCount_openAll_le (H : Bytes → Digest) {W : ℕ} (root : Digest) (height : ℕ)
    {width : ℕ} (hw : width ≤ W) :
    ∀ (ps : List ℕ) (os : List Opening),
      prefixCount (openAll (LogM.hash H) root height width ps os).log ≤ ps.length * leafBlocks W
  | [], _ => Nat.zero_le _
  | _ :: _, [] => Nat.zero_le _
  | q :: qs, o :: os => by
    simp only [openAll]
    rw [prefixCount_bind, List.length_cons, Nat.succ_mul, Nat.add_comm _ (leafBlocks W)]
    refine Nat.add_le_add (prefixCount_openOne_le H root height hw q o) ?_
    split
    · rw [prefixCount_bind]
      simp only [LogM.pure_log, prefixCount_nil, Nat.add_zero]
      exact prefixCount_openAll_le H root height hw qs os
    · exact Nat.zero_le _

/-- **The count of a run**: a program opening at most `n` leaves, every commitment at most `W`
wide, from roots at most `W` wide, logs at most `n * leafBlocks W` block prefixes. -/
theorem prefixCount_run_le (H : Bytes → Digest) {W : ℕ} :
    ∀ (p : Prog α) (n : ℕ) (st : St), LeafBound W p n → (∀ r ∈ st.roots, r.2.2 ≤ W) →
      prefixCount (run (LogM.hash H) p st).log ≤ n * leafBlocks W := by
  intro p
  induction p with
  | ret a => intro _ _ _ _; exact Nat.zero_le _
  | fail => intro _ _ _ _; exact Nat.zero_le _
  | read k ih =>
    intro n st hp hr
    simp only [run]
    split
    · exact Nat.zero_le _
    · rw [prefixCount_bind, prefixCount_absorbBlock, Nat.zero_add]
      exact ih _ n _ (hp _) hr
  | sample k ih =>
    intro n st hp hr
    simp only [run]
    rw [prefixCount_bind, prefixCount_absorbBlock, Nat.zero_add]
    exact ih _ n _ (hp _) hr
  | grind b k ih =>
    intro n st hp hr
    simp only [run]
    split
    · exact Nat.zero_le _
    · rw [prefixCount_bind, prefixCount_absorbBlock, Nat.zero_add, prefixCount_bind,
        prefixCount_absorbBlock, Nat.zero_add, prefixCount_bind, prefixCount_absorbBlock,
        Nat.zero_add]
      split
      · exact ih n _ hp hr
      · exact Nat.zero_le _
  | commit ht w k ih =>
    intro n st hp hr
    simp only [run]
    split
    · rw [prefixCount_bind, prefixCount_absorbBlock, Nat.zero_add, prefixCount_bind,
        prefixCount_absorbBlock, Nat.zero_add]
      split
      · refine ih n _ hp.2 fun r hm ↦ ?_
        rcases List.mem_append.mp hm with hm | hm
        · exact hr r hm
        · rw [List.mem_singleton] at hm
          exact hm ▸ hp.1
      · exact Nat.zero_le _
    · exact Nat.zero_le _
  | query i ps k ih =>
    intro n st hp hr
    simp only [run]
    split
    · exact Nat.zero_le _
    · rename_i root height width hi
      have hw : width ≤ W := hr _ (List.mem_of_getElem? hi)
      rw [prefixCount_bind]
      refine (Nat.add_le_add (prefixCount_openAll_le H root height hw ps st.openings) ?_).trans
        (show ps.length * leafBlocks W + (n - ps.length) * leafBlocks W ≤ n * leafBlocks W by
          rw [← Nat.add_mul, Nat.add_sub_cancel' hp.1])
      split
      · exact ih _ _ _ (hp.2 _) hr
      · exact Nat.zero_le _

/-- **The count of a compiled verifier** on a proof. -/
theorem prefixCount_runProof_le (H : Bytes → Digest) {W n : ℕ} {P : Prog Bool}
    (hP : LeafBound W P n) (seed : Digest) (π : Proof) :
    prefixCount (runProof (LogM.hash H) P seed π).log ≤ n * leafBlocks W := by
  unfold runProof
  rw [prefixCount_bind]
  refine (Nat.add_le_add (prefixCount_run_le H P n _ hP fun _ h ↦ by simp at h)
    (show prefixCount (_ : LogM Bool).log ≤ 0 by split <;> exact Nat.le_refl _)).trans
    (Nat.le_of_eq (Nat.add_zero _))

/-- **The count of the deferring verifier** on a child's proof: its seed is one block. -/
theorem prefixCount_verifyDeferredWith_le (H : Bytes → Digest) {W n : ℕ} {bytecode : List K}
    {c : FixedClaims} {pi : Digest} (h : LeafBound W (deferredProgram c bytecode pi) n)
    (iv : Digest) (π : Proof) :
    prefixCount (verifyDeferredWith (LogM.hash H) bytecode iv pi c π).log ≤ n * leafBlocks W := by
  unfold verifyDeferredWith
  rw [prefixCount_bind, prefixCount_hash, nBlocks_eq_zero_of_length_le (by
    rw [List.length_append, length_digestBytes_count, length_digestBytes_count]), Nat.zero_add]
  exact prefixCount_runProof_le H h _ π

end
end LeanVM.E2E.Complete
