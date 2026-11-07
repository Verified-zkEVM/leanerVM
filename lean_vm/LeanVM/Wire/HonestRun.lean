/-
  LeanVM.Wire.HonestRun

  The honest prover's run, for a strategy that wins (`Strategy.AcceptsFrom`) against a program
  whose openings are within the wire bounds (`Wired`): its phases are openings of one committed
  tree each, within the bounds, and its stream is as long as the program's cost allows; run with a
  hash that logs its inputs, it hashed every node of every tree it opened.
-/

module

public import LeanVM.Protocol.Compile.Rom.Prover
public import LeanVM.Wire.HonestTree
public import LeanVM.Wire.HonestShape
public import LeanVM.Wire.CompleteSpec

/-!
# The honest prover's run

From a history whose strategy wins (`S.AcceptsFrom p hist`), with its commitments well shaped
and `p` wired from their shapes (`Wired`, `LeanVM.Wire.HonestShape`):

* `proveFrom_phases`: every phase of the honest prover's output (`proveFrom`) is the openings of
  one committed word's tree at positions within the bounds (`QueryShape`), at most as many phases
  as openings were left;
* `proveFrom_stream_le`: its stream is at most the program's cost (`VerifierProgram.Costs`), a
  read, a nonce and a root half each costing at least one;
* `proveFromM_logged`: the prover building its trees with the hash `loggedHash h` (and
  the permutation `loggedPerm F`) computes `proveFrom h F`, and every path of its output is an
  opening of a tree whose every node input it logged (`TreeInLog`: the leaves' bytes, and each
  parent's pair of children, `buildTree_logged`).

The pruning idea and its formalization on leanerVM's main branch are scaraven's
(https://github.com/scaraven).
-/

@[expose] public section

namespace LeanVM.Wire

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Compile LeanVM.Protocol.MerkleTree
open LeanVM.Prover (Tree buildTreeWithHash leafDigestsWithHash parentsWithHash levelsWithHash
  powStepM searchM findNonceM)

/-- The shapes (height, width) of a list of commitments. -/
def shapesOf (cs : List (ℕ × ℕ × Word)) : List (ℕ × ℕ) := cs.map fun c ↦ (c.1, c.2.1)

theorem commits_append_single_of {hist : List Ev} {e : Ev} (he : commits [e] = []) :
    commits (hist ++ [e]) = commits hist := by
  rw [commits_append, he, List.append_nil]

/-! ## The phases and the stream -/

section Pure

variable (h : Bytes → Digest) (F : KeccakState → KeccakState) (S : Strategy) (fuel : ℕ)

/-- **The honest prover's phases**: each opens one committed word's tree at positions within the
wire bounds, the word well shaped, and there are at most as many as openings left. -/
theorem proveFrom_phases :
    ∀ (p : VerifierProgram Bool) (sp : Sponge) (hist : List Ev) (n : ℕ)
      {Q : Bool → List (ℕ × ℕ) → ℕ → Prop} {xs : List E} {os : List (List Opening)},
      S.AcceptsFrom p hist → (∀ c ∈ commits hist, WellShaped c.2.1 c.2.2) →
      Wired p (shapesOf (commits hist)) n Q →
      proveFrom h F S fuel p sp hist = some (xs, os) →
      os.length ≤ n ∧ ∀ phase ∈ os, ∃ (ht w : ℕ) (word : Word) (ps : List ℕ),
        phase = ps.map (openingAt h ht word) ∧ WellShaped w word ∧ QueryShape (ht, w) ps := by
  intro p
  induction p with
  | ret b =>
    intro sp hist n Q xs os _ _ _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    simp
  | fail =>
    intro sp hist n Q xs os _ _ _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨-, rfl⟩ := hp
    simp
  | read k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have hc := commits_append_single_of (hist := hist) (e := Ev.read (S.msg hist)) rfl
    refine ih _ _ _ n hacc (hc ▸ hws) (hc ▸ hw (S.msg hist)) hp
  | sample k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom] at hp
    have hc := commits_append_single_of (hist := hist) (e := Ev.sample (squeezeI F sp).1) rfl
    exact ih _ _ _ n (hacc _) (hc ▸ hws) (hc ▸ hw _) hp
  | grind bits k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom] at hp
    split at hp
    · cases hp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hc := commits_append_single_of (hist := hist) (e := Ev.grind bits) rfl
      exact ih _ _ n hacc (hc ▸ hws) (hc ▸ hw) hp
  | commit ht w k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨-, rfl⟩ := he
    have hc : commits (hist ++ [Ev.commit ht w (S.word hist)]) =
        commits hist ++ [(ht, w, S.word hist)] := by
      rw [commits_append]; rfl
    refine ih _ _ n (Q := Q) hacc.2 (fun c hcm ↦ ?_) ?_ hp
    · rw [hc] at hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · exact hws c hcm
      · simp only [List.mem_singleton] at hcm
        subst hcm
        exact hacc.1
    · rw [hc, shapesOf, List.map_append]
      exact hw
  | query i ps k ih =>
    intro sp hist n Q xs os hacc hws hw hp
    obtain ⟨rows, hrows, hacc'⟩ := hacc
    simp only [proveFrom] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨-, rfl⟩ := hp
      simp
    · next ht w' word hci =>
      simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨-, rfl⟩ := he
      have hrows' : rows = ps.map fun q ↦ word (q % 2 ^ ht) := by
        simp only [answer, hci, Option.map_some, Option.some.injEq] at hrows
        exact hrows.symm
      subst hrows'
      have hshape : (shapesOf (commits hist)).getD i (0, 0) = (ht, w') := by
        simp [shapesOf, List.getD_eq_getElem?_getD, hci]
      obtain ⟨hn, hq, hk⟩ := hw
      have hc := commits_append_single_of (hist := hist)
        (e := Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))) rfl
      obtain ⟨hlen, hph⟩ := ih _ _ _ (n - 1) hacc' (hc ▸ hws) (hc ▸ hk _) hp
      refine ⟨by simp only [List.length_cons]; omega, fun phase hphase ↦ ?_⟩
      rcases List.mem_cons.mp hphase with rfl | hphase
      · exact ⟨ht, w', word, ps, rfl, hws _ (List.mem_of_getElem? hci), hshape ▸ hq⟩
      · exact hph phase hphase

/-- **The honest prover's stream is at most the program's cost.** -/
theorem proveFrom_stream_le {height : ℕ} {α : Type} :
    ∀ (p : VerifierProgram α) (sp : Sponge) (hist : List Ev) (n : ℕ) {Q : α → Prop}
      {xs : List E} {os : List (List Opening)},
      VerifierProgram.Costs height p n Q → proveFrom h F S fuel p sp hist = some (xs, os) →
      xs.length ≤ n := by
  intro p
  induction p with
  | ret b =>
    intro sp hist n Q xs os _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    simp
  | fail =>
    intro sp hist n Q xs os _ hp
    simp only [proveFrom, Option.some.injEq, Prod.mk.injEq] at hp
    obtain ⟨rfl, -⟩ := hp
    simp
  | read k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := ih _ _ _ _ (hc.2 _) hp
    simp only [List.length_cons]
    have := hc.1
    omega
  | sample k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom] at hp
    have := ih _ _ _ _ (hc.2 _) hp
    omega
  | grind bits k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom] at hp
    split at hp
    · cases hp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := ih _ _ _ hc.2 hp
      simp only [List.length_cons]
      have := hc.1
      omega
  | commit ht w k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom, Option.map_eq_some_iff] at hp
    obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
    simp only [Prod.mk.injEq] at he
    obtain ⟨rfl, -⟩ := he
    have := ih _ _ _ hc.2.2 hp
    simp only [List.length_cons]
    have := hc.2.1
    omega
  | query i ps k ih =>
    intro sp hist n Q xs os hc hp
    simp only [proveFrom] at hp
    split at hp
    · simp only [Option.some.injEq, Prod.mk.injEq] at hp
      obtain ⟨rfl, -⟩ := hp
      simp
    · simp only [Option.map_eq_some_iff] at hp
      obtain ⟨⟨xs', os'⟩, hp, he⟩ := hp
      simp only [Prod.mk.injEq] at he
      obtain ⟨rfl, -⟩ := he
      have := ih _ _ _ _ (hc.2 _) hp
      omega

end Pure

/-! ## The trees' node inputs -/

/-- **Every node input of the tree of `word` over `h` is in `log`**: for every position below
`2^height`, the input of each level of its opening's climb, from the leaf to the root. -/
def TreeInLog (h : Bytes → Digest) (height : ℕ) (word : Word) (log : List Bytes) : Prop :=
  ∀ q < 2 ^ height, ∀ l ≤ height, climbInput h (openingAt h height word q) l ∈ log

theorem TreeInLog.mono {h : Bytes → Digest} {height : ℕ} {word : Word} {log log' : List Bytes}
    (ht : TreeInLog h height word log) (hl : log <+: log') : TreeInLog h height word log' :=
  fun q hq l hl' ↦ hl.subset (ht q hq l hl')

section Logged

variable (h : Bytes → Digest)

theorem run_bind_of {σ α β : Type} {x : StateM σ α} {f : α → StateM σ β} {s s' : σ} {a : α}
    (hx : x.run s = (a, s')) : (x >>= f).run s = (f a).run s' := by
  simp only [StateT.run_bind, hx]
  rfl

theorem loggedHash_run (x : Bytes) (log : List Bytes) :
    (loggedHash h x).run log = (h x, log ++ [x]) := rfl

theorem mapM_logged {γ : Type} (g : γ → Bytes) : ∀ (l : List γ) (log : List Bytes),
    (l.mapM fun a ↦ loggedHash h (g a)).run log = (l.map fun a ↦ h (g a), log ++ l.map g)
  | [], log => by simp; rfl
  | a :: l, log => by
    rw [List.mapM_cons, run_bind_of (loggedHash_run h (g a) log),
      run_bind_of (mapM_logged g l _)]
    simp only [List.map_cons, List.append_assoc, List.singleton_append]
    rfl

theorem arrayRange_mapM_logged (g : ℕ → Bytes) (n : ℕ) (log : List Bytes) :
    ((Array.range n).mapM fun i ↦ loggedHash h (g i)).run log =
      ((Array.range n).map fun i ↦ h (g i), log ++ (List.range n).map g) := by
  rw [Array.mapM_eq_mapM_toList, StateT.run_map, Array.toList_range, mapM_logged]
  refine Prod.ext ?_ rfl
  apply Array.toList_inj.mp
  simp only [Array.toList_map, Array.toList_range]
  rfl

theorem leafDigests_logged (ht : ℕ) (word : Word) (log : List Bytes) :
    (leafDigestsWithHash (loggedHash h) ht word).run log =
      (leafDigestsWithHash (m := Id) h ht word,
        log ++ (List.range (2 ^ ht)).map fun i ↦ (word i).flatMap K.toBytes) := by
  rw [leafDigestsWithHash, arrayRange_mapM_logged h (fun i ↦ (word i).flatMap K.toBytes)]
  refine Prod.ext ?_ rfl
  exact (Array.idRun_mapM).symm

theorem parents_logged (level : Array Digest) (n : ℕ) (log : List Bytes) :
    (parentsWithHash (loggedHash h) level n).run log =
      (parentsWithHash (m := Id) h level n, log ++ (List.range n).map fun j ↦
        digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default)) := by
  rw [parentsWithHash, arrayRange_mapM_logged h (fun j ↦
    digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))]
  refine Prod.ext ?_ rfl
  exact (parentsM_id h level n).symm

/-- The levels built with the logging hash are the plain ones, and every parent's pair of
children is logged. -/
theorem levels_logged : ∀ (k : ℕ) (level : Array Digest) (log : List Bytes), ∃ L,
    (levelsWithHash (loggedHash h) k level).run log = (levelsWithHash (m := Id) h k level, log ++ L) ∧
      ∀ l < k, ∀ j < 2 ^ (k - 1 - l),
        digestBytes (((levelsWithHash (m := Id) h k level).getD l #[]).getD (2 * j) default) ++
          digestBytes (((levelsWithHash (m := Id) h k level).getD l #[]).getD (2 * j + 1) default)
            ∈ L
  | 0, level, log => ⟨[], by simp [levelsWithHash]; rfl, fun l hl ↦ absurd hl (Nat.not_lt_zero _)⟩
  | k + 1, level, log => by
    obtain ⟨L, hL, hmem⟩ := levels_logged k (parentsWithHash (m := Id) h level (2 ^ k))
      (log ++ (List.range (2 ^ k)).map fun j ↦
        digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default))
    refine ⟨(List.range (2 ^ k)).map (fun j ↦
        digestBytes (level.getD (2 * j) default) ++ digestBytes (level.getD (2 * j + 1) default)) ++
        L, ?_, fun l hl j hj ↦ ?_⟩
    · rw [levelsWithHash, run_bind_of (parents_logged h level _ log), run_bind_of hL]
      simp only [levelsM_id_succ, List.append_assoc]
      rfl
    · rw [levelsM_id_succ]
      cases l with
      | zero =>
        refine List.mem_append_left _ (List.mem_map.mpr ⟨j, List.mem_range.mpr ?_, rfl⟩)
        simpa using hj
      | succ l =>
        simp only [List.getD_cons_succ]
        exact List.mem_append_right _ (hmem l (by omega) j (by
          rw [show k + 1 - 1 - (l + 1) = k - 1 - l by omega] at hj; exact hj))

/-- The plain levels from a level of the tree's nodes at level `l0` are the tree's nodes. -/
theorem levels_honestNode (word : Word) : ∀ (k : ℕ) (level : Array Digest) (l0 : ℕ),
    (∀ j < 2 ^ k, level.getD j default = honestNode h word l0 j) →
      ∀ l ≤ k, ∀ j < 2 ^ (k - l),
        ((levelsWithHash (m := Id) h k level).getD l #[]).getD j default =
          honestNode h word (l0 + l) j
  | 0, level, l0, hlv, l, hl, j, hj => by
    obtain rfl : l = 0 := by omega
    exact hlv j hj
  | k + 1, level, l0, hlv, l, hl, j, hj => by
    rw [levelsM_id_succ]
    cases l with
    | zero => exact hlv j hj
    | succ l =>
      simp only [List.getD_cons_succ]
      rw [levels_honestNode word k _ (l0 + 1) (fun j hj ↦ ?_) l (by omega) j (by
          rw [show k + 1 - (l + 1) = k - l by omega] at hj; exact hj)]
      · rw [show l0 + 1 + l = l0 + (l + 1) by omega]
      · rw [parentsM_id, Array.getD_eq_getD_getElem?, Array.getElem?_map,
          Array.getElem?_range]
        simp only [hj, ↓reduceIte, Option.map_some, Option.getD_some]
        have h1 : 2 * j < 2 ^ (k + 1) := by rw [pow_succ]; omega
        have h2 : 2 * j + 1 < 2 ^ (k + 1) := by rw [pow_succ]; omega
        rw [hlv _ h1, hlv _ h2, honestNode_succ, nodeHash]

/-- An opening's leaf input. -/
theorem climbInput_openingAt_zero {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) :
    climbInput h (openingAt h ht word q) 0 = (word q).flatMap K.toBytes := by
  simp [climbInput, openingAt, Nat.mod_eq_of_lt hq]

/-- An opening's input at level `l + 1`: the tree's two children of its node there. -/
theorem climbInput_openingAt_succ {ht : ℕ} {word : Word} {q : ℕ} (hq : q < 2 ^ ht) {l : ℕ}
    (hl : l < ht) :
    climbInput h (openingAt h ht word q) (l + 1) =
      digestBytes (honestNode h word l (2 * (q / 2 ^ (l + 1)))) ++
        digestBytes (honestNode h word l (2 * (q / 2 ^ (l + 1)) + 1)) := by
  simp only [climbInput]
  rw [climbTo_openingAt hq hl.le, getD_openingAt hq hl,
    show (openingAt h ht word q).leafIndex = q from rfl, Nat.shiftRight_eq_div_pow,
    pow_succ, ← Nat.div_div_eq_div_mul]
  generalize q / 2 ^ l = x
  unfold sibling
  split
  · rw [show 2 * (x / 2) = x by omega]
  · rw [show 2 * (x / 2) = x - 1 by omega, show x - 1 + 1 = x by omega]

/-- **The tree built with the logging hash** is the plain one, and it logs every node input. -/
theorem buildTree_logged (ht : ℕ) (word : Word) (log : List Bytes) : ∃ L,
    (buildTreeWithHash (loggedHash h) ht word).run log =
        (buildTreeWithHash (m := Id) h ht word, log ++ L) ∧
      TreeInLog h ht word (log ++ L) := by
  obtain ⟨L, hL, hmem⟩ := levels_logged h ht (leafDigestsWithHash (m := Id) h ht word)
    (log ++ (List.range (2 ^ ht)).map fun i ↦ (word i).flatMap K.toBytes)
  refine ⟨(List.range (2 ^ ht)).map (fun i ↦ (word i).flatMap K.toBytes) ++ L, ?_,
    fun q hq l hl ↦ ?_⟩
  · rw [buildTreeWithHash, run_bind_of (leafDigests_logged h ht word log), run_bind_of hL]
    simp only [List.append_assoc]
    rfl
  · have hleaves : ∀ j < 2 ^ ht, (leafDigestsWithHash (m := Id) h ht word).getD j default =
        honestNode h word 0 j := by
      intro j hj
      rw [leafDigestsM_id, Array.getD_eq_getD_getElem?, Array.getElem?_eq_getElem (by simpa)]
      simp [leavesOf, honestNode]
    cases l with
    | zero =>
      rw [climbInput_openingAt_zero h hq]
      exact List.mem_append_right _ (List.mem_append_left _
        (List.mem_map.mpr ⟨q, List.mem_range.mpr hq, rfl⟩))
    | succ l =>
      rw [climbInput_openingAt_succ h hq (by omega)]
      have hj : q / 2 ^ (l + 1) < 2 ^ (ht - 1 - l) := by
        rw [Nat.div_lt_iff_lt_mul (Nat.two_pow_pos _), ← pow_add,
          show ht - 1 - l + (l + 1) = ht by omega]
        exact hq
      have h2 : 2 * (q / 2 ^ (l + 1)) + 1 < 2 ^ (ht - l) := by
        generalize q / 2 ^ (l + 1) = X at hj ⊢
        rw [show ht - l = ht - 1 - l + 1 by omega, pow_succ]
        omega
      have := hmem l (by omega) _ hj
      rw [levels_honestNode h word ht _ 0 hleaves l (by omega) _ (by omega),
        levels_honestNode h word ht _ 0 hleaves l (by omega) _ h2, Nat.zero_add] at this
      exact List.mem_append_right _ (List.mem_append_right _ this)

end Logged

/-! ## The prover with the logging hash -/

section PurePermutation

variable {m : Type → Type} [Monad m] [LawfulMonad m] (F : KeccakState → KeccakState)

theorem absorb_pureF (sp : Sponge) (x : E) (tag : ℕ) :
    Compile.absorb (m := m) (fun s ↦ pure (F s)) sp x tag = pure (absorbI F sp x tag) := by
  unfold absorbI Compile.absorb Compile.duplex
  by_cases hc : sp.pending.length = rateScalars
  · simp [hc]; rfl
  · simp [hc]

theorem squeeze_pureF (sp : Sponge) :
    Compile.squeeze (m := m) (fun s ↦ pure (F s)) sp = pure (squeezeI F sp) := by
  unfold squeezeI Compile.squeeze Compile.duplex
  simp
  rfl

theorem powStepM_pureF (sp : Sponge) (n : E) :
    powStepM (m := m) (fun s ↦ pure (F s)) sp n = pure (powStep F sp n) := by
  unfold powStepM
  rw [absorb_pureF, pure_bind, squeeze_pureF]
  rfl

theorem searchM_pureF (bits : ℕ) (sp : Sponge) : ∀ (count n : ℕ),
    searchM (m := m) (fun s ↦ pure (F s)) bits sp n count =
      pure (((List.range' n count).find? fun j ↦
        powOk bits (nonceOf j) (powStep F sp (nonceOf j)).1).map nonceOf)
  | 0, _ => rfl
  | count + 1, n => by
    unfold searchM
    rw [powStepM_pureF, pure_bind, List.range'_succ, List.find?_cons]
    by_cases hp : powOk bits (nonceOf n) (powStep F sp (nonceOf n)).1
    · simp only [prover_nonceOf, hp, ↓reduceIte, Option.map_some]
    · simp only [prover_nonceOf, hp, Bool.false_eq_true, ↓reduceIte]
      exact searchM_pureF bits sp count (n + 1)

theorem findNonceM_pureF (bits : ℕ) (sp : Sponge) (fuel : ℕ) :
    findNonceM (m := m) (fun s ↦ pure (F s)) bits sp fuel = pure (findNonce F bits sp fuel) := by
  unfold findNonceM findNonce
  split
  · rfl
  · rw [searchM_pureF, List.range_eq_range']

end PurePermutation

section LoggedProver

variable (h : Bytes → Digest) (F : KeccakState → KeccakState) (S : Strategy) (fuel : ℕ)

/-- **The prover with the logging hash** computes the plain prover's output, logging after what
was logged before; and every path of its output is an opening of a tree whose node inputs are
all logged. -/
theorem proveFromM_logged {α : Type} :
    ∀ (p : VerifierProgram α) (sp : Sponge) (hist : List Ev) (log : List Bytes)
      {r : Option (List E × List (List Opening))} {log' : List Bytes},
      (∀ c ∈ commits hist, TreeInLog h c.1 c.2.2 log) →
      (proveFromM (loggedHash h) (loggedPerm F) S fuel p sp hist
          (treesOf h (commits hist))).run log = (r, log') →
      r = proveFrom h F S fuel p sp hist ∧ log <+: log' ∧
        ∀ t, r = some t → ∀ phase ∈ t.2, ∀ path ∈ phase,
          ∃ (ht : ℕ) (word : Word), path = openingAt h ht word path.leafIndex ∧
            TreeInLog h ht word log' := by
  intro p
  induction p with
  | ret b =>
    intro sp hist log r log' _ hr
    simp only [proveFromM] at hr
    cases hr
    refine ⟨rfl, List.prefix_refl _, fun t ht ↦ ?_⟩
    cases ht
    simp
  | fail =>
    intro sp hist log r log' _ hr
    simp only [proveFromM] at hr
    cases hr
    refine ⟨rfl, List.prefix_refl _, fun t ht ↦ ?_⟩
    cases ht
    simp
  | read k ih =>
    intro sp hist log r log' hin hr
    simp only [proveFromM] at hr
    have hc := commits_append_single_of (hist := hist) (e := Ev.read (S.msg hist)) rfl
    rw [show loggedPerm F = fun s ↦ pure (F s) from rfl, absorb_pureF, pure_bind] at hr
    rw [show treesOf h (commits hist) = treesOf h (commits (hist ++ [Ev.read (S.msg hist)]))
      by rw [hc]] at hr
    obtain ⟨r', log'', hrun⟩ : ∃ r' log'', (proveFromM (loggedHash h) (fun s ↦ pure (F s)) S fuel
        (k (S.msg hist)) (absorbI F sp (S.msg hist) dsObserve) (hist ++ [Ev.read (S.msg hist)])
        (treesOf h (commits (hist ++ [Ev.read (S.msg hist)])))).run log = (r', log'') :=
      ⟨_, _, rfl⟩
    rw [run_bind_of hrun] at hr
    cases hr
    obtain ⟨rfl, hpre, hpath⟩ := ih _ _ _ _ (hc ▸ hin) hrun
    refine ⟨rfl, hpre, fun t ht ↦ ?_⟩
    obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
    exact hpath t' ht'
  | sample k ih =>
    intro sp hist log r log' hin hr
    simp only [proveFromM] at hr
    rw [show loggedPerm F = fun s ↦ pure (F s) from rfl, squeeze_pureF, pure_bind] at hr
    have hc := commits_append_single_of (hist := hist) (e := Ev.sample (squeezeI F sp).1) rfl
    rw [show treesOf h (commits hist) = treesOf h (commits (hist ++ [Ev.sample (squeezeI F sp).1]))
      by rw [hc]] at hr
    exact ih _ _ _ _ (hc ▸ hin) hr
  | grind bits k ih =>
    intro sp hist log r log' hin hr
    simp only [proveFromM] at hr
    rw [show loggedPerm F = fun s ↦ pure (F s) from rfl, findNonceM_pureF, pure_bind] at hr
    simp only [proveFrom]
    cases hn : findNonce F bits sp fuel with
    | none =>
      rw [hn] at hr
      cases hr
      exact ⟨rfl, List.prefix_refl _, fun t ht ↦ by cases ht⟩
    | some n =>
      rw [hn] at hr
      simp only at hr
      rw [powStepM_pureF, pure_bind] at hr
      have hc := commits_append_single_of (hist := hist) (e := Ev.grind bits) rfl
      rw [show treesOf h (commits hist) = treesOf h (commits (hist ++ [Ev.grind bits]))
        by rw [hc]] at hr
      obtain ⟨r', log'', hrun⟩ : ∃ r' log'', (proveFromM (loggedHash h) (fun s ↦ pure (F s)) S
          fuel k (powStep F sp n).2 (hist ++ [Ev.grind bits])
          (treesOf h (commits (hist ++ [Ev.grind bits])))).run log = (r', log'') :=
        ⟨_, _, rfl⟩
      rw [run_bind_of hrun] at hr
      cases hr
      obtain ⟨rfl, hpre, hpath⟩ := ih _ _ _ (hc ▸ hin) hrun
      refine ⟨rfl, hpre, fun t ht ↦ ?_⟩
      obtain ⟨t', ht', rfl⟩ := Option.map_eq_some_iff.mp ht
      exact hpath t' ht'
  | commit ht w k ih =>
    intro sp hist log r log' hin hr
    simp only [proveFromM] at hr
    obtain ⟨L, hL, htree⟩ := buildTree_logged h ht (S.word hist) log
    rw [run_bind_of hL, show loggedPerm F = fun s ↦ pure (F s) from rfl, absorb_pureF, pure_bind,
      absorb_pureF, pure_bind, ← treesOf_append, root_buildTreeM_id] at hr
    obtain ⟨r', log'', hrun⟩ : ∃ r' log'', (proveFromM (loggedHash h) (fun s ↦ pure (F s)) S fuel k
        (absorbI F (absorbI F sp (digestHalves (treeRoot h ht (S.word hist))).1 dsObserve)
          (digestHalves (treeRoot h ht (S.word hist))).2 dsObserve)
        (hist ++ [Ev.commit ht w (S.word hist)])
        (treesOf h (commits (hist ++ [Ev.commit ht w (S.word hist)])))).run (log ++ L) =
          (r', log'') :=
      ⟨_, _, rfl⟩
    rw [run_bind_of hrun] at hr
    cases hr
    have hc : commits (hist ++ [Ev.commit ht w (S.word hist)]) =
        commits hist ++ [(ht, w, S.word hist)] := by
      rw [commits_append]; rfl
    have hin' : ∀ c ∈ commits (hist ++ [Ev.commit ht w (S.word hist)]),
        TreeInLog h c.1 c.2.2 (log ++ L) := by
      intro c hcm
      rw [hc] at hcm
      rcases List.mem_append.mp hcm with hcm | hcm
      · exact (hin c hcm).mono (List.prefix_append _ _)
      · simp only [List.mem_singleton] at hcm
        subst hcm
        exact htree
    obtain ⟨rfl, hpre, hpath⟩ := ih _ _ _ hin' hrun
    refine ⟨rfl, (List.prefix_append _ _).trans hpre, fun t hts ↦ ?_⟩
    obtain ⟨t', ht'', rfl⟩ := Option.map_eq_some_iff.mp hts
    exact hpath t' ht''
  | query i ps k ih =>
    intro sp hist log r log' hin hr
    simp only [proveFromM] at hr
    have hci : (treesOf h (commits hist))[i]? =
        ((commits hist)[i]?).map fun c ↦ buildTreeWithHash (m := Id) h c.1 c.2.2 := by
      simp [treesOf]
    rw [hci] at hr
    simp only [proveFrom]
    rcases hcm : (commits hist)[i]? with _ | ⟨ht, w, word⟩
    · rw [hcm] at hr
      cases hr
      exact ⟨rfl, List.prefix_refl _, fun t ht ↦ by cases ht; simp⟩
    · rw [hcm] at hr
      simp only [Option.map_some] at hr
      have hc := commits_append_single_of (hist := hist)
        (e := Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))) rfl
      have ho : (buildTreeWithHash (m := Id) h ht word).opening = openingAt h ht word :=
        funext (opening_buildTreeM_id h ht word)
      obtain ⟨r', log'', hrun⟩ : ∃ r' log'', (proveFromM (loggedHash h) (loggedPerm F) S fuel
          (k (ps.map fun q ↦ word (q % 2 ^ ht))) sp
          (hist ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])
          (treesOf h (commits (hist ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])))).run log =
            (r', log'') :=
        ⟨_, _, rfl⟩
      rw [show treesOf h (commits hist) =
          treesOf h (commits (hist ++ [Ev.query (ps.map fun q ↦ word (q % 2 ^ ht))])) by rw [hc]]
        at hr
      erw [run_bind_of hrun] at hr
      cases hr
      obtain ⟨rfl, hpre, hpath⟩ := ih _ _ _ _ (hc ▸ hin) hrun
      refine ⟨by simp only [ho], hpre, fun t hts ↦ ?_⟩
      obtain ⟨t', ht'', rfl⟩ := Option.map_eq_some_iff.mp hts
      intro phase hphase
      rw [ho] at hphase
      rcases List.mem_cons.mp hphase with rfl | hphase
      · intro path hpath
        obtain ⟨q, -, rfl⟩ := List.mem_map.mp hpath
        exact ⟨ht, word, rfl, (hin _ (List.mem_of_getElem? hcm)).mono hpre⟩
      · exact hpath t' ht'' phase hphase

end LoggedProver

end LeanVM.Wire

end
