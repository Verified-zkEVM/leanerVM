/-
  LeanVM.Guest.B1.Digest.CommonM

  The prefix layer of `B1/Digest` and `B1/Da` over a hash model: straight-line blocks under any
  semantics, a run of `BLAKE2S` rows as the rows it checked, and how such a run extends a prefix
  and ends in an answered hash.
-/

module

public import LeanVM.Guest.B1.Digest.Common
public import LeanVM.Guest.CoreB
public import LeanVM.Guest.Value.ModelChain

/-!
# The prefix layer (`Common` over a `HashModel`)

`Common.lean` states a run of `BLAKE2S` instructions as `ChainCells`, the fold `chainRun` of the
compression function. Over a `HashModel` no chaining value is named (pattern C of
`docs/roadmap/w2-guest-model.md` (removed; in git at `6ffa1d1f`)):

* `ChainSteps S st blocks md n out`: the rows a run of `n` chained `BLAKE2S` instructions checked
  under the semantics `S`, from the cells `st` to the cells `out`, the intermediate states free;
* `ChainSteps.prefix`: from a prefix, a run at the counters after it extends the prefix
  (`HashModel.prefix_run`); `ChainSteps.append` glues two runs;
* `prefixBlocks cs k`, the bytes of the first `k` blocks of a list of cells, and
  `chainSteps_prefix`, a run from the state after `k` blocks (`chainCells_prefix`'s forward
  direction);
* `Ans M x c`: the model answers the hash of `x` with the cells `c` (`ansD`, its digest);
* the `B` forms of `Common`'s block lemmas (`holdsListB_atoms`, `holdsListB_flatMap`,
  `relB_of_find`) and `loopB_fwd`, `loop_iff`'s forward direction under any semantics.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

/-! ## Straight-line blocks under any semantics -/

section Blocks

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val}

/-- A run of atoms holds under `S` exactly when each does (`holdsList_atoms`). -/
theorem holdsListB_atoms (as : List Atom) (rest : List Stmt) (next : Prop)
    (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ (as.map .atom ++ rest) next kret ↔
      (∀ a ∈ as, a.HoldsB S rd σ) ∧ Stmt.HoldsListB S C rd σ rest next kret := by
  induction as with
  | nil => simp
  | cons a as ih =>
      simp only [List.map_cons, List.cons_append, Stmt.HoldsListB, Stmt.HoldsB, ih,
        List.forall_mem_cons]
      tauto

/-- An atom other than `BLAKE2S`. -/
def atomNoBlake : Atom → Bool
  | .blake2s .. => false
  | _ => true

/-- An atom other than `BLAKE2S` holds under any semantics as it does deployed. -/
theorem atom_holdsB_noBlake {a : Atom} (h : atomNoBlake a = true) : a.HoldsB S rd σ ↔ a.Holds rd σ := by
  cases a <;> first | rfl | exact absurd h (by simp [atomNoBlake])

/-- A run of atoms other than `BLAKE2S` holds under any semantics as it does deployed. -/
theorem forall_holdsB_noBlake {as : List Atom} (h : as.all atomNoBlake = true) :
    (∀ a ∈ as, a.HoldsB S rd σ) ↔ ∀ a ∈ as, a.Holds rd σ := by
  rw [List.all_eq_true] at h
  exact forall₂_congr fun a ha => atom_holdsB_noBlake (h a ha)

/-- A `ret` under `S` hands its words to the continuation (`holdsList_ret`). -/
theorem holdsListB_ret (vs : List V) (next : Prop) (rets : List E) :
    Stmt.HoldsListB S C rd σ [.ret vs] next (fun rs => rs = rets) ↔ vs.map σ = rets := Iff.rfl

/-- Return-free blocks indexed by `i < n`, then the rest, under any semantics. -/
theorem holdsListB_flatMap (n : ℕ) (f : ℕ → List Stmt) (hf : ∀ i, Stmt.noRetList (f i) = true)
    (rest : List Stmt) (next : Prop) (kret : List E → Prop) :
    Stmt.HoldsListB S C rd σ ((List.range n).flatMap f ++ rest) next kret ↔
      (∀ i < n, Stmt.HoldsListB S C rd σ (f i) True kret) ∧
        Stmt.HoldsListB S C rd σ rest next kret := by
  rw [holdsListB_append, List.flatMap_def, holdsListB_flatten _ (fun b hb => by
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hb; exact hf i)]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]

/-- A function's relation under `S`, unfolded: its body under `Program.RelB`. -/
theorem relB_of_find {f : String} {fn : Fn} (h : coreProgram.find? f = some fn)
    (args rets : List E) :
    coreProgram.RelB S rd f args rets ↔ fn.SemB S (coreProgram.RelB S rd) rd args rets := by
  rw [relB_iff]
  constructor
  · rintro ⟨fn', h', hs⟩
    rw [h] at h'
    cases h'
    exact hs
  · exact fun hs => ⟨fn, h, hs⟩

/-- **A `mul_range` loop helper, forward, under any semantics** (`loop_iff`): its relation from
`g^k` makes its end `N` the first `g^m`, `m > k`, the loop reaches, its body holding at every
`g^j`, `k ≤ j < m`. -/
theorem loopB_fwd {f : String} {ps : List E} {N : E} {B : CallRel → E → Prop}
    (hmono : ∀ C C' x, CallRel.Le C C' → B C x → B C' x)
    (hstep : ∀ C x, (∃ fn, coreProgram.find? f = some fn ∧ fn.SemB S C rd (x :: ps) []) →
      B C x ∧ IsInK (x * gen + N) ∧ (x * gen + N ≠ 0 → C f (x * gen :: ps) []))
    (k : ℕ) (h : coreProgram.RelB S rd f (gen ^ k :: ps) []) :
    ∃ m, k < m ∧ N = gen ^ m ∧ (∀ j, k < j → j < m → gen ^ j ≠ N) ∧
      ∀ j, k ≤ j → j < m → B (coreProgram.RelB S rd) (gen ^ j) := by
  have hadd : ∀ j, gen ^ j * gen + N = 0 ↔ N = gen ^ (j + 1) := fun j => by
    rw [e_add_eq_zero_iff, pow_succ, eq_comm]
  obtain ⟨d, hd⟩ := h
  induction d generalizing k with
  | zero => exact hd.elim
  | succ d ih =>
    obtain ⟨hB, -, hnext⟩ := hstep _ _ hd
    have hB' := hmono _ _ _ (relNB_le_rel coreProgram d) hB
    by_cases h0 : gen ^ k * gen + N = 0
    · refine ⟨k + 1, by omega, (hadd k).mp h0, fun j h1 h2 => by omega, fun j h1 h2 => ?_⟩
      rwa [show j = k by omega]
    · have := hnext h0
      rw [← pow_succ] at this
      obtain ⟨m, hm, hN, hfirst, hall⟩ := ih (k + 1) this
      refine ⟨m, by omega, hN, fun j h1 h2 => ?_, fun j h1 h2 => ?_⟩
      · rcases Nat.lt_or_ge (k + 1) j with h | h
        · exact hfirst j h h2
        · rw [show j = k + 1 by omega]
          intro he
          exact h0 ((hadd k).mpr he.symm)
      · rcases Nat.lt_or_ge k j with h | h
        · exact hall j (by omega) h2
        · rwa [show j = k by omega]

end Blocks

/-! ## Runs of `BLAKE2S` rows -/

/-- **`n` chained `BLAKE2S` rows under `S`** from the cells `st` to the cells `out`: states
`sts 0 = st`, …, `sts n = out`, row `j` checked on block `j` from `sts j` to `sts (j + 1)` under
the metadata cell `md j`. -/
def ChainSteps (S : BlakeSem) (st : E × E) (blocks : ℕ → Fin 4 → E) (md : ℕ → E) (n : ℕ)
    (out : E × E) : Prop :=
  ∃ sts : ℕ → E × E, sts 0 = st ∧ sts n = out ∧
    ∀ j < n, S.check (blocks j) (sts j).1 (sts j).2 (sts (j + 1)).1 (sts (j + 1)).2 (md j)

section Steps

variable {S : BlakeSem} {M : HashModel}

/-- A family of chained rows is a run. -/
theorem chainSteps_of_steps {n : ℕ} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {st : ℕ → E × E}
    (hc : ∀ j < n, S.check (blocks j) (st j).1 (st j).2 (st (j + 1)).1 (st (j + 1)).2 (md j)) :
    ChainSteps S (st 0) blocks md n (st n) :=
  ⟨st, rfl, rfl, hc⟩

/-- A run of no rows ends where it starts. -/
theorem chainSteps_zero {st out : E × E} {blocks : ℕ → Fin 4 → E} {md : ℕ → E}
    (h : ChainSteps S st blocks md 0 out) : out = st := by
  obtain ⟨sts, h0, hn, -⟩ := h
  rw [← hn, h0]

/-- A run depends only on its first `n` blocks and metadata cells. -/
theorem chainSteps_congr {st out : E × E} {b b' : ℕ → Fin 4 → E} {md md' : ℕ → E} {n : ℕ}
    (hb : ∀ j < n, b j = b' j) (hm : ∀ j < n, md j = md' j) :
    ChainSteps S st b md n out ↔ ChainSteps S st b' md' n out := by
  constructor
  · rintro ⟨sts, h0, hn, hc⟩
    exact ⟨sts, h0, hn, fun j hj => by rw [← hb j hj, ← hm j hj]; exact hc j hj⟩
  · rintro ⟨sts, h0, hn, hc⟩
    exact ⟨sts, h0, hn, fun j hj => by rw [hb j hj, hm j hj]; exact hc j hj⟩

/-- The blocks and metadata cells of a run under a model are canonical. -/
theorem ChainSteps.canonical {st out : E × E} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {n : ℕ}
    (h : ChainSteps M.sem st blocks md n out) :
    ∀ j < n, (∀ r, IsCanonical128 (blocks j r)) ∧ IsCanonical128 (md j) := by
  obtain ⟨sts, -, -, hc⟩ := h
  intro j hj
  have := M.canonical (hc j hj)
  exact ⟨this.1, this.2.2.2.2.2⟩

/-- **A run at the counters after a prefix extends it** (`chainRun_nonfinal` from a prefix,
`HashModel.prefix_run`). -/
theorem ChainSteps.prefix {bs : List (List UInt8)} {st out : E × E} {blocks : ℕ → Fin 4 → E}
    {md : ℕ → E} {n : ℕ} (hp : M.Prefix bs st) (h : ChainSteps M.sem st blocks md n out)
    (hmd : ∀ j < n, md j = metadataCell (64 * (bs.length + j + 1)) false) :
    M.Prefix (bs ++ (List.range n).map fun j => blockBytes (blocks j)) out := by
  obtain ⟨sts, h0, hn, hc⟩ := h
  rw [← hn]
  exact HashModel.prefix_run (st := sts) (by rw [h0]; exact hp) hmd hc

/-- **A whole run from the IV** (`chain_eq_blake2sBytes_blocks`): `n + 1` blocks, the last final,
give the answered hash of their bytes (`HashModel.chain_blocks`). -/
theorem ChainSteps.blocks {n : ℕ} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {out : E × E}
    (h : ChainSteps M.sem ivCells blocks md (n + 1) out)
    (hmd : ∀ j < n, md j = metadataCell (64 * (j + 1)) false)
    (hfin : md n = metadataCell (64 * (n + 1)) true) :
    ∃ d, M.H ((List.range (n + 1)).flatMap fun j => blockBytes (blocks j)) = some d ∧
      out = digestScalars d := by
  obtain ⟨sts, h0, hn, hc⟩ := h
  rw [← hn]
  exact HashModel.chain_blocks h0 hmd hfin fun j hj => hc j (by omega)

/-- Two runs, the second from the first's end, are one. -/
theorem ChainSteps.append {st mid out : E × E} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {n m : ℕ}
    (h1 : ChainSteps S st blocks md n mid)
    (h2 : ChainSteps S mid (fun j => blocks (n + j)) (fun j => md (n + j)) m out) :
    ChainSteps S st blocks md (n + m) out := by
  obtain ⟨s1, a0, an, ac⟩ := h1
  obtain ⟨s2, b0, bm, bc⟩ := h2
  refine ⟨fun j => if j ≤ n then s1 j else s2 (j - n), by simp [a0], ?_, fun j hj => ?_⟩
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp only [Nat.add_zero, le_refl, ↓reduceIte]
      rw [an, ← bm, b0]
    · simp only [show ¬(n + m ≤ n) by omega, ↓reduceIte, Nat.add_sub_cancel_left, bm]
  · rcases Nat.lt_or_ge j n with h | h
    · simp only [show j ≤ n by omega, show j + 1 ≤ n by omega, ↓reduceIte]
      exact ac j h
    · have := bc (j - n) (by omega)
      simp only [show n + (j - n) = j by omega, show j - n + 1 = j + 1 - n by omega] at this
      simp only [show ¬(j + 1 ≤ n) by omega, ↓reduceIte]
      rcases Nat.eq_or_lt_of_le h with rfl | h'
      · simp only [le_refl, ↓reduceIte]
        rw [an, ← b0]
        simpa using this
      · simp only [show ¬(j ≤ n) by omega, ↓reduceIte]
        exact this

/-- At the deployed semantics a run is a `ChainCells` run. -/
theorem chainCells_of_chainSteps {st out : E × E} {blocks : ℕ → Fin 4 → E} {md : ℕ → E} {n : ℕ}
    (h : ChainSteps blakeDeployed st blocks md n out) : ChainCells st blocks md n out := by
  obtain ⟨sts, h0, hn, hc⟩ := h
  rw [← h0, ← hn]
  exact chainCells_of_steps hc

end Steps

/-! ## Answered hashes -/

/-- **The model answers the hash of `x` with a digest whose cells are `c`.** -/
def Ans (M : HashModel) (x : List UInt8) (c : E × E) : Prop :=
  ∃ d, M.H x = some d ∧ c = digestScalars d

/-- The model's digest of `x`, `default` where it does not answer. -/
def ansD (M : HashModel) (x : List UInt8) : Digest := (M.H x).getD default

/-- An answered hash is the model's digest of its input (`ansD`). -/
theorem Ans.eq {M : HashModel} {x : List UInt8} {c : E × E} (h : Ans M x c) :
    M.H x = some (ansD M x) ∧ c = digestScalars (ansD M x) := by
  obtain ⟨d, hd, rfl⟩ := h
  simp [ansD, hd]

/-- The model's digest of an answered input is the answer. -/
theorem ansD_of {M : HashModel} {x : List UInt8} {d : Digest} (h : M.H x = some d) :
    ansD M x = d := by
  simp [ansD, h]


/-! ## Prefixes of a list of cells -/

/-- The bytes of the first `k` blocks of the cells `cs`. -/
def prefixBlocks (cs : List E) (k : ℕ) : List (List UInt8) :=
  (List.range k).map fun j => blockBytes (blocksOf cs j)

/-- The first `k` blocks are `k` blocks. -/
theorem length_prefixBlocks (cs : List E) (k : ℕ) : (prefixBlocks cs k).length = k := by
  simp [prefixBlocks]

/-- No blocks. -/
theorem prefixBlocks_zero (cs : List E) : prefixBlocks cs 0 = [] := rfl

/-- The first `k + m` blocks: the first `k`, then the `m` after them. -/
theorem prefixBlocks_add (cs : List E) (k m : ℕ) :
    prefixBlocks cs (k + m) =
      prefixBlocks cs k ++ (List.range m).map fun j => blockBytes (blocksOf cs (k + j)) := by
  rw [prefixBlocks, List.range_add, List.map_append, List.map_map]
  rfl

section Prefix

variable {M : HashModel}

/-- **A run of `m` blocks from block `k`** (`claims_window`, `claims_tail`), forward: from a
prefix of the first `k` blocks, under the counters `64·k + 64·(j + 1)`, a run reaches a prefix of
the first `k + m`, over canonical blocks (`chainCells_prefix`'s forward direction). -/
theorem chainSteps_prefix {cs : List E} {k m : ℕ} {st out : E × E} {b : ℕ → Fin 4 → E}
    {md : ℕ → E} (hp : M.Prefix (prefixBlocks cs k) st)
    (hb : ∀ j < m, b j = blocksOf cs (k + j))
    (hmd : ∀ j < m, md j = metadataCell (64 * k + 64 * (j + 1)) false)
    (h : ChainSteps M.sem st b md m out) :
    (∀ j < m, ∀ r, IsCanonical128 (blocksOf cs (k + j) r)) ∧
      M.Prefix (prefixBlocks cs (k + m)) out := by
  refine ⟨fun j hj r => by rw [← hb j hj]; exact (h.canonical j hj).1 r, ?_⟩
  have := h.prefix hp (fun j hj => by
    rw [hmd j hj, length_prefixBlocks]; congr 1; ring)
  rw [prefixBlocks_add]
  convert this using 2
  exact List.map_congr_left fun j hj => by rw [hb j (List.mem_range.mp hj)]

end Prefix

end
end LeanVM.Guest.B1.Digest
