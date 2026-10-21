/-
  LeanVM.E2E.Complete.Table

  The honest table of the idealized system's completeness (T6-det): for a hash `H` and the byte
  strings `D` a node hashes, the `BLAKE2S` rows of their standard chains, every intermediate
  chaining value a fresh code of its prefix; such rows pass V_I's precheck and table check.
-/

module

public import LeanVM.E2E.Statement
public import LeanVM.Protocol.Verifier.Load

/-!
# The honest table

V_I (`LeanVM/E2E/Statement.lean`, `docs/roadmap/e2e-security.md` §2) checks each candidate's
`BLAKE2S` rows: the precheck (`Precheck`: non-final rows with equal outputs have equal inputs) and
the table check with the hash `H` (`tableOKWith`: every standard chain of a string `x` among the
rows ends at `H x`). The honest prover of T6-det (`docs/roadmap/t6-completeness.md`) fills the rows
of a node's execution by the stateful rule of §4 T6-det: a final row outputs `H` of the whole
string, a non-final row a fresh code of the block prefix it absorbed. This module defines those
rows and proves that they pass both checks, for every `H`.

* `nBlocks`, `blockAt`, `prefixAt`, `tailOf`: the whole blocks and the rest of a string, as a
  standard chain reads them (`StdChain`); `eq_of_prefix_tail`: a string is its blocks and its tail.
* `Intermediates D`: the codes of the non-empty block prefixes of the strings `D` (`prefixesOf D`),
  injective there and never the IV (`exists_intermediates`: one exists below `2^64` prefixes);
  `Intermediates.stD p` is the chaining value after the prefix `p` (the IV after none).
* `ChainRow I H r`: `r` is a row of the standard chain of a string of `D` under the codes, its
  final row output `H` of the string; `chainSem I H` is the semantics accepting exactly the
  canonical chain rows.
* `stdChain_chainRows`: **every standard chain of chain rows is the chain of a string of `D`** and
  ends at its `H`; so the rows pass the table check (`tableOK_chainRows`), their chain inputs are
  among `D` (`chainInputs_subset`), they pass the precheck (`precheck_chainRows`), and V_I's
  `tableOKWith` accepts them (`tableOKWith_chainRows`).
* `chainSem_functional`: the semantics is a function of the row's inputs (the guest's compiled
  code shares equal compressions).
* `blakeRows_of_validB`, `haltingRunB_of_validB`: an execution valid under a semantics of canonical
  rows is the one V_I re-runs under the Flock-blind semantics (`candidateRun`), and its rows are
  rows of that semantics.
-/

namespace LeanVM.E2E.Complete

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Guest.Value LeanVM.Protocol.Verifier LeanVM.Protocol.Compile

@[expose] public section

/-! ## Bytes, words and cells -/

/-- The four bytes of a little-endian word are its bytes. -/
theorem wordBytes_leWord (b0 b1 b2 b3 : UInt8) : wordBytes (leWord b0 b1 b2 b3) = [b0, b1, b2, b3] := by
  have h := wordBytes_wordOfBytes b0 b1 b2 b3
  generalize wordOfBytes b0 b1 b2 b3 = w at h
  simp only [wordBytes, List.cons.injEq, and_true] at h
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  rw [leWord_wordBytes]
  rfl

/-- Two byte strings with the same block words agree on their first 64 bytes. -/
theorem getD_eq_of_blockWords_eq {b b' : List UInt8} (h : blockWords b = blockWords b') {n : ℕ}
    (hn : n < 64) : b.getD n 0 = b'.getD n 0 := by
  have hq : n / 4 < 16 := by omega
  have e := congrArg (fun v : Vector UInt32 16 ↦ wordBytes v[n / 4]) h
  simp only [blockWords_getElem _ _ hq, wordBytes_leWord, List.cons.injEq, and_true] at e
  obtain ⟨e0, e1, e2, e3⟩ := e
  have hn' : n = 4 * (n / 4) + n % 4 := (Nat.div_add_mod n 4).symm
  have hr : n % 4 < 4 := Nat.mod_lt _ (by norm_num)
  generalize n % 4 = k at hn' hr
  rw [hn']
  interval_cases k
  · exact e0
  · exact e1
  · exact e2
  · exact e3

/-- **Block words determine a block**: two strings of the same length, at most 64 bytes, with the
same block words are equal. -/
theorem eq_of_blockWords_eq {b b' : List UInt8} (h : blockWords b = blockWords b')
    (hl : b.length = b'.length) (h64 : b.length ≤ 64) : b = b' := by
  apply List.ext_getElem hl
  intro n h1 h2
  have := getD_eq_of_blockWords_eq h (n := n) (by omega)
  simpa only [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1,
    List.getElem?_eq_getElem h2, Option.getD_some] using this

/-- The message words of four cells, split. -/
theorem cellWords_eq_of_messageWords_eq {m m' : Fin 4 → E} (h : messageWords m = messageWords m')
    (i : Fin 4) : cellWords (m i) = cellWords (m' i) := by
  have e := congrArg Vector.toList h
  simp only [messageWords, Vector.toList_append] at e
  obtain ⟨e, e3⟩ := List.append_inj e (by simp)
  obtain ⟨e, e2⟩ := List.append_inj e (by simp)
  obtain ⟨e0, e1⟩ := List.append_inj e (by simp)
  fin_cases i
  · exact Vector.toList_inj.mp e0
  · exact Vector.toList_inj.mp e1
  · exact Vector.toList_inj.mp e2
  · exact Vector.toList_inj.mp e3

/-- **Canonical cells are their block's bytes**: canonical message cells with the same bytes are
equal. -/
theorem eq_of_blockBytes_eq {m m' : Fin 4 → E} (hm : ∀ i, IsCanonical128 (m i))
    (hm' : ∀ i, IsCanonical128 (m' i)) (h : blockBytes m = blockBytes m') : m = m' := by
  have hw : messageWords m = messageWords m' := by
    rw [messageWords_eq_blockWords, messageWords_eq_blockWords, h]
  funext i
  rw [← wordsCell_cellWords (hm i), ← wordsCell_cellWords (hm' i),
    cellWords_eq_of_messageWords_eq hw i]

/-- The cells of a digest give it back. -/
theorem digest_of_cells {a b : E} {d : Digest} (h : (a, b) = digestScalars d) :
    cellWords a ++ cellWords b = d := by
  rw [show a = (digestScalars d).1 from congrArg Prod.fst h,
    show b = (digestScalars d).2 from congrArg Prod.snd h, cellWords_digestScalars]

/-- The last-block flag is not the empty flag. -/
theorem lastBlock_ne_zero : lastBlock ≠ 0 := by decide

/-- Lengths agreeing modulo `2^64`, within 64 of a common multiple of 64, are equal. -/
theorem eq_of_toUInt64_eq {n a b : ℕ} (ha : a ≤ 64) (hb : b ≤ 64)
    (h : (64 * n + a).toUInt64 = (64 * n + b).toUInt64) : a = b := by
  have e := congrArg UInt64.toNat h
  simp only [Nat.toUInt64_eq, UInt64.toNat_ofNat'] at e
  rcases Nat.le_total a b with hab | hab
  · have := Nat.sub_mod_eq_zero_of_mod_eq e.symm
    rw [show 64 * n + b - (64 * n + a) = b - a by omega] at this
    have := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero this) (by omega)
    omega
  · have := Nat.sub_mod_eq_zero_of_mod_eq e
    rw [show 64 * n + a - (64 * n + b) = a - b by omega] at this
    have := Nat.eq_zero_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero this) (by omega)
    omega

/-! ## The blocks of a string -/

/-- The whole blocks a standard chain absorbs before its last row: `(|x| − 1)/64`. -/
def nBlocks (x : Bytes) : ℕ := (x.length - 1) / 64

/-- Block `i` of a string: bytes `64i .. 64i + 63`. -/
def blockAt (x : Bytes) (i : ℕ) : List UInt8 := (x.drop (64 * i)).take 64

/-- The first `i` blocks of a string. -/
def prefixAt (x : Bytes) (i : ℕ) : List (List UInt8) := (List.range i).map (blockAt x)

/-- The rest of a string after its whole blocks: what the last row compresses, zero-filled. -/
def tailOf (x : Bytes) : List UInt8 := x.drop (64 * nBlocks x)

@[simp] theorem prefixAt_zero (x : Bytes) : prefixAt x 0 = [] := rfl

theorem prefixAt_succ (x : Bytes) (i : ℕ) : prefixAt x (i + 1) = prefixAt x i ++ [blockAt x i] := by
  simp only [prefixAt, List.range_succ, List.map_append, List.map_cons, List.map_nil]

@[simp] theorem length_prefixAt (x : Bytes) (i : ℕ) : (prefixAt x i).length = i := by
  simp [prefixAt]

/-- Equal prefixes have equal lengths. -/
theorem eq_of_prefixAt_eq {x y : Bytes} {i j : ℕ} (h : prefixAt x i = prefixAt y j) : i = j := by
  simpa using congrArg List.length h

/-- Equal prefixes of one more block: the same block count, prefix and last block. -/
theorem prefixAt_succ_inj {x y : Bytes} {i j : ℕ} (h : prefixAt x (i + 1) = prefixAt y (j + 1)) :
    i = j ∧ prefixAt x i = prefixAt y j ∧ blockAt x i = blockAt y j := by
  obtain rfl : i = j := by have := eq_of_prefixAt_eq h; omega
  rw [prefixAt_succ, prefixAt_succ] at h
  obtain ⟨h1, h2⟩ := List.append_inj' h rfl
  exact ⟨rfl, h1, List.singleton_inj.mp h2⟩

/-- A whole block has 64 bytes. -/
theorem length_blockAt {x : Bytes} {i : ℕ} (hi : i < nBlocks x) : (blockAt x i).length = 64 := by
  unfold nBlocks at hi
  simp only [blockAt, List.length_take, List.length_drop]
  omega

/-- The rest has the length the last row's counter counts past the whole blocks. -/
theorem length_tailOf (x : Bytes) : (tailOf x).length = x.length - 64 * nBlocks x := by
  simp [tailOf]

theorem length_tailOf_le (x : Bytes) : (tailOf x).length ≤ 64 := by
  rw [length_tailOf]
  unfold nBlocks
  omega

/-- The first `i` whole blocks are the first `64 i` bytes. -/
theorem flatten_prefixAt (x : Bytes) : ∀ i, 64 * i ≤ x.length →
    (prefixAt x i).flatten = x.take (64 * i)
  | 0, _ => by simp
  | i + 1, h => by
    rw [prefixAt_succ, List.flatten_append, flatten_prefixAt x i (by omega), List.flatten_singleton,
      blockAt, show 64 * (i + 1) = 64 * i + 64 by ring, List.take_add]

/-- **A string is its whole blocks and its rest.** -/
theorem eq_flatten_tailOf (x : Bytes) : x = (prefixAt x (nBlocks x)).flatten ++ tailOf x := by
  rw [flatten_prefixAt x _ (by unfold nBlocks; omega), tailOf, List.take_append_drop]

/-- Two strings with the same whole blocks, the same length modulo `2^64` and the same words of
their rest are equal. -/
theorem eq_of_prefix_tail {x y : Bytes} (hp : prefixAt x (nBlocks x) = prefixAt y (nBlocks y))
    (hl : x.length.toUInt64 = y.length.toUInt64) (hw : blockWords (tailOf x) = blockWords (tailOf y)) :
    x = y := by
  have hn := eq_of_prefixAt_eq hp
  have hx := length_tailOf x
  have hy := length_tailOf y
  have hx' := length_tailOf_le x
  have hy' := length_tailOf_le y
  have hlen : (tailOf x).length = (tailOf y).length := by
    have hxl : x.length = 64 * nBlocks x + (tailOf x).length := by
      unfold nBlocks at hx ⊢; omega
    have hyl : y.length = 64 * nBlocks x + (tailOf y).length := by
      rw [hn]; unfold nBlocks at hy ⊢; omega
    rw [hxl, hyl] at hl
    exact eq_of_toUInt64_eq hx' hy' hl
  rw [eq_flatten_tailOf x, eq_flatten_tailOf y, hp, eq_of_blockWords_eq hw hlen hx']

/-! ## The intermediate chaining values -/

/-- The non-empty whole-block prefixes of the strings `D`: the inputs of their chains' non-final
rows' outputs. -/
def prefixesOf (D : List Bytes) : List (List (List UInt8)) :=
  D.flatMap fun x ↦ (List.range (nBlocks x)).map fun i ↦ prefixAt x (i + 1)

/-- A prefix of a string of `D`, non-empty and of whole blocks, is one of `D`'s prefixes. -/
theorem mem_prefixesOf {D : List Bytes} {x : Bytes} (hx : x ∈ D) {j : ℕ} (hj : 0 < j)
    (hj' : j ≤ nBlocks x) : prefixAt x j ∈ prefixesOf D := by
  simp only [prefixesOf, List.mem_flatMap, List.mem_map, List.mem_range]
  exact ⟨x, hx, j - 1, by omega, by rw [Nat.sub_add_cancel hj]⟩

/-- **Codes for the intermediate chaining values** of the strings `D`: injective on their prefixes,
never the IV. -/
structure Intermediates (D : List Bytes) where
  /-- The code of a prefix. -/
  ι : List (List UInt8) → Digest
  /-- Distinct prefixes have distinct codes. -/
  inj : ∀ p ∈ prefixesOf D, ∀ p' ∈ prefixesOf D, ι p = ι p' → p = p'
  /-- No code is the IV. -/
  ne_iv : ∀ p ∈ prefixesOf D, ι p ≠ paramIv

namespace Intermediates

variable {D : List Bytes} (I : Intermediates D)

/-- The chaining value after the prefix `p`: the IV after none, its code after one. -/
def stD (p : List (List UInt8)) : Digest := if p = [] then paramIv else I.ι p

/-- The chaining value's cells. -/
def st (p : List (List UInt8)) : E × E := digestScalars (I.stD p)

variable {I}

/-- **The chaining value after a prefix determines it**, among the prefixes of `D`'s strings. -/
theorem stD_inj {x x' : Bytes} (hx : x ∈ D) (hx' : x' ∈ D) {j j' : ℕ} (hj : j ≤ nBlocks x)
    (hj' : j' ≤ nBlocks x') (h : I.stD (prefixAt x j) = I.stD (prefixAt x' j')) :
    prefixAt x j = prefixAt x' j' := by
  rcases Nat.eq_zero_or_pos j with rfl | hj0 <;> rcases Nat.eq_zero_or_pos j' with rfl | hj0'
  · rfl
  · have hm := mem_prefixesOf hx' hj0' hj'
    have hne : prefixAt x' j' ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    simp only [stD, prefixAt_zero, ↓reduceIte, hne] at h
    exact absurd h.symm (I.ne_iv _ hm)
  · have hm := mem_prefixesOf hx hj0 hj
    have hne : prefixAt x j ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    simp only [stD, prefixAt_zero, ↓reduceIte, hne] at h
    exact absurd h (I.ne_iv _ hm)
  · have hm := mem_prefixesOf hx hj0 hj
    have hm' := mem_prefixesOf hx' hj0' hj'
    have hne : prefixAt x j ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    have hne' : prefixAt x' j' ≠ [] := by
      intro e; have := congrArg List.length e; simp at this; omega
    simp only [stD, hne, hne', ↓reduceIte] at h
    exact I.inj _ hm _ hm' h

/-- The cells after a prefix are canonical. -/
theorem isCanonical_st (p : List (List UInt8)) :
    IsCanonical128 (I.st p).1 ∧ IsCanonical128 (I.st p).2 :=
  isCanonical128_digestScalars _

/-- After the empty prefix: the IV's cells. -/
theorem st_nil : I.st [] = ivCells := by simp [st, stD, ivCells]

end Intermediates

/-- A code of a number below `2^64` in the last two words, the first word zero. -/
def codeOf (k : ℕ) : Digest :=
  #v[0, 0, 0, 0, 0, 0, (k % 2 ^ 32).toUInt32, (k / 2 ^ 32).toUInt32]

theorem codeOf_ne_paramIv (k : ℕ) : codeOf k ≠ paramIv := by
  intro h
  have h0 : (0 : UInt32) = paramIv[0] := by rw [← h]; rfl
  exact absurd h0 (by decide)

theorem codeOf_inj {k k' : ℕ} (hk : k < 2 ^ 64) (hk' : k' < 2 ^ 64) (h : codeOf k = codeOf k') :
    k = k' := by
  have e6 := congrArg (fun v : Digest ↦ (v[6]).toNat) h
  have e7 := congrArg (fun v : Digest ↦ (v[7]).toNat) h
  simp only [codeOf, Nat.toUInt32_eq, UInt32.toNat_ofNat', Vector.getElem_mk,
    List.getElem_toArray, List.getElem_cons_succ, List.getElem_cons_zero] at e6 e7
  rw [Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num)), Nat.mod_eq_of_lt (Nat.mod_lt _ (by norm_num))]
    at e6
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at e7
  rw [← Nat.div_add_mod k (2 ^ 32), ← Nat.div_add_mod k' (2 ^ 32), e6, e7]

/-- **Codes exist** for fewer than `2^64` prefixes: a prefix's index among them. -/
noncomputable def intermediatesOf (D : List Bytes) (hD : (prefixesOf D).length < 2 ^ 64) :
    Intermediates D where
  ι p := codeOf ((prefixesOf D).idxOf p)
  inj p hp p' hp' h := by
    have hi := List.idxOf_lt_length_of_mem hp
    have hi' := List.idxOf_lt_length_of_mem hp'
    have := codeOf_inj (by omega) (by omega) h
    rw [← List.getElem_idxOf hi, ← List.getElem_idxOf hi']
    simp only [this]
  ne_iv _ _ := codeOf_ne_paramIv _

/-! ## The rows of the honest table -/

variable {D : List Bytes}

/-- **A row of the honest table**: a row of the standard chain of a string `x` of `D` under the
codes `I`, its non-final rows from the code after block `i` to the code after block `i + 1`, its
last row from the code after the whole blocks to `H x`. -/
def ChainRow (I : Intermediates D) (H : Bytes → Digest) (r : BlakeRow) : Prop :=
  ∃ x ∈ D,
    (∃ i < nBlocks x, blockBytes r.m = blockAt x i ∧ (r.cv0, r.cv1) = I.st (prefixAt x i) ∧
      (r.out0, r.out1) = I.st (prefixAt x (i + 1)) ∧ r.md = metadataCell (64 * (i + 1)) false) ∨
    (blockBytes r.m = tailOf x ++ List.replicate (64 - (tailOf x).length) 0 ∧
      (r.cv0, r.cv1) = I.st (prefixAt x (nBlocks x)) ∧ (r.out0, r.out1) = digestScalars (H x) ∧
      r.md = metadataCell x.length true)

/-- The row's cells are canonical. -/
def CanonRow (r : BlakeRow) : Prop := CanonicalCells r.m r.cv0 r.cv1 r.out0 r.out1 r.md

/-- **The honest table's semantics**: a `BLAKE2S` instruction checks when its cells are canonical
and it is a row of the honest table. -/
noncomputable def chainSem (I : Intermediates D) (H : Bytes → Digest) : BlakeSem where
  check m cv0 cv1 out0 out1 md :=
    CanonicalCells m cv0 cv1 out0 out1 md ∧ ChainRow I H ⟨m, cv0, cv1, out0, out1, md⟩
  dec _ _ _ _ _ _ := Classical.dec _

variable {I : Intermediates D} {H : Bytes → Digest}

/-- A row of the semantics is canonical and a chain row. -/
theorem chainSem_row {r : BlakeRow} : (chainSem I H).row r ↔ CanonRow r ∧ ChainRow I H r :=
  Iff.rfl

/-- A row's chaining value, read off the cells of a prefix. -/
theorem cv_of_st {r : BlakeRow} {p : List (List UInt8)} (h : (r.cv0, r.cv1) = I.st p) :
    r.cv = I.stD p :=
  digest_of_cells h

/-- A row's output, read off the cells of a prefix. -/
theorem out_of_st {r : BlakeRow} {p : List (List UInt8)} (h : (r.out0, r.out1) = I.st p) :
    r.out = I.stD p :=
  digest_of_cells h

/-- The counter and flags of a metadata cell. -/
theorem unpackMetadata_eq {md : E} {c : ℕ} {f : Bool} (h : md = metadataCell c f) :
    unpackMetadata md = (c.toUInt64, if f then lastBlock else 0, 0) := by
  rw [h, unpackMetadata_metadataCell]

/-! ## Standard chains of the honest table -/

/-- Row `i < nBlocks y` of a standard chain of `y` of chain rows: a non-final row of a string of
`D` with the same first `i + 1` blocks, its output the code after them. The chaining value of
row `i ≤ nBlocks y` is the code after `y`'s first `i` blocks, which are a string of `D`'s. -/
theorem stdChain_cv {y : Bytes} {c : List BlakeRow} (hc : StdChain y c)
    (hrows : ∀ r ∈ c, ChainRow I H r) :
    ∀ i (hi : i ≤ nBlocks y), ∃ x ∈ D, i ≤ nBlocks x ∧ prefixAt x i = prefixAt y i ∧
      (c[i]'(by rw [hc.1]; unfold nBlocks at hi; omega)).cv = I.stD (prefixAt y i)
  | 0, hi => by
    have hlen : 0 < c.length := by rw [hc.1]; omega
    obtain ⟨x, hx, -⟩ := hrows _ (List.getElem_mem hlen)
    refine ⟨x, hx, Nat.zero_le _, rfl, ?_⟩
    have := hc.2.1 0 hlen
    simp only [↓reduceDIte] at this
    rw [this]
    simp [Intermediates.stD]
  | i + 1, hi => by
    have hlen : i + 1 < c.length := by rw [hc.1]; unfold nBlocks at hi; omega
    obtain ⟨x', hx', hi', hp', hcv'⟩ := stdChain_cv hc hrows i (by omega)
    obtain ⟨x, hx, hrow⟩ := hrows _ (List.getElem_mem (show i < c.length by omega))
    obtain ⟨hmw, hmd⟩ := hc.2.2.1 i hlen
    rcases hrow with ⟨j, hj, hm, hcv, hout, hmd'⟩ | ⟨-, -, -, hmd'⟩
    · have hji := stD_cv_eq hx hx' hj hi' hcv hp' hcv'
      obtain rfl : j = i := eq_of_prefixAt_eq hji
      have hb : blockAt x j = blockAt y j := by
        refine eq_of_blockWords_eq ?_ (by rw [length_blockAt hj, length_blockAt (by omega)])
          (by rw [length_blockAt hj])
        rw [← hm, ← messageWords_eq_blockWords, hmw]
        rfl
      have hpre : prefixAt x (j + 1) = prefixAt y (j + 1) := by
        rw [prefixAt_succ, prefixAt_succ, hji, hb]
      refine ⟨x, hx, hj, hpre, ?_⟩
      have hl := hc.2.1 (j + 1) hlen
      simp only [Nat.add_one_ne_zero, ↓reduceDIte, Nat.add_sub_cancel] at hl
      rw [hl, out_of_st hout, hpre]
    · rw [unpackMetadata_eq hmd'] at hmd
      simp only [↓reduceIte, Prod.mk.injEq] at hmd
      exact absurd hmd.2.1 lastBlock_ne_zero
where
  /-- Two chain rows' chaining values agree only after equal prefixes. -/
  stD_cv_eq {x x' : Bytes} (hx : x ∈ D) (hx' : x' ∈ D) {j i : ℕ} (hj : j < nBlocks x)
      (hi' : i ≤ nBlocks x') {r : BlakeRow} (hcv : (r.cv0, r.cv1) = I.st (prefixAt x j))
      {y : Bytes} (hp' : prefixAt x' i = prefixAt y i) (hcv' : r.cv = I.stD (prefixAt y i)) :
      prefixAt x j = prefixAt y i := by
    rw [← hp'] at hcv' ⊢
    exact Intermediates.stD_inj hx hx' (le_of_lt hj) hi' ((cv_of_st hcv).symm.trans hcv')

/-- **Every standard chain of chain rows is the chain of a string of `D`**, ending at its hash. -/
theorem stdChain_chainRows {y : Bytes} {c : List BlakeRow} (hc : StdChain y c)
    (hrows : ∀ r ∈ c, ChainRow I H r) (hpos : 0 < c.length) :
    y ∈ D ∧ (c[c.length - 1]'(by omega)).out = H y := by
  have hn : c.length - 1 = nBlocks y := by rw [hc.1]; rfl
  obtain ⟨x', hx', hn', hp', hcv'⟩ := stdChain_cv hc hrows (c.length - 1) hn.le
  obtain ⟨hmw, hmd⟩ := hc.2.2.2 hpos
  obtain ⟨x, hx, hrow⟩ := hrows _ (List.getElem_mem (show c.length - 1 < c.length by omega))
  rcases hrow with ⟨j, -, -, -, -, hmd'⟩ | ⟨hm, hcv, hout, hmd'⟩
  · rw [unpackMetadata_eq hmd'] at hmd
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at hmd
    exact absurd hmd.2.1.symm lastBlock_ne_zero
  · have hpre : prefixAt x (nBlocks x) = prefixAt y (nBlocks y) := by
      rw [← hn, ← hp']
      refine Intermediates.stD_inj (I := I) hx hx' le_rfl hn' ?_
      rw [← cv_of_st hcv, hcv', hp']
    rw [unpackMetadata_eq hmd'] at hmd
    simp only [↓reduceIte, Prod.mk.injEq] at hmd
    have hw : blockWords (tailOf x) = blockWords (tailOf y) := by
      rw [← blockWords_append_zeros (tailOf x) (64 - (tailOf x).length), ← hm,
        ← messageWords_eq_blockWords, hmw, hn]
      rfl
    obtain rfl := eq_of_prefix_tail hpre hmd.1 hw
    exact ⟨hx, digest_of_cells hout⟩

/-- **The honest rows pass the table check** with `H`. -/
theorem tableOK_chainRows {rows : List BlakeRow} (h : ∀ r ∈ rows, ChainRow I H r) :
    TableOK (fun x ↦ some (H x)) rows :=
  fun _ _ hc hsub hs ↦
    congrArg some (stdChain_chainRows hs (fun r hr ↦ h r (hsub r hr)) hc).2.symm

/-- The strings with a standard chain among the honest rows are strings of `D`. -/
theorem chainInputs_subset {rows : List BlakeRow} (h : ∀ r ∈ rows, ChainRow I H r) :
    chainInputs rows ⊆ {x | x ∈ D} := by
  rintro x ⟨c, hc, hsub, hs⟩
  exact (stdChain_chainRows hs (fun r hr ↦ h r (hsub r hr)) hc).1

/-- Finitely many strings have a standard chain among the honest rows. -/
theorem chainInputs_finite {rows : List BlakeRow} (h : ∀ r ∈ rows, ChainRow I H r) :
    (chainInputs rows).Finite :=
  (List.finite_toSet D).subset (chainInputs_subset h)

/-- A chain row's last-block flag is set exactly on the last row of its string. -/
theorem rowFinal_of_final {r : BlakeRow} {x : Bytes} (h : r.md = metadataCell x.length true) :
    RowFinal r := by
  rw [RowFinal, unpackMetadata_eq h]
  rfl

/-- **The honest rows pass the precheck**: non-final chain rows with equal outputs absorbed the
same prefix, so they have equal inputs. -/
theorem precheck_chainRows {rows : List BlakeRow} (h : ∀ r ∈ rows, CanonRow r ∧ ChainRow I H r) :
    Precheck rows := by
  intro r₁ h₁ r₂ h₂ hf₁ hf₂ hout
  obtain ⟨hc₁, x₁, hx₁, hr₁⟩ := h r₁ h₁
  obtain ⟨hc₂, x₂, hx₂, hr₂⟩ := h r₂ h₂
  rcases hr₁ with ⟨j₁, hj₁, hm₁, hcv₁, hout₁, hmd₁⟩ | ⟨-, -, -, hmd₁⟩
  swap
  · exact absurd (rowFinal_of_final hmd₁) hf₁
  rcases hr₂ with ⟨j₂, hj₂, hm₂, hcv₂, hout₂, hmd₂⟩ | ⟨-, -, -, hmd₂⟩
  swap
  · exact absurd (rowFinal_of_final hmd₂) hf₂
  have e := (out_of_st hout₁).symm.trans (hout.trans (out_of_st hout₂))
  obtain ⟨rfl, hpre, hb⟩ := prefixAt_succ_inj (Intermediates.stD_inj hx₁ hx₂ hj₁ hj₂ e)
  have hm : r₁.m = r₂.m := eq_of_blockBytes_eq hc₁.1 hc₂.1 (by rw [hm₁, hm₂, hb])
  have hcv : (r₁.cv0, r₁.cv1) = (r₂.cv0, r₂.cv1) := by rw [hcv₁, hcv₂, hpre]
  simp only [Prod.mk.injEq] at hcv
  simp only [rowInput, hm, hcv, hmd₁, hmd₂]

/-- A list's `allM` in `Id` is `true` when the test is. -/
theorem allM_id_true {α : Type} (f : α → Id Bool) :
    ∀ l : List α, (∀ x ∈ l, f x = true) → l.allM f = true
  | [], _ => by simp only [List.allM_nil]; rfl
  | x :: l, h => by
    simp only [List.allM_cons, h x List.mem_cons_self]
    exact allM_id_true f l fun y hy ↦ h y (List.mem_cons_of_mem x hy)

/-- **V_I's table check accepts the honest rows** with `H`. -/
theorem tableOKWith_chainRows {rows : List BlakeRow}
    (h : ∀ r ∈ rows, CanonRow r ∧ ChainRow I H r) :
    tableOKWith (m := Id) (fun x ↦ (pure (H x) : Id Digest)) rows = true := by
  have hC : ∀ r ∈ rows, ChainRow I H r := fun r hr ↦ (h r hr).2
  unfold tableOKWith
  split
  · split
    · refine allM_id_true _ _ fun x _ ↦ ?_
      classical
      exact decide_eq_true fun c hc hsub hs ↦
        (stdChain_chainRows hs (fun r hr ↦ hC r (hsub r hr)) hc).2
    · exact absurd (chainInputs_finite hC) ‹_›
  · exact absurd (precheck_chainRows h) ‹_›

/-! ## The semantics is a function -/

/-- **A semantics is functional** when a row's inputs determine its output. -/
def Functional (S : BlakeSem) : Prop :=
  ∀ {m : Fin 4 → E} {cv0 cv1 o0 o1 o0' o1' md : E}, S.check m cv0 cv1 o0 o1 md →
    S.check m cv0 cv1 o0' o1' md → o0 = o0' ∧ o1 = o1'

/-- **The honest table's semantics is functional**: equal inputs absorbed the same prefix of the
same string. -/
theorem chainSem_functional : Functional (chainSem I H) := by
  intro m cv0 cv1 o0 o1 o0' o1' md h h'
  obtain ⟨hc, x, hx, hr⟩ := h
  obtain ⟨-, x', hx', hr'⟩ := h'
  rcases hr with ⟨j, hj, hm, hcv, hout, hmd⟩ | ⟨hm, hcv, hout, hmd⟩ <;>
    rcases hr' with ⟨j', hj', hm', hcv', hout', hmd'⟩ | ⟨hm', hcv', hout', hmd'⟩
  · dsimp only at hm hcv hout hmd hm' hcv' hout' hmd'
    have e := (digest_of_cells hcv).symm.trans (digest_of_cells hcv')
    have hp := Intermediates.stD_inj hx hx' hj.le hj'.le e
    obtain rfl := eq_of_prefixAt_eq hp
    have hb : blockAt x j = blockAt x' j := hm.symm.trans hm'
    have hpre : prefixAt x (j + 1) = prefixAt x' (j + 1) := by
      rw [prefixAt_succ, prefixAt_succ, hp, hb]
    rw [hpre] at hout
    have := hout.trans hout'.symm
    simp only [Prod.mk.injEq] at this
    exact this
  · dsimp only at hmd hmd'
    have := congrArg unpackMetadata (hmd.symm.trans hmd')
    rw [unpackMetadata_metadataCell, unpackMetadata_metadataCell] at this
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at this
    exact absurd this.2.1.symm lastBlock_ne_zero
  · dsimp only at hmd hmd'
    have := congrArg unpackMetadata (hmd.symm.trans hmd')
    rw [unpackMetadata_metadataCell, unpackMetadata_metadataCell] at this
    simp only [Bool.false_eq_true, ↓reduceIte, Prod.mk.injEq] at this
    exact absurd this.2.1 lastBlock_ne_zero
  · dsimp only at hm hcv hout hmd hm' hcv' hout' hmd'
    have e := (digest_of_cells hcv).symm.trans (digest_of_cells hcv')
    have hp := Intermediates.stD_inj hx hx' le_rfl le_rfl e
    have hl := congrArg unpackMetadata (hmd.symm.trans hmd')
    rw [unpackMetadata_metadataCell, unpackMetadata_metadataCell] at hl
    simp only [↓reduceIte, Prod.mk.injEq] at hl
    have hw : blockWords (tailOf x) = blockWords (tailOf x') := by
      rw [← blockWords_append_zeros (tailOf x) (64 - (tailOf x).length),
        ← blockWords_append_zeros (tailOf x') (64 - (tailOf x').length), ← hm, ← hm']
    obtain rfl := eq_of_prefix_tail hp hl.1 hw
    have := hout.trans hout'.symm
    simp only [Prod.mk.injEq] at this
    exact this

/-! ## The honest rows the guest computes -/

/-- **A non-final block of a string of `D`** checks, from the cells after the blocks before it to
the cells after it. -/
theorem chainSem_step {x : Bytes} (hx : x ∈ D) {i : ℕ} (hi : i < nBlocks x) {m : Fin 4 → E}
    (hm : ∀ j, IsCanonical128 (m j)) (hb : blockBytes m = blockAt x i) :
    (chainSem I H).check m (I.st (prefixAt x i)).1 (I.st (prefixAt x i)).2
      (I.st (prefixAt x (i + 1))).1 (I.st (prefixAt x (i + 1))).2
      (metadataCell (64 * (i + 1)) false) :=
  ⟨⟨hm, (Intermediates.isCanonical_st _).1, (Intermediates.isCanonical_st _).2,
      (Intermediates.isCanonical_st _).1, (Intermediates.isCanonical_st _).2,
      isCanonical128_metadataCell _ _⟩,
    x, hx, Or.inl ⟨i, hi, hb, rfl, rfl, rfl⟩⟩

/-- **The last block of a string of `D`** checks, from the cells after its whole blocks to the
cells of `H` of the string. -/
theorem chainSem_final {x : Bytes} (hx : x ∈ D) {m : Fin 4 → E}
    (hm : ∀ j, IsCanonical128 (m j))
    (hb : blockBytes m = tailOf x ++ List.replicate (64 - (tailOf x).length) 0) :
    (chainSem I H).check m (I.st (prefixAt x (nBlocks x))).1 (I.st (prefixAt x (nBlocks x))).2
      (digestScalars (H x)).1 (digestScalars (H x)).2 (metadataCell x.length true) :=
  ⟨⟨hm, (Intermediates.isCanonical_st _).1, (Intermediates.isCanonical_st _).2,
      (isCanonical128_digestScalars _).1, (isCanonical128_digestScalars _).2,
      isCanonical128_metadataCell _ _⟩,
    x, hx, Or.inr ⟨hb, rfl, rfl, rfl⟩⟩

/-! ## The execution V_I re-runs -/

/-- Along a run under `S`, a semantics accepting every row `S` accepts lists the same rows. -/
theorem runRows_eq_of_runB {S S' : BlakeSem} (hS : ∀ b, S.row b → S'.row b) {κ : ℕ}
    {prog : Program} {L : MemImage κ} :
    ∀ {n : ℕ} {r rf : Regs K}, runB S prog L n r = some rf →
      runRows S' prog L n r = runRows S prog L n r
  | 0, _, _, _ => rfl
  | n + 1, r, rf, h => by
    by_cases hpc : r.pc = prog.finalPc
    · simp [runB, hpc] at h
    simp only [runB, hpc, ↓reduceIte, Option.bind_eq_bind, Option.bind_eq_some_iff] at h
    obtain ⟨r', hs, hrun⟩ := h
    obtain ⟨i, hf, he⟩ := Option.bind_eq_some_iff.mp hs
    have hs' : stepB S' prog L r = some r' := by
      simp only [stepB, hf, Option.bind_eq_bind, Option.bind_some]
      exact executeWithB_of (fun b _ hb ↦ hS b hb) he
    rw [runRows_succ hpc hf hs, runRows_succ hpc hf hs', runRows_eq_of_runB hS hrun]

/-- **The rows of an execution valid under a semantics of canonical rows**, as V_I lists them
under the Flock-blind semantics, are rows of that semantics. -/
theorem blakeRows_of_validB {S : BlakeSem} (hS : ∀ b, S.row b → blakeFree.row b) {prog : Program}
    {input : PublicInput} {t : Trace prog} (hv : ValidExecutionB S prog input t) :
    ∀ b ∈ t.blakeRows blakeFree, S.row b := by
  intro b hb
  unfold Trace.blakeRows at hb
  rw [runRows_eq_of_runB hS hv.2] at hb
  exact row_of_mem_runRows hb

/-- Runs compose. -/
theorem runB_add (S : BlakeSem) {κ : ℕ} (prog : Program) (L : MemImage κ) :
    ∀ (n k : ℕ) (r : Regs K), runB S prog L (n + k) r = runB S prog L n r >>= runB S prog L k
  | 0, k, r => by simp [runB]
  | n + 1, k, r => by
    rw [show n + 1 + k = (n + k) + 1 by omega]
    by_cases hpc : r.pc = prog.finalPc
    · simp [runB, hpc]
    · simp only [runB, hpc, ↓reduceIte, Option.bind_eq_bind, Option.bind_assoc]
      congr 1
      funext r'
      exact runB_add S prog L n k r'

/-- **A halting run has one length**: a run reaching the final registers stops there. -/
theorem steps_unique {S : BlakeSem} {κ : ℕ} {prog : Program} {L : MemImage κ} {n n' : ℕ}
    (h : runB S prog L n Regs.initial = some (Regs.final prog))
    (h' : runB S prog L n' Regs.initial = some (Regs.final prog)) : n = n' := by
  have key : ∀ {a b : ℕ}, a < b → runB S prog L a Regs.initial = some (Regs.final prog) →
      runB S prog L b Regs.initial ≠ some (Regs.final prog) := by
    intro a b hab ha hb
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hab
    rw [show a + k + 1 = a + (k + 1) by omega, runB_add, ha] at hb
    simp [runB, Regs.final] at hb
  rcases Nat.lt_trichotomy n n' with hlt | heq | hgt
  · exact absurd h' (key hlt h)
  · exact heq
  · exact absurd h (key hgt h')

/-- **V_I re-runs the execution**: an execution valid under a semantics of canonical rows is the
halting Flock-blind run of its memory image. -/
theorem haltingRunB_of_validB {S : BlakeSem} (hS : ∀ b, S.row b → blakeFree.row b)
    {prog : Program} {input : PublicInput} {t : Trace prog} (hv : ValidExecutionB S prog input t) :
    haltingRunB blakeFree prog t.image = some t := by
  have hfree : runB blakeFree prog t.image t.steps Regs.initial = some (Regs.final prog) :=
    runB_of_runRows (fun b _ hb ↦ hS b hb) hv.2
  have hex : ∃ n, runB blakeFree prog t.image n Regs.initial = some (Regs.final prog) :=
    ⟨_, hfree⟩
  unfold haltingRunB
  split
  · rename_i h
    rw [steps_unique (Nat.find_spec h) hfree]
  · exact absurd hex ‹_›

/-- The honest table's semantics accepts only canonical rows. -/
theorem chainSem_le_free (b : BlakeRow) (h : (chainSem I H).row b) : blakeFree.row b := h.1

end
end LeanVM.E2E.Complete
