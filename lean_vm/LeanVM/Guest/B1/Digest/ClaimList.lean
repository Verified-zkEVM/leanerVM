/-
  LeanVM.Guest.B1.Digest.ClaimList

  B1 for `claim_list_digest` (G:3827-3861; TRIAGE #88): the digest of a declared claim list,
  hashed seventeen claims a loop frame through a heap chain of sponge states.
-/

module

public import LeanVM.Guest.B1.Digest.Steps

/-!
# `claim_list_digest`

`claim_list_digest(entries, n_g)`: for `n_g = 1` the digest of the empty string; otherwise
`list_split` writes `n = 17 a + b`, a heap chain starts at the zero state (`zero_state`), the
loop `__loop16` absorbs group `q < a` (68 cells, `1088` bytes, eight blocks, `final=0`) from the
state at `chain · g^(13q)` into the state at `chain · g^(13(q + 1))` (`l16_step`), and
`claim_list_last__L{b}` absorbs the last `4b` cells with the padding from the state at
`chain · g^(13a)` (`claimLast_sound`). By induction over the groups (`groups_sound`), the
digest is Keccak-256 of the `4n` cells' bytes.
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `claim_list_last__L{k}` -/

/-- The names of `claim_list_last`'s specializations, `k ≤ 16`. -/
def clNames : List String :=
  ["claim_list_last__L0", "claim_list_last__L1", "claim_list_last__L2", "claim_list_last__L3",
   "claim_list_last__L4", "claim_list_last__L5", "claim_list_last__L6", "claim_list_last__L7",
   "claim_list_last__L8", "claim_list_last__L9", "claim_list_last__L10", "claim_list_last__L11",
   "claim_list_last__L12", "claim_list_last__L13", "claim_list_last__L14", "claim_list_last__L15",
   "claim_list_last__L16"]

/-- The state cells `claim_list_last__L{k}` loads. -/
def clSt (k : ℕ) : List V := (List.range 13).map fun c => V.n (2 + 4 * k + c)

/-- The chain of `claim_list_last__L{k}`: `4k` cells loaded as `.n 2 …`, `64k` bytes, from the
state loaded as `clSt k`. -/
def clSpec (k : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨(List.range (4 * k)).map (fun i => some (V.n (i + 2))), 64 * k, true, some (clSt k),
    keccakBlocks atoms⟩

/-- `claim_list_last__L{k}`'s body is the chain over the cells at its second argument from the
state at its first. -/
def clOk (k : ℕ) (f : Fn) : Bool :=
  decide (f.params = [V.n 0, V.n 1]) &&
  match splitBody f.body with
  | some (atoms, [r0, r1]) =>
    (clSpec k atoms).check atoms && retOk atoms (clSpec k atoms) r0 r1 &&
      loadsOk atoms (V.n 1) (clSpec k atoms).msg && stLoadsOk atoms (V.n 0) (clSt k) 0
  | _ => false

set_option maxRecDepth 100000 in
theorem cl_all : ∀ k < 17, clOk k (coreProgram.getD (324 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem cl_idx : ∀ k < 17, coreProgram.indexOf? (clNames.getD k "") = some (324 + k) := by
  decide +kernel

/-- **`claim_list_last__L{k}`**: from a state at its first argument after whole blocks `pre`, it
returns the digest of `pre ++` the `4k` canonical cells at its second. -/
theorem claimLast_sound {k : ℕ} (hk : k < 17) {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (clNames.getD k "") args rets) :
    ∃ sp blk, args = [sp, blk] ∧ ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
      StateAt rd sp 0 (absorbChunks n zeroState pre) →
      ∃ cells : List E, cells.length = 4 * k ∧ ReadsAt rd blk cells ∧ AllCanonical cells ∧
        rets = digestCells (keccak256 (pre ++ cellsBytes cells)) := by
  have hf := find_of_idx (cl_idx k hk) (by rw [coreProgram_length]; omega)
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf args rets).mp h
  have hok := cl_all k hk
  set f := coreProgram.getD (324 + k) default
  simp only [clOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  rw [hpar] at hp
  refine ⟨σ (V.n 0), σ (V.n 1), by rw [← hp]; rfl, fun n pre hpre hS => ?_⟩
  split at hok
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hc, hr⟩, hl⟩, hst⟩ := hok
    rw [splitBody_eq hsb, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    obtain ⟨hreads, hcan, hd⟩ := chain_final_mem hc rfl rfl hst hl hr hat hpre hS
    have hlen : ((clSpec k atoms).vals σ).length = 4 * k := by
      simp [ChainSpec.vals, clSpec]
    have htake : ((clSpec k atoms).vals σ).take ((clSpec k atoms).len / 16) =
        (clSpec k atoms).vals σ := by
      rw [List.take_of_length_le]
      rw [hlen]; simp only [clSpec]; omega
    rw [htake] at hd hcan
    refine ⟨(clSpec k atoms).vals σ, hlen, hreads, hcan, ?_⟩
    rw [← hret, ← hd]
    rfl
  · exact absurd hok (by simp)

/-! ## `__loop16`: one group of seventeen claims -/

/-- The state cells `__loop16` loads. -/
def l16St : List V := (List.range 13).map fun c => V.n (86 + c)

/-- The chain of `__loop16`: 68 cells loaded as `.n 18 …`, eight blocks, `final=0`. -/
def l16Spec (atoms : List Atom) : ChainSpec :=
  ⟨(List.range 68).map (fun i => some (V.n (i + 18))), 0, false, some l16St, keccakBlocks atoms⟩

/-- `__loop16`'s body: the state at `chain · x^13`, the cells at `entries · x^68`, the next state
at `chain · x^13 · g^13`. -/
def l16Ok (fn : Fn) : Bool :=
  loopShape fn "__loop16" && decide (fn.params.length = 4) &&
    (l16Spec (loopAtoms fn)).check (loopAtoms fn) && stLoadsOk (loopAtoms fn) (V.n 9) l16St 0 &&
    loadsOk (loopAtoms fn) (V.n 17) (l16Spec (loopAtoms fn)).msg &&
    stLoadsOk (loopAtoms fn) (V.n 9)
      ((List.range 13).map ((l16Spec (loopAtoms fn)).outV ((l16Spec (loopAtoms fn)).nb - 1))) 13 &&
    monoIs (loopAtoms fn) (V.n 9) (V.n 2) (V.n 0) 13 &&
    monoIs (loopAtoms fn) (V.n 17) (V.n 3) (V.n 0) 68

set_option maxRecDepth 100000 in
theorem l16_ok : l16Ok (coreProgram.getD 323 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l16_idx : coreProgram.indexOf? "__loop16" = some 323 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l16_nb : (l16Spec (loopAtoms (coreProgram.getD 323 default))).nb = 8 := by decide +kernel

/-- **One group**: from the state at `chain · x^13` after whole blocks `pre`, the 68 canonical
cells at `entries · x^68` absorbed, the state written at `chain · x^13 · g^13`. -/
def GroupStep (rd : Reader) (chain entries x : E) : Prop :=
  ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
    StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre) →
    ∃ cells : List E, cells.length = 68 ∧ ReadsAt rd (entries * x ^ 68) cells ∧
      AllCanonical cells ∧
      StateAt rd (chain * x ^ 13) 13 (absorbChunks (n + 8) zeroState (pre ++ cellsBytes cells))

theorem l16_step {rd : Reader} {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop16" (x :: ps) []) :
    (∀ N chain entries, ps = [N, chain, entries] → GroupStep rd chain entries x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop16" (x * gen :: ps) []) := by
  have hf := find_of_idx l16_idx (by rw [coreProgram_length]; omega)
  have hok := l16_ok
  simp only [l16Ok, loopShape, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen4⟩, hc⟩, hst⟩, hl⟩, hout⟩, hm9⟩, hm17⟩ := hok
  have hshape' : loopShape (coreProgram.getD 323 default) "__loop16" = true := by
    simpa only [loopShape, Bool.and_eq_true, decide_eq_true_eq] using hshape
  obtain ⟨σ, hx, hps, hat, hnext⟩ := loop_step hf hshape' h
  refine ⟨fun N chain entries hNce n pre hpre hS => ?_, hnext⟩
  have hpar : (coreProgram.getD 323 default).params = [V.n 0, V.n 1, V.n 2, V.n 3] := by
    rw [hshape.1.2, hlen4]; rfl
  rw [hpar, hNce] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hchain, hentries⟩ := hps
  have h9 : σ (V.n 9) = chain * x ^ 13 := by rw [monoIs_sound hm9 hat, hchain, hx]
  have h17 : σ (V.n 17) = entries * x ^ 68 := by rw [monoIs_sound hm17 hat, hentries, hx]
  rw [← h9] at hS
  obtain ⟨hreads, hcan, hS', hl'⟩ := chain_whole_mem hc rfl rfl hst hl hout hat hpre hS
  have hnb : (l16Spec (loopAtoms (coreProgram.getD 323 default))).nb = 8 := l16_nb
  rw [hnb] at hS'
  refine ⟨_, by simp [ChainSpec.vals, l16Spec], by rwa [← h17], hcan, by rwa [← h9]⟩

/-! ## The groups, by induction -/

theorem gen_pow_pow (q e : ℕ) : (gen ^ q) ^ e = gen ^ (e * q) := by rw [← pow_mul, mul_comm]

/-- **The groups**: after `q ≤ a` groups, the state at `chain · g^(13q)` is the sponge after the
`68q` canonical cells at `entries`. -/
theorem groups_sound {rd : Reader} {chain entries : E} {a : ℕ}
    (h0 : StateAt rd chain 0 zeroState)
    (hstep : ∀ q < a, GroupStep rd chain entries (gen ^ q)) :
    ∀ q ≤ a, ∃ cells : List E, cells.length = 68 * q ∧ ReadsAt rd entries cells ∧
      AllCanonical cells ∧
      StateAt rd (chain * gen ^ (13 * q)) 0 (absorbChunks (8 * q) zeroState (cellsBytes cells)) := by
  intro q
  induction q with
  | zero =>
    intro _
    refine ⟨[], rfl, readsAt_nil _ _, fun _ h => absurd h (by simp), ?_⟩
    simpa [absorbChunks] using h0
  | succ q ih =>
    intro hq
    obtain ⟨cells, hlen, hreads, hcan, hS⟩ := ih (by omega)
    have hpre : (cellsBytes cells).length = rate * (8 * q) := by
      rw [length_cellsBytes, hlen]; show 16 * (68 * q) = 136 * (8 * q); omega
    rw [show chain * gen ^ (13 * q) = chain * (gen ^ q) ^ 13 by rw [gen_pow_pow]] at hS
    obtain ⟨c2, hl2, hr2, hcan2, hS2⟩ := hstep q (by omega) (8 * q) (cellsBytes cells) hpre hS
    refine ⟨cells ++ c2, by rw [List.length_append, hlen, hl2]; ring, ?_, ?_, ?_⟩
    · rw [readsAt_append, hlen]
      refine ⟨hreads, ?_⟩
      rwa [gen_pow_pow] at hr2
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hcan c hc
      · exact hcan2 c hc
    · intro c
      have := hS2 c
      rw [gen_pow_pow, loadHolds_mul_gen_pow] at this
      rw [loadHolds_mul_gen_pow, cellsBytes_append,
        show 13 * (q + 1) + (0 + c.val) = 13 * q + (13 + c.val) by ring,
        show 8 * (q + 1) = 8 * q + 8 by ring]
      exact this

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## `claim_list_digest` -/

/-- The branch of an empty list. -/
noncomputable def cl23Zero : List Stmt := match Fn.body Data.core23 with
  | [_, _, .ite _ z _, _, _, _] => z
  | _ => []

/-- The branch of a nonempty list. -/
noncomputable def cl23Else : List Stmt := match Fn.body Data.core23 with
  | [_, _, .ite _ _ n, _, _, _] => n
  | _ => []

set_option maxRecDepth 100000 in
theorem core23_shape : Fn.body Data.core23 =
    [.atom (.const (.n 2) (word 1 0 0)), .atom (.add (.n 3) (.n 1) (.n 2)),
     .ite (.n 3) cl23Zero cl23Else, .atom (.copy (.n 65) (.n 10)), .atom (.copy (.n 66) (.n 11)),
     .ret [.n 65, .n 66]] :=
  stmtsEqb_sound (by decide +kernel)

/-- The empty list's chain: the empty message from the zero state. -/
noncomputable def czSpec : ChainSpec := ⟨[], 0, true, none, keccakBlocks (atomsIn cl23Zero)⟩

/-- The empty list's branch hashes the empty string into `.n 10`, `.n 11`. -/
noncomputable def czOk : Bool :=
  cl23Zero.all Stmt.flat && czSpec.check (atomsIn cl23Zero) &&
    decide (czSpec.outV (czSpec.nb - 1) 0 = V.n 10) && decide (czSpec.outV (czSpec.nb - 1) 1 = V.n 11)

/-- The nonempty list's branch: `list_split`, the zero state at `chain = .n 32`, the loop over the
groups, `last = chain · groups^13`, `blk = entries · groups^68`, the dispatch on the rest. -/
noncomputable def ceOk : Bool :=
  cl23Else.all Stmt.flat &&
  cl23Else.any (stmtEqb · (.call "list_split" [.n 1] [.n 23, .n 24])) &&
  cl23Else.any (stmtEqb · (.callIf (.n 47) "__loop16" [.n 48, .n 23, .n 32, .n 0])) &&
  cl23Else.any (stmtEqb · (.dispatch (.n 24) clNames [.n 54, .n 62] [.n 63, .n 64])) &&
  (atomsIn cl23Else).any (isConstAt (.n 48) 1 0) &&
  (atomsIn cl23Else).any (isAddAt (.n 47) (.n 46) (.n 23)) &&
  (atomsIn cl23Else).any (isConstAt (.n 46) 1 0) &&
  (List.range 13).all (fun c => (atomsIn cl23Else).any (isLoadAt (.n (33 + c)) (.n 32) c) &&
    (atomsIn cl23Else).any (isConstAt (.n (33 + c)) 0 0)) &&
  monoIs (atomsIn cl23Else) (.n 54) (.n 32) (.n 23) 13 &&
  monoIs (atomsIn cl23Else) (.n 62) (.n 0) (.n 23) 68 &&
  (atomsIn cl23Else).any (isCopyAt (.n 10) (.n 63)) &&
  (atomsIn cl23Else).any (isCopyAt (.n 11) (.n 64))

set_option maxRecDepth 100000 in
theorem cz_ok : czOk = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem ce_ok : ceOk = true := by decide +kernel

/-- **`claim_list_digest` computes the digest of the claims.** -/
theorem claim_list_digest_sound : claim_list_digest_sound_Spec := by
  intro rd hm args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_claim_list_digest args rets).mp h
  have hp' : args = [σ (.n 0), σ (.n 1)] := by rw [← hp]; rfl
  subst hp'
  rw [core23_shape] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨c2, a3, -, hz, hnz⟩ := hb
  have hz1 := cz_ok
  have he1 := ce_ok
  simp only [czOk, Bool.and_eq_true, decide_eq_true_eq] at hz1
  simp only [ceOk, Bool.and_eq_true, List.all_eq_true, List.mem_range] at he1
  obtain ⟨⟨⟨hzf, hzc⟩, hz10⟩, hz11⟩ := hz1
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hef, hls⟩, hlp⟩, hdis⟩, h48⟩, h47⟩, h46⟩, hzs⟩, hm54⟩, hm62⟩, hc10⟩, hc11⟩ := he1
  by_cases h3 : σ (.n 3) = 0
  · -- the empty list
    have hn1 : σ (.n 1) = 1 := by
      rw [a3, c2, word_one] at h3; exact e_add_eq_zero_iff.mp h3
    obtain ⟨hall, h65, h66, hr⟩ := holdsList_flat _ hzf _ _ (hz h3)
    have hat := atoms_of_flat hall
    obtain ⟨hd, -⟩ := chain_final hzc rfl hat (pre := []) (n := 0) rfl
      (fun c => (cellsOfState_zero false c).symm)
    rw [hz10, hz11, show List.take (czSpec.len / 16) (czSpec.vals σ) = [] by simp [czSpec],
      List.nil_append] at hd
    refine ⟨0, by norm_num, by rw [hn1, pow_zero], [], rfl, readsAt_nil _ _,
      fun _ h => absurd h (by simp), ?_⟩
    rw [← hr, h65, h66, digestCells, ← hd]
  · -- a nonempty list
    obtain ⟨hall, h65, h66, hr⟩ := holdsList_flat _ (List.all_eq_true.mpr hef) _ _ (hnz h3)
    have hat := atoms_of_flat hall
    obtain ⟨a, ha, b, hb, hn, hab⟩ :=
      list_split_sound rd hm _ _ (call_of_flat hall hls)
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hab
    obtain ⟨h23, h24⟩ := hab
    simp only [maxKeys, claimGroup] at ha hb hn
    -- the zero state
    have h0 : StateAt rd (σ (.n 32)) 0 zeroState := by
      intro c
      have hl := load_sound (hzs c c.isLt).1 hat
      rw [const_sound (hzs c c.isLt).2 hat, word_zero] at hl
      rw [Nat.zero_add, cellsOfState_zero]
      exact hl
    -- the groups
    have hloop := callIf_of_flat hall hlp
    have h47v : σ (.n 47) = 1 + σ (.n 23) := by
      rw [add_sound h47 hat, const_sound h46 hat, word_one]
    have h48v : σ (.n 48) = 1 := by rw [const_sound h48 hat, word_one]
    have hsteps : ∀ q < a, GroupStep rd (σ (.n 32)) (σ (.n 0)) (gen ^ q) :=
      loop_sound (f := "__loop16") (ps := [σ (.n 23), σ (.n 32), σ (.n 0)]) (N := σ (.n 23))
        (B := GroupStep rd (σ (.n 32)) (σ (.n 0))) (by unfold ordG; omega) h23
        (fun x hx => by
          obtain ⟨h1, h2⟩ := l16_step hx
          exact ⟨h1 _ _ _ rfl, h2⟩)
        (fun hne => by
          have := hloop.2 (by rw [h47v]; exact hne)
          simpa [h48v] using this)
    obtain ⟨ca, hla, hra, hcana, hSa⟩ := groups_sound h0 hsteps a le_rfl
    -- the rest
    obtain ⟨j, hj, hsel, hcall⟩ := dispatch_of_flat hall hdis
    have hj17 : j < 17 := hj
    have hjb : j = b := by
      rw [h24, gen_pow_eq_ofK] at hsel
      exact (gpow_injOn (by simp only [Set.mem_Iio]; omega) (by simp only [Set.mem_Iio]; omega)
        (ofK_injective hsel)).symm
    subst hjb
    rw [show clNames[j] = clNames.getD j "" by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
    obtain ⟨sp, blk, hargs, hlast⟩ := claimLast_sound hj17 hcall
    simp only [List.map_cons, List.map_nil, List.cons.injEq, and_true] at hargs
    obtain ⟨hsp, hblk⟩ := hargs
    have h54 : σ (.n 54) = σ (.n 32) * gen ^ (13 * a) := by
      rw [monoIs_sound hm54 hat, h23, gen_pow_pow]
    have h62 : σ (.n 62) = σ (.n 0) * gen ^ (68 * a) := by
      rw [monoIs_sound hm62 hat, h23, gen_pow_pow]
    have hpre : (cellsBytes ca).length = rate * (8 * a) := by
      rw [length_cellsBytes, hla]; show 16 * (68 * a) = 136 * (8 * a); omega
    obtain ⟨cb, hlb, hrb, hcanb, hd⟩ := hlast (8 * a) (cellsBytes ca) hpre (by rw [← hsp, h54]; exact hSa)
    refine ⟨17 * a + j, by simp only [claimGroup, maxKeys]; omega, by rw [hn],
      ca ++ cb, by rw [List.length_append, hla, hlb]; ring, ?_, ?_, ?_⟩
    · rw [readsAt_append, hla]
      exact ⟨hra, by rw [← h62, hblk]; exact hrb⟩
    · intro c hc
      rcases List.mem_append.mp hc with hc | hc
      · exact hcana c hc
      · exact hcanb c hc
    · rw [← hr, h65, h66, copy_sound hc10 hat, copy_sound hc11 hat, cellsBytes_append]
      exact hd

end
end LeanVM.Guest.B1.Digest
