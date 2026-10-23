/-
  LeanVM.Guest.B1.Digest.ChildList

  B1 for `child_claim_list_digest` (G:3864-3917; TRIAGE #89): a child's claim list rebuilt from
  this node's table through hinted slots, each marked in the coverage table, and its digest.
-/

module

public import LeanVM.Guest.B1.Digest.ClaimList

/-!
# `child_claim_list_digest`

As `claim_list_digest`, but claim `j` of a group is read at a hinted slot `o` of the table
(`child_claims`, G:3864-3874): `o` passes a range check against the region's bound, the coverage
table's slot `origin · g^o` holds the mark `marks · g^j`, and the four cells are read at
`entries · g^(4o)`. `claimOk` checks one such record in a list of atoms, by evaluation, and
`claimOk_sound` gives it on a memory image. The records sit at fixed value offsets in the 17
specializations `child_claim_list_last__L{k}` and in the group loop `__loop17` (`ccOV`, `ccMark`,
`ccCell`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## One claim record -/

/-- The bound of the first range check of `x`. -/
def rcOf (atoms : List Atom) (x : V) : Option V :=
  atoms.findSome? fun a => match a with
    | .rangeCheck x' _ _ _ k => if x' = x then some k else none
    | _ => none

/-- The pointer and offset of the first load into `x`. -/
def loadOf (atoms : List Atom) (x : V) : Option (V × ℕ) :=
  atoms.findSome? fun a => match a with
    | .load d p off => if d = x then some (p, off) else none
    | _ => none

theorem rcOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x k : V}
    (h : rcOf atoms x = some k) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ y t1 t2 : E, LoadHolds rd (σ x) 0 t1 ∧ σ k = σ x * y ∧ LoadHolds rd y 0 t2 := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  rename_i x' y t1 t2 k'
  split at hs
  · rename_i hd
    obtain rfl := Option.some.inj hs
    subst hd
    exact ⟨σ y, σ t1, σ t2, this⟩
  · exact absurd hs (by simp)

theorem loadOf_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x p : V} {off : ℕ}
    (h : loadOf atoms x = some (p, off)) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    LoadHolds rd (σ p) off (σ x) := by
  obtain ⟨a, ha, hs⟩ := List.exists_of_findSome?_eq_some h
  have := hat a ha
  cases a <;> simp only [reduceCtorEq] at hs
  split at hs
  · rename_i hd
    obtain ⟨rfl, rfl⟩ := Option.some.inj hs
    subst hd
    exact this
  · exact absurd hs (by simp)

theorem monoPerm_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x : V} {l : List V}
    (h : (monoOf atoms 40 x).isPerm l = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    σ x = (l.map σ).prod := by
  rw [mono_sound hat 40 x, (List.isPerm_iff.mp h).map σ |>.prod_eq]

/-- The values a claim record reads: the coverage table, the origin and bound of the region, the
table, the first mark. -/
structure ClaimVs where
  cover : V
  origin : V
  limit : V
  entries : V
  marks : V

/-- **Claim `j`'s record**: its slot `o` range-checked against `limit · g⁻¹`, its mark
(`marks`, or `marks · E(2^j)`) loaded at `cover · origin · o`, its four cells loaded at
`entries · o^4`. -/
def claimOk (atoms : List Atom) (P : ClaimVs) (j : ℕ) (o mark : V) (cells : List V) : Bool :=
  (match rcOf atoms o with
   | some k => (match mulOf atoms k with
       | some (l, gi) => decide (l = P.limit) && atoms.any (isConstAt gi 9223372036854775821 0)
       | none => false)
   | none => false) &&
  (if j = 0 then decide (mark = P.marks) else
    (match mulOf atoms mark with
     | some (m, c) => decide (m = P.marks) && atoms.any (isConstAt c (2 ^ j) 0)
     | none => false)) &&
  (match loadOf atoms mark with
   | some (b, off) => off == 0 && (monoOf atoms 40 b).isPerm [P.cover, P.origin, o]
   | none => false) &&
  cells.length == 4 &&
  (List.range 4).all fun c => match loadOf atoms (cells.getD c default) with
    | some (p, off) => off == c && (monoOf atoms 40 p).isPerm (P.entries :: List.replicate 4 o)
    | none => false

/-- What a claim record establishes: the slot `e` below the region's bound, the mark
`marks · g^j` at `cover · origin · g^e`, the four cells at `entries · g^(4e)`. -/
def ClaimAtSlot (rd : Reader) (cover origin limit entries marks : E) (j e : ℕ)
    (cells : List E) : Prop :=
  BelowLog limit e ∧ LoadHolds rd (cover * (origin * gen ^ e)) 0 (marks * gen ^ j) ∧
    ∀ c < 4, LoadHolds rd entries (4 * e + c) (cells.getD c 0)

theorem claimOk_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {P : ClaimVs}
    {j : ℕ} (hj : j < 64) {o mark : V} {cells : List V} (h : claimOk atoms P j o mark cells = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ e, σ o = gen ^ e ∧ ClaimAtSlot rd (σ P.cover) (σ P.origin) (σ P.limit) (σ P.entries)
      (σ P.marks) j e (cells.map σ) := by
  simp only [claimOk, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨hrc, hmk⟩, hld⟩, hlen⟩, hcells⟩ := h
  -- the range check
  split at hrc
  · rename_i k hk
    split at hrc
    · rename_i l gi hlg
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hrc
      obtain ⟨rfl, hgi⟩ := hrc
      obtain ⟨y, t1, t2, h1, h2, h3⟩ := rcOf_sound hk hat
      have hkv : σ k = σ P.limit * ginvW := by rw [mulOf_sound hlg hat, const_sound hgi hat]
      obtain ⟨e, he, hbl⟩ := rc_below hm (b := σ P.limit) (k := σ k) hkv ⟨h1, h2, h3⟩
      refine ⟨e, he, hbl, ?_, fun c hc => ?_⟩
      · -- the mark
        have hmark : σ mark = σ P.marks * gen ^ j := by
          by_cases h0 : j = 0
          · subst h0
            simp only [↓reduceIte, decide_eq_true_eq] at hmk
            rw [hmk, pow_zero, mul_one]
          · rw [ite_neg' h0] at hmk
            split at hmk
            · rename_i m c hmc
              simp only [Bool.and_eq_true, decide_eq_true_eq] at hmk
              obtain ⟨rfl, hc⟩ := hmk
              rw [mulOf_sound hmc hat, const_sound hc hat, word_two_pow hj]
            · exact absurd hmk (by simp)
        split at hld
        · rename_i b off hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hld
          obtain ⟨rfl, hperm⟩ := hld
          have := loadOf_sound hb hat
          rw [monoPerm_sound hperm hat, hmark] at this
          simpa [he, mul_assoc] using this
        · exact absurd hld (by simp)
      · -- the cells
        have hc' := hcells c hc
        split at hc'
        · rename_i p off hp
          simp only [Bool.and_eq_true, beq_iff_eq] at hc'
          obtain ⟨rfl, hperm⟩ := hc'
          have := loadOf_sound hp hat
          rw [monoPerm_sound hperm hat] at this
          simp only [List.map_cons, List.map_replicate, List.prod_cons, List.prod_replicate] at this
          rw [he, ← pow_mul, mul_comm e 4] at this
          have := (loadHolds_mul_gen_pow rd _ _ _ _).mp this
          rw [List.getD_eq_getElem?_getD, List.getElem?_map,
            List.getElem?_eq_getElem (by omega)]
          rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at this
          exact this
        · exact absurd hc' (by simp)
    · exact absurd hrc (by simp)
  · exact absurd hrc (by simp)

/-! ## The records' layout -/

/-- Claim `j`'s slot value, the first at `o0`. -/
def ccOV (o0 j : ℕ) : V := if j = 0 then .n o0 else .n (o0 + 15 + 17 * (j - 1))

/-- Claim `j`'s mark value (the first: the marks argument `mk`). -/
def ccMark (o0 : ℕ) (mk : V) (j : ℕ) : V := if j = 0 then mk else .n (o0 + 15 + 17 * (j - 1) + 7)

/-- Claim `j`'s cell `c`. -/
def ccCell (o0 j c : ℕ) : ℕ := if j = 0 then o0 + 11 + c else o0 + 15 + 17 * (j - 1) + 13 + c

/-- Claim `j`'s four cells. -/
def ccCells (o0 j : ℕ) : List V := (List.range 4).map fun c => .n (ccCell o0 j c)

/-- The records of `n` claims. -/
def recordsOk (atoms : List Atom) (P : ClaimVs) (o0 n : ℕ) : Bool :=
  (List.range n).all fun j => claimOk atoms P j (ccOV o0 j) (ccMark o0 P.marks j) (ccCells o0 j)

/-- The message of `n` claims: their cells, in order. -/
def ccMsg (o0 n : ℕ) : List (Option V) :=
  (List.range (4 * n)).map fun i => some (.n (ccCell o0 (i / 4) (i % 4)))

/-- **The records of `n ≤ 17` claims**: slots `o j`, the message's cells. -/
theorem records_sound {rd : Reader} (hm : MemOk rd) {σ : Val} {atoms : List Atom} {P : ClaimVs}
    {o0 n : ℕ} (hn : n ≤ 17) (h : recordsOk atoms P o0 n = true)
    (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ∃ os : List ℕ, os.length = n ∧ ∀ j < n,
      ClaimAtSlot rd (σ P.cover) (σ P.origin) (σ P.limit) (σ P.entries) (σ P.marks) j
        (os.getD j 0) (((ccMsg o0 n).map (srcVal σ)).drop (4 * j)) := by
  simp only [recordsOk, List.all_eq_true, List.mem_range] at h
  have hex : ∀ j < n, ∃ e, ClaimAtSlot rd (σ P.cover) (σ P.origin) (σ P.limit) (σ P.entries)
      (σ P.marks) j e ((ccCells o0 j).map σ) := fun j hj => by
    obtain ⟨e, -, he⟩ := claimOk_sound hm (by omega) (h j hj) hat
    exact ⟨e, he⟩
  classical
  refine ⟨(List.range n).map fun j => if hj : j < n then Classical.choose (hex j hj) else 0,
    by simp, fun j hj => ?_⟩
  have hs := Classical.choose_spec (hex j hj)
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hj]
  simp only [Option.map_some, Option.getD_some, hj, ↓reduceDIte]
  refine ⟨hs.1, hs.2.1, fun c hc => ?_⟩
  have := hs.2.2 c hc
  have e1 : (((ccMsg o0 n).map (srcVal σ)).drop (4 * j)).getD c 0 = σ (.n (ccCell o0 j c)) := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_drop, List.getElem?_map, ccMsg, List.getElem?_map,
      List.getElem?_range (by omega)]
    simp only [Option.map_some, Option.getD_some, srcVal]
    rw [show (4 * j + c) / 4 = j by omega, show (4 * j + c) % 4 = c by omega]
  have e2 : ((ccCells o0 j).map σ).getD c 0 = σ (.n (ccCell o0 j c)) := by
    simp [ccCells, List.getD_eq_getElem?_getD, hc]
  rw [e1, ← e2]
  exact this

end
end LeanVM.Guest.B1.Digest

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Records over several claims -/

/-- The records of `n` claims: slot `o j`, the mark `marks · g^j`, four cells each. -/
def ClaimsAt (rd : Reader) (cover origin limit entries marks : E) (n : ℕ) (os : List ℕ)
    (cells : List E) : Prop :=
  os.length = n ∧ cells.length = 4 * n ∧
    ∀ j < n, ClaimAtSlot rd cover origin limit entries marks j (os.getD j 0) (cells.drop (4 * j))

theorem getD_drop' {α : Type} (l : List α) (a c : ℕ) (d : α) :
    (l.drop a).getD c d = l.getD (a + c) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD]

theorem getD_append_left'' {α : Type} (l l' : List α) {i : ℕ} (d : α) (h : i < l.length) :
    (l ++ l').getD i d = l.getD i d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_left h, ← List.getD_eq_getElem?_getD]

theorem getD_append_right'' {α : Type} (l l' : List α) {i : ℕ} (d : α) (h : l.length ≤ i) :
    (l ++ l').getD i d = l'.getD (i - l.length) d := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_append_right h, ← List.getD_eq_getElem?_getD]

theorem claimsAt_append {rd : Reader} {cover origin limit entries base : E} {m k : ℕ}
    {os os' : List ℕ} {cs cs' : List E} (h : ClaimsAt rd cover origin limit entries base m os cs)
    (h' : ClaimsAt rd cover origin limit entries (base * gen ^ m) k os' cs') :
    ClaimsAt rd cover origin limit entries base (m + k) (os ++ os') (cs ++ cs') := by
  obtain ⟨hl, hcl, hc⟩ := h
  obtain ⟨hl', hcl', hc'⟩ := h'
  refine ⟨by rw [List.length_append, hl, hl'], by rw [List.length_append, hcl, hcl']; ring,
    fun j hj => ?_⟩
  by_cases hjm : j < m
  · obtain ⟨h1, h2, h3⟩ := hc j hjm
    have hos : (os ++ os').getD j 0 = os.getD j 0 := getD_append_left'' _ _ _ (by omega)
    refine ⟨by rw [hos]; exact h1, by rw [hos]; exact h2, fun c hcc => ?_⟩
    rw [hos, getD_drop', getD_append_left'' _ _ _ (by omega)]
    have := h3 c hcc
    rwa [getD_drop'] at this
  · obtain ⟨h1, h2, h3⟩ := hc' (j - m) (by omega)
    have hos : (os ++ os').getD j 0 = os'.getD (j - m) 0 := by
      rw [getD_append_right'' _ _ _ (by omega), hl]
    refine ⟨by rw [hos]; exact h1, ?_, fun c hcc => ?_⟩
    · have hb : base * gen ^ j = base * gen ^ m * gen ^ (j - m) := by
        rw [mul_assoc, ← pow_add, Nat.add_sub_cancel' (by omega)]
      rw [hos, hb]
      exact h2
    · rw [hos, getD_drop', getD_append_right'' _ _ _ (by omega), hcl,
        show 4 * j + c - 4 * m = 4 * (j - m) + c by omega]
      have := h3 c hcc
      rwa [getD_drop'] at this

/-! ## `child_claim_list_last__L{k}` -/

/-- The names of `child_claim_list_last`'s specializations, `k ≤ 16`. -/
def cclNames : List String :=
  ["child_claim_list_last__L0", "child_claim_list_last__L1", "child_claim_list_last__L2",
   "child_claim_list_last__L3", "child_claim_list_last__L4", "child_claim_list_last__L5",
   "child_claim_list_last__L6", "child_claim_list_last__L7", "child_claim_list_last__L8",
   "child_claim_list_last__L9", "child_claim_list_last__L10", "child_claim_list_last__L11",
   "child_claim_list_last__L12", "child_claim_list_last__L13", "child_claim_list_last__L14",
   "child_claim_list_last__L15", "child_claim_list_last__L16"]

/-- The state cells `child_claim_list_last__L{k}` loads. -/
def cclSt (k : ℕ) : List V :=
  (List.range 13).map fun c => V.n ((if k = 0 then 6 else 17 * k + 4) + c)

/-- The record values of `child_claim_list_last__L{k}`'s arguments. -/
def cclP : ClaimVs := ⟨.n 2, .n 4, .n 5, .n 1, .n 3⟩

/-- The chain of `child_claim_list_last__L{k}`. -/
def cclSpec (k : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨ccMsg 6 k, 64 * k, true, some (cclSt k), keccakBlocks atoms⟩

/-- `child_claim_list_last__L{k}`'s body: `k` records, the chain over their cells from the state
at its first argument. -/
def cclOk (k : ℕ) (f : Fn) : Bool :=
  decide (f.params = [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5]) &&
  match splitBody f.body with
  | some (atoms, [r0, r1]) =>
    (cclSpec k atoms).check atoms && retOk atoms (cclSpec k atoms) r0 r1 &&
      recordsOk atoms cclP 6 k && stLoadsOk atoms (V.n 0) (cclSt k) 0
  | _ => false

set_option maxRecDepth 100000 in
theorem ccl_all : ∀ k < 17, cclOk k (coreProgram.getD (342 + k) default) = true := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem ccl_idx : ∀ k < 17, coreProgram.indexOf? (cclNames.getD k "") = some (342 + k) := by
  decide +kernel

theorem length_ccMsg (o0 n : ℕ) : (ccMsg o0 n).length = 4 * n := by simp [ccMsg]

/-- **`child_claim_list_last__L{k}`**: from a state at its first argument after whole blocks
`pre`, `k` claims read at hinted slots and marked, and the digest of `pre ++` their cells. -/
theorem childLast_sound {rd : Reader} (hm : MemOk rd) {k : ℕ} (hk : k < 17) {args rets : List E}
    (h : coreProgram.Rel rd (cclNames.getD k "") args rets) :
    ∃ sp entries cover marks origin limit, args = [sp, entries, cover, marks, origin, limit] ∧
      ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
      StateAt rd sp 0 (absorbChunks n zeroState pre) →
      ∃ (os : List ℕ) (cells : List E), ClaimsAt rd cover origin limit entries marks k os cells ∧
        AllCanonical cells ∧ rets = digestCells (keccak256 (pre ++ cellsBytes cells)) := by
  have hf := find_of_idx (ccl_idx k hk) (by rw [coreProgram_length]; omega)
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf args rets).mp h
  have hok := ccl_all k hk
  set f := coreProgram.getD (342 + k) default
  simp only [cclOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  rw [hpar] at hp
  refine ⟨σ (V.n 0), σ (V.n 1), σ (V.n 2), σ (V.n 3), σ (V.n 4), σ (V.n 5), by rw [← hp]; rfl,
    fun n pre hpre hS => ?_⟩
  split at hok
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨⟨hc, hr⟩, hrec⟩, hst⟩ := hok
    rw [splitBody_eq hsb, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    obtain ⟨hd, hcan⟩ := chain_final hc rfl hat hpre (initCell_of_loads rfl hst hat hS)
    obtain ⟨os, hos, hcl⟩ := records_sound hm (by omega) hrec hat
    have hlen : ((cclSpec k atoms).vals σ).length = 4 * k := by
      simp [ChainSpec.vals, cclSpec, length_ccMsg]
    have htake : ((cclSpec k atoms).vals σ).take ((cclSpec k atoms).len / 16) =
        (cclSpec k atoms).vals σ := by
      rw [List.take_of_length_le]
      rw [hlen]; simp only [cclSpec]; omega
    rw [htake] at hd hcan
    simp only [retOk, Bool.and_eq_true] at hr
    refine ⟨os, (cclSpec k atoms).vals σ, ⟨hos, hlen, hcl⟩, hcan, ?_⟩
    rw [← hret, List.map_cons, List.map_cons, List.map_nil, copy_sound hr.1 hat,
      copy_sound hr.2 hat, digestCells, ← hd]
  · exact absurd hok (by simp)

theorem getD_map_range {α : Type} (f : ℕ → α) {n c : ℕ} (h : c < n) (d : α) :
    ((List.range n).map f).getD c d = f c := by
  simp [List.getD_eq_getElem?_getD, h]

/-! ## `__loop17`: one group of seventeen child claims -/

/-- The state cells `__loop17` loads. -/
def l17St : List V := (List.range 13).map fun c => V.n (307 + c)

/-- The record values of `__loop17`. -/
def l17P : ClaimVs := ⟨.n 4, .n 6, .n 7, .n 3, .n 19⟩

/-- The chain of `__loop17`: the 68 record cells, eight blocks, `final=0`. -/
def l17Spec (atoms : List Atom) : ChainSpec :=
  ⟨ccMsg 20 17, 0, false, some l17St, keccakBlocks atoms⟩

/-- `__loop17`'s body: 17 records with the marks `base · x^17`, the state at `chain · x^13`, the
next at `chain · x^13 · g^13`. -/
def l17Ok (fn : Fn) : Bool :=
  loopShape fn "__loop17" && decide (fn.params.length = 8) &&
    (l17Spec (loopAtoms fn)).check (loopAtoms fn) && stLoadsOk (loopAtoms fn) (V.n 13) l17St 0 &&
    recordsOk (loopAtoms fn) l17P 20 17 &&
    stLoadsOk (loopAtoms fn) (V.n 13)
      ((List.range 13).map ((l17Spec (loopAtoms fn)).outV ((l17Spec (loopAtoms fn)).nb - 1))) 13 &&
    monoIs (loopAtoms fn) (V.n 13) (V.n 2) (V.n 0) 13 &&
    monoIs (loopAtoms fn) (V.n 19) (V.n 5) (V.n 0) 17

set_option maxRecDepth 100000 in
theorem l17_ok : l17Ok (coreProgram.getD 341 default) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_idx : coreProgram.indexOf? "__loop17" = some 341 := by decide +kernel

set_option maxRecDepth 100000 in
theorem l17_nb : (l17Spec (loopAtoms (coreProgram.getD 341 default))).nb = 8 := by decide +kernel

/-- **One group of child claims**: from the state at `chain · x^13` after whole blocks `pre`,
17 claims read at hinted slots and marked `base · x^17 · g^j`, absorbed, the state written at
`chain · x^13 · g^13`. -/
def ChildGroupStep (rd : Reader) (chain entries cover base origin limit x : E) : Prop :=
  ∀ (n : ℕ) (pre : List UInt8), pre.length = rate * n →
    StateAt rd (chain * x ^ 13) 0 (absorbChunks n zeroState pre) →
    ∃ (os : List ℕ) (cells : List E),
      ClaimsAt rd cover origin limit entries (base * x ^ 17) 17 os cells ∧ AllCanonical cells ∧
      StateAt rd (chain * x ^ 13) 13 (absorbChunks (n + 8) zeroState (pre ++ cellsBytes cells))

theorem l17_step {rd : Reader} (hm : MemOk rd) {x : E} {ps : List E}
    (h : coreProgram.Rel rd "__loop17" (x :: ps) []) :
    (∀ N chain entries cover base origin limit,
      ps = [N, chain, entries, cover, base, origin, limit] →
      ChildGroupStep rd chain entries cover base origin limit x) ∧
      (x * gen + ps.headD 0 ≠ 0 → coreProgram.Rel rd "__loop17" (x * gen :: ps) []) := by
  have hf := find_of_idx l17_idx (by rw [coreProgram_length]; omega)
  have hok := l17_ok
  simp only [l17Ok, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hshape, hlen8⟩, hc⟩, hst⟩, hrec⟩, hout⟩, hm13⟩, hm19⟩ := hok
  obtain ⟨σ, hx, hps, hat, hnext⟩ := loop_step hf hshape h
  refine ⟨fun N chain entries cover base origin limit hN n pre hpre hS => ?_, hnext⟩
  have hpar : (coreProgram.getD 341 default).params =
      [V.n 0, V.n 1, V.n 2, V.n 3, V.n 4, V.n 5, V.n 6, V.n 7] := by
    have hs := hshape
    simp only [loopShape, Bool.and_eq_true, decide_eq_true_eq] at hs
    rw [hs.1.2, hlen8]; rfl
  rw [hpar, hN] at hps
  simp only [List.tail_cons, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hps
  obtain ⟨-, hchain, hentries, hcover, hbase, horigin, hlimit⟩ := hps
  have h13 : σ (V.n 13) = chain * x ^ 13 := by rw [monoIs_sound hm13 hat, hchain, hx]
  have h19 : σ (V.n 19) = base * x ^ 17 := by rw [monoIs_sound hm19 hat, hbase, hx]
  rw [← h13] at hS
  obtain ⟨hw, -, hcan⟩ := chain_whole hc rfl hat hpre (initCell_of_loads rfl hst hat hS)
  obtain ⟨os, hos, hcl⟩ := records_sound hm (le_refl 17) hrec hat
  have hlen : ((l17Spec (loopAtoms (coreProgram.getD 341 default))).vals σ).length = 68 := by
    simp [ChainSpec.vals, l17Spec, length_ccMsg]
  refine ⟨os, _, ⟨hos, hlen, ?_⟩, hcan, fun c => ?_⟩
  · intro j hj
    have := hcl j hj
    simp only [l17P] at this
    rwa [hcover, horigin, hlimit, hentries, h19] at this
  · have hout' := stLoads_sound hout hat c
    have hw' := hw c
    rw [l17_nb] at hw' hout'
    rw [getD_map_range _ c.isLt, hw', h13] at hout'
    exact hout'

end
end LeanVM.Guest.B1.Digest
