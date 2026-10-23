/-
  LeanVM.Guest.B1.Digest.Lists

  Straight-line `KECCAK` chains over loaded cells, checked by evaluation; B1 for `da_list_digest`
  and its 17 specializations `da_hash_roots__L{n}` (G:4063-4075; TRIAGE #94).
-/

module

public import LeanVM.Guest.B1.Digest.Chain

/-!
# Chains over loaded cells; `da_list_digest`

A straight-line body (`splitBody`: atoms, then a `ret`) that loads its message cells through a
pointer (`loadsOk`), hashes them by a padded chain (`ChainSpec.check`) and returns copies of the
digest's cells (`retOk`) returns the digest of the cells read (`straight_digest`).

`da_hash_roots__L{n}` (`core377 … core393`) loads `4n` cells from its argument and hashes their
`64n` bytes, all 17 by one kernel evaluation (`hr_all`); `da_list_digest` dispatches on `g^n`
(`da_list_digest_sound`).
-/

namespace LeanVM.Guest.B1.Digest

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Value.Keccak
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-! ## Straight-line bodies -/

/-- A body of atoms then a `ret`: the atoms and the returned values. -/
def splitBody : List Stmt → Option (List Atom × List V)
  | [.ret vs] => some ([], vs)
  | .atom a :: rest => (splitBody rest).map fun p => (a :: p.1, p.2)
  | _ => none

theorem splitBody_eq : ∀ {body : List Stmt} {as : List Atom} {vs : List V},
    splitBody body = some (as, vs) → body = as.map Stmt.atom ++ [Stmt.ret vs]
  | [], _, _, h => by simp [splitBody] at h
  | [.ret vs'], as, vs, h => by
    simp only [splitBody, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    rfl
  | .atom a :: rest, as, vs, h => by
    simp only [splitBody, Option.map_eq_some_iff, Prod.exists] at h
    obtain ⟨as', vs', h1, h2⟩ := h
    simp only [Prod.mk.injEq] at h2
    obtain ⟨rfl, rfl⟩ := h2
    rw [splitBody_eq h1]
    rfl
  | .ret _ :: _ :: _, _, _, h | .ite .. :: _, _, _, h | .match_ .. :: _, _, _, h
  | .call .. :: _, _, _, h | .callIf .. :: _, _, _, h | .dispatch .. :: _, _, _, h => by
    simp [splitBody] at h

/-- The blocks of the `KECCAK` atoms of a list, in order. -/
def keccakBlocks (atoms : List Atom) : List (List V × List V) :=
  atoms.filterMap fun a => match a with
    | .keccak i o _ _ => some (i, o)
    | _ => none

/-! ## Loads -/

/-- `x` is loaded through `p` at offset `o`. -/
def isLoadAt (x p : V) (o : ℕ) : Atom → Bool
  | .load d q off => decide (d = x) && decide (q = p) && off == o
  | _ => false

theorem load_sound {rd : Reader} {σ : Val} {atoms : List Atom} {x p : V} {o : ℕ}
    (h : atoms.any (isLoadAt x p o) = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    LoadHolds rd (σ p) o (σ x) := by
  obtain ⟨a, hp, ha⟩ := any_holds h hat
  cases a <;> simp only [isLoadAt, Bool.false_eq_true, Bool.and_eq_true, decide_eq_true_eq,
    beq_iff_eq] at hp
  obtain ⟨⟨rfl, rfl⟩, rfl⟩ := hp
  exact ha

/-- Every message cell `i` is a value loaded through `p` at offset `i`. -/
def loadsOk (atoms : List Atom) (p : V) (msg : List (Option V)) : Bool :=
  (List.range msg.length).all fun i => match msg.getD i none with
    | some v => atoms.any (isLoadAt v p i)
    | none => false

theorem loads_sound {rd : Reader} {σ : Val} {atoms : List Atom} {p : V} {msg : List (Option V)}
    (h : loadsOk atoms p msg = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    ReadsAt rd (σ p) (msg.map (srcVal σ)) := by
  intro i hi
  rw [List.length_map] at hi
  simp only [loadsOk, List.all_eq_true, List.mem_range] at h
  have hi' := h i hi
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at hi'
  rw [List.getElem_map]
  revert hi'
  cases msg[i] with
  | none => simp
  | some v => intro hv; exact load_sound hv hat

/-! ## Straight-line digests -/

/-- The returned values are copies of the chain's digest cells. -/
def retOk (atoms : List Atom) (s : ChainSpec) (r0 r1 : V) : Bool :=
  atoms.any (isCopyAt r0 (s.outV (s.nb - 1) 0)) && atoms.any (isCopyAt r1 (s.outV (s.nb - 1) 1))

/-- **A straight-line padded chain from the zero state returns the digest of its cells.** -/
theorem straight_digest {rd : Reader} {σ : Val} {atoms : List Atom} {s : ChainSpec} {r0 r1 : V}
    (hc : s.check atoms = true) (hfin : s.final = true) (hinit : s.init = none)
    (hr : retOk atoms s r0 r1 = true) (hat : ∀ a ∈ atoms, a.Holds rd σ) :
    [σ r0, σ r1] = digestCells (keccak256 (cellsBytes ((s.vals σ).take (s.len / 16)))) ∧
      AllCanonical ((s.vals σ).take (s.len / 16)) := by
  have h0 : ∀ c : Fin 13, s.initCell σ c =
      cellsOfState (absorbChunks 0 zeroState []) false c := fun c => by
    rw [ChainSpec.initCell, hinit]
    exact (cellsOfState_zero false c).symm
  obtain ⟨hd, hcan⟩ := chain_final hc hfin hat (pre := []) (n := 0) rfl h0
  rw [List.nil_append] at hd
  simp only [retOk, Bool.and_eq_true] at hr
  refine ⟨?_, hcan⟩
  rw [copy_sound hr.1 hat, copy_sound hr.2 hat, digestCells, ← hd]

/-! ## `da_hash_roots__L{n}` -/

/-- The chain of `da_hash_roots__L{n}`: `4n` cells loaded as `.n 1 … .n (4n)`, `64n` bytes. -/
def hrSpec (n : ℕ) (atoms : List Atom) : ChainSpec :=
  ⟨(List.range (4 * n)).map (fun i => some (V.n (i + 1))), 64 * n, true, none, keccakBlocks atoms⟩

/-- `da_hash_roots__L{n}`'s body is the chain over the cells at its argument. -/
def hrOk (n : ℕ) (f : Fn) : Bool :=
  decide (f.params = [V.n 0]) &&
  match splitBody f.body with
  | some (atoms, [r0, r1]) =>
    (hrSpec n atoms).check atoms && retOk atoms (hrSpec n atoms) r0 r1 &&
      loadsOk atoms (V.n 0) (hrSpec n atoms).msg
  | _ => false

set_option maxRecDepth 100000 in
theorem hr_all : ∀ n < 17, hrOk n (coreProgram.getD (377 + n) default) = true := by
  decide +kernel

/-- The names of `da_hash_roots`' specializations, `n ≤ 16`. -/
def hrNames : List String :=
  ["da_hash_roots__L0", "da_hash_roots__L1", "da_hash_roots__L2", "da_hash_roots__L3", "da_hash_roots__L4", "da_hash_roots__L5", "da_hash_roots__L6", "da_hash_roots__L7", "da_hash_roots__L8", "da_hash_roots__L9", "da_hash_roots__L10", "da_hash_roots__L11", "da_hash_roots__L12", "da_hash_roots__L13", "da_hash_roots__L14", "da_hash_roots__L15", "da_hash_roots__L16"]

set_option maxRecDepth 100000 in
theorem hr_idx : ∀ n < 17, coreProgram.indexOf? (hrNames.getD n "") = some (377 + n) := by
  decide +kernel

theorem find_of_idx {name : String} {j : ℕ} (h : coreProgram.indexOf? name = some j)
    (hj : j < coreProgram.length) : coreProgram.find? name = some (coreProgram.getD j default) := by
  refine Program.find?_of_indexOf? h ?_
  rw [List.getElem?_eq_getElem hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]
  rfl

/-- **`da_hash_roots__L{n}`** returns the digest of the `4n` canonical cells at its argument. -/
theorem hashRoots_sound {n : ℕ} (hn : n < 17) {rd : Reader} {args rets : List E}
    (h : coreProgram.Rel rd (hrNames.getD n "") args rets) :
    ∃ p, args = [p] ∧ ClaimListOut rd p n rets := by
  have hf := find_of_idx (hr_idx n hn) (by rw [coreProgram_length]; omega)
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem hf args rets).mp h
  have hok := hr_all n hn
  set f := coreProgram.getD (377 + n) default
  simp only [hrOk, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hpar, hok⟩ := hok
  split at hok
  · rename_i atoms r0 r1 hsb
    simp only [Bool.and_eq_true] at hok
    obtain ⟨⟨hc, hr⟩, hl⟩ := hok
    rw [splitBody_eq hsb, holdsList_atoms_ret] at hb
    obtain ⟨hat, hret⟩ := hb
    obtain ⟨hd, hcan⟩ := straight_digest hc rfl rfl hr hat
    have hlen : ((hrSpec n atoms).vals σ).length = 4 * n := by
      simp [ChainSpec.vals, hrSpec]
    have htake : ((hrSpec n atoms).vals σ).take ((hrSpec n atoms).len / 16) =
        (hrSpec n atoms).vals σ := by
      rw [List.take_of_length_le]
      rw [hlen]; simp only [hrSpec]; omega
    rw [htake] at hd hcan
    rw [hpar] at hp
    refine ⟨σ (V.n 0), by rw [← hp]; rfl, (hrSpec n atoms).vals σ, hlen, loads_sound hl hat, hcan, ?_⟩
    rw [← hret, ← hd]
    rfl
  · exact absurd hok (by simp)

/-! ## `da_list_digest` -/

theorem core29_body : Fn.body Data.core29 =
    [.dispatch (.n 1) hrNames [.n 0]
      [.n 2, .n 3], .atom (.copy (.n 4) (.n 2)), .atom (.copy (.n 5) (.n 3)), .ret [.n 4, .n 5]] :=
  stmtsEqb_sound (by decide +kernel)

/-- **`da_list_digest` computes the DA list's digest.** -/
theorem da_list_digest_sound : da_list_digest_sound_Spec := by
  intro rd args rets h
  obtain ⟨σ, hp, hb⟩ := (rel_iff_sem find_da_list_digest args rets).mp h
  rw [core29_body] at hb
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at hb
  obtain ⟨⟨j, hj, hsel, hcall⟩, e4, e5, hr⟩ := hb
  have hj17 : j < 17 := hj
  rw [show hrNames[j] = hrNames.getD j "" by
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj]; rfl] at hcall
  obtain ⟨p, hpa, hout⟩ := hashRoots_sound hj17 hcall
  simp only [List.cons.injEq, and_true] at hpa
  have hp' : args = [σ (.n 0), σ (.n 1)] := by rw [← hp]; rfl
  subst hp'
  refine ⟨j, by simp only [maxDaRoots]; omega, by rw [hsel, gen_pow_eq_ofK], ?_⟩
  rw [hpa, ← hr, e4, e5]
  exact hout

end
end LeanVM.Guest.B1.Digest
