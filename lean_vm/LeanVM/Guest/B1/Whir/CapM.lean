/-
  LeanVM.Guest.B1.Whir.CapM

  The Merkle cap under a hash model: `hash_cap_node`, `verify_merkle_cap` and the climb to the
  cap's root, every node the model's answered hash of its children.
-/

module

public import LeanVM.Guest.B1.Whir.Cap
public import LeanVM.Guest.B1.ModelAux

/-!
# The Merkle cap under a hash model (TRIAGE #29, #30)

`Whir/Cap.lean` over a `HashModel`: a hashed node is the model's answered hash of its children's
digests (`CapHashedM`, from one `BLAKE2S` row under the IV, `HashModel.one_block`), and the
refutation argument climbs from a flagged cap leaf to the root over `Compile.climb` at
`Option` over `M.H` (`cap_climbM`). The generic meaning is `MeaningVerifyMerkleCapWith`,
`verify_merkle_cap_model` its soundness at every depth; at the deployed model each is the deployed
one (`capHashedM_deployed`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader} {σ : Val}

/-! ## Cap nodes -/

/-- Cap node `i` is the model's answered hash of its children's digests. -/
def CapHashedM (M : HashModel) (rd : Reader) (cap : E) (i : ℕ) : Prop :=
  ∃ l r d : Digest, CapCell rd cap (2 * i) l ∧ CapCell rd cap (2 * i + 1) r ∧
    M.H (digestBytes l ++ digestBytes r) = some d ∧ CapCell rd cap i d

/-- At the deployed model it is `CapHashed`. -/
theorem capHashedM_deployed (rd : Reader) (cap : E) (i : ℕ) :
    CapHashedM HashModel.deployed rd cap i ↔ CapHashed rd cap i := by
  simp only [CapHashedM, CapHashed, HashModel.deployed_H]
  constructor
  · rintro ⟨l, r, d, a, b, rfl, c⟩
    exact ⟨l, r, a, b, c⟩
  · rintro ⟨l, r, a, b, c⟩
    exact ⟨l, r, _, a, b, rfl, c⟩

/-- **One cap node, hashed, under a hash model**: a row of four cells under the IV is the
answered hash of the two digests they are. -/
theorem check_hashPairM {m : Fin 4 → E} {o0 o1 : E}
    (hc : M.sem.check m ivCells.1 ivCells.2 o0 o1 (metadataCell 64 true)) :
    ∃ l r d : Digest, (m 0, m 1) = digestScalars l ∧ (m 2, m 3) = digestScalars r ∧
      M.H (digestBytes l ++ digestBytes r) = some d ∧ (o0, o1) = digestScalars d := by
  obtain ⟨l, hl⟩ := exists_digest ((M.canonical hc).1 0) ((M.canonical hc).1 1)
  obtain ⟨r, hr⟩ := exists_digest ((M.canonical hc).1 2) ((M.canonical hc).1 3)
  have hm : m = ![(digestScalars l).1, (digestScalars l).2, (digestScalars r).1,
      (digestScalars r).2] := by
    funext i
    fin_cases i
    · exact congrArg Prod.fst hl
    · exact congrArg Prod.snd hl
    · exact congrArg Prod.fst hr
    · exact congrArg Prod.snd hr
  obtain ⟨d, hd, ho⟩ := HashModel.one_block hc
  rw [hm, blockBytes_digests] at hd
  exact ⟨l, r, d, hl, hr, hd, ho⟩

/-- What `hash_cap_node(cap, c)` asks of memory under a hash model: `HashCapSem` with the model's
row. -/
def HashCapSemM (M : HashModel) (rd : Reader) (cap c : E) : Prop :=
  ∃ m0 m1 m2 m3 o0 o1 : E, LoadHolds rd (cap * (c * c * (c * c))) 0 m0 ∧
    LoadHolds rd (cap * (c * c * (c * c))) 1 m1 ∧ LoadHolds rd (cap * (c * c * (c * c))) 2 m2 ∧
    LoadHolds rd (cap * (c * c * (c * c))) 3 m3 ∧
    M.sem.check ![m0, m1, m2, m3] ivCells.1 ivCells.2 o0 o1 (metadataCell 64 true) ∧
    LoadHolds rd (cap * (c * c)) 0 o0 ∧ LoadHolds rd (cap * (gen * c * c)) 0 o1

theorem hashCapNodeT_soundM {cap c : V} {b : ℕ} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (hashCapNodeT cap c b) next kret) :
    HashCapSemM M rd (σ cap) (σ c) ∧ next := by
  simp only [hashCapNodeT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, word_iv0, word_iv1, word_md64,
    word_gen] at h
  obtain ⟨h0, h1, h2, l3, l4, l5, l6, h7, h8, h9, hc, h12, h13, l10, h14, h15, h16, h17, l11, hn⟩ := h
  rw [h1, h0] at h2
  rw [h2] at l3 l4 l5 l6
  rw [h7, h8, h9] at hc
  rw [h13, h12] at l10
  rw [h17, h16, h15, h14] at l11
  exact ⟨⟨_, _, _, _, _, _, l3, l4, l5, l6, hc, l10, l11⟩, hn⟩

/-- **`hash_cap_node` at `g^i` under a hash model**: node `i` is the answered hash of its
children. -/
theorem hashCapSemM_gen_pow {cap : E} {i : ℕ} (h : HashCapSemM M rd cap (gen ^ i)) :
    CapHashedM M rd cap i := by
  have e4 : gen ^ i * gen ^ i * (gen ^ i * gen ^ i) = gen ^ (4 * i) := by
    simp only [gen_pow_mul_gen_pow]; congr 1; ring
  have e2 : gen ^ i * gen ^ i = gen ^ (2 * i) := by rw [gen_pow_mul_gen_pow]; congr 1; ring
  have e2' : gen * gen ^ i * gen ^ i = gen ^ (2 * i + 1) := by
    rw [← pow_succ', gen_pow_mul_gen_pow]; congr 1; ring
  unfold HashCapSemM at h
  rw [e4, e2', e2] at h
  simp only [loadHolds_mul_gen_pow, Nat.add_zero, show 4 * i = 2 * (2 * i) by ring,
    show 2 * (2 * i) + 2 = 2 * (2 * i + 1) by ring,
    show 2 * (2 * i) + 3 = 2 * (2 * i + 1) + 1 by ring] at h
  obtain ⟨m0, m1, m2, m3, o0, o1, a0, a1, a2, a3, hc, l0, l1⟩ := h
  obtain ⟨l, r, d, hl, hr, hd, ho⟩ := check_hashPairM hc
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three] at hl hr
  rw [show m0 = _ from congrArg Prod.fst hl] at a0
  rw [show m1 = _ from congrArg Prod.snd hl] at a1
  rw [show m2 = _ from congrArg Prod.fst hr] at a2
  rw [show m3 = _ from congrArg Prod.snd hr] at a3
  rw [show o0 = _ from congrArg Prod.fst ho] at l0
  rw [show o1 = _ from congrArg Prod.snd ho] at l1
  exact ⟨l, r, d, ⟨a0, a1⟩, ⟨a2, a3⟩, hd, l0, l1⟩

/-! ## The loop of `verify_merkle_cap` -/

/-- One side under a hash model: `CapSideSem` with the model's row. -/
def CapSideSemM (M : HashModel) (rd : Reader) (flags cap x c : E) : Prop :=
  ∃ f, LoadHolds rd (flags * c) 0 f ∧ IsInK f ∧
    (f ≠ 0 → LoadHolds rd (flags * x) 0 1 ∧ HashCapSemM M rd cap c)

theorem capSideT_soundM {flags cap x c : V} {b : ℕ} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (capSideT flags cap x c b) True kret) :
    CapSideSemM M rd (σ flags) (σ cap) (σ x) (σ c) := by
  simp only [capSideT, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, holdsListB_append, word_one] at h
  obtain ⟨h0, l1, hK, -, hnz⟩ := h
  refine ⟨σ (.n (b + 1)), by rwa [h0] at l1, hK, fun hf => ?_⟩
  obtain ⟨h2, h3, l2, hh⟩ := hnz hf
  rw [h3, h2] at l2
  exact ⟨l2, (hashCapNodeT_soundM hh).1⟩

/-- The loop's body at the parent `x` under a hash model. -/
def CapLoopBodyM (M : HashModel) (rd : Reader) (flags cap x : E) : Prop :=
  CapSideSemM M rd flags cap x (x * x) ∧ CapSideSemM M rd flags cap x (x * x * gen)

theorem capLoop_stepM {loop : String} {fn : Fn} (hfind : coreProgram.find? loop = some fn)
    (hp : fn.params = [.n 0, .n 1, .n 2, .n 3]) (hb : fn.body = capLoopBody loop)
    (rd : Reader) (N flags cap : E) (d : ℕ) (x : E)
    (h : coreProgram.relNB M.sem rd (d + 1) loop (x :: [N, flags, cap]) []) :
    CapLoopBodyM M rd flags cap x ∧ IsInK (x * gen + N) ∧
      (x * gen + N ≠ 0 → coreProgram.relNB M.sem rd d loop (x * gen :: [N, flags, cap]) []) := by
  rw [relNB_succ_iff hfind, hp, hb, capLoopBody] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, -⟩ := hp
  simp only [holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] at h
  obtain ⟨h4, hs⟩ := h
  rw [holdsListB_noRet _ rfl] at hs
  obtain ⟨hs0, h27, h28, h29, hs⟩ := hs
  rw [holdsListB_noRet _ rfl] at hs
  obtain ⟨hs1, h52, h53, h54, h55, h56, hK, hcall, -⟩ := hs
  simp only [word_gen, List.map_cons, List.map_nil] at h28 h52 h55 hcall
  have s0 := capSideT_soundM hs0
  have s1 := capSideT_soundM hs1
  rw [h4] at s0
  rw [h29, h28, h27] at s1
  refine ⟨⟨s0, s1⟩, by rwa [h54, h53, h52] at hK, fun hne => ?_⟩
  have := hcall (by rwa [h54, h53, h52])
  rwa [h56, h55] at this

/-! ## `verify_merkle_cap` -/

/-- Node `c` of the cap's interior under a hash model: `CapFlagged` with the node hashed by the
model. -/
def CapFlaggedM (M : HashModel) (rd : Reader) (flags cap : E) (c : ℕ) : Prop :=
  ∃ f, LoadHolds rd flags c f ∧ IsInK f ∧
    (f ≠ 0 → LoadHolds rd flags (c / 2) 1 ∧ CapHashedM M rd cap c)

/-- **`verify_merkle_cap(cap, flags, D)` under a hash model** (the meaning of
`MeaningVerifyMerkleCap`, every node the model's answered hash). -/
def MeaningVerifyMerkleCapWith (M : HashModel) (D : ℕ) (rd : Reader) : List E → List E → Prop
  | [cap, flags], rets =>
      LoadHolds rd flags 1 1 ∧ CapHashedM M rd cap 1 ∧
        (∀ c, 2 ≤ c → c < 2 ^ D → CapFlaggedM M rd flags cap c) ∧
        ∃ r, CapCell rd cap 1 r ∧ rets = [(digestScalars r).1, (digestScalars r).2]
  | _, _ => False

/-- At the deployed model it is `MeaningVerifyMerkleCap`. -/
theorem meaningVerifyMerkleCapWith_deployed (D : ℕ) (rd : Reader) (args rets : List E) :
    MeaningVerifyMerkleCapWith HashModel.deployed D rd args rets ↔
      MeaningVerifyMerkleCap D rd args rets := by
  rcases args with _ | ⟨a, _ | ⟨b, _ | ⟨c, l⟩⟩⟩ <;>
    simp only [MeaningVerifyMerkleCapWith, MeaningVerifyMerkleCap, CapFlaggedM, CapFlagged,
      capHashedM_deployed]

theorem capSideSemM_gen_pow {flags cap : E} {p s : ℕ} (hs : s < 2)
    (h : CapSideSemM M rd flags cap (gen ^ p) (gen ^ (2 * p + s))) :
    CapFlaggedM M rd flags cap (2 * p + s) := by
  have hdiv : (2 * p + s) / 2 = p := by omega
  obtain ⟨f, lf, hK, hnz⟩ := h
  rw [loadHolds_gen_pow] at lf
  refine ⟨f, lf, hK, fun hf => ?_⟩
  obtain ⟨l1, hh⟩ := hnz hf
  rw [loadHolds_gen_pow] at l1
  exact ⟨by rwa [hdiv], hashCapSemM_gen_pow hh⟩

theorem capLoopBodyM_gen_pow {flags cap : E} {p : ℕ} (h : CapLoopBodyM M rd flags cap (gen ^ p)) :
    CapFlaggedM M rd flags cap (2 * p) ∧ CapFlaggedM M rd flags cap (2 * p + 1) := by
  have e0 : gen ^ p * gen ^ p = gen ^ (2 * p + 0) := by rw [gen_pow_mul_gen_pow]; congr 1; ring
  have e1 : gen ^ p * gen ^ p * gen = gen ^ (2 * p + 1) := by
    rw [gen_pow_mul_gen_pow, ← pow_succ]; congr 1; ring
  obtain ⟨h0, h1⟩ := h
  rw [e0] at h0
  rw [e1] at h1
  have r0 := capSideSemM_gen_pow (p := p) (s := 0) (by omega) h0
  have r1 := capSideSemM_gen_pow (p := p) (s := 1) (by omega) h1
  rw [Nat.add_zero] at r0
  exact ⟨r0, r1⟩

/-- **`verify_merkle_cap` is sound under a hash model**, at a depth `2 ≤ D ≤ 8`, for a compiled
function whose body is `vmcBody` with its loop helper's body `capLoopBody`. -/
theorem verify_merkle_cap_model {name loop : String} {f lf : Fn} (D : ℕ) (hD : 2 ≤ D) (hD8 : D ≤ 8)
    (hfind : coreProgram.find? name = some f) (hp : f.params = [.n 0, .n 1])
    (hb : f.body = vmcBody (word (gSquaresBits.getD (D - 1) 0) 0 0) loop)
    (hlf : coreProgram.find? loop = some lf) (hlp : lf.params = [.n 0, .n 1, .n 2, .n 3])
    (hlb : lf.body = capLoopBody loop) (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd name args rets) : MeaningVerifyMerkleCapWith M D rd args rets := by
  have hW : word (gSquaresBits.getD (D - 1) 0) 0 0 = gen ^ 2 ^ (D - 1) :=
    word_gSquares (by simp only [sizeBits]; omega)
  have hm1 : 1 < 2 ^ (D - 1) := Nat.one_lt_two_pow (by omega)
  have hmo : 2 ^ (D - 1) < ordG := by
    have : 2 ^ (D - 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by omega)
    simp only [ordG]; omega
  have hall : ∀ flags cap, coreProgram.RelB M.sem rd loop [gen, gen ^ 2 ^ (D - 1), flags, cap] [] →
      ∀ c, 2 ≤ c → c < 2 ^ D → CapFlaggedM M rd flags cap c := by
    intro flags cap hl
    rw [← pow_one gen] at hl
    obtain ⟨m, hm, hN, hfirst, hB⟩ := loopB_sound (P := coreProgram) (f := loop)
      (ps := [gen ^ 2 ^ (D - 1), flags, cap]) (N := gen ^ 2 ^ (D - 1))
      (B := fun x => CapLoopBodyM M rd flags cap x)
      (fun d x hx => capLoop_stepM hlf hlp hlb rd _ flags cap d x hx) 1 (by rwa [pow_one] at hl ⊢)
    have hm' : m = 2 ^ (D - 1) := by
      rcases Nat.lt_trichotomy m (2 ^ (D - 1)) with h | h | h
      · have := gen_pow_inj (a := 2 ^ (D - 1)) (b := m) (by simp only [ordG] at hmo; omega)
          (by simp only [ordG] at hmo; omega) hN
        omega
      · exact h
      · exact absurd rfl (hfirst (2 ^ (D - 1)) hm1 h)
    subst hm'
    exact (interior_iff _ D (by omega)).mp fun j h1 h2 => capLoopBodyM_gen_pow (hB j h1 h2)
  have e4 : ∀ cap : E, cap * (gen * gen * (gen * gen)) = cap * gen ^ 4 := fun cap => by ring
  have e2 : ∀ cap : E, cap * (gen * gen) = cap * gen ^ 2 := fun cap => by ring
  have e3 : ∀ cap : E, cap * (gen * gen * gen) = cap * gen ^ 3 := fun cap => by ring
  rw [relB_iff_sem hfind, hb, hp, vmcBody] at h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, List.map_cons, List.map_nil, word_iv0,
    word_iv1, word_md64, word_one, word_gen, word_sixteen, hW] at h
  obtain ⟨σ, hp, h2, h3, l4, l5, l6, l7, h8, h9, h10, hc, l11, l12, h13, l13, h14, h15, h16, h17, h18,
    hK, hcall, l19, l20, hret⟩ := h
  subst hp hret
  simp only [MeaningVerifyMerkleCapWith]
  rw [h3, h2] at l4 l5 l6 l7
  rw [h8, h9, h10] at hc
  rw [h13] at l13
  have hroot : CapHashedM M rd (σ (.n 0)) 1 := by
    refine hashCapSemM_gen_pow (i := 1) ?_
    rw [pow_one]
    refine ⟨_, _, _, _, _, _, ?_, ?_, ?_, ?_, hc, ?_, ?_⟩
    · rw [e4]; exact l4
    · rw [e4]; exact l5
    · rw [e4]; exact l6
    · rw [e4]; exact l7
    · rw [e2, loadHolds_gen_pow]; exact l11
    · rw [e3, loadHolds_gen_pow]; exact l12
  have hne : σ (.n 16) ≠ 0 := by
    rw [h16, h14, h15]
    intro h0
    have := gen_pow_inj (a := 1) (b := 2 ^ (D - 1)) (by decide)
      (by simp only [ordG] at hmo; omega) (by rw [pow_one]; exact e_add_eq_zero_iff.mp h0)
    omega
  have hl := hcall hne
  rw [h17, h18] at hl
  obtain ⟨l, r, d, hl2, hr3, hd, hlr⟩ := hroot
  refine ⟨l13, ⟨l, r, d, hl2, hr3, hd, hlr⟩, hall _ _ hl, d, hlr, ?_⟩
  rw [Option.some.inj (l19.2.symm.trans hlr.1.2), Option.some.inj (l20.2.symm.trans hlr.2.2)]

/-! ## The root at the end of a flagged path -/

/-- `climb` (V:526) over a hash model, one level. -/
theorem climbM_cons (node s : Digest) (q : ℕ) (ss : List Digest) :
    climb (m := Option) M.H node q (s :: ss) =
      (if q % 2 = 0 then M.H (digestBytes node ++ digestBytes s)
        else M.H (digestBytes s ++ digestBytes node)).bind fun p ↦ climb (m := Option) M.H p (q / 2) ss := by
  simp only [climb]
  split <;> rfl

/-- A hashed node under a hash model, from either child: the parent is the answered hash of the
child and its sibling in order. -/
theorem capHashedM_climb {cap : E} {c : ℕ} (hh : CapHashedM M rd cap (c / 2)) :
    (if c % 2 = 0 then M.H (digestBytes (capNode rd cap c) ++ digestBytes (capNode rd cap (capSib c)))
      else M.H (digestBytes (capNode rd cap (capSib c)) ++ digestBytes (capNode rd cap c))) =
      some (capNode rd cap (c / 2)) := by
  obtain ⟨l, r, d, hl, hr, hd, hp⟩ := hh
  rw [capNode_eq hp]
  by_cases he : c % 2 = 0
  · simp only [he, ↓reduceIte, capSib]
    rw [capNode_eq (show CapCell rd cap c l by rw [show c = 2 * (c / 2) by omega]; exact hl),
      capNode_eq (show CapCell rd cap (c + 1) r by rw [show c + 1 = 2 * (c / 2) + 1 by omega]; exact hr)]
    exact hd
  · simp only [he, ↓reduceIte, capSib]
    rw [capNode_eq (show CapCell rd cap (c - 1) l by rw [show c - 1 = 2 * (c / 2) by omega]; exact hl),
      capNode_eq (show CapCell rd cap c r by rw [show c = 2 * (c / 2) + 1 by omega]; exact hr)]
    exact hd

/-- **The refutation argument under a hash model**: in a cap of depth `D` whose interior nodes are
`CapFlaggedM` and whose root is hashed, from a node `c` of level `h ≤ D` whose parent's flag is
`1`, `climb` (V:526) at `Option` over `M.H` and the cap's siblings answers the root. -/
theorem cap_climbM {flags cap : E} {D : ℕ} (hroot : CapHashedM M rd cap 1)
    (hint : ∀ c, 2 ≤ c → c < 2 ^ D → CapFlaggedM M rd flags cap c) :
    ∀ h c, 1 ≤ h → h ≤ D → 2 ^ h ≤ c → c < 2 ^ (h + 1) → LoadHolds rd flags (c / 2) 1 →
      climb (m := Option) M.H (capNode rd cap c) (c - 2 ^ h) (capSibs rd cap h c) =
        some (capNode rd cap 1) := by
  intro h
  induction h with
  | zero => intro c h1; omega
  | succ h ih =>
    intro c _ hD hlo hhi hf
    have hp1 : 2 ^ (h + 1) = 2 * 2 ^ h := by ring
    have hp2 : 2 ^ (h + 1 + 1) = 2 * 2 ^ (h + 1) := by ring
    have hpar : CapHashedM M rd cap (c / 2) ∧ (1 ≤ h → LoadHolds rd flags (c / 2 / 2) 1) := by
      rcases Nat.eq_zero_or_pos h with h0 | hpos
      · subst h0
        rw [show c / 2 = 1 by simp at hlo hhi; omega]
        exact ⟨hroot, fun h => absurd h (by omega)⟩
      · have hpos' : 1 ≤ 2 ^ h := Nat.one_le_two_pow
        have hle : 2 ^ (h + 1) ≤ 2 ^ D := Nat.pow_le_pow_right (by decide) hD
        have hh2 : 2 ≤ 2 ^ h := by
          have := Nat.pow_le_pow_right (show 0 < 2 by decide) hpos; simpa using this
        obtain ⟨fv, lf, -, hnz⟩ := hint (c / 2) (by omega) (by omega)
        have : fv = 1 := Option.some.inj (lf.2.symm.trans hf.2)
        obtain ⟨hf', hh⟩ := hnz (by rw [this]; exact one_ne_zero)
        exact ⟨hh, fun _ => hf'⟩
    have hq : (c - 2 ^ (h + 1)) % 2 = c % 2 := by omega
    have hq2 : (c - 2 ^ (h + 1)) / 2 = c / 2 - 2 ^ h := by omega
    rw [capSibs, climbM_cons, hq, hq2, capHashedM_climb hpar.1, Option.bind_some]
    rcases Nat.eq_zero_or_pos h with h0 | hpos
    · subst h0
      rw [show c / 2 = 1 by simp at hlo hhi; omega]
      rfl
    · exact ih (c / 2) hpos (by omega) (by omega) (by omega) (hpar.2 hpos)

/-! ## The specializations -/

set_option maxRecDepth 100000 in
/-- `verify_merkle_cap__L4` under a hash model. -/
theorem verify_merkle_cap_L4_model (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "verify_merkle_cap__L4" args rets) :
    MeaningVerifyMerkleCapWith M 4 rd args rets :=
  verify_merkle_cap_model (loop := "__loop454") 4 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 674) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1006) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets h

set_option maxRecDepth 100000 in
/-- `verify_merkle_cap__L5` under a hash model. -/
theorem verify_merkle_cap_L5_model (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "verify_merkle_cap__L5" args rets) :
    MeaningVerifyMerkleCapWith M 5 rd args rets :=
  verify_merkle_cap_model (loop := "__loop433") 5 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 586) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 978) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets h

set_option maxRecDepth 100000 in
/-- `verify_merkle_cap__L6` under a hash model. -/
theorem verify_merkle_cap_L6_model (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "verify_merkle_cap__L6" args rets) :
    MeaningVerifyMerkleCapWith M 6 rd args rets :=
  verify_merkle_cap_model (loop := "__loop431") 6 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 583) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 975) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets h

set_option maxRecDepth 100000 in
/-- `verify_merkle_cap__L7` under a hash model. -/
theorem verify_merkle_cap_L7_model (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "verify_merkle_cap__L7" args rets) :
    MeaningVerifyMerkleCapWith M 7 rd args rets :=
  verify_merkle_cap_model (loop := "__loop456") 7 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 683) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 1008) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets h

set_option maxRecDepth 100000 in
/-- `verify_merkle_cap__L8` under a hash model. -/
theorem verify_merkle_cap_L8_model (rd : Reader) (args rets : List E)
    (h : coreProgram.RelB M.sem rd "verify_merkle_cap__L8" args rets) :
    MeaningVerifyMerkleCapWith M 8 rd args rets :=
  verify_merkle_cap_model (loop := "__loop429") 8 (by decide) (by decide)
    (Program.find?_of_indexOf? (j := 579) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel))
    (Program.find?_of_indexOf? (j := 972) (by decide +kernel) rfl) rfl
    (stmtsEqb_sound (by decide +kernel)) rd args rets h

end
end LeanVM.Guest.B1
