/-
  LeanVM.Guest.B1.Opening.QueriesMain

  `opening_queries`: the soundness direction of its meaning, from its body and its loop's.
-/

module

public import LeanVM.Guest.B1.Opening.QueriesLoop

/-!
# `opening_queries` is sound (G:1246-1269, TRIAGE #40)

`oqLoop_step`: the loop helper satisfies `loop_iff`'s step with its body of atoms
(`loop_step_atoms`). `oqMain1_sound`, `oqMain0_sound`: the function's relation, its loop's
iterations (`oqIter1_sound`, `oqIter0_sound`) and its start give `MeaningOpeningQueries`, the
bit pointers pointing to bits.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

variable {rd : Reader}

/-- The loop's parameters. -/
def oqLoopParams : List V := [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6, .n 7]

/-- A list literal of atoms. -/
macro "atoms_lit" : tactic => `(tactic| (repeat' apply allAtoms_cons) <;> exact allAtoms_nil)

/-- A list literal of atoms. -/
theorem allAtoms_of_forall {ss : List Stmt} (h : ∀ s ∈ ss, ∃ a, s = .atom a) : AllAtoms ss := h

theorem oqPadT_atoms (pr : ℕ) : AllAtoms (oqPadT pr) :=
  allAtoms_of_forall fun x hx => by simp [oqPadT] at hx; rcases hx with h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqXorT_atoms (s : Oq) (b pr kL k c : ℕ) : AllAtoms (oqXorT s b pr kL k c) := by
  unfold oqXorT
  dsimp only
  split
  · exact allAtoms_cons allAtoms_nil
  · split
    · exact allAtoms_cons allAtoms_nil
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)

theorem oqBlockT_atoms (s : Oq) (b pr kL k : ℕ) : AllAtoms (oqBlockT s b pr kL k) := by
  unfold oqBlockT
  split
  · exact allAtoms_cons allAtoms_nil
  · exact allAtoms_append (allAtoms_map_flatten fun _ _ => oqXorT_atoms _ _ _ _ _ _)
      (allAtoms_cons allAtoms_nil)

theorem oqLeafT_atoms (s : Oq) (b pr kL : ℕ) : AllAtoms (oqLeafT s b pr kL) :=
  allAtoms_map_flatten fun _ _ => oqBlockT_atoms _ _ _ _ _

theorem oqLevelT_atoms (s : Oq) (bp : V) (pr kL ch l : ℕ) : AllAtoms (oqLevelT s bp pr kL ch l) :=
  allAtoms_of_forall fun x hx => by
    simp only [oqLevelT, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqPathT_atoms (s : Oq) (bp : V) (pr kL ch : ℕ) : AllAtoms (oqPathT s bp pr kL ch) :=
  allAtoms_append (allAtoms_cons (allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))))
    (allAtoms_map_flatten fun _ _ => oqLevelT_atoms _ _ _ _ _ _)

theorem oqCapBitT_atoms (s : Oq) (bp : V) (ch j : ℕ) : AllAtoms (oqCapBitT s bp ch j) :=
  allAtoms_of_forall fun x hx => by
    simp only [oqCapBitT, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with h | h | h | h | h | h <;> exact ⟨_, h⟩

theorem oqCapT_atoms (s : Oq) (bp cap flags : V) (kL ch : ℕ) : AllAtoms (oqCapT s bp cap flags kL ch) := by
  unfold oqCapT
  refine allAtoms_append (allAtoms_append ?_ (allAtoms_map_flatten fun _ _ => oqCapBitT_atoms _ _ _ _)) ?_
  all_goals atoms_lit

theorem oqQueryT_atoms (s : Oq) (bp cap flags wp : V) (b : ℕ) (emit : Bool) (pr : ℕ) :
    AllAtoms (oqQueryT s bp cap flags wp b emit pr) := by
  unfold oqQueryT
  refine allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append
    (allAtoms_append (oqRowT_atoms _ _) (oqPacksT_atoms _ _)) (oqDotT_atoms _ _ _)) ?_)
    (oqLeafT_atoms _ _ _ _)) (oqPathT_atoms _ _ _ _ _)) (oqCapT_atoms _ _ _ _ _ _)
  split
  · exact oqPadT_atoms _
  · exact allAtoms_nil

theorem atoms_list {ss : List Stmt} (h : ∀ s ∈ ss, ∃ a, s = .atom a) : AllAtoms ss := h

theorem oqLoop1A_atoms (s : Oq) (odd : ℕ) : AllAtoms (oqLoop1A s odd) := by
  unfold oqLoop1A
  dsimp only
  refine allAtoms_append (allAtoms_append (allAtoms_append (allAtoms_append ?_ (oqQueryT_atoms _ _ _ _ _ _ _ _))
    ?_) (oqQueryT_atoms _ _ _ _ _ _ _ _)) ?_
  all_goals atoms_lit

theorem oqLoop0A_atoms (s : Oq) : AllAtoms (oqLoop0A s) := by
  unfold oqLoop0A
  dsimp only
  refine allAtoms_append (allAtoms_append ?_ (oqQueryT_atoms _ _ _ _ _ _ _ _)) ?_
  all_goals atoms_lit

theorem oqMainA_atoms (s : Oq) (odd : ℕ) : AllAtoms (oqMainA s odd) := by
  unfold oqMainA
  dsimp only
  refine allAtoms_append (allAtoms_append ?_ ?_) ?_
  · atoms_lit
  · split
    · exact allAtoms_append (allAtoms_append (allAtoms_cons allAtoms_nil) (oqQueryT_atoms _ _ _ _ _ _ _ _))
        (allAtoms_cons (allAtoms_cons allAtoms_nil))
    · exact allAtoms_cons (allAtoms_cons allAtoms_nil)
  · exact allAtoms_cons (allAtoms_cons (allAtoms_cons allAtoms_nil))

/-! ## The loop's step -/

theorem oqLoop1_step {s : Oq} {odd : ℕ} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop) (ps : List E) (hps : ps.length = 7) :
    ∀ d x, coreProgram.relN rd (d + 1) loop (x :: ps) [] ↔
      AtomsBody rd fl.params (oqLoop1A s odd) (x :: ps) ∧ IsInK (x * gen + ps.headD 0) ∧
        (x * gen + ps.headD 0 ≠ 0 → coreProgram.relN rd d loop (x * gen :: ps) []) := by
  intro d x
  obtain ⟨N, rest, rfl⟩ : ∃ N rest, ps = N :: rest := by
    match ps, hps with
    | N :: rest, _ => exact ⟨N, rest, rfl⟩
  refine loop_step_atoms hfl hbl (oqLoop1A_atoms s odd) (fun σ hp hA => ?_) d
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil] at hp
  set c := oqC1 s with hc
  have a7 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.const (.n (c + 7)) (word 2 0 0)) ∈ _)
  have a8 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.mul (.n (c + 8)) (.n 0) (.n (c + 7))) ∈ _)
  have a9 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.add (.n (c + 9)) (.n (c + 8)) (.n 1)) ∈ _)
  have a10 := hA _ (by simp [oqLoop1A, ← hc] : Stmt.atom (.const (.n (c + 10)) (word 2 0 0)) ∈ _)
  have a11 := hA _ (by simp [oqLoop1A, ← hc] :
    Stmt.atom (.mul (.n (c + 11)) (.n 0) (.n (c + 10))) ∈ _)
  simp only [Atom.Holds] at a7 a8 a9 a10 a11
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a9, a8, a7, word_gen, h0, h1], ?_⟩
  simp [a11, a10, word_gen, h0, h1]

theorem oqLoop0_step {s : Oq} {loop : String} {fl : Fn}
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop) (ps : List E) (hps : ps.length = 7) :
    ∀ d x, coreProgram.relN rd (d + 1) loop (x :: ps) [] ↔
      AtomsBody rd fl.params (oqLoop0A s) (x :: ps) ∧ IsInK (x * gen + ps.headD 0) ∧
        (x * gen + ps.headD 0 ≠ 0 → coreProgram.relN rd d loop (x * gen :: ps) []) := by
  intro d x
  obtain ⟨N, rest, rfl⟩ : ∃ N rest, ps = N :: rest := by
    match ps, hps with
    | N :: rest, _ => exact ⟨N, rest, rfl⟩
  refine loop_step_atoms hfl hbl (oqLoop0A_atoms s) (fun σ hp hA => ?_) d
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil] at hp
  set c := oqC0 s with hc
  have a5 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.const (.n (c + 5)) (word 2 0 0)) ∈ _)
  have a6 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.mul (.n (c + 6)) (.n 0) (.n (c + 5))) ∈ _)
  have a7 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.add (.n (c + 7)) (.n (c + 6)) (.n 1)) ∈ _)
  have a8 := hA _ (by simp [oqLoop0A, ← hc] : Stmt.atom (.const (.n (c + 8)) (word 2 0 0)) ∈ _)
  have a9 := hA _ (by simp [oqLoop0A, ← hc] :
    Stmt.atom (.mul (.n (c + 9)) (.n 0) (.n (c + 8))) ∈ _)
  simp only [Atom.Holds] at a5 a6 a7 a8 a9
  simp only [List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  subst hr
  refine ⟨by rw [a7, a6, a5, word_gen, h0, h1], ?_⟩
  simp [a9, a8, word_gen, h0, h1]

/-! ## The function -/

/-- What the start of the function gives: `1 = μ·λ`, the loop's guard `1 + N` and start `1`, and
at an even count the chain's first word `0`. -/
theorem oqMainA_basic {s : Oq} {odd : ℕ} {σ : Val}
    (hA : ∀ a, Stmt.atom a ∈ oqMainA s odd → a.Holds rd σ) :
    σ (.n 8) * σ (.n 2) = 1 ∧ σ (.n (oqMK s odd + 1)) = 1 + σ (.n 6) ∧
      σ (.n (oqMK s odd + 2)) = 1 ∧ (odd ≠ 1 → LoadHolds rd (σ (.n 11)) 0 0) := by
  set k := oqMK s odd with hk
  have m0 := hA _ (by simp [oqMainA] : Stmt.atom (.const (.n 7) (word 1 0 0)) ∈ _)
  have m1 := hA _ (by simp [oqMainA] : Stmt.atom (.mul (.n 7) (.n 8) (.n 2)) ∈ _)
  have m2 := hA _ (by simp [oqMainA, ← hk] : Stmt.atom (.const (.n k) (word 1 0 0)) ∈ _)
  have m3 := hA _ (by simp [oqMainA, ← hk] : Stmt.atom (.add (.n (k + 1)) (.n k) (.n 6)) ∈ _)
  have m4 := hA _ (by simp [oqMainA, ← hk] : Stmt.atom (.const (.n (k + 2)) (word 1 0 0)) ∈ _)
  simp only [Atom.Holds] at m0 m1 m2 m3 m4
  refine ⟨by rw [← m1, m0, word_one], by rw [m3, m2, word_one], by rw [m4, word_one], fun h1 => ?_⟩
  have c1 := hA _ (by simp [oqMainA, h1] : Stmt.atom (.const (.n 12) (word 0 0 0)) ∈ _)
  have c2 := hA _ (by simp [oqMainA, h1] : Stmt.atom (.load (.n 12) (.n 11) 0) ∈ _)
  simp only [Atom.Holds] at c1 c2
  rw [c1, word_zero] at c2
  exact c2

/-- The odd first query of the function's start, and the chain's first word, its value times
`μ`. -/
theorem oqMainA_odd {s : Oq} (hs : s.RowShape) (hcd : 2 ≤ s.cd) (hcd8 : s.cd ≤ 8) {σ : Val}
    (hA : ∀ a, Stmt.atom a ∈ oqMainA s 1 → a.Holds rd σ)
    (hbool : ∀ bp, LoadHolds rd (σ (.n 4)) 0 bp →
      ∀ l < s.pd + s.cd, ∀ w, LoadHolds rd bp l w → w = 0 ∨ w = 1) :
    ∃ (bp : E) (q : ℕ) (r : List K) (d : E), LoadHolds rd (σ (.n 4)) 0 bp ∧
      q < 2 ^ (s.pd + s.cd) ∧ (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd (σ (.n 0)) (σ (.n 1)) (σ (.n 5)) q r d ∧
      LoadHolds rd (σ (.n 11)) 0 (d * σ (.n 8)) := by
  have mem : ∀ a, Stmt.atom a ∈ oqQueryT s (.n 12) (.n 0) (.n 1) (.n 5) 13 true 0 →
      a.Holds rd σ := fun a ha => hA a (by
    simp only [oqMainA, ↓reduceIte, List.mem_append]; simp_all)
  have l12 := hA _ (by simp [oqMainA] : Stmt.atom (.load (.n 12) (.n 4) 0) ∈ _)
  have c1 := hA _ (by simp [oqMainA] :
    Stmt.atom (.mul (.n (oqMK s 1 - 1)) (.n (oqDot s 13)) (.n 8)) ∈ _)
  have c2 := hA _ (by simp [oqMainA] : Stmt.atom (.load (.n (oqMK s 1 - 1)) (.n 11) 0) ∈ _)
  simp only [Atom.Holds] at c1
  obtain ⟨-, -, hpd, -, -, -⟩ := oqQuery_pieces mem
  obtain ⟨e1, z⟩ := oqPad_values (hpd rfl)
  obtain ⟨q, hq, hb, ho⟩ := oqQuery_sound_bits hs hcd hcd8 mem e1 z (hbool _ l12)
  refine ⟨_, q, _, _, l12, hq, hb, ho, ?_⟩
  have := c2
  simp only [Atom.Holds, c1] at this
  exact this

/-- A loop iteration's parameters. -/
theorem atomsBody_params {fl : Fn} (hpl : fl.params = oqLoopParams) {A : List Stmt}
    {x N qptrs cap flags wp ch mu : E}
    (h : AtomsBody rd fl.params A [x, N, qptrs, cap, flags, wp, ch, mu]) :
    ∃ σ : Val, (∀ a, Stmt.atom a ∈ A → a.Holds rd σ) ∧ σ (.n 0) = x ∧ σ (.n 1) = N ∧
      σ (.n 2) = qptrs ∧ σ (.n 3) = cap ∧ σ (.n 4) = flags ∧ σ (.n 5) = wp ∧ σ (.n 6) = ch ∧
      σ (.n 7) = mu := by
  obtain ⟨σ, hp, hA⟩ := h
  rw [hpl] at hp
  simp only [oqLoopParams, List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨h0, h1, h2, h3, h4, h5, h6, h7, -⟩ := hp
  exact ⟨σ, hA, h0, h1, h2, h3, h4, h5, h6, h7⟩

/-- **`opening_queries` at level 0 is sound** (G:1246-1269): with the bit pointers pointing to
bits, its relation is `MeaningOpeningQueries`. -/
theorem oqMain1_sound {s : Oq} (hs : s.RowShape) (hb1 : s.base = 1) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {odd : ℕ} (hodd : odd ≤ 1) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s odd loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop1T s odd loop)
    {cap flags lam lamN qptrs wp nG : E} {rets : List E}
    (hbits : ∀ N, nG = gen ^ N → N < ordG →
      QueryBitsBool rd qptrs (oqCount odd s.base N) (s.pd + s.cd))
    (h : coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries odd s.base s.I (s.pd + s.cd) s.cd rd
      [cap, flags, lam, lamN, qptrs, wp, nG] rets := by
  rw [rel_iff_sem hfm, hbm, hpm] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, -⟩ := hp
  rw [oqMainT, holdsList_append, holdsList_atoms (oqMainA_atoms s odd)] at h
  obtain ⟨hA, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨hK, hcall, e3, e4, e5, hret⟩ := h
  -- the start and the loop
  obtain ⟨hmu, hg, hst, h0even⟩ := oqMainA_basic hA
  have hlam : σ (.n 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmu; exact zero_ne_one hmu
  have hmuinv : σ (.n 8) = (σ (.n 2))⁻¹ := eq_inv_of_mul_eq_one_left hmu
  set ps : List E := [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1), σ (.n 5), σ (.n 11), σ (.n 8)]
    with hps
  have hstep := oqLoop1_step (rd := rd) hfl hpl hbl ps (by simp [hps])
  obtain ⟨m, hm, hnG, hB⟩ := (guarded_loop_iff hstep).mp ⟨by
    show IsInK (1 + σ (.n 6)); rw [← hg]; exact hK, fun hne => by
    have := hcall (by rw [hg]; exact hne)
    rwa [hst] at this⟩
  have hbool := hbits m (by rw [← p6]; exact hnG) hm
  rw [hb1] at hbool
  simp only [oqCount, ↓reduceIte] at hbool
  -- the iterations
  have hit : ∀ j < m, ∃ (bp1 bp2 : E) (q1 q2 : ℕ) (r1 r2 : List K) (d0 d1 v : E),
      LoadHolds rd qptrs (2 * j + odd) bp1 ∧ q1 < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp1 l (bitE (q1.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q1 r1 d0 ∧
      LoadHolds rd qptrs (2 * j + odd + 1) bp2 ∧ q2 < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp2 l (bitE (q2.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q2 r2 d1 ∧
      LoadHolds rd (σ (.n 11)) j v ∧
      LoadHolds rd (σ (.n 11)) (j + 1) (((v + d0) * σ (.n 8) + d1) * σ (.n 8)) := by
    intro j hj
    obtain ⟨τ, hτ, t0, t1, t2, t3, t4, t5, t6, t7⟩ := atomsBody_params hpl (hB j hj)
    have := oqIter1_sound hs hcd hcd8 (odd := odd) (i := j) hτ t0 (fun k hk bp hbp => by
      rw [t2, p4] at hbp
      exact hbool k (by omega) bp hbp)
    rwa [t2, t3, t4, t5, t6, t7, p0, p1, p4, p5] at this
  choose! bp1 bp2 q1 q2 r1 r2 d0 d1 v hit using hit
  -- the odd first query
  obtain ⟨bp0, q0, r0, dM, hM⟩ : ∃ (bp : E) (q : ℕ) (r : List K) (d : E), odd = 1 →
      LoadHolds rd qptrs 0 bp ∧ q < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q r d ∧
      LoadHolds rd (σ (.n 11)) 0 (d * σ (.n 8)) := by
    by_cases h1 : odd = 1
    · subst h1
      obtain ⟨bp, q, r, d, h⟩ := oqMainA_odd hs hcd hcd8 hA (fun bp hbp => by
        rw [p4] at hbp; exact hbool 0 (by omega) bp hbp)
      rw [p0, p1, p4, p5] at h
      exact ⟨bp, q, r, d, fun _ => h⟩
    · exact ⟨0, 0, [], 0, fun h => absurd h h1⟩
  -- the queries' functions
  let fsel : ∀ {α : Type}, α → (ℕ → α) → (ℕ → α) → ℕ → α := fun a f g k =>
    if k < odd then a else if (k - odd) % 2 = 0 then f ((k - odd) / 2) else g ((k - odd) / 2)
  have fsel0 : ∀ {α : Type} (a : α) (f g : ℕ → α) (j : ℕ), fsel a f g (odd + 2 * j) = f j :=
    fun a f g j => by simp [fsel]
  have fsel1 : ∀ {α : Type} (a : α) (f g : ℕ → α) (j : ℕ), fsel a f g (odd + 2 * j + 1) = g j :=
    fun a f g j => by
      simp [fsel, show ¬ odd + 2 * j + 1 < odd by omega, show (odd + 2 * j + 1 - odd) % 2 = 1 by omega,
        show (odd + 2 * j + 1 - odd) / 2 = j by omega]
  have fselM : ∀ {α : Type} (a : α) (f g : ℕ → α), odd = 1 → fsel a f g 0 = a :=
    fun a f g h => by simp [fsel, h]
  set ds := fsel dM d0 d1 with hds
  -- the chain
  have hchain : ∀ i ≤ m, LoadHolds rd (σ (.n 11)) i (oqChain odd s.base (σ (.n 2))⁻¹ ds i) := by
    intro i hi
    induction i with
    | zero =>
      by_cases h1 : odd = 1
      · have := (hM h1).2.2.2.2
        simp only [oqChain, h1, ↓reduceIte]
        rw [hds, fselM _ _ _ h1, ← hmuinv]
        exact this
      · simp only [oqChain, h1, ↓reduceIte]
        exact h0even h1
    | succ i ih =>
      obtain ⟨-, -, -, -, -, -, -, -, hv, hv1⟩ := hit i (by omega)
      have e := loadHolds_unique hv (ih (by omega))
      rw [e] at hv1
      have q0 : ds (odd + 2 * i) = d0 i := fsel0 _ _ _ _
      have q1 : ds (odd + 2 * i + 1) = d1 i := fsel1 _ _ _ _
      simp only [oqChain, hb1, ↓reduceIte]
      rw [q0, q1]
      rw [hmuinv, hb1] at hv1
      exact hv1
  have hlast := e4
  have hnG' : σ (.n 6) = gen ^ m := hnG
  rw [e3, hnG', loadHolds_mul_gen_pow, Nat.add_zero] at hlast
  have hv := loadHolds_unique hlast (hchain m le_rfl)
  refine ⟨m, hm, by rw [← p6]; exact hnG, by rw [← p2]; exact hlam, fsel bp0 bp1 bp2,
    fsel q0 q1 q2, fsel r0 r1 r2, ds, fun k hk => ?_, σ (.n 11), fun i hi => ?_, ?_⟩
  · simp only [oqCount, hb1, ↓reduceIte] at hk
    by_cases hk0 : k < odd
    · have h1 : odd = 1 := by omega
      obtain rfl : k = 0 := by omega
      obtain ⟨a1, a2, a3, a4, -⟩ := hM h1
      rw [fselM _ _ _ h1, fselM _ _ _ h1, fselM _ _ _ h1, hds, fselM _ _ _ h1]
      exact ⟨a1, a2, a3, a4⟩
    · obtain ⟨j, hj, hk'⟩ : ∃ j < m, k = odd + 2 * j ∨ k = odd + 2 * j + 1 :=
        ⟨(k - odd) / 2, by omega, by omega⟩
      obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, -⟩ := hit j hj
      rcases hk' with rfl | rfl
      · rw [fsel0, fsel0, fsel0, hds, fsel0, show odd + 2 * j = 2 * j + odd by omega]
        exact ⟨a1, a2, a3, a4⟩
      · rw [fsel1, fsel1, fsel1, hds, fsel1, show odd + 2 * j + 1 = 2 * j + odd + 1 by omega]
        exact ⟨a5, a6, a7, a8⟩
  · rw [← p2]; exact hchain i hi
  · rw [← hret, e5, hv, p3, p2]

/-- **`opening_queries` deeper is sound** (G:1246-1269, `base = 0`, `odd = 0`): with the bit
pointers pointing to bits, its relation is `MeaningOpeningQueries`. -/
theorem oqMain0_sound {s : Oq} (hs : s.RowShape) (hb0 : s.base = 0) (hcd : 2 ≤ s.cd)
    (hcd8 : s.cd ≤ 8) {name loop : String} {fm fl : Fn}
    (hfm : coreProgram.find? name = some fm)
    (hpm : fm.params = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5, .n 6])
    (hbm : fm.body = oqMainT s 0 loop)
    (hfl : coreProgram.find? loop = some fl) (hpl : fl.params = oqLoopParams)
    (hbl : fl.body = oqLoop0T s loop)
    {cap flags lam lamN qptrs wp nG : E} {rets : List E}
    (hbits : ∀ N, nG = gen ^ N → N < ordG →
      QueryBitsBool rd qptrs (oqCount 0 s.base N) (s.pd + s.cd))
    (h : coreProgram.Rel rd name [cap, flags, lam, lamN, qptrs, wp, nG] rets) :
    MeaningOpeningQueries 0 s.base s.I (s.pd + s.cd) s.cd rd
      [cap, flags, lam, lamN, qptrs, wp, nG] rets := by
  rw [rel_iff_sem hfm, hbm, hpm] at h
  obtain ⟨σ, hp, h⟩ := h
  simp only [List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨p0, p1, p2, p3, p4, p5, p6, -⟩ := hp
  rw [oqMainT, holdsList_append, holdsList_atoms (oqMainA_atoms s 0)] at h
  obtain ⟨hA, h⟩ := h
  simp only [Stmt.HoldsList, Stmt.Holds, Atom.Holds, List.map_cons, List.map_nil] at h
  obtain ⟨hK, hcall, e3, e4, e5, hret⟩ := h
  obtain ⟨hmu, hg, hst, h0even⟩ := oqMainA_basic hA
  have hlam : σ (.n 2) ≠ 0 := fun h0 => by rw [h0, mul_zero] at hmu; exact zero_ne_one hmu
  have hmuinv : σ (.n 8) = (σ (.n 2))⁻¹ := eq_inv_of_mul_eq_one_left hmu
  set ps : List E := [σ (.n 6), σ (.n 4), σ (.n 0), σ (.n 1), σ (.n 5), σ (.n 11), σ (.n 8)]
    with hps
  have hstep := oqLoop0_step (rd := rd) hfl hpl hbl ps (by simp [hps])
  obtain ⟨m, hm, hnG, hB⟩ := (guarded_loop_iff hstep).mp ⟨by
    show IsInK (1 + σ (.n 6)); rw [← hg]; exact hK, fun hne => by
    have := hcall (by rw [hg]; exact hne)
    rwa [hst] at this⟩
  have hnG' : σ (.n 6) = gen ^ m := hnG
  have hbool := hbits m (by rw [← p6]; exact hnG) hm
  rw [hb0] at hbool
  simp only [oqCount, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hbool
  have hit : ∀ j < m, ∃ (bp : E) (q : ℕ) (r : List K) (d v : E),
      LoadHolds rd qptrs j bp ∧ q < 2 ^ (s.pd + s.cd) ∧
      (∀ l < s.pd + s.cd, LoadHolds rd bp l (bitE (q.testBit l))) ∧
      QueryOpens rd s.base s.I (s.pd + s.cd) s.cd cap flags wp q r d ∧
      LoadHolds rd (σ (.n 11)) j v ∧ LoadHolds rd (σ (.n 11)) (j + 1) ((v + d) * σ (.n 8)) := by
    intro j hj
    obtain ⟨τ, hτ, t0, t1, t2, t3, t4, t5, t6, t7⟩ := atomsBody_params hpl (hB j hj)
    have := oqIter0_sound hs hcd hcd8 (i := j) hτ t0 (fun bp hbp => by
      rw [t2, p4] at hbp
      exact hbool j hj bp hbp)
    rwa [t2, t3, t4, t5, t6, t7, p0, p1, p4, p5] at this
  choose! bp q r d v hit using hit
  have hchain : ∀ i ≤ m, LoadHolds rd (σ (.n 11)) i (oqChain 0 s.base (σ (.n 2))⁻¹ d i) := by
    intro i hi
    induction i with
    | zero =>
      simp only [oqChain, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
      exact h0even (by decide)
    | succ i ih =>
      obtain ⟨-, -, -, -, hv, hv1⟩ := hit i (by omega)
      have e := loadHolds_unique hv (ih (by omega))
      rw [e] at hv1
      simp only [oqChain, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte]
      rw [hmuinv, hb0] at hv1
      exact hv1
  have hlast := e4
  rw [e3, hnG', loadHolds_mul_gen_pow, Nat.add_zero] at hlast
  have hv := loadHolds_unique hlast (hchain m le_rfl)
  refine ⟨m, hm, by rw [← p6]; exact hnG, by rw [← p2]; exact hlam, bp, q, r, d, fun k hk => ?_,
    σ (.n 11), fun i hi => ?_, ?_⟩
  · simp only [oqCount, hb0, show (0 : ℕ) ≠ 1 by decide, ↓reduceIte] at hk
    obtain ⟨a1, a2, a3, a4, -⟩ := hit k hk
    exact ⟨a1, a2, a3, a4⟩
  · rw [← p2]; exact hchain i hi
  · rw [← hret, e5, hv, p3, p2]

end
end LeanVM.Guest.B1
