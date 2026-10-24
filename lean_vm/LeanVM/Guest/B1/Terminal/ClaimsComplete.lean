/-
  LeanVM.Guest.B1.Terminal.ClaimsComplete

  The claims' blocks of `check_opening_terminal`, completely: on an evaluated valuation whose loads
  read their words and whose length checks agree, every statement holds and every load lies in a
  given region.
-/

module

public import LeanVM.Guest.B1.Terminal.TermFacts
public import LeanVM.Guest.B1.Ring.Loop14Complete

/-!
# The claims' blocks, completely

The completeness counterpart of `Terminal/Blocks`: on a valuation satisfying the blocks' defining
equations (`GoodS`, the evaluator's), whose stores are the public input's chain's only
(`StoresAt25`), a block holds once its loads read words (`LoadHolds`) and its length check's words
agree; its loads lie in a region `R` when their addresses do (`AddrIn`). `zrT_complete`,
`qT_complete`, `pT_complete`: the three kinds of block; `claimsT_complete`: all of them.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol.Verifier hiding gpow
open LeanVM.Guest.Memory LeanVM.Guest.B1.Fwd

@[expose] public section

/-- The word at `P·g^k` lies in the region `R`. -/
def AddrIn (R : ℕ → Prop) (P : E) (k : ℕ) : Prop := ∃ i, P.limb 0 * gpow k = gpow i ∧ R i

/-- The stores load through `.n 25`. -/
def StoresAt25 (S : List Atom) : Prop := ∀ a ∈ S, ∃ d off, a = .load d (.n 25) off

variable {C : CallRel} {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {R : ℕ → Prop}

theorem good_load (hS : StoresAt25 S) {d p : V} {off : ℕ} (hp : p ≠ .n 25)
    (h : GoodS rd S w σ (.atom (.load d p off))) : σ d = rdAt rd (σ p) off := by
  simp only [GoodS, Good] at h
  rcases h with h | h
  · obtain ⟨d', off', he⟩ := hS _ h
    simp only [Atom.load.injEq] at he
    exact absurd he.2.1 hp
  · exact h

theorem good_load_eq (hS : StoresAt25 S) {d p : V} {off : ℕ} (hp : p ≠ .n 25) {v : E}
    (h : GoodS rd S w σ (.atom (.load d p off))) (hl : LoadHolds rd (σ p) off v) :
    σ d = v ∧ (Atom.load d p off).Holds rd σ := by
  have e := (good_load hS hp h).trans (rt_rdAt_of_load hl)
  refine ⟨e, ?_⟩
  show LoadHolds rd (σ p) off (σ d)
  rw [e]; exact hl

theorem good_mul {d x y : ℕ} (h : GoodS rd S w σ (.atom (.mul (.n d) (.n x) (.n y))))
    (hx : x < d) (hy : y < d) : σ (.n d) = σ (.n x) * σ (.n y) := by
  simp only [GoodS, Good] at h
  rwa [ite_pos' (show (Core.V.n x).idx < (Core.V.n d).idx ∧ (Core.V.n y).idx < (Core.V.n d).idx from
    ⟨hx, hy⟩)] at h

theorem good_add {d x y : ℕ} (h : GoodS rd S w σ (.atom (.add (.n d) (.n x) (.n y)))) :
    σ (.n d) = σ (.n x) + σ (.n y) := h

theorem good_const {d : ℕ} {e : E} (h : GoodS rd S w σ (.atom (.const (.n d) e))) :
    σ (.n d) = e := h

theorem n_ne_25 {k : ℕ} (h : k ≠ 25) : (Core.V.n k) ≠ .n 25 := fun e => h (by injection e)

/-! ## The blocks -/

/-- **A claim on a prefix chain, completely.** -/
theorem zrT_complete (hS : StoresAt25 S) {ch j c r acc n : ℕ} (hch' : ch < r) (hsel : selV c < r)
    (hr : 25 < r) (hg : ∀ s ∈ zrT ch j c r acc, GoodS rd S w σ s)
    (hcp : LoadHolds rd (σ (.n 7)) j (gen ^ n)) (acp : AddrIn R (σ (.n 7)) j)
    (hch : ∃ v, LoadHolds rd (σ (.n ch) * gen ^ n) 0 v) (ach : AddrIn R (σ (.n ch) * gen ^ n) 0)
    (hkv : LoadHolds rd (σ (.n 11)) c (gen ^ n)) (akv : AddrIn R (σ (.n 11)) c)
    (hlam : ∃ v, LoadHolds rd (σ (.n 9)) j v) (alam : AddrIn R (σ (.n 9)) j) :
    (∀ s ∈ zrT ch j c r acc, Fwd.SHolds C rd σ s) ∧
      ∀ q ∈ (zrT ch j c r acc).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2 := by
  have m : ∀ s, s ∈ zrT ch j c r acc → GoodS rd S w σ s := hg
  simp only [zrT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at m
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8⟩ := m
  obtain ⟨CH, hch⟩ := hch
  obtain ⟨L, hlam⟩ := hlam
  obtain ⟨e0, l0⟩ := good_load_eq hS (n_ne_25 (by decide)) g0 hcp
  have e1 := good_mul g1 (by omega) (by omega)
  rw [e0] at e1
  rw [← e1] at hch ach
  obtain ⟨-, l2⟩ := good_load_eq hS (n_ne_25 (by omega)) g2 hch
  obtain ⟨e3, l3⟩ := good_load_eq hS (n_ne_25 (by decide)) g3 hkv
  obtain ⟨-, l5⟩ := good_load_eq hS (n_ne_25 (by decide)) g5 hlam
  have e6 := good_mul g6 (by omega) (by omega)
  have e7 := good_mul g7 (by omega) (by omega)
  have e8 := good_add g8
  refine ⟨fun s hs => ?_, fun q hq => ?_⟩
  · simp only [zrT, List.mem_cons, List.not_mem_nil, or_false] at hs
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l0
    · exact (by rw [e1, e0] : σ (.n (r + 1)) = σ (.n ch) * σ (.n r))
    · exact l2
    · exact l3
    · show σ (.n r) + σ (.n (r + 3)) = 0
      rw [e0, e3]; exact e_add_self _
    · exact l5
    · exact e6
    · exact e7
    · exact e8
  · simp only [zrT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl
    · exact acp
    · exact ach
    · exact akv
    · exact alam

/-- **A `q_keccak` lane's claim, completely.** -/
theorem qT_complete (hS : StoresAt25 S) {j s r acc n : ℕ} (hr : 333 ≤ r)
    (hg : ∀ t ∈ qT j s r acc, GoodS rd S w σ t)
    (hcp : LoadHolds rd (σ (.n 7)) j (gen ^ n)) (acp : AddrIn R (σ (.n 7)) j)
    (hslot : ∀ k < 6, ∀ t, (t = 23 ∨ t = 24) →
      (∃ v, LoadHolds rd (σ (.n t)) k v) ∧ AddrIn R (σ (.n t)) k)
    (hch : ∃ v, LoadHolds rd (σ (.n 21) * gen ^ n) 0 v) (ach : AddrIn R (σ (.n 21) * gen ^ n) 0)
    (hkv : LoadHolds rd (σ (.n 11)) 5 (gen ^ n * word 64 0 0)) (akv : AddrIn R (σ (.n 11)) 5)
    (hlam : ∃ v, LoadHolds rd (σ (.n 9)) j v) (alam : AddrIn R (σ (.n 9)) j) :
    (∀ t ∈ qT j s r acc, Fwd.SHolds C rd σ t) ∧
      ∀ q ∈ (qT j s r acc).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2 := by
  have m : ∀ t, t ∈ qT j s r acc → GoodS rd S w σ t := hg
  simp only [qT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at m
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, g17, g18,
    g19, g20, g21, g22⟩ := m
  obtain ⟨CH, hch⟩ := hch
  obtain ⟨L, hlam⟩ := hlam
  have hsp : ∀ k < 6, slotPt s k = 23 ∨ slotPt s k = 24 := fun k _ => by
    unfold slotPt; split <;> simp
  have ls : ∀ k < 6, ∀ d, GoodS rd S w σ (.atom (.load (.n d) (.n (slotPt s k)) k)) →
      (Atom.load (.n d) (.n (slotPt s k)) k).Holds rd σ := fun k hk d g => by
    obtain ⟨v, hv⟩ := (hslot k hk _ (hsp k hk)).1
    exact (good_load_eq hS (n_ne_25 (by rcases hsp k hk with h | h <;> rw [h] <;> decide)) g hv).2
  obtain ⟨e0, l0⟩ := good_load_eq hS (n_ne_25 (by decide)) g0 hcp
  have e12 := good_mul g12 (by omega) (by omega)
  rw [e0] at e12
  rw [← e12] at hch ach
  obtain ⟨-, l13⟩ := good_load_eq hS (n_ne_25 (by omega)) g13 hch
  have e15 := good_const g15
  have e16 := good_mul g16 (by omega) (by omega)
  obtain ⟨e17, l17⟩ := good_load_eq hS (n_ne_25 (by decide)) g17 hkv
  obtain ⟨-, l18⟩ := good_load_eq hS (n_ne_25 (by decide)) g19 hlam
  refine ⟨fun t ht => ?_, fun q hq => ?_⟩
  · simp only [qT, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact l0
    · exact ls 5 (by decide) _ g1
    · exact ls 4 (by decide) _ g2
    · exact good_mul g3 (by omega) (by omega)
    · exact ls 3 (by decide) _ g4
    · exact good_mul g5 (by omega) (by omega)
    · exact ls 2 (by decide) _ g6
    · exact good_mul g7 (by omega) (by omega)
    · exact ls 1 (by decide) _ g8
    · exact good_mul g9 (by omega) (by omega)
    · exact ls 0 (by decide) _ g10
    · exact good_mul g11 (by omega) (by omega)
    · exact (by rw [e12, e0] : σ (.n (r + 12)) = σ (.n 21) * σ (.n r))
    · exact l13
    · exact good_mul g14 (by omega) (by omega)
    · exact e15
    · exact e16
    · exact l17
    · show σ (.n (r + 16)) + σ (.n (r + 17)) = 0
      rw [e16, e15, e0, e17]; exact e_add_self _
    · exact l18
    · exact good_mul g20 (by omega) (by omega)
    · exact good_mul g21 (by omega) (by unfold selV; omega)
    · exact good_add g22
  · simp only [qT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact acp
    · exact (hslot 5 (by decide) _ (hsp 5 (by decide))).2
    · exact (hslot 4 (by decide) _ (hsp 4 (by decide))).2
    · exact (hslot 3 (by decide) _ (hsp 3 (by decide))).2
    · exact (hslot 2 (by decide) _ (hsp 2 (by decide))).2
    · exact (hslot 1 (by decide) _ (hsp 1 (by decide))).2
    · exact (hslot 0 (by decide) _ (hsp 0 (by decide))).2
    · exact ach
    · exact akv
    · exact alam

/-- **A public input's claim, completely.** -/
theorem pT_complete (hS : StoresAt25 S) {j c r acc : ℕ} (hsel : selV c < r) (hr : 33 < r)
    (hg : ∀ t ∈ pT j c r acc, GoodS rd S w σ t)
    (hkv : LoadHolds rd (σ (.n 11)) c (σ (.n 5))) (akv : AddrIn R (σ (.n 11)) c)
    (hlam : ∃ v, LoadHolds rd (σ (.n 9)) j v) (alam : AddrIn R (σ (.n 9)) j) :
    (∀ t ∈ pT j c r acc, Fwd.SHolds C rd σ t) ∧
      ∀ q ∈ (pT j c r acc).filterMap Stmt.loadS, AddrIn R (σ q.1) q.2 := by
  have m : ∀ t, t ∈ pT j c r acc → GoodS rd S w σ t := hg
  simp only [pT, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at m
  obtain ⟨g0, g1, g2, g3, g4, g5⟩ := m
  obtain ⟨L, hlam⟩ := hlam
  obtain ⟨e0, l0⟩ := good_load_eq hS (n_ne_25 (by decide)) g0 hkv
  obtain ⟨-, l2⟩ := good_load_eq hS (n_ne_25 (by decide)) g2 hlam
  refine ⟨fun t ht => ?_, fun q hq => ?_⟩
  · simp only [pT, List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
    · exact l0
    · show σ (.n 5) + σ (.n r) = 0
      rw [e0]; exact e_add_self _
    · exact l2
    · exact good_mul g3 (by omega) (by omega)
    · exact good_mul g4 (by omega) (by omega)
    · exact good_add g5
  · simp only [pT, List.filterMap_cons, Stmt.loadS, List.filterMap_nil, List.mem_cons,
      List.not_mem_nil, or_false] at hq
    rcases hq with rfl | rfl
    · exact akv
    · exact alam

/-! ## All the claims -/

/-- What claim `j`'s block needs of the memory, its low point's length `cp j`: its length read
at `claim_cplen_g` and checked against its column's, its chain's word, its batching power, each
load's address in `R`. -/
def ClaimIn (rd : Reader) (σ : Val) (R : ℕ → Prop) (cp : ℕ → ℕ) (j : ℕ) : Prop :=
  match termKind j with
  | 0 => LoadHolds rd (σ (.n 7)) j (gen ^ cp j) ∧ AddrIn R (σ (.n 7)) j ∧
      (∃ v, LoadHolds rd (σ (.n 19) * gen ^ cp j) 0 v) ∧ AddrIn R (σ (.n 19) * gen ^ cp j) 0 ∧
      LoadHolds rd (σ (.n 11)) (termCol j) (gen ^ cp j) ∧ AddrIn R (σ (.n 11)) (termCol j) ∧
      (∃ v, LoadHolds rd (σ (.n 9)) j v) ∧ AddrIn R (σ (.n 9)) j
  | 1 => LoadHolds rd (σ (.n 7)) j (gen ^ cp j) ∧ AddrIn R (σ (.n 7)) j ∧
      (∃ v, LoadHolds rd (σ (.n 21) * gen ^ cp j) 0 v) ∧ AddrIn R (σ (.n 21) * gen ^ cp j) 0 ∧
      LoadHolds rd (σ (.n 11)) (termCol j) (gen ^ cp j) ∧ AddrIn R (σ (.n 11)) (termCol j) ∧
      (∃ v, LoadHolds rd (σ (.n 9)) j v) ∧ AddrIn R (σ (.n 9)) j
  | 2 => LoadHolds rd (σ (.n 7)) j (gen ^ cp j) ∧ AddrIn R (σ (.n 7)) j ∧
      (∃ v, LoadHolds rd (σ (.n 21) * gen ^ cp j) 0 v) ∧ AddrIn R (σ (.n 21) * gen ^ cp j) 0 ∧
      LoadHolds rd (σ (.n 11)) 5 (gen ^ cp j * word 64 0 0) ∧ AddrIn R (σ (.n 11)) 5 ∧
      (∃ v, LoadHolds rd (σ (.n 9)) j v) ∧ AddrIn R (σ (.n 9)) j
  | 3 => LoadHolds rd (σ (.n 11)) (termCol j) (σ (.n 5)) ∧ AddrIn R (σ (.n 11)) (termCol j) ∧
      (∃ v, LoadHolds rd (σ (.n 9)) j v) ∧ AddrIn R (σ (.n 9)) j
  | _ => True

theorem termCol_lt {j : ℕ} (hj : j < 165) : termCol j < 99 := by
  unfold termCol; split_ifs <;> omega

/-- **The claims' blocks, completely.** -/
theorem claimsT_complete (hS : StoresAt25 S) {cp : ℕ → ℕ}
    (hslot : ∀ k < 6, ∀ t, (t = 23 ∨ t = 24) →
      (∃ v, LoadHolds rd (σ (.n t)) k v) ∧ AddrIn R (σ (.n t)) k) :
    ∀ (js : List ℕ) (r acc : ℕ), 333 ≤ r → (∀ j ∈ js, j < 165) →
      (∀ j ∈ js, ClaimIn rd σ R cp j) →
      (∀ s ∈ (claimsT js r acc).1, GoodS rd S w σ s) →
      (∀ s ∈ (claimsT js r acc).1, Fwd.SHolds C rd σ s) ∧
        ∀ q ∈ (claimsT js r acc).1.filterMap Stmt.loadS, AddrIn R (σ q.1) q.2
  | [], _, _, _, _, _, _ => ⟨fun s hs => by simp [claimsT] at hs, fun q hq => by simp [claimsT] at hq⟩
  | j :: js, r, acc, hr, hjs, hin, hg => by
    have hj := hjs j List.mem_cons_self
    have hjs' : ∀ j' ∈ js, j' < 165 := fun j' h => hjs j' (List.mem_cons_of_mem _ h)
    have hin' : ∀ j' ∈ js, ClaimIn rd σ R cp j' := fun j' h => hin j' (List.mem_cons_of_mem _ h)
    have hij := hin j List.mem_cons_self
    have hc := termCol_lt hj
    have hsel : selV (termCol j) < r := by unfold selV; omega
    simp only [claimsT, List.mem_append, List.filterMap_append] at hg ⊢
    have hg1 : ∀ s ∈ (claimT j r acc).1, GoodS rd S w σ s := fun s h => hg s (Or.inl h)
    have hg2 := fun s h => hg s (Or.inr h)
    unfold claimT at hg1 hg2 ⊢
    unfold ClaimIn at hij
    split at hij
    all_goals rename_i hk
    all_goals simp only [hk] at hg1 hg2 ⊢
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hij
      obtain ⟨b1, b2⟩ := zrT_complete (C := C) hS (by omega) hsel (by omega) hg1 a1 a2 a3 a4 a5
        a6 a7 a8
      obtain ⟨c1, c2⟩ := claimsT_complete hS hslot js _ _ (by omega) hjs' hin' hg2
      exact ⟨fun s h => h.elim (b1 s) (c1 s), fun q h => h.elim (b2 q) (c2 q)⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hij
      obtain ⟨b1, b2⟩ := zrT_complete (C := C) hS (by omega) hsel (by omega) hg1 a1 a2 a3 a4 a5
        a6 a7 a8
      obtain ⟨c1, c2⟩ := claimsT_complete hS hslot js _ _ (by omega) hjs' hin' hg2
      exact ⟨fun s h => h.elim (b1 s) (c1 s), fun q h => h.elim (b2 q) (c2 q)⟩
    · obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8⟩ := hij
      obtain ⟨b1, b2⟩ := qT_complete (C := C) hS hr hg1 a1 a2 hslot a3 a4 a5 a6 a7 a8
      obtain ⟨c1, c2⟩ := claimsT_complete hS hslot js _ _ (by omega) hjs' hin' hg2
      exact ⟨fun s h => h.elim (b1 s) (c1 s), fun q h => h.elim (b2 q) (c2 q)⟩
    · obtain ⟨a1, a2, a3, a4⟩ := hij
      obtain ⟨b1, b2⟩ := pT_complete (C := C) hS hsel (by omega) hg1 a1 a2 a3 a4
      obtain ⟨c1, c2⟩ := claimsT_complete hS hslot js _ _ (by omega) hjs' hin' hg2
      exact ⟨fun s h => h.elim (b1 s) (c1 s), fun q h => h.elim (b2 q) (c2 q)⟩
    · obtain ⟨c1, c2⟩ := claimsT_complete hS hslot js _ _ hr hjs' hin' hg2
      exact ⟨fun s h => h.elim (fun h => by simp at h) (c1 s),
        fun q h => h.elim (fun h => by simp at h) (c2 q)⟩

end
end LeanVM.Guest.B1.VerifySub
