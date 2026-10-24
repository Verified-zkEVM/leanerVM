/-
  LeanVM.Guest.B1.VerifySub.H.Loads

  Every load of `verify_sub`'s body on an honest child reads the caller's words or its own buffers.
-/

module

public import LeanVM.Guest.B1.VerifySub.H.Calls

/-!
# The loads

`vs_loads_class` (by the kernel): `verify_sub`'s loads are through its own buffers' pointers within
their sizes, through `out` (argument `6`) below `24`, or through a push block's square pointer
(`g_squares·g^κ_b`) at offset `0`. `vs_push_ptr`: on the honest valuation a push block's square
pointer is `g_squares·g^κ_b`. `vs_loads`: so every load's address lies in the caller's words or the
own buffers.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.B1.Fwd LeanVM.Guest.Memory
open LeanVM.Node LeanVM.Protocol.Verifier

@[expose] public section

/-- A push block's square pointer. -/
def vsPushPtr (b : ℕ) : ℕ := if b = 0 then 308 else 307 + 4 * b

/-- The loads' pointers and offsets. -/
def vsLoadOk (q : V × ℕ) : Bool :=
  (q.1 == .n 27 && q.2 < 10) || (q.1 == .n 28 && q.2 < 6) || (q.1 == .n 129 && q.2 < 7) ||
    (q.1 == .n 141 && q.2 < 8) || (q.1 == .n 149 && q.2 < 153) || (q.1 == .n 640 && q.2 < 16) ||
    (q.1 == .n 876 && q.2 < 6) || (q.1 == .n 877 && q.2 < 64) || (q.1 == .n 1324 && q.2 < 165) ||
    (q.1 == .n 7 && q.2 < 165) || (q.1 == .n 523 && q.2 < 19) || (q.1 == .n 559 && q.2 < 4) ||
    (q.1 == .n 6 && q.2 < 24) ||
    (((List.range 54).map fun b ↦ V.n (vsPushPtr b)).contains q.1 && q.2 == 0)

theorem vs_loads_class : (vsCPre.filterMap Stmt.loadS).all vsLoadOk = true := by decide +kernel

variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **A push block's square pointer.** -/
theorem vs_push_ptr (hl : args.length = 7) {logMem : ℕ} {hs : List ℕ} (hsl : hs.length = 6)
    (hbk : ReadsAt rd (vsσ rd w args (.n 149))
      (Tables.blockKappaWords (gen ^ logMem) (hs.map (gen ^ ·)))) {b : ℕ} (hb : b < 54) :
    vsσ rd w args (.n (vsPushPtr b)) = vsσ rd w args (.n 5) * gen ^ pushKappa logMem hs b := by
  have hG := vsPushT_good (rd := rd) (w := w) hl
  have hbL : LoadHolds rd (vsσ rd w args (.n 149)) b (gen ^ pushKappa logMem hs b) := by
    rw [← bkw_getD hsl (by show b < 153; omega), List.getD_eq_getElem _ _
      (by simp only [Tables.blockKappaWords, List.length_map, List.length_range]; show b < 153; omega)]
    exact hbk _ _
  have h1 : vsLd (if b = 0 then 307 else 306 + 4 * b) 149 b ∈ vsPushStep b := by
    by_cases h0 : b = 0 <;> simp [vsPushStep, h0]
  have hm : vsMul (vsPushPtr b) 5 (if b = 0 then 307 else 306 + 4 * b) ∈ vsPushStep b := by
    by_cases h0 : b = 0 <;> simp [vsPushStep, vsPushPtr, h0]
  have g1 : Good rd vsSL w (vsσ rd w args) (.load (.n (if b = 0 then 307 else 306 + 4 * b))
      (.n 149) b) := hG _ (vsPushStep_mem hb h1)
  have r1 := good_read g1 (vsPush_notS b hb).1 hbL
  have gm : Good rd vsSL w (vsσ rd w args) (.mul (.n (vsPushPtr b)) (.n 5)
      (.n (if b = 0 then 307 else 306 + 4 * b))) := hG _ (vsPushStep_mem hb hm)
  simp only [Good] at gm
  rw [ite_eq_left_of_eq_true _ _ (eq_true (by
    unfold vsPushPtr; by_cases h0 : b = 0 <;> simp [h0]; omega))] at gm
  rw [gm, r1.1]

/-- **Every load reads the caller's words or the own buffers.** -/
theorem vs_loads {σ : Val} {bs : List ℕ} {own Lin : Main.Layout} {ownW : List (List E)}
    (hown : ∀ k < 16, (bs.getD k 0, ownW.getD k []) ∈ own)
    (hptr : ∀ k < 16, σ (.n (vsAllocVars.getD k 0)) = ofK (gpow (bs.getD k 0)))
    (hlen : 165 ≤ (ownW.getD 0 []).length ∧ 10 ≤ (ownW.getD 2 []).length ∧
      6 ≤ (ownW.getD 3 []).length ∧ 7 ≤ (ownW.getD 4 []).length ∧ 8 ≤ (ownW.getD 5 []).length ∧
      153 ≤ (ownW.getD 6 []).length ∧ 19 ≤ (ownW.getD 7 []).length ∧
      4 ≤ (ownW.getD 8 []).length ∧ 16 ≤ (ownW.getD 9 []).length ∧
      6 ≤ (ownW.getD 13 []).length ∧ 64 ≤ (ownW.getD 14 []).length ∧
      165 ≤ (ownW.getD 15 []).length)
    {outE sqE : ℕ} {cells : List E} (houtL : (outE, cells) ∈ Lin) (hcl : 24 ≤ cells.length)
    (h6 : σ (.n 6) = ofK (gpow outE))
    (hsqL : (sqE, Tables.gSquaresList) ∈ Lin)
    (hpush : ∀ b < 54, ∃ κ < 34, σ (.n (vsPushPtr b)) = ofK (gpow (sqE + κ))) {X : ℕ → Prop} :
    ∀ q ∈ vsCPre.filterMap Stmt.loadS, ∃ i, (σ q.1).limb 0 * Parameters.gpow q.2 = Parameters.gpow i ∧
      (Main.RegionL Lin i ∨ Main.RegionL own i ∨ X i) := by
  intro q hq
  have hc := List.all_eq_true.mp vs_loads_class q hq
  obtain ⟨p, off⟩ := q
  obtain ⟨l0, l2, l3, l4, l5, l6, l7, l8, l9, l13, l14, l15⟩ := hlen
  have own' : ∀ k < 16, ∀ (hk : off < (ownW.getD k []).length), p = .n (vsAllocVars.getD k 0) →
      ∃ i, (σ p).limb 0 * Parameters.gpow off = Parameters.gpow i ∧ (Main.RegionL Lin i ∨ Main.RegionL own i ∨ X i) :=
    fun k hk hoff hp ↦ ⟨bs.getD k 0 + off, by rw [hp, hptr k hk, Main.addr_ofK],
      Or.inr (Or.inl ⟨_, hown k hk, Nat.le_add_right _ _, Nat.add_lt_add_left hoff _⟩)⟩
  simp only [vsLoadOk, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.contains_iff_mem] at hc
  rcases hc with ((((((((((((⟨h1, h2⟩ | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) |
    ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩) | ⟨h1, h2⟩
  · exact own' 2 (by norm_num) (by omega) h1
  · exact own' 3 (by norm_num) (by omega) h1
  · exact own' 4 (by norm_num) (by omega) h1
  · exact own' 5 (by norm_num) (by omega) h1
  · exact own' 6 (by norm_num) (by omega) h1
  · exact own' 9 (by norm_num) (by omega) h1
  · exact own' 13 (by norm_num) (by omega) h1
  · exact own' 14 (by norm_num) (by omega) h1
  · exact own' 15 (by norm_num) (by omega) h1
  · exact own' 0 (by norm_num) (by omega) h1
  · exact own' 7 (by norm_num) (by omega) h1
  · exact own' 8 (by norm_num) (by omega) h1
  · subst h1
    exact ⟨outE + off, by rw [h6, Main.addr_ofK],
      Or.inl ⟨_, houtL, Nat.le_add_right _ _, Nat.add_lt_add_left (by show off < cells.length; omega) _⟩⟩
  · obtain ⟨b, hb, rfl⟩ := List.mem_map.mp h1
    obtain ⟨κ, hκ, e⟩ := hpush b (List.mem_range.mp hb)
    subst h2
    exact ⟨sqE + κ, by rw [e, Main.addr_ofK, Nat.add_zero],
      Or.inl ⟨_, hsqL, Nat.le_add_right _ _, Nat.add_lt_add_left (by show κ < Tables.gSquaresList.length; simp [Tables.gSquaresList]; omega) _⟩⟩

end
end LeanVM.Guest.B1.VerifySub
