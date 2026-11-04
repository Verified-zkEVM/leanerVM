/-
  LeanVM.Guest.B1.Sig.XmssSegPathC

  The path of the leanXMSS check in `__loop2` (`lx_window`, `lx_top_window`, `lx_levels`,
  `lean_ethereum.py:3609-3649, 3712-3721`), complete a window at a time: the dispatch by the
  honest window `lxWin L w`, each level's sibling hinted, the arm's pin by `lx_his_honest`.
-/

module

public import LeanVM.Guest.B1.Sig.XmssSegPath
public import LeanVM.Guest.B1.Sig.XmssSegStepC
public import LeanVM.Guest.B1.Sig.XmssBound
public import LeanVM.Guest.B1.Sig.CwComplete

/-!
# A window of the path, complete

* `CompletesO`: completeness changing a range and, besides, the run of `13` values at `o` (an arm
  `k ≠ 0` of a window writes its output where arm `0` numbered it); `Completes.appendO`,
  `CompletesO.append`, `CompletesO.toC`, `k64_completeO`;
* `LxEnv`: the values below `103` a window reads (the padding run, `P`, the shifts `his[v]` of the
  index `L`, the powers `g^s`);
* `lxLevelT_complete`, `lxLevelsT_complete`, `lxArmT_complete`: a level, the eight levels and an
  arm of window `w` by the honest arm `lxWin L w`, each level's sibling hinted;
* `lxWindowT_complete`: the window completes, its output canonical and the siblings the hinted
  ones; `lxWindowT_complete_fold`: its output is the fold of its eight levels over the index;
* `lxWindowT_numBelow`: the window's values lie below its end;
* `lxWindows_complete`: a layer's two windows complete, their output the layer's path fold
  `xFold` over the addresses `lxLayerA` and bits `lxLayerBit` of the index.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Completeness writing a run elsewhere -/

/-- `σ'` is `σ` outside `lo ..< hi` and the run of `13` values at `o`. -/
def ExtO (lo hi o : Nat) (σ σ' : Val) : Prop :=
  ∀ v, (∀ k, lo ≤ k → k < hi → v ≠ .n k) → ¬ InR o 13 v → σ' v = σ v

/-- **Completeness changing `lo ..< hi` and the run at `o`.** -/
def CompletesO (C : CallRel) (rd : Reader) (lo hi o : Nat) (ss : List Stmt) (σ : Val)
    (Post : Val → Prop) : Prop :=
  ∃ σ', ExtO lo hi o σ σ' ∧ Post σ' ∧
    ∀ (next : Prop) (kret : List E → Prop), next → Stmt.HoldsList C rd σ' ss next kret

theorem ExtO.apply {lo hi o : Nat} {σ σ' : Val} (h : ExtO lo hi o σ σ') {j : Nat}
    (hj : j < lo ∨ hi ≤ j) (ho : j < o ∨ o + 13 ≤ j) : σ' (.n j) = σ (.n j) :=
  h _ (fun k h1 h2 e => by simp only [V.mk.injEq, true_and] at e; omega)
    (by rintro ⟨i, hi, e⟩; simp only [V.mk.injEq, true_and] at e; omega)

theorem Completes.toO {lo hi : Nat} (o : Nat) {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd lo hi ss σ P) : CompletesO C rd lo hi o ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', fun v hv _ => he v hv, hp, hh⟩

/-- A block writing only the run at `o`. -/
theorem Completes.toO_run {lo hi o : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : Completes C rd o (o + 13) ss σ P) : CompletesO C rd lo hi o ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', fun v _ hr => he v (fun k h1 h2 e => hr ⟨k - o, by omega, by rw [e]; congr 1; omega⟩), hp, hh⟩

theorem CompletesO.toC {lo hi o lo' hi' : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesO C rd lo hi o ss σ P) (hlo : lo' ≤ lo) (hlo' : lo' ≤ o) (hhi : hi ≤ hi')
    (hhi' : o + 13 ≤ hi') : Completes C rd lo' hi' ss σ P :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', fun v hv => he v (fun k h1 h2 => hv k (by omega) (by omega))
    (by rintro ⟨i, hi, rfl⟩; exact hv (o + i) (by omega) (by omega) rfl), hp, hh⟩

theorem CompletesO.mono {lo hi o lo' hi' : Nat} {ss : List Stmt} {σ : Val} {P Q : Val → Prop}
    (h : CompletesO C rd lo hi o ss σ P) (hlo : lo' ≤ lo) (hhi : hi ≤ hi') (hPQ : ∀ σ', P σ' → Q σ') :
    CompletesO C rd lo' hi' o ss σ Q :=
  let ⟨σ', he, hp, hh⟩ := h
  ⟨σ', fun v hv hr => he v (fun k h1 h2 => hv k (by omega) (by omega)) hr, hPQ σ' hp, hh⟩

theorem CompletesO.reload {lo hi o : Nat} {ss : List Stmt} {σ σr : Val} {P : Val → Prop}
    (he : Ext lo hi σ σr) (h : CompletesO C rd lo hi o ss σr P) : CompletesO C rd lo hi o ss σ P :=
  let ⟨σ', he', hp, hh⟩ := h
  ⟨σ', fun v hv hr => (he' v hv hr).trans (he v hv), hp, hh⟩

/-- **A block, then one writing the run at `o` besides its range.** -/
theorem Completes.appendO {lo m hi o : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hxs : ∀ v ∈ Stmt.valsList xs, NBv m v ∧ ¬ InR o 13 v)
    (h1 : Completes C rd lo m xs σ P) (h2 : ∀ σ', Ext lo m σ σ' → P σ' → CompletesO C rd m hi o ys σ' Q) :
    CompletesO C rd lo hi o (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, fun v hv hr => ?_, hq2, fun next kret hn => ?_⟩
  · rw [he2 v (fun k h1 h2 => hv k (by omega) h2) hr, he1 v (fun k h1 h2 => hv k h1 (by omega))]
  · rw [holdsList_append]
    refine (holdsList_congr xs (fun v hv => ?_) _ _).mp (hh1 _ kret (hh2 next kret hn))
    obtain ⟨⟨j, hj, rfl⟩, hr⟩ := hxs v hv
    exact (he2 _ (fun k h1 h2 e => by simp only [V.mk.injEq, true_and] at e; omega) hr).symm

theorem CompletesO.keep {lo hi o : Nat} {ss : List Stmt} {σ : Val} {P : Val → Prop}
    (h : CompletesO C rd lo hi o ss σ P) : CompletesO C rd lo hi o ss σ (fun σ' => P σ' ∧ ExtO lo hi o σ σ') :=
  let ⟨σ', he, hp, hh⟩ := h; ⟨σ', he, ⟨hp, he⟩, hh⟩

/-- **A block writing the run at `o`, then one on the next range.** -/
theorem CompletesO.append {lo m hi o : Nat} {xs ys : List Stmt} {σ : Val} {P Q : Val → Prop}
    (hlo : lo ≤ m) (hhi : m ≤ hi) (hxs : NumBelow m (Stmt.valsList xs))
    (h1 : CompletesO C rd lo m o xs σ P) (h2 : ∀ σ', ExtO lo m o σ σ' → P σ' → Completes C rd m hi ys σ' Q) :
    CompletesO C rd lo hi o (xs ++ ys) σ Q := by
  obtain ⟨σ1, he1, hp1, hh1⟩ := h1
  obtain ⟨σ2, he2, hq2, hh2⟩ := h2 σ1 he1 hp1
  refine ⟨σ2, fun v hv hr => ?_, hq2, fun next kret hn => ?_⟩
  · rw [he2 v (fun k h1 h2 => hv k (by omega) h2), he1 v (fun k h1 h2 => hv k h1 (by omega)) hr]
  · rw [holdsList_append]
    exact (holdsList_frame hxs he2.agree _ _).mp (hh1 _ kret (hh2 next kret hn))

/-! ## A `KECCAK` writing its run anywhere -/

/-- **A 64-byte `keccak` completes**, its constant at `c` and its run at `o` off its inputs. -/
theorem k64_completeO {pad : Nat} {m0 m1 m2 m3 : V} {c o : Nat} (σ : Val) (hp : PadOK σ pad)
    (hpc : pad + 5 ≤ c) (hpo : pad + 5 ≤ o) (hco : c + 1 ≤ o ∨ o + 13 ≤ c)
    (hm : ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ ¬ InR o 13 v ∧ IsCanonical128 (σ v)) :
    CompletesO C rd c (c + 1) o (k64 pad m0 m1 m2 m3 c o) σ (fun σ' => IsCanonical128 (σ' (.n o))) := by
  rw [k64_vals_eq]
  refine Completes.appendO (m := c + 1) (by omega) le_rfl (fun v hv => ?_) (cst_complete σ c _) (fun σ1 he1 hp1 => ?_)
  · simp only [cst, valsList_cons, valsList_nil, Stmt.vals, Atom.vals, List.append_nil,
      List.mem_singleton] at hv
    subst hv
    exact ⟨⟨c, by omega, rfl⟩, by rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega⟩
  have hag : AgreeBelow c σ σ1 := he1.agree
  have hin : ∀ v ∈ [m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n c, .n (pad + 1),
      .n (pad + 2), .n (pad + 3), .n (pad + 4)], ¬ InR o 13 v := by
    intro v hv
    rcases (k64_ins pad m0 m1 m2 m3 c v).mp hv with h | rfl | ⟨k, hk, rfl⟩
    · exact (hm v h).2.1
    · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
    · rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
  obtain ⟨q0, q1, q2, q3, q4⟩ := hp.congr hpc hag
  have h4 : ∀ v ∈ [m0, m1, m2, m3], IsCanonical128 (σ1 v) := fun v hv => by
    rw [hag.apply (hm v hv).1]; exact (hm v hv).2.2
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([m0, m1, m2, m3, .n pad, .n (pad + 1), .n (pad + 2),
      .n (pad + 3), .n c, .n (pad + 1), .n (pad + 2), .n (pad + 3), .n (pad + 4)].map σ1) cc) := by
    intro cc
    fin_cases cc <;> simp [cells13, q0, q1, q2, q3, q4, hp1] <;>
      first | exact h4 _ (by simp) | exact canon_word _ _ | exact canon_zero
  refine (kecS_complete_at (C := C) (rd := rd) σ1 o rfl hin hcan false false).toO_run.mono le_rfl le_rfl
    (fun σ' h => ?_)
  have := h 0 (by norm_num)
  rw [Nat.add_zero] at this
  rw [this]
  exact canon_kOut _ _ _ _

/-! ## A level, generically -/

/-- **A level completes**: sequential values `b ..< s`, the hinted sibling at `s` (loaded), the
sequential values `s + 1 ..< c`, the `keccak` at `c` writing the run at `o`. -/
theorem lvl_completeO {xs ys : List Stmt} {nm : String} {b s c o pad : Nat} {m0 m1 m2 m3 : V}
    (σ : Val) (hx : SeqOK b xs s) (hy : SeqOK (s + 1) ys c) (hpad : PadOK σ pad) (hpb : pad + 5 ≤ b)
    (hco : c + 1 ≤ o ∨ o + 13 ≤ b) (hpo : pad + 5 ≤ o)
    (hxo : ∀ v ∈ Stmt.valsList xs ++ Stmt.valsList ys, ¬ InR o 13 v)
    (hm : ∀ σ1, Ext b c σ σ1 → σ1 (.n s) = σ (.n s) →
      AtomsHold rd σ1 (xs ++ hintW nm [.n s] :: ys) →
      ∀ v ∈ [m0, m1, m2, m3], NBv c v ∧ ¬ InR o 13 v ∧ IsCanonical128 (σ1 v)) :
    CompletesO C rd b (c + 1) o (xs ++ hintW nm [.n s] :: ys ++ k64 pad m0 m1 m2 m3 c o) σ
      (fun σ' => σ' (.n s) = σ (.n s) ∧ IsCanonical128 (σ' (.n o))) := by
  have hsb := hx.le
  have hsc := hy.le
  have hatoms : atomsOnly (xs ++ hintW nm [.n s] :: ys) = true := by
    rw [atomsOnly_append, hx.atoms]
    exact hy.atoms
  have hpre : Completes C rd b c (xs ++ hintW nm [.n s] :: ys) σ (fun σ1 => σ1 (.n s) = σ (.n s)) := by
    refine Completes.seq hx (by omega) (fun σa hea _ => ?_)
    obtain ⟨σ1, he1, -, hh1⟩ := seq_completes (C := C) (rd := rd) hy σa
    refine (Completes.hint (lo := s + 1) (hi := c) (.cons ⟨s, by omega, rfl⟩ (.nil _)) (by omega)
      ⟨σ1, he1, ?_, hh1⟩).mono (by omega) le_rfl (fun _ h => h)
    show σ1 (.n s) = σ (.n s)
    rw [he1.apply (Or.inl (by omega)), hea.apply (Or.inr le_rfl)]
  have hvals : ∀ v ∈ Stmt.valsList (xs ++ hintW nm [.n s] :: ys), NBv c v ∧ ¬ InR o 13 v := by
    intro v hv
    rw [show xs ++ hintW nm [.n s] :: ys = xs ++ [hintW nm [.n s]] ++ ys by simp, valsList_append,
      valsList_append, valsList_hint] at hv
    rcases List.mem_append.mp hv with hv | hv
    · rcases List.mem_append.mp hv with hv | hv
      · obtain ⟨j, hj, rfl⟩ := hx.numBelow _ hv
        exact ⟨⟨j, by omega, rfl⟩, hxo _ (List.mem_append_left _ hv)⟩
      · simp only [List.mem_singleton] at hv
        subst hv
        refine ⟨⟨s, by omega, rfl⟩, ?_⟩
        rintro ⟨j, hj, e⟩; simp only [V.mk.injEq, true_and] at e; omega
    · obtain ⟨j, hj, rfl⟩ := hy.numBelow _ hv
      exact ⟨⟨j, by omega, rfl⟩, hxo _ (List.mem_append_right _ hv)⟩
  rw [List.append_assoc, List.cons_append, ← List.cons_append, ← List.append_assoc]
  refine Completes.appendO (by omega) (by omega) hvals hpre.withHolds (fun σ1 he1 ⟨hs1, hh1⟩ => ?_)
  have hm1 := hm σ1 he1 hs1 (atomsHold_of_holdsList hatoms hh1)
  refine (k64_completeO (C := C) (rd := rd) σ1 (hpad.congr hpb (he1.agree)) (by omega) hpo
    (by omega) hm1).keep.mono le_rfl le_rfl (fun σ' ⟨hc, he⟩ => ⟨?_, hc⟩)
  rw [he.apply (Or.inl (by omega)) (by omega), hs1]

/-! ## The values a window reads -/

/-- The values below `103` a window of the index `L` reads: the padding run, `P`, the shifts
`his[v] = L >>> 8v` and the powers `g^s`. -/
def LxEnv (L : Nat) (σ : Val) : Prop :=
  PadOK σ sLxPad ∧ IsCanonical128 (σ sLxPP) ∧ (∀ v < 4, σ (sHis v) = eOfNat (L >>> (8 * v))) ∧
    ∀ s < 13, σ (sPower s) = gen ^ s

theorem LxEnv.congr {L : Nat} {σ σ' : Val} (h : LxEnv L σ) (hσ : ∀ j < 103, σ' (.n j) = σ (.n j)) :
    LxEnv L σ' := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h1.congr (b := 103) (by simp [sLxPad]) (fun j hj => (hσ j hj).symm), ?_, fun v hv => ?_,
    fun s hs => ?_⟩
  · rw [show sLxPP = .n 66 from rfl, hσ 66 (by omega)]; exact h2
  · rw [show sHis v = .n (67 + v) from rfl, hσ _ (by omega)]; exact h3 v hv
  · rw [show sPower s = .n (75 + s) from rfl, hσ _ (by omega)]; exact h4 s hs

theorem lxCanon_eOfNat (n : Nat) : IsCanonical128 (eOfNat n) := by
  rw [← word_eq_eOfNat]; exact canon_word n 0

theorem notInR_of {o j : Nat} (h : j < o ∨ o + 13 ≤ j) : ¬ InR o 13 (.n j) := by
  rintro ⟨i, hi, e⟩; simp only [V.mk.injEq, true_and] at e; omega

theorem ord_cases {k r : Nat} (x y : V) :
    ((if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).1 = x ∧ (if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).2 = y) ∨
    ((if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).1 = y ∧ (if k / 2 ^ r % 2 = 0 then (x, y) else (y, x)).2 = x) := by
  split
  · exact Or.inl ⟨rfl, rfl⟩
  · exact Or.inr ⟨rfl, rfl⟩

/-- A level's inputs: `P`, the address at `a`, the node and the sibling at `s` in either order. -/
theorem lvl_inputs {L : Nat} {σ1 : Val} {cur m2 m3 : V} {s a c o : Nat} (hE : LxEnv L σ1)
    (hcur : NBv c cur) (hcurO : ¬ InR o 13 cur) (hcc : IsCanonical128 (σ1 cur))
    (hs : s < c) (hsO : s < o ∨ o + 13 ≤ s) (hsc : IsCanonical128 (σ1 (.n s)))
    (ha : a < c) (haO : a < o ∨ o + 13 ≤ a) (hac : IsCanonical128 (σ1 (.n a))) (h66 : 66 < c) (ho : 103 ≤ o)
    (h23 : (m2 = cur ∧ m3 = .n s) ∨ (m2 = .n s ∧ m3 = cur)) :
    ∀ v ∈ [sLxPP, .n a, m2, m3], NBv c v ∧ ¬ InR o 13 v ∧ IsCanonical128 (σ1 v) := by
  have hcv : NBv c cur ∧ ¬ InR o 13 cur ∧ IsCanonical128 (σ1 cur) := ⟨hcur, hcurO, hcc⟩
  have hsv : NBv c (.n s) ∧ ¬ InR o 13 (.n s) ∧ IsCanonical128 (σ1 (.n s)) := ⟨⟨s, hs, rfl⟩, notInR_of hsO, hsc⟩
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  rintro v (rfl | rfl | rfl | rfl)
  · exact ⟨⟨66, h66, rfl⟩, notInR_of (by omega), hE.2.1⟩
  · exact ⟨⟨a, ha, rfl⟩, notInR_of haO, hac⟩
  · rcases h23 with ⟨rfl, -⟩ | ⟨rfl, -⟩
    exacts [hcv, hsv]
  · rcases h23 with ⟨-, rfl⟩ | ⟨-, rfl⟩
    exacts [hsv, hcv]

/-! ## A level -/

/-- Where level `r` of window `w` from base `b` writes its node. -/
def lxLvlO (w r : Nat) (outO : Option Nat) (b : Nat) : Nat :=
  if w + 1 = 4 then (if r + 1 = 8 then outO.getD (b + 3) else b + 3)
  else if r + 1 = 8 then outO.getD (b + 4) else b + 5

theorem lxLevelT_out (w k r : Nat) (cur : V) (outO : Option Nat) (b : Nat) :
    (lxLevelT w k r cur outO b).2.2 = .n (lxLvlO w r outO b) := by
  unfold lxLevelT lxLvlO
  by_cases hw : w + 1 = 4 <;> by_cases hr : r + 1 = 8 <;> simp [hw, hr]

theorem getD_cases {outO : Option Nat} {b d : Nat} {cur : V}
    (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 13 ≤ b ∧ ¬ InR o 13 cur) :
    outO.getD d = d ∨ (103 ≤ outO.getD d ∧ outO.getD d + 13 ≤ b ∧ ¬ InR (outO.getD d) 13 cur) := by
  cases outO with
  | none => exact Or.inl rfl
  | some o => exact Or.inr (hO o rfl)

/-- **A level of a window completes** by the honest arm, its sibling `sib` hinted. -/
theorem lxLevelT_complete {L : Nat} (hL : L < 2 ^ 32) {w r : Nat} (hw : w < 4) (hr : r < 8) {cur : V}
    {outO : Option Nat} {b : Nat} (σ : Val) (hE : LxEnv L σ) (hb : 103 ≤ b) (hcur : NBv b cur)
    (hcc : IsCanonical128 (σ cur)) (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 13 ≤ b ∧ ¬ InR o 13 cur)
    {sib : E} (hsib : IsCanonical128 sib) :
    CompletesO C rd b (lxLevelT w (lxWin L w) r cur outO b).2.1 (lxLvlO w r outO b)
      (lxLevelT w (lxWin L w) r cur outO b).1 σ
      (fun σ' => σ' (.n (lxSibCell w r b)) = sib ∧ IsCanonical128 (σ' (.n (lxLvlO w r outO b)))) := by
  obtain ⟨jc, hjc, rfl⟩ := hcur
  have hpad := hE.1
  unfold lxLevelT lxLvlO lxSibCell
  by_cases hw3 : w + 1 = 4
  · simp only [hw3, ↓reduceIte]
    generalize hOd : (if r + 1 = 8 then outO.getD (b + 3) else b + 3) = O
    have hOc : O = b + 3 ∨ (103 ≤ O ∧ O + 13 ≤ b ∧ ¬ InR O 13 (.n jc)) := by
      rw [← hOd]; split
      · exact getD_cases hO
      · exact Or.inl rfl
    have hcO : ¬ InR O 13 (.n jc) := by
      rcases hOc with h | h
      · exact notInR_of (by omega)
      · exact h.2.2
    refine CompletesO.reload (σr := Function.update σ (.n b) sib) (fun v hv => Function.update_of_ne
      (hv b le_rfl (by split <;> omega)) _ _) ?_
    have hσr : ∀ j, j ≠ b → Function.update σ (.n b) sib (.n j) = σ (.n j) := fun j hj =>
      Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; exact hj) _ _
    refine (lvl_completeO (xs := []) (ys := [cst (b + 1) (word (lxNodeConst w r + lxWin L w / 2 ^ (r + 1)) 0 0)])
      (nm := "lx_path") (s := b) (c := b + 2) (o := O) _ rfl ⟨rfl, rfl⟩
      (hpad.congr (b := 103) (by simp [sLxPad]) (fun j hj => (hσr j (by omega)).symm)) (by simp [sLxPad]; omega)
      (by omega) (by simp only [sLxPad]; rcases hOc with h | h <;> omega) ?_ ?_).mono le_rfl (by split <;> omega)
      (fun σ' ⟨h1, h2⟩ => ⟨by rw [h1, Function.update_self], h2⟩)
    · intro v hv
      simp [cst, Stmt.vals, Atom.vals] at hv
      subst hv
      exact notInR_of (by rcases hOc with h | h <;> omega)
    · intro σ1 he1 hs1 hh1
      have hE1 : LxEnv L σ1 := hE.congr fun j hj => by
        rw [he1.apply (Or.inl (by omega)), hσr j (by omega)]
      have ha : σ1 (.n (b + 1)) = word (lxNodeConst w r + lxWin L w / 2 ^ (r + 1)) 0 0 :=
        hh1.atom (a := .const _ _) (by simp [cst])
      exact lvl_inputs hE1 ⟨jc, by omega, rfl⟩ hcO
        (by rw [he1.apply (Or.inl (by omega)), hσr jc (by omega)]; exact hcc) (by omega)
        (by rcases hOc with h | h <;> omega) (by rw [hs1, Function.update_self]; exact hsib) (by omega)
        (by rcases hOc with h | h <;> omega) (by rw [ha]; exact canon_word _ _) (by omega)
        (by rcases hOc with h | h <;> omega) (ord_cases _ _)
  · simp only [hw3, ↓reduceIte]
    have hσr : ∀ (s j : Nat), j ≠ s → Function.update σ (.n s) sib (.n j) = σ (.n j) := fun s j hj =>
      Function.update_of_ne (by simp only [ne_eq, V.mk.injEq, true_and]; exact hj) _ _
    have hhis : NBv b (sHis (w + 1)) := ⟨67 + (w + 1), by omega, rfl⟩
    by_cases hr7 : r + 1 = 8
    · obtain rfl : r = 7 := by omega
      simp only [show 7 + 1 = 8 from rfl, ↓reduceIte]
      generalize hOd : outO.getD (b + 4) = O
      have hOc : O = b + 4 ∨ (103 ≤ O ∧ O + 13 ≤ b ∧ ¬ InR O 13 (.n jc)) := by
        rw [← hOd]; exact getD_cases hO
      have hcO : ¬ InR O 13 (.n jc) := by
        rcases hOc with h | h
        · exact notInR_of (by omega)
        · exact h.2.2
      refine CompletesO.reload (σr := Function.update σ (.n (b + 2)) sib) (fun v hv => Function.update_of_ne
        (hv (b + 2) (by omega) (by cases outO <;> simp)) _ _) ?_
      refine (lvl_completeO (xs := [cst b (word (lxNodeConst w 7 + lxWin L w / 2 ^ 8) 0 0),
          addS (.n (b + 1)) (sHis (w + 1)) (.n b)]) (ys := [])
        (nm := "lx_path") (s := b + 2) (c := b + 3) (o := O) _ ⟨rfl, ⟨rfl, hhis.mono' (by omega),
          ⟨b, by omega, rfl⟩⟩, rfl⟩ rfl
        (hpad.congr (b := 103) (by simp [sLxPad]) (fun j hj => (hσr (b + 2) j (by omega)).symm))
        (by simp [sLxPad]; omega)
        (by omega) (by simp only [sLxPad]; rcases hOc with h | h <;> omega) ?_ ?_).mono le_rfl
        (by cases outO <;> simp) (fun σ' ⟨h1, h2⟩ => ⟨by rw [h1, Function.update_self], h2⟩)
      · intro v hv
        simp [cst, addS, Stmt.vals, Atom.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notInR_of (by rcases hOc with h | h <;> omega)
      · intro σ1 he1 hs1 hh1
        have hE1 : LxEnv L σ1 := hE.congr fun j hj => by
          rw [he1.apply (Or.inl (by omega)), hσr (b + 2) j (by omega)]
        have hc : σ1 (.n b) = word (lxNodeConst w 7 + lxWin L w / 2 ^ 8) 0 0 :=
          hh1.atom (a := .const _ _) (by simp [cst])
        have ha : σ1 (.n (b + 1)) = σ1 (sHis (w + 1)) + σ1 (.n b) :=
          hh1.atom (a := .add _ _ _) (by simp [addS])
        exact lvl_inputs hE1 ⟨jc, by omega, rfl⟩ hcO
          (by rw [he1.apply (Or.inl (by omega)), hσr (b + 2) jc (by omega)]; exact hcc) (by omega)
          (by rcases hOc with h | h <;> omega) (by rw [hs1, Function.update_self]; exact hsib) (by omega)
          (by rcases hOc with h | h <;> omega)
          (by rw [ha, hc, hE1.2.2.1 (w + 1) (by omega)]; exact canon_add (lxCanon_eOfNat _) (canon_word _ _))
          (by omega) (by rcases hOc with h | h <;> omega) (ord_cases _ _)
    · simp only [hr7, ↓reduceIte]
      have hpw : NBv b (sPower (7 - r)) := ⟨75 + (7 - r), by omega, rfl⟩
      refine CompletesO.reload (σr := Function.update σ (.n (b + 3)) sib) (fun v hv => Function.update_of_ne
        (hv (b + 3) (by omega) (by omega)) _ _) ?_
      refine (lvl_completeO (xs := [mulS (.n b) (sHis (w + 1)) (sPower (7 - r)),
          cst (b + 1) (word (lxNodeConst w r + lxWin L w / 2 ^ (r + 1)) 0 0),
          addS (.n (b + 2)) (.n b) (.n (b + 1))]) (ys := [])
        (nm := "lx_path") (s := b + 3) (c := b + 4) (o := b + 5) _
        ⟨⟨rfl, hhis, hpw⟩, rfl, ⟨rfl, ⟨b, by omega, rfl⟩, ⟨b + 1, by omega, rfl⟩⟩, rfl⟩ rfl
        (hpad.congr (b := 103) (by simp [sLxPad]) (fun j hj => (hσr (b + 3) j (by omega)).symm))
        (by simp [sLxPad]; omega) (by omega) (by simp only [sLxPad]; omega) ?_ ?_).mono le_rfl
        (by omega) (fun σ' ⟨h1, h2⟩ => ⟨by rw [h1, Function.update_self], h2⟩)
      · intro v hv
        simp [cst, addS, mulS, Stmt.vals, Atom.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          exact notInR_of (by omega)
      · intro σ1 he1 hs1 hh1
        have hE1 : LxEnv L σ1 := hE.congr fun j hj => by
          rw [he1.apply (Or.inl (by omega)), hσr (b + 3) j (by omega)]
        have hm : σ1 (.n b) = σ1 (sHis (w + 1)) * σ1 (sPower (7 - r)) :=
          hh1.atom (a := .mul _ _ _) (by simp [mulS])
        have hc : σ1 (.n (b + 1)) = word (lxNodeConst w r + lxWin L w / 2 ^ (r + 1)) 0 0 :=
          hh1.atom (a := .const _ _) (by simp [cst])
        have ha : σ1 (.n (b + 2)) = σ1 (.n b) + σ1 (.n (b + 1)) :=
          hh1.atom (a := .add (.n (b + 2)) _ _) (by simp [addS])
        have hlt : 2 ^ (7 - r) * (L >>> (8 * (w + 1))) < 2 ^ 64 := by
          have h1 : L >>> (8 * (w + 1)) < 2 ^ 32 := lt_of_le_of_lt (Nat.shiftRight_le _ _) hL
          have h2 : 2 ^ (7 - r) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by norm_num) (by omega)
          calc 2 ^ (7 - r) * (L >>> (8 * (w + 1))) ≤ 2 ^ 7 * 2 ^ 32 := Nat.mul_le_mul h2 (by omega)
            _ < 2 ^ 64 := by norm_num
        exact lvl_inputs hE1 ⟨jc, by omega, rfl⟩ (notInR_of (by omega))
          (by rw [he1.apply (Or.inl (by omega)), hσr (b + 3) jc (by omega)]; exact hcc) (by omega)
          (by omega) (by rw [hs1, Function.update_self]; exact hsib) (by omega) (by omega)
          (by
            rw [ha, hc, hm, hE1.2.2.1 (w + 1) (by omega), hE1.2.2.2 (7 - r) (by omega),
              gen_pow_eq_eOfNat (by omega), eOfNat_mul_two_pow hlt]
            exact canon_add (lxCanon_eOfNat _) (canon_word _ _))
          (by omega) (by omega) (ord_cases _ _)


/-! ## A level's values -/

theorem k64_vals_all {pad : Nat} {m0 m1 m2 m3 : V} {c o : Nat} {P : V → Prop}
    (h0 : P m0) (h1 : P m1) (h2 : P m2) (h3 : P m3) (hc : P (.n c)) (hp : ∀ v, InR pad 5 v → P v)
    (ho : ∀ v, InR o 13 v → P v) : ∀ v ∈ Stmt.valsList (k64 pad m0 m1 m2 m3 c o), P v := by
  intro v hv
  rcases k64_vals pad m0 m1 m2 m3 c o hv with h | rfl | h | h
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl <;> assumption
  exacts [hc, hp v h, ho v h]

/-- What a level's values are: its node, a value below `103`, one of its own, or its run. -/
def LvlVal (cur : V) (b nb o : Nat) (v : V) : Prop :=
  v = cur ∨ (∃ j < 103, v = .n j) ∨ (∃ j, b ≤ j ∧ j < nb ∧ v = .n j) ∨ InR o 13 v

theorem lxLevelT_vals {w r : Nat} (hw : w < 4) (hr : r < 8) (k : Nat) (cur : V) (outO : Option Nat) {b : Nat} :
    ∀ v ∈ Stmt.valsList (lxLevelT w k r cur outO b).1,
      LvlVal cur b (lxLevelT w k r cur outO b).2.1 (lxLvlO w r outO b) v := by
  have hn : ∀ {nb o j : Nat}, j < 103 ∨ (b ≤ j ∧ j < nb) → LvlVal cur b nb o (.n j) := by
    intro nb o j h
    rcases h with h | h
    · exact Or.inr (Or.inl ⟨_, h, rfl⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨_, h.1, h.2, rfl⟩))
  have hpad : ∀ {nb o : Nat} (v : V), InR sLxPad 5 v → LvlVal cur b nb o v :=
    fun v ⟨i, hi, e⟩ => e ▸ hn (Or.inl (by simp [sLxPad]; omega))
  have hrun : ∀ {nb o : Nat} (v : V), InR o 13 v → LvlVal cur b nb o v :=
    fun v h => Or.inr (Or.inr (Or.inr h))
  have hord : ∀ {nb o s : Nat} (k' r' : Nat), LvlVal cur b nb o (.n s) →
      LvlVal cur b nb o (if k' / 2 ^ r' % 2 = 0 then (cur, V.n s) else (.n s, cur)).1 ∧
        LvlVal cur b nb o (if k' / 2 ^ r' % 2 = 0 then (cur, V.n s) else (.n s, cur)).2 := by
    intro nb o s k' r' hs
    split
    · exact ⟨Or.inl rfl, hs⟩
    · exact ⟨hs, Or.inl rfl⟩
  unfold lxLevelT lxLvlO
  by_cases hw3 : w + 1 = 4
  · simp only [hw3, ↓reduceIte]
    intro v hv
    rw [valsList_append] at hv
    rcases List.mem_append.mp hv with hv | hv
    · simp [hintW, cst, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hv
      rcases hv with rfl | rfl <;> exact hn (Or.inr ⟨by omega, by split <;> omega⟩)
    · exact k64_vals_all (hn (Or.inl (by simp))) (hn (Or.inr ⟨by omega, by split <;> omega⟩))
        (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).1
        (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).2
        (hn (Or.inr ⟨by omega, by split <;> omega⟩)) hpad hrun v hv
  · simp only [hw3, ↓reduceIte]
    by_cases hr7 : r + 1 = 8
    · simp only [hr7, ↓reduceIte]
      intro v hv
      rw [valsList_append] at hv
      rcases List.mem_append.mp hv with hv | hv
      · simp [hintW, cst, addS, sHis, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hn (Or.inl (by omega)) | exact hn (Or.inr ⟨by omega, by split <;> omega⟩)
      · exact k64_vals_all (hn (Or.inl (by simp))) (hn (Or.inr ⟨by omega, by split <;> omega⟩))
          (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).1
          (hord _ _ (hn (Or.inr ⟨by omega, by split <;> omega⟩))).2
          (hn (Or.inr ⟨by omega, by split <;> omega⟩)) hpad hrun v hv
    · simp only [hr7, ↓reduceIte]
      intro v hv
      rw [valsList_append] at hv
      rcases List.mem_append.mp hv with hv | hv
      · simp [hintW, cst, addS, mulS, sHis, sPower, Stmt.vals, Atom.vals, Hint.vals, Dest.vals] at hv
        rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
          first | exact hn (Or.inl (by omega)) | exact hn (Or.inr ⟨by omega, by omega⟩)
      · exact k64_vals_all (hn (Or.inl (by simp))) (hn (Or.inr ⟨by omega, by omega⟩))
          (hord _ _ (hn (Or.inr ⟨by omega, by omega⟩))).1
          (hord _ _ (hn (Or.inr ⟨by omega, by omega⟩))).2
          (hn (Or.inr ⟨by omega, by omega⟩)) hpad hrun v hv

/-! ## The eight levels of an arm -/

/-- Where the last level of an arm of window `w` from base `b0` writes its node. -/
def lxArmO (w : Nat) (outO : Option Nat) (b0 : Nat) : Nat := lxLvlO w 7 outO (b0 + lxStride w * 7)

theorem lxArmO_cases (w : Nat) (outO : Option Nat) (b0 : Nat) :
    (∃ o, outO = some o ∧ lxArmO w outO b0 = o) ∨
      (outO = none ∧ b0 + lxStride w * 7 + 3 ≤ lxArmO w outO b0 ∧ lxArmO w outO b0 ≤ b0 + lxStride w * 7 + 4) := by
  unfold lxArmO lxLvlO
  cases outO with
  | none => right; refine ⟨rfl, ?_⟩; split <;> simp
  | some o => left; exact ⟨o, rfl, by split <;> simp⟩

theorem lxStride_ge (w : Nat) : 16 ≤ lxStride w := by unfold lxStride; split <;> omega

theorem lxLvlO_lt {w r : Nat} (hr : r + 1 ≠ 8) (outO : Option Nat) (b : Nat) :
    b + 3 ≤ lxLvlO w r outO b ∧ lxLvlO w r outO b + 13 = b + lxStride w := by
  unfold lxLvlO lxStride
  by_cases hw : w + 1 = 4 <;> simp [hw, hr]

theorem lxSibCell_lt (w r b : Nat) : b ≤ lxSibCell w r b ∧ lxSibCell w r b ≤ b + 3 := by
  unfold lxSibCell; split <;> [omega; split <;> omega]

/-- **The levels of an arm complete** by the honest arm, level `j`'s sibling `sibs j`. -/
theorem lxLevelsT_complete {L : Nat} (hL : L < 2 ^ 32) {w : Nat} (hw : w < 4) {outO : Option Nat}
    {b0 : Nat} (hb0 : 103 ≤ b0) (sibs : Nat → E) (hsc : ∀ r < 8, IsCanonical128 (sibs r))
    (hO : ∀ o, outO = some o → 103 ≤ o ∧ o + 13 ≤ b0) :
    ∀ m r (cur : V) b (σ : Val), r + m = 8 → b = b0 + lxStride w * r → LxEnv L σ → NBv b cur →
      IsCanonical128 (σ cur) → (∀ o, outO = some o → ¬ InR o 13 cur) →
      CompletesO C rd b (lxLevelsT w (lxWin L w) outO m r cur b).2.1 (lxArmO w outO b0)
        (lxLevelsT w (lxWin L w) outO m r cur b).1 σ
        (fun σ' => (∀ j, r ≤ j → j < 8 → lxSibF σ' w b0 j = sibs j) ∧
          IsCanonical128 (σ' (lxLevelsT w (lxWin L w) outO m r cur b).2.2))
  | 0, r, cur, b, σ, hrm, _, _, _, hcc, _ =>
      ⟨σ, fun _ _ _ => rfl, ⟨fun j h1 h2 => absurd h2 (by omega), hcc⟩, fun _ _ hn => hn⟩
  | m + 1, r, cur, b, σ, hrm, hb, hE, hcur, hcc, hcO => by
      have hr : r < 8 := by omega
      have hst := lxStride_ge w
      have hbb : b0 ≤ b := by rw [hb]; omega
      have hlv := lxLevelT_complete (C := C) (rd := rd) hL hw hr σ hE (by omega) hcur hcc
        (fun o ho => ⟨(hO o ho).1, by have := (hO o ho).2; omega, hcO o ho⟩) (hsc r hr)
      have hsl := lxSibCell_lt w r b
      simp only [lxLevelsT]
      by_cases hm : m = 0
      · subst hm
        have hr7 : r = 7 := by omega
        subst hr7
        simp only [lxLevelsT, List.append_nil]
        have ho : lxArmO w outO b0 = lxLvlO w 7 outO b := by rw [lxArmO, hb]
        rw [ho, lxLevelT_out]
        refine hlv.mono le_rfl le_rfl (fun σ' ⟨h1, h2⟩ => ⟨fun j h1' h2' => ?_, h2⟩)
        obtain rfl : j = 7 := by omega
        rw [lxSibF, ← hb]
        exact h1
      · have hr7 : r + 1 ≠ 8 := by omega
        obtain ⟨hlo3, hlo13⟩ := lxLvlO_lt (w := w) hr7 outO b
        have hnb : (lxLevelT w (lxWin L w) r cur outO b).2.1 = b + lxStride w := lxLevelT_next hr7
        have hshape := (lxLevelsT_shape (w := w) (k := lxWin L w) (outO := outO) (b0 := b0) m (r + 1)
          (lxLevelT w (lxWin L w) r cur outO b).2.2 (lxLevelT w (lxWin L w) r cur outO b).2.1 (by omega)
          (by omega) (by rw [hnb, hb]; ring)).1
        have hOg := lxArmO_cases w outO b0
        have hb7 : b + lxStride w ≤ b0 + lxStride w * 7 := by
          have := Nat.mul_le_mul_left (lxStride w) (show r + 1 ≤ 7 by omega)
          rw [Nat.mul_succ] at this
          omega
        -- the level's values: below its end, off the arm's run
        have hoff : ∀ j, b ≤ j → j < b + lxStride w → ¬ InR (lxArmO w outO b0) 13 (.n j) := fun j h1 h2 =>
          notInR_of (by rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
                        · have := (hO o ho).2; omega
                        · omega)
        have hxs : ∀ v ∈ Stmt.valsList (lxLevelT w (lxWin L w) r cur outO b).1,
            NBv (b + lxStride w) v ∧ ¬ InR (lxArmO w outO b0) 13 v := by
          intro v hv
          rcases lxLevelT_vals hw hr (lxWin L w) cur outO v hv with rfl | ⟨j, hj, rfl⟩ | ⟨j, h1, h2, rfl⟩ | ⟨i, hi, rfl⟩
          · obtain ⟨j, hj, rfl⟩ := hcur
            refine ⟨⟨j, by omega, rfl⟩, ?_⟩
            rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
            · rw [e]; exact hcO o ho
            · exact notInR_of (by omega)
          · refine ⟨⟨j, by omega, rfl⟩, notInR_of ?_⟩
            rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
            · have := (hO o ho).1; omega
            · omega
          · rw [hnb] at h2; exact ⟨⟨j, h2, rfl⟩, hoff j h1 h2⟩
          · exact ⟨⟨_, by omega, rfl⟩, hoff _ (by omega) (by omega)⟩
        rw [hnb] at hlv hshape
        rw [hnb]
        refine Completes.appendO (by omega) (by rw [hshape]; omega) hxs
          (hlv.toC le_rfl (by omega) le_rfl (by omega)) (fun σ1 he1 ⟨hs1, hc1⟩ => ?_)
        have hE1 : LxEnv L σ1 := hE.congr fun j hj => he1.apply (Or.inl (by omega))
        have ih := lxLevelsT_complete hL hw hb0 sibs hsc hO m (r + 1) (lxLevelT w (lxWin L w) r cur outO b).2.2
          (b + lxStride w) σ1 (by omega) (by rw [hb]; ring) hE1
          (by rw [lxLevelT_out]; exact ⟨_, by omega, rfl⟩) (by rw [lxLevelT_out]; exact hc1)
          (fun o ho => by rw [lxLevelT_out]; exact notInR_of (by have := (hO o ho).2; omega))
        refine ih.keep.mono le_rfl le_rfl (fun σ' ⟨⟨h1, h2⟩, he⟩ => ⟨fun j hj1 hj2 => ?_, h2⟩)
        rcases Nat.lt_or_ge r j with hrj | hrj
        · exact h1 j hrj hj2
        · obtain rfl : j = r := by omega
          rw [lxSibF, ← hb, he.apply (Or.inl (by omega)) ?_, hs1]
          rcases hOg with ⟨o, ho, e⟩ | ⟨-, e1, -⟩
          · have := (hO o ho).2; omega
          · omega

end
end LeanVM.Guest.B1.Sig
