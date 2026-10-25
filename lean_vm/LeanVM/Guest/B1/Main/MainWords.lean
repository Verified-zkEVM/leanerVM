/-
  LeanVM.Guest.B1.Main.MainWords

  `main`'s words on an honest run (`Bmain`) bounded by a budget linear in the work
  (`End.Linear`): its buffers and each callee's bound, every bound linear in the claims, the raw
  signatures, the direct DA rows and the children.
-/

module

public import LeanVM.Guest.B1.Main.MainHonestBudgetB
public import LeanVM.Guest.Complete

/-!
# `main`'s words, linear in the work

Component bounds: `colB_le` (a DA column, linear in its rows), `dvB_le` (`da_verify`),
`clB_le`, `ccB_le` (the claim lists' digests, linear in the list's length), `l5Chain_le` (the
children's loop, linear in the children and their claims). `mainWords`: the budget;
`Bmain_le`: `Bmain` at `0` within it.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Verifier LeanVM.Node
open LeanVM.Guest.B1 (Kid kidsBoundL)

@[expose] public section

/-- The bounds `g` of the first `n` names of `names`. -/
def nameSum (g : String → ℕ) (names : List String) (n : ℕ) : ℕ :=
  ((List.range n).map fun j => g names[j]!).sum

theorem le_nameSum {g : String → ℕ} {names : List String} {n j : ℕ} (hj : j < n) :
    g names[j]! ≤ nameSum g names n :=
  List.single_le_sum (fun _ _ => Nat.zero_le _) _ (List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩)

theorem ite_le_add {p : Prop} [Decidable p] (a b : ℕ) : (if p then a else b) ≤ a + b := by
  split <;> omega

variable (fs SB SK : String → ℕ)

/-! ## `da_verify` -/

/-- The selected DA level's words per padded row, at most: the largest over the `11` levels of
`⌈SB (da_levels at j) / 2^j⌉`. -/
def dlK : ℕ := (Finset.range 11).sup fun j => (SB Da.dlNames[j]! + 2 ^ j - 1) / 2 ^ j

theorem le_cdiv_mul (a d : ℕ) (hd : 0 < d) : a ≤ (a + d - 1) / d * d := by
  have h1 := Nat.div_add_mod (a + d - 1) d
  have h2 := Nat.mod_lt (a + d - 1) hd
  have h3 : d * ((a + d - 1) / d) = (a + d - 1) / d * d := Nat.mul_comm _ _
  omega

/-- **The selected DA level within `dlK` words per padded row.** -/
theorem dl_le {L : ℕ} (hL : L < 11) : SB Da.dlNames[L]! ≤ dlK SB * 2 ^ L := by
  have h1 := le_cdiv_mul (SB Da.dlNames[L]!) (2 ^ L) (Nat.two_pow_pos L)
  have h2 : (SB Da.dlNames[L]! + 2 ^ L - 1) / 2 ^ L ≤ dlK SB :=
    Finset.le_sup (f := fun j => (SB Da.dlNames[j]! + 2 ^ j - 1) / 2 ^ j)
      (Finset.mem_range.mpr hL)
  exact le_trans h1 (Nat.mul_le_mul_right _ h2)

/-- A DA column's constant words. -/
def colC (fname gl : String) : ℕ := fs fname + fs "da_vector_cell" + fs gl

/-- A DA column's words per row. -/
def colS (rl gl : String) : ℕ := 8 + SK rl + SK gl + 2 * dlK SB

theorem colB_le {fname rl gl : String} {r L : ℕ} (hP : 2 ^ L ≤ 2 * r) (hL : L < 11) :
    Da.colB fs SB SK fname rl gl r L ≤ colC fs fname gl + r * colS SB SK rl gl := by
  unfold Da.colB colC colS
  have h1 : (if 2 ^ L - r ≠ 0 then (2 ^ L - r) * SK gl else fs gl) ≤ r * SK gl + fs gl := by
    split
    · have : (2 ^ L - r) * SK gl ≤ r * SK gl := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
  have h2 := dl_le SB hL
  have h4 : dlK SB * 2 ^ L ≤ dlK SB * (2 * r) := Nat.mul_le_mul_left _ hP
  have h3 : r * (8 + SK rl + SK gl + 2 * dlK SB) =
      8 * r + r * SK rl + r * SK gl + dlK SB * (2 * r) := by ring
  omega

/-- `da_verify`'s constant words. -/
def dvC : ℕ :=
  fs "da_verify" + 768 + fs "da_row_shape" + fs "__loop24" + SB "da_levels__L128_L7" +
    (65 * fs "__loop20" + 64 * colC fs "da_verify_column__L1" "__loop418") +
    (65 * fs "__loop21" + 64 * colC fs "da_verify_column__L0" "__loop420")

/-- `da_verify`'s words per row. -/
def dvS : ℕ :=
  395 + SK "__loop18" + SK "__loop19" + SK "__loop22" + SK "__loop23" + SK "__loop24" +
    2 * dlK SB + 64 * colS SB SK "__loop417" "__loop418" + 64 * colS SB SK "__loop419" "__loop420"

theorem clLoop_le {f : String} {Bc C S r : ℕ} (h : Bc ≤ C + r * S) :
    Da.clB fs f Bc 64 ≤ 65 * fs f + 64 * C + r * (64 * S) := by
  unfold Da.clB
  have : r * (64 * S) = 64 * (r * S) := by ring
  omega

theorem dvB_le {r L : ℕ} (hr : 1 ≤ r) (hP : 2 ^ L ≤ 2 * r) (hL : L < 11) :
    Da.dvB fs SB SK r L ≤ dvC fs SB + r * dvS SB SK := by
  unfold Da.dvB Da.dvKB dvC dvS Da.dvSizes
  have c1 := clLoop_le fs (f := "__loop20") (colB_le fs SB SK (fname := "da_verify_column__L1")
    (rl := "__loop417") (gl := "__loop418") hP hL)
  have c0 := clLoop_le fs (f := "__loop21") (colB_le fs SB SK (fname := "da_verify_column__L0")
    (rl := "__loop419") (gl := "__loop420") hP hL)
  have h24 : (if 2 ^ L - r ≠ 0 then (2 ^ L - r) * SK "__loop24" else fs "__loop24") ≤
      r * SK "__loop24" + fs "__loop24" := by
    split
    · have : (2 ^ L - r) * SK "__loop24" ≤ r * SK "__loop24" := Nat.mul_le_mul_right _ (by omega)
      omega
    · omega
  have hd := dl_le SB hL
  have h4 : dlK SB * 2 ^ L ≤ dlK SB * (2 * r) := Nat.mul_le_mul_left _ hP
  simp only [List.sum_cons, List.sum_nil]
  have e : r * (395 + SK "__loop18" + SK "__loop19" + SK "__loop22" + SK "__loop23" +
      SK "__loop24" + 2 * dlK SB + 64 * colS SB SK "__loop417" "__loop418" +
      64 * colS SB SK "__loop419" "__loop420") =
      395 * r + r * SK "__loop18" + r * SK "__loop19" + r * SK "__loop22" + r * SK "__loop23" +
      r * SK "__loop24" + dlK SB * (2 * r) + r * (64 * colS SB SK "__loop417" "__loop418") +
      r * (64 * colS SB SK "__loop419" "__loop420") := by ring
  omega

/-! ## The claim lists

A claim list's digest takes `13` words and a loop iteration per `17` claims (`CLAIM_GROUP`):
`(n / 17) · K ≤ n · ⌈K / 17⌉` (`div17_mul_le`), so the words per claim are `1 + ⌈K / 17⌉`. -/

theorem div17_mul_le (n K : ℕ) : n / 17 * K ≤ n * ((K + 16) / 17) := by
  have h1 : K ≤ 17 * ((K + 16) / 17) := by omega
  have h2 : n / 17 * 17 ≤ n := Nat.div_mul_le_self n 17
  calc n / 17 * K ≤ n / 17 * (17 * ((K + 16) / 17)) := Nat.mul_le_mul_left _ h1
    _ = n / 17 * 17 * ((K + 16) / 17) := by ring
    _ ≤ n * ((K + 16) / 17) := Nat.mul_le_mul_right _ h2

/-- A claim list's digest's constant words. -/
def clC : ℕ :=
  fs "claim_list_digest" + 13 + SB "list_split" + fs "__loop16" + nameSum SB B1.Digest.clNames 17

/-- A claim list's digest's words per claim: `13` and a `__loop16` iteration per `17` claims. -/
def clS : ℕ := 1 + (SK "__loop16" + 16) / 17

theorem clB_le (n : ℕ) : B1.Digest.clB fs SB SK n ≤ clC fs SB + n * clS SK := by
  unfold B1.Digest.clB clC clS
  split
  · omega
  · have h1 := le_nameSum (g := SB) (names := B1.Digest.clNames) (j := n % 17) (Nat.mod_lt _ (by omega))
    have h2 := div17_mul_le n (SK "__loop16")
    have h3 : (if n / 17 ≠ 0 then n / 17 * SK "__loop16" else fs "__loop16") ≤
        n * ((SK "__loop16" + 16) / 17) + fs "__loop16" := by
      split <;> omega
    have h4 : 13 * (n / 17) ≤ n := by omega
    have e : n * (1 + (SK "__loop16" + 16) / 17) = n + n * ((SK "__loop16" + 16) / 17) := by ring
    omega

/-- A child's claim list's digest's constant words. -/
def ccC : ℕ :=
  fs "child_claim_list_digest" + 13 + SB "list_split" + fs "__loop17" +
    nameSum (fun g => fs g) B1.Digest.cclNames 17

/-- A child's claim list's digest's words per claim: `13` and a `__loop17` frame per `17` claims. -/
def ccS : ℕ := 1 + (fs "__loop17" + 16) / 17

theorem ccB_le (n : ℕ) : B1.Digest.ccB fs SB n ≤ ccC fs SB + n * ccS fs := by
  unfold B1.Digest.ccB ccC ccS
  split
  · omega
  · have h1 := le_nameSum (g := fun g => fs g) (names := B1.Digest.cclNames) (j := n % 17)
      (Nat.mod_lt _ (by omega))
    have hg : B1.Digest.cclNames.getD (n % 17) "" = B1.Digest.cclNames[n % 17]! := by
      simp only [List.getD_eq_getElem?_getD, getElem!_def]
      cases B1.Digest.cclNames[n % 17]? <;> rfl
    rw [hg]
    have h2 := div17_mul_le n (fs "__loop17")
    have h3 : (if n / 17 ≠ 0 then (n / 17 + 1) * fs "__loop17" else fs "__loop17") ≤
        n * ((fs "__loop17" + 16) / 17) + fs "__loop17" := by
      split
      · have e : (n / 17 + 1) * fs "__loop17" = n / 17 * fs "__loop17" + fs "__loop17" := by ring
        omega
      · omega
    have h4 : 13 * (n / 17) ≤ n := by omega
    have e : n * (1 + (fs "__loop17" + 16) / 17) = n + n * ((fs "__loop17" + 16) / 17) := by ring
    omega

/-! ## The children's loop -/

/-- A child's constant words in the children's loop (but `verify_sub`'s): the iteration's frame and
`HeapBuf`s, its claim lists' digests' constants, `__loop28` over at most `16` DA roots
(`MAX_DA_ROOTS`, `Limits.daRoots`), `da_list_digest`, `statement_digest`. -/
def l5A1 : ℕ :=
  fs "__loop5" + 2 + 2 * ccC fs SB + (64 + 16 * (fs "__loop28" + fs "cover_da_root") +
    fs "__loop28") + SB "da_list_digest" + SB "statement_digest"

/-- The children's loop's words per child's claim. -/
def l5A2 : ℕ := ccS fs

/-- The children's loop's constant words. -/
def l5A0 : ℕ := fs "__loop5"

theorem l5Chain_le (K : ℕ → ℕ) : ∀ t c, l5ChainB fs K t c ≤
    (t + 2) * fs "__loop5" + ∑ i ∈ Finset.range (t + 1), K (c + i)
  | 0, c => by simp [l5ChainB]; omega
  | t + 1, c => by
    have ih := l5Chain_le K t (c + 1)
    rw [l5ChainB, Finset.sum_range_succ']
    have e : ∑ i ∈ Finset.range (t + 1), K (c + 1 + i) = ∑ i ∈ Finset.range (t + 1), K (c + (i + 1)) :=
      Finset.sum_congr rfl fun i _ => by rw [Nat.add_right_comm, Nat.add_assoc]
    rw [e] at ih
    have e2 : (t + 1 + 2) * fs "__loop5" = fs "__loop5" + (t + 2) * fs "__loop5" := by ring
    simp only [Nat.add_zero]
    omega

theorem sum_range_getD : ∀ l : List ℕ, ∑ i ∈ Finset.range l.length, l.getD i 0 = l.sum
  | [] => rfl
  | a :: l => by
    rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
    simp only [List.getD_cons_succ, List.getD_cons_zero, sum_range_getD l]
    omega

theorem kid_counts (w : NodeWitness) (c : ℕ) : hEx w c + hEs w c + hEd w c =
    (w.children.map fun ch => ch.statement.claims.xmss.length + ch.statement.claims.sphincs.length +
      ch.statement.claims.da.length).getD c 0 := by
  simp only [hEx, hEs, hEd, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases w.children[c]? <;> rfl

/-- A child's DA roots are at most `16` (`MAX_DA_ROOTS`). -/
theorem hEd_le {bytecode : List K} {s : NodeStatement} {w : NodeWitness} (hl : Limits bytecode s w)
    (c : ℕ) : hEd w c ≤ 16 := by
  simp only [hEd, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : w.children[c]? with
  | none => simp
  | some ch => simpa using hl.daRoots.2 ch (List.mem_of_getElem? h)

/-- **The children's loop's words**: a constant, each child's constant and `verify_sub`'s bound
`Bv c`, and a slope per child's claim. -/
theorem l5B_le (Bv : ℕ → ℕ) {bytecode : List K} {s : NodeStatement} {w : NodeWitness}
    (hl : Limits bytecode s w) (hnc : w.children.length ≠ 0) :
    l5B fs SB (fun c => B1.Digest.ccB fs SB (hKid s w c).ex) (fun c => B1.Digest.ccB fs SB (hKid s w c).es)
      Bv s w ≤ l5A0 fs + w.children.length * l5A1 fs SB +
        ∑ c ∈ Finset.range w.children.length, Bv c + l5A2 fs * (End.work s w).childClaims := by
  unfold l5B
  have h := l5Chain_le fs (fun c => l5K fs SB (B1.Digest.ccB fs SB (hKid s w c).ex)
    (B1.Digest.ccB fs SB (hKid s w c).es) (Bv c) (hKid s w c).ed) (w.children.length - 1) 0
  rw [show w.children.length - 1 + 1 = w.children.length by omega] at h
  have hK : ∀ c, l5K fs SB (B1.Digest.ccB fs SB (hKid s w c).ex) (B1.Digest.ccB fs SB (hKid s w c).es)
      (Bv c) (hKid s w c).ed ≤ ((l5A1 fs SB - fs "__loop5" + Bv c) +
        l5A2 fs * (hEx w c + hEs w c + hEd w c)) := by
    intro c
    have h1 := ccB_le fs SB (hKid s w c).ex
    have h2 := ccB_le fs SB (hKid s w c).es
    have hd := hEd_le hl c
    have h3 : hEd w c * (fs "__loop28" + fs "cover_da_root") ≤
        16 * (fs "__loop28" + fs "cover_da_root") := Nat.mul_le_mul_right _ hd
    unfold l5K l28B l5A1 l5A2
    simp only [List.sum_cons, List.sum_nil, hKid] at h1 h2 ⊢
    have e : ccS fs * (hEx w c + hEs w c + hEd w c) =
        hEx w c * ccS fs + hEs w c * ccS fs + hEd w c * ccS fs := by ring
    omega
  have hs := Finset.sum_le_sum fun c (_ : c ∈ Finset.range w.children.length) => hK c
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, Finset.card_range,
    smul_eq_mul, ← Finset.mul_sum] at hs
  have hcc : ∑ c ∈ Finset.range w.children.length, (hEx w c + hEs w c + hEd w c) =
      (End.work s w).childClaims := by
    simp only [kid_counts]
    rw [show w.children.length = (w.children.map fun ch => ch.statement.claims.xmss.length +
      ch.statement.claims.sphincs.length + ch.statement.claims.da.length).length by simp,
      sum_range_getD]
    rfl
  rw [hcc] at hs
  simp only [Nat.zero_add] at h
  have hA : fs "__loop5" ≤ l5A1 fs SB := by unfold l5A1; omega
  unfold l5A0
  have e : w.children.length * l5A1 fs SB =
      w.children.length * (l5A1 fs SB - fs "__loop5") + w.children.length * fs "__loop5" := by
    rw [← Nat.mul_add]; congr 1; omega
  have e2 : (w.children.length + 1) * fs "__loop5" = w.children.length * fs "__loop5" + fs "__loop5" := by
    ring
  rw [show w.children.length - 1 + 2 = w.children.length + 1 by omega] at h
  beta_reduce at h hs ⊢
  omega

/-! ## `da_verify` at the direct witness, `aggregate_claims` -/

theorem hDvB_le {bytecode : List K} {seed : Digest} {s : NodeStatement} {w : NodeWitness}
    (hr : NodeRel bytecode seed s w) (hl : Limits bytecode s w) :
    hDvB fs SB SK s w ≤ (End.work s w).rawDa * dvC fs SB + (End.work s w).rawDaRows * dvS SB SK := by
  have h1 := hl.directDa
  unfold hDvB
  show _ ≤ (hRawD s w).length * dvC fs SB +
    ((hRawD s w).map fun p => p.2.rows.length).sum * dvS SB SK
  match hp : hRawD s w, h1 with
  | [], _ => simp
  | [p], _ =>
    have hw : p.2.Opens p.1.daRoot p.1.membershipVectorDigest :=
      direct_held (H := DaHeld w.children)
        (P := fun c x => x.Opens c.daRoot c.membershipVectorDigest) (fun _ _ h => h)
        hr.2.2.2.2.1 p (show p ∈ hRawD s w by rw [hp]; exact List.mem_singleton_self p)
    have hb := Da.nPad_bounds hw.1
    have hm := hw.2.1
    unfold LeanDa.maxRows at hm
    unfold LeanDa.nPad at hb
    have hL : Da.wLog p.2 < 11 := by
      unfold Da.wLog
      have : 2 ^ LeanDa.logPad p.2.rows.length < 2 ^ 11 := by omega
      exact (Nat.pow_lt_pow_iff_right (by norm_num)).mp this
    simp only [List.map_cons, List.map_nil, List.headD_cons, List.sum_cons, List.sum_nil, Nat.add_zero,
      List.length_singleton, Nat.one_mul]
    exact dvB_le fs SB SK hw.1 (by unfold Da.wLog; omega) hL
  | _ :: _ :: _, h =>
    exact absurd h (by rw [show Hints.direct s.claims.da w.da = hRawD s w from rfl, hp]; simp)

/-- `aggregate_claims`' constant words. -/
def agA0 : ℕ := fs "aggregate_claims" + 97 + SB "batch_sumcheck__L23"

/-- `aggregate_claims`' words per child. -/
def agA1 : ℕ := 32 + SK "__loop25" + SK "__loop26" + SK "__loop27"

theorem aggB_eq (m : ℕ) : aggB fs SB SK m = agA0 fs SB + agA1 SK * m := by
  unfold aggB aggKB agA0 agA1 aggSizes
  simp only [List.sum_cons, List.sum_nil]
  ring

/-! ## `main`'s callees' words -/

theorem kidsBoundL_le_sum : ∀ (ks : List Kid) (Bs : List ℕ),
    kidsBoundL fs ks Bs ≤ Bs.sum + (ks.map fun k => fs k.f).sum
  | [], _ => Nat.zero_le _
  | k :: ks, [] => by
    have := kidsBoundL_le_sum ks []
    simp only [kidsBoundL, List.headD_nil, List.tail_nil, List.sum_nil, List.map_cons,
      List.sum_cons] at this ⊢
    have := ite_le_add (p := k.taken = true) 0 (fs k.f)
    omega
  | k :: ks, B :: Bs => by
    have := kidsBoundL_le_sum ks Bs
    simp only [kidsBoundL, List.headD_cons, List.tail_cons, List.map_cons, List.sum_cons] at this ⊢
    have := ite_le_add (p := k.taken = true) B (fs k.f)
    omega

theorem kidsBoundL_append (b : List Kid) (Bb : List ℕ) : ∀ (a : List Kid) (Ba : List ℕ),
    a.length = Ba.length → kidsBoundL fs (a ++ b) (Ba ++ Bb) = kidsBoundL fs a Ba + kidsBoundL fs b Bb
  | [], [], _ => by simp [kidsBoundL]
  | k :: a, B :: Ba, h => by
    simp only [List.cons_append, kidsBoundL, List.headD_cons, List.tail_cons]
    rw [kidsBoundL_append b Bb a Ba (by simpa using h)]
    omega
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- Child `c`'s `verify_sub` words, `Bvf` at its announced stack log and rate (`childShape`). -/
def childBv (Bvf : ℕ → ℕ → ℕ) (w : NodeWitness) (c : ℕ) : ℕ :=
  (w.children.map fun ch => Bvf (childShape End.bytecode ch).1 (childShape End.bytecode ch).2).getD c 0

theorem childBv_of_lt (Bvf : ℕ → ℕ → ℕ) (w : NodeWitness) {c : ℕ} (hc : c < w.children.length) :
    childBv Bvf w c = Bvf (childShape End.bytecode w.children[c]).1
      (childShape End.bytecode w.children[c]).2 := by
  simp [childBv, List.getD_eq_getElem?_getD, hc]

theorem sum_childBv (Bvf : ℕ → ℕ → ℕ) (s : NodeStatement) (w : NodeWitness) :
    ∑ c ∈ Finset.range w.children.length, childBv Bvf w c =
      ((End.work s w).childShapes.map fun p => Bvf p.1 p.2).sum := by
  have h := sum_range_getD (w.children.map fun ch =>
    Bvf (childShape End.bytecode ch).1 (childShape End.bytecode ch).2)
  simp only [List.length_map] at h
  unfold childBv
  rw [h]
  simp only [End.work, List.map_map]
  rfl

/-- **`main`'s words budget**, linear in the work: `main`'s frame and buffers, `exponent_tables`',
and each callee's frame and bound, child `c`'s `verify_sub` within `Bvf` at its announced stack log
and rate. -/
def mainWords (Bvf : ℕ → ℕ → ℕ) : End.Linear where
  base := fs "main" + 283 + fs "exponent_tables" + 68 + fs "__loop0" + SB "da_list_digest" +
    fs "da_list_digest" + 2 * (clC fs SB + fs "claim_list_digest") + fs "__loop1" + fs "__loop2" +
    fs "__loop3" + fs "__loop4" + 2 * l5A0 fs + (agA0 fs SB + fs "aggregate_claims") + SB "statement_digest" +
    fs "statement_digest"
  declared := clS SK
  coverage := 5 + SK "__loop0" + SK "__loop1" + SK "__loop2"
  rawXmss := SK "__loop3"
  rawSphincs := SK "__loop4"
  rawDa := dvC fs SB + fs "da_verify" + 2 * fs "cover_da_root"
  rawDaRows := dvS SB SK
  children := 51 + l5A1 fs SB + agA1 SK
  childClaims := l5A2 fs
  childShape := Bvf

theorem mSizes_sum (seed : Digest) (s : NodeStatement) (w : NodeWitness) :
    (mSizes (hData seed s w)).sum = 5 * coverage s w + 51 * w.children.length + 283 := by
  rw [coverage_eq]
  simp only [mSizes, MainData.T, MainData.X, MainData.Y, MainData.S, hData, List.sum_cons,
    List.sum_nil, List.length_append]
  ring

/-- **`main`'s callees' words**: each callee's bound and frame, the children's loop's frame
alone when there is no child. -/
theorem kidsBoundL_mKids (m : MainIn) (L : Layout) (b : MainBs) :
    kidsBoundL fs (mKids m L) (mBs fs SB SK m b) ≤
      (m.nda + m.ndd) * SK "__loop0" + fs "__loop0" + SB "da_list_digest" + fs "da_list_digest" +
      b.Bx + b.Bs + 2 * fs "claim_list_digest" + m.nxd * SK "__loop1" + fs "__loop1" +
      m.nsd * SK "__loop2" + fs "__loop2" + m.nrx * SK "__loop3" + fs "__loop3" +
      m.nrs * SK "__loop4" + fs "__loop4" +
      (if m.nd = 1 then b.Bd + fs "da_verify" + 2 * fs "cover_da_root" else 0) +
      (if m.nc = 0 then fs "__loop5" else b.B5 + fs "__loop5" + b.Ba + fs "aggregate_claims") +
      SB "statement_digest" + fs "statement_digest" := by
  unfold mKids mBs
  by_cases hnd : m.nd = 1 <;> by_cases hnc : m.nc = 0 <;>
    simp only [hnd, hnc, ↓reduceIte, List.append_nil, List.cons_append, List.nil_append,
      kidsBoundL, List.headD_cons, List.tail_cons, ne_eq, not_true_eq_false, not_false_eq_true,
      decide_false, decide_true, Bool.false_eq_true] <;>
    split_ifs <;> omega

/-- **`main`'s words on the honest run within the budget**, child `c`'s `verify_sub` within
`childBv Bvf w c`. -/
theorem Bmain_le (Bvf : ℕ → ℕ → ℕ) {bytecode : List K} {seed : Digest} {s : NodeStatement}
    {w : NodeWitness} (hr : NodeRel bytecode seed s w) (hl : Limits bytecode s w) :
    Bmain fs SB SK (childBv Bvf w) 0 seed s w ≤ (mainWords fs SB SK Bvf).eval (End.work s w) := by
  have hmsz := mSizes_sum seed s w
  have hX := clB_le fs SB SK s.claims.xmss.length
  have hS := clB_le fs SB SK s.claims.sphincs.length
  have hD := hDvB_le fs SB SK hr hl
  have hA := aggB_eq fs SB SK w.children.length
  have hcov := coverage_eq (s := s) (w := w)
  simp only [List.length_append] at hcov
  have c0 : (s.claims.da.length + (dPlan s w).dups.length) * SK "__loop0" ≤
      coverage s w * SK "__loop0" := Nat.mul_le_mul_right _ (by omega)
  have c1 : (xPlan s w).dups.length * SK "__loop1" ≤ coverage s w * SK "__loop1" :=
    Nat.mul_le_mul_right _ (by omega)
  have c2 : (sPlan s w).dups.length * SK "__loop2" ≤ coverage s w * SK "__loop2" :=
    Nat.mul_le_mul_right _ (by omega)
  have hK := kidsBoundL_mKids fs SB SK (hm fs 0 seed s w) (hLmain fs 0 seed s w)
    (mainBsH fs SB SK (childBv Bvf w) s w)
  have hB : Bmain fs SB SK (childBv Bvf w) 0 seed s w = fs "main" + (mSizes (hData seed s w)).sum +
      (fs "exponent_tables" + 68 + kidsBoundL fs (mKids (hm fs 0 seed s w) (hLmain fs 0 seed s w))
        (mBs fs SB SK (hm fs 0 seed s w) (mainBsH fs SB SK (childBv Bvf w) s w))) := rfl
  generalize kidsBoundL fs (mKids (hm fs 0 seed s w) (hLmain fs 0 seed s w))
    (mBs fs SB SK (hm fs 0 seed s w) (mainBsH fs SB SK (childBv Bvf w) s w)) = KB at hK hB
  rw [hB, hmsz]
  have hd : (hm fs 0 seed s w).nd ≤ 1 := hl.directDa
  have hcl : s.claims.xmss.length + s.claims.sphincs.length ≤ (End.work s w).declared := by
    simp only [End.work]; omega
  have hcl2 := Nat.mul_le_mul_right (clS SK) hcl
  have hcov' : coverage s w = (End.work s w).coverage := rfl
  have e0 : (hm fs 0 seed s w).nda + (hm fs 0 seed s w).ndd =
      s.claims.da.length + (dPlan s w).dups.length := rfl
  have e1 : (hm fs 0 seed s w).nxd = (xPlan s w).dups.length := rfl
  have e2 : (hm fs 0 seed s w).nsd = (sPlan s w).dups.length := rfl
  have e3 : (hm fs 0 seed s w).nrx = (End.work s w).rawXmss := rfl
  have e4 : (hm fs 0 seed s w).nrs = (End.work s w).rawSphincs := rfl
  have e6 : w.children.length = (End.work s w).children := rfl
  have e7 : (mainBsH fs SB SK (childBv Bvf w) s w).Bx = B1.Digest.clB fs SB SK s.claims.xmss.length := rfl
  have e8 : (mainBsH fs SB SK (childBv Bvf w) s w).Bs = B1.Digest.clB fs SB SK s.claims.sphincs.length :=
    rfl
  have e9 : (mainBsH fs SB SK (childBv Bvf w) s w).Bd = hDvB fs SB SK s w := rfl
  have e10 : (mainBsH fs SB SK (childBv Bvf w) s w).Ba = aggB fs SB SK w.children.length := rfl
  have e11 : (mainBsH fs SB SK (childBv Bvf w) s w).B5 = l5B fs SB
      (fun c => B1.Digest.ccB fs SB (hKid s w c).ex) (fun c => B1.Digest.ccB fs SB (hKid s w c).es)
      (childBv Bvf w) s w := rfl
  rw [e0, e1, e2, e3, e4, e7, e8, e9, e10, e11] at hK
  rw [hcov'] at c0 c1 c2 ⊢
  rw [e6]
  simp only [End.Linear.eval, mainWords, l5A0]
  have r1 : clS SK * (End.work s w).declared = (End.work s w).declared * clS SK := Nat.mul_comm _ _
  have r2 : (s.claims.xmss.length + s.claims.sphincs.length) * clS SK =
      s.claims.xmss.length * clS SK + s.claims.sphincs.length * clS SK := Nat.add_mul _ _ _
  have r3 : (5 + SK "__loop0" + SK "__loop1" + SK "__loop2") * (End.work s w).coverage =
      5 * (End.work s w).coverage + (End.work s w).coverage * SK "__loop0" +
        (End.work s w).coverage * SK "__loop1" + (End.work s w).coverage * SK "__loop2" := by ring
  have r4 : SK "__loop3" * (End.work s w).rawXmss = (End.work s w).rawXmss * SK "__loop3" :=
    Nat.mul_comm _ _
  have r5 : SK "__loop4" * (End.work s w).rawSphincs = (End.work s w).rawSphincs * SK "__loop4" :=
    Nat.mul_comm _ _
  have r6 : dvS SB SK * (End.work s w).rawDaRows = (End.work s w).rawDaRows * dvS SB SK :=
    Nat.mul_comm _ _
  have r8 : (dvC fs SB + fs "da_verify" + 2 * fs "cover_da_root") * (End.work s w).rawDa =
      (End.work s w).rawDa * dvC fs SB + (End.work s w).rawDa * (fs "da_verify" + 2 * fs "cover_da_root") :=
    by ring
  have erd : (End.work s w).rawDa = (hm fs 0 seed s w).nd := rfl
  have r7 : (51 + l5A1 fs SB + agA1 SK) * (End.work s w).children =
      51 * (End.work s w).children + (End.work s w).children * l5A1 fs SB +
        agA1 SK * (End.work s w).children := by ring
  by_cases hnc : w.children.length = 0
  · have hnc' : (hm fs 0 seed s w).nc = 0 := hnc
    rw [e6] at hnc
    simp only [hnc', ↓reduceIte] at hK
    rw [hnc]
    simp only [Nat.mul_zero, Nat.add_zero]
    split_ifs at hK with hnd
    · have r9 : (End.work s w).rawDa * (fs "da_verify" + 2 * fs "cover_da_root") =
          fs "da_verify" + 2 * fs "cover_da_root" := by rw [erd, hnd, Nat.one_mul]
      omega
    · omega
  · have hnc' : ¬ (hm fs 0 seed s w).nc = 0 := hnc
    have h5 := l5B_le fs SB (childBv Bvf w) hl hnc
    rw [sum_childBv Bvf s w] at h5
    simp only [l5A0] at h5
    simp only [hnc', ↓reduceIte] at hK
    rw [e6] at hA h5 hK
    split_ifs at hK with hnd
    · have r9 : (End.work s w).rawDa * (fs "da_verify" + 2 * fs "cover_da_root") =
          fs "da_verify" + 2 * fs "cover_da_root" := by rw [erd, hnd, Nat.one_mul]
      omega
    · omega
end
end LeanVM.Guest.B1.Main
