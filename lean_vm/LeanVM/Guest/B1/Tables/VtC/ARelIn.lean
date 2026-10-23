/-
  LeanVM.Guest.B1.Tables.VtC.ARelIn

  **`verify_tables`' calls load from its layout**: on the honest memory and oracle, every
  statement holds with its calls by relations loading from the caller's and the own buffers only.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.AMain
public import LeanVM.Guest.B1.Tables.Kids.Families
public import LeanVM.Guest.B1.Tables.Kids.BlockSelTab
public import LeanVM.Guest.B1.Tables.Kids.Shared
public import LeanVM.Guest.B1.Tables.Kids.EqChain
public import LeanVM.Guest.B1.Tables.Kids.Loop10

/-!
# The calls, placed

`plainStB`: an atom, or an `ite` of atoms, whose `VSH` does not depend on the call relation
(`vsh_plain`). `verify_tables`' other statements are its `116` calls (`vt_calls`, by the kernel):
the padding weights (`pwCall`), `plus_one_run` (`porCall`), the shared selector tables (`shCall`),
the framework blocks' selectors and `index_mle` (`fwCall`, `imCall`), the table blocks' selectors
(`selCall`), `__loop10` and `eq_prefix_chain`.

A call's pointers are buffer bases times powers of `g` (from the statements' equations and the
memory's words), inside the buffers (`ptr_lin`, `ptr_own`, the own buffers full length by
`ownW_lengths`), so the callees' `RelIn` lemmas (`Tables/Kids`) apply. `vt_relIn_complete`: under
`vt_rel_complete`'s hypotheses, every statement holds by `coreProgram.RelIn` on `RegionL` of the
caller's and the own buffers.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd
open LeanVM.Guest.B1.Main (RegionL)

@[expose] public section

/-! ## Statements without calls -/

/-- An atom. -/
def atomStB : Stmt → Bool
  | .atom _ => true
  | _ => false

/-- An atom, or an `ite` of atoms. -/
def plainStB : Stmt → Bool
  | .atom _ => true
  | .ite _ z n => z.all atomStB && n.all atomStB
  | _ => false

theorem sholds_atom {C C' : CallRel} {rd : Reader} {σ : Val} {s : Stmt} (h : atomStB s = true)
    (hs : SHolds C rd σ s) : SHolds C' rd σ s := by
  cases s with
  | atom a => exact hs
  | _ => simp [atomStB] at h

theorem vsh_plain {C C' : CallRel} {rd : Reader} {σ : Val} {s : Stmt} (h : plainStB s = true)
    (hs : VSH C rd σ s) : VSH C' rd σ s := by
  cases s with
  | atom a => exact hs
  | ite c z n =>
    simp only [plainStB, Bool.and_eq_true, List.all_eq_true] at h
    exact ⟨hs.1, fun h0 s hs' ↦ sholds_atom (h.1 s hs') (hs.2.1 h0 s hs'),
      fun h0 s hs' ↦ sholds_atom (h.2 s hs') (hs.2.2 h0 s hs')⟩
  | _ => simp [plainStB] at h

/-- A dispatch on `g^m` by `C` is one by `C'` when arm `m`'s call is. -/
theorem vsh_disp {C C' : CallRel} {rd : Reader} {σ : Val} {x : V} {fs : List String}
    {a r : List V} {m : ℕ} (hx : σ x = gen ^ m) (hm : m < fs.length) (hfs : fs.length ≤ 64)
    (hup : C fs[m] (a.map σ) (r.map σ) → C' fs[m] (a.map σ) (r.map σ))
    (h : VSH C rd σ (.dispatch x fs a r)) : VSH C' rd σ (.dispatch x fs a r) := by
  rw [vsh_dispatch] at h ⊢
  obtain ⟨j, hj, e, hc⟩ := h
  obtain rfl : m = j := by
    rw [hx, gen_pow_eq_ofK] at e
    have := congrArg LeanVM.Guest.Memory.logG e
    rwa [LeanVM.Guest.Memory.logG_spec (e := m) (by omega),
      LeanVM.Guest.Memory.logG_spec (e := j) (by omega)] at this
  exact ⟨m, hm, by rw [hx, gen_pow_eq_ofK], hup hc⟩

/-! ## The calls -/

/-- Table `t`'s `padding_weight` dispatch. -/
def pwCall (t : ℕ) : Stmt :=
  .dispatch (.n (2640 + 14 * t)) vtPadNames [.n (2640 + 14 * t + 5), .n 8]
    [.n (2640 + 14 * t + 6), .n (2640 + 14 * t + 7), .n (2640 + 14 * t + 8)]

/-- The `plus_one_run` dispatch. -/
def porCall : Stmt := .dispatch (.n 9) plusOneRunNames [.n 2767, .n 8] [.n 2768]

/-- Table `t`'s `shared_selector_tables` call. -/
def shCall (t : ℕ) : Stmt :=
  if t = 0 then
    .call "shared_selector_tables" [.n 2769, .n 2770, .n 2778, .n 2779, .n 2780, .n 2773] []
  else
    .call "shared_selector_tables" [.n (2781 + 14 * (t - 1) + 8), .n (2781 + 14 * (t - 1) + 10),
      .n (2781 + 14 * (t - 1) + 11), .n (2781 + 14 * (t - 1) + 12), .n (2781 + 14 * (t - 1) + 13),
      .n (2781 + 14 * (t - 1) + 2)] []

/-- Framework block `b`'s `block_selector` dispatch. -/
def fwCall (b : ℕ) : Stmt :=
  .dispatch (.n (vtFwV.getD b 0 + 8)) vtBsNames [.n (vtFwV.getD b 0 + 13),
    .n (vtFwV.getD b 0 + 14), .n (vtFwV.getD b 0 + 15)]
    [.n (vtFwV.getD b 0 + 16), .n (vtFwV.getD b 0 + 17)]

/-- An `index_mle` dispatch on framework block `b`'s `g^κ`. -/
def imCall (b r : ℕ) : Stmt := .dispatch (.n (vtFwV.getD b 0)) vtImNames [.n 8] [.n r]

/-- A table block's `block_selector_tab` dispatch (`vtSelT`). -/
def selCall (x : ℕ × ℕ × ℕ × ℕ × Option ℕ) : Stmt :=
  .dispatch (.n (vtShLen x.2.2.2.1)) vtBstNames [.n (x.2.2.1 + 9),
      .n (if x.2.2.2.1 = 0 then 2769 else x.2.2.1 + 11),
      .n (if x.2.2.2.1 = 0 then 2770 else x.2.2.1 + 13)]
    [.n (vtSelE x.2.2.1 x.2.2.2.1), .n (vtSelE x.2.2.1 x.2.2.2.1 + 1)]

/-- The `__loop10` call. -/
def loopCall : Stmt :=
  .callIf (.n 5920) "__loop10" [.n 5921, .n 5817, .n 5912, .n 18, .n 5817, .n 5915]

/-- The `eq_prefix_chain` call. -/
def epcCall : Stmt := .call "eq_prefix_chain" [.n 5936, .n 5937, .n 18, .n 2767, .n 5817] []

/-- `verify_tables`' calls, in order. -/
def vtCalls : List Stmt :=
  (List.range 6).map pwCall ++ [porCall] ++ (List.range 6).map shCall ++
    [fwCall 0, fwCall 1, imCall 1 2908, fwCall 2, imCall 2 2983] ++
    (List.range 51).map (fun i ↦ selCall (vtPushSel.getD i default)) ++
    (List.range 45).map (fun i ↦ selCall (vtCountSel.getD i default)) ++ [loopCall, epcCall]

set_option maxRecDepth 100000 in
/-- **The calls, by the kernel**: the statements that are not plain. -/
theorem vt_calls : tbStmtsEqb (vtPre.filter fun s ↦ !plainStB s) vtCalls = true := by
  decide +kernel

theorem vt_call_mem {s : Stmt} (hs : s ∈ vtPre) (hp : plainStB s = false) : s ∈ vtCalls := by
  rw [← tbStmtsEqb_sound vt_calls]
  exact List.mem_filter.mpr ⟨hs, by simp [hp]⟩

set_option maxRecDepth 100000 in
theorem vt_pw_reads : ∀ t < 6, Atom.load (.n (2640 + 14 * t)) (.n 10) (t + 1) ∉ vtSL := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vt_sh_reads : ∀ t < 6, 1 ≤ t → Atom.load (.n (2781 + 14 * (t - 1))) (.n 10) (t + 1) ∉ vtSL := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem vt_sel_shapes : (∀ i < 51, (vtPushSel.getD i default).2.2.2.1 < 6 ∧
      2770 < (vtPushSel.getD i default).2.2.1) ∧
    ∀ i < 45, (vtCountSel.getD i default).2.2.2.1 < 6 ∧ 2770 < (vtCountSel.getD i default).2.2.1 := by
  decide +kernel

/-! ## Regions -/

/-- The region of the caller's and the own buffers. -/
abbrev VtHonest.reg (H : VtHonest) (B : VtBases) : ℕ → Prop := RegionL (H.linL B ++ H.ownL B)

theorem allocVars_mem {j : ℕ} (hj : j < 110) : vtAllocVars.getD j 0 ∈ vtAllocVars := by
  rw [List.getD_eq_getElem _ _ (by rw [vtAllocVars_length]; exact hj)]
  exact List.getElem_mem _

theorem getD_length_map : ∀ (l : List (List E)) (j : ℕ),
    (l.getD j []).length = (l.map List.length).getD j 0
  | [], _ => rfl
  | _ :: _, 0 => rfl
  | _ :: l, j + 1 => by simpa using getD_length_map l j

theorem sizes_bits (H : VtHonest) {j : ℕ} (h1 : 8 ≤ j) (h2 : j < 107) : H.sizes.getD j 0 = 34 := by
  unfold VtHonest.sizes
  rw [List.getD_append _ _ _ _ (by simp; omega), List.getD_append_right _ _ _ _ (by simp; omega),
    List.getD_eq_getElem _ _ (by simp; omega), List.getElem_replicate]

/-- **What `verify_tables`' placed calls need**: the shapes, the oracle, the memory. -/
structure VtIn (H : VtHonest) (B : VtBases) (w : ℕ → E) (rd : Reader) : Prop where
  ok : H.Ok
  hs : VtShape H
  hw : VtWOk H B w
  hm : MemLay rd (H.linL B ++ H.ownL B)

section
variable {H : VtHonest} {B : VtBases} {w : ℕ → E} {rd : Reader}

theorem ptr_lin {q : ℕ × List E} (hq : q ∈ H.linL B) {j n : ℕ} (h : j + n ≤ q.2.length) :
    PtrIn (H.reg B) (ofK (gpow q.1) * gen ^ j) n := by
  refine ptrIn_mul (ptrIn_ofK fun i hi ↦ ?_)
  unfold VtHonest.reg RegionL
  exact ⟨q, List.mem_append_left _ hq, by omega, by omega⟩

theorem ptr_lin0 {q : ℕ × List E} (hq : q ∈ H.linL B) {n : ℕ} (h : n ≤ q.2.length) :
    PtrIn (H.reg B) (ofK (gpow q.1)) n := by
  simpa using ptr_lin hq (j := 0) (n := n) (by omega)

theorem ptr_own (hw : VtWOk H B w) {j v : ℕ} (hj : j < 110) (hv : vtAllocVars.getD j 0 = v)
    {a n : ℕ} (h : a + n ≤ H.sizes.getD j 0) : PtrIn (H.reg B) (w v * gen ^ a) n := by
  subst hv
  rw [hw.alloc j hj]
  have hb := ownB_length H B
  have ho := ownW_length H B
  have hmem : ((H.ownB B).getD j 0, (H.ownW B).getD j []) ∈ H.ownL B := by
    rw [VtHonest.ownL, List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)]
    exact List.mem_iff_getElem.mpr ⟨j, by simp [hb, ho]; omega, by simp⟩
  have hl : ((H.ownW B).getD j []).length = H.sizes.getD j 0 := by
    rw [getD_length_map, ownW_lengths]
  refine ptrIn_mul (ptrIn_ofK fun i hi ↦ ?_)
  unfold VtHonest.reg RegionL
  exact ⟨_, List.mem_append_right _ hmem, by simp, by simp only; omega⟩

theorem ptr_own0 (hw : VtWOk H B w) {j v : ℕ} (hj : j < 110) (hv : vtAllocVars.getD j 0 = v)
    {n : ℕ} (h : n ≤ H.sizes.getD j 0) : PtrIn (H.reg B) (w v) n := by
  simpa using ptr_own hw hj hv (a := 0) (n := n) (by omega)

/-! ## The valuation's values -/

local notation "σv" => vtσ rd w (H.args B)

theorem vt_p {i : ℕ} (hi : i < 22) : σv (.n i) = (H.args B).getD i 0 := vt_param rfl hi

theorem vt_s8 : σv (.n 8) = ofK (gpow B.zeta) := vt_p (by norm_num)

theorem vt_s9 : σv (.n 9) = gen ^ H.μ := vt_p (by norm_num)

theorem vt_s13 : σv (.n 13) = ofK (gpow B.sq) := vt_p (by norm_num)

theorem vt_s18 : σv (.n 18) = ofK (gpow B.chi) := vt_p (by norm_num)

theorem vt_alloc' {v : ℕ} (hv : v ∈ vtAllocVars) : σv (.n v) = w v := vt_alloc_var rfl hv

theorem vt_const {d : ℕ} {e : E} (hs : Stmt.atom (.const (.n d) e) ∈ vtPre) : σv (.n d) = e :=
  vt_goodS rfl hs

theorem vt_copy {d x : ℕ} (hs : Stmt.atom (.copy (.n d) (.n x)) ∈ vtPre) :
    σv (.n d) = σv (.n x) :=
  vt_goodS rfl hs

theorem vt_add {d x y : ℕ} (hs : Stmt.atom (.add (.n d) (.n x) (.n y)) ∈ vtPre) :
    σv (.n d) = σv (.n x) + σv (.n y) :=
  vt_goodS rfl hs

theorem vt_mulF {d x y : ℕ} (hs : Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ vtPre) (h1 : x < d)
    (h2 : y < d) : σv (.n d) = σv (.n x) * σv (.n y) := by
  have g : GoodS rd vtSL w σv (fixNe (.atom (.mul (.n d) (.n x) (.n y)))) := vt_goodS rfl hs
  simp only [fixNe, GoodS, Good] at g
  rwa [ite_pos' (show (V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx from ⟨h1, h2⟩)] at g

theorem vt_mulB {d x y : ℕ} (hs : Stmt.atom (.mul (.n d) (.n x) (.n y)) ∈ vtPre) (h : d < x) :
    σv (.n x) = σv (.n d) * (σv (.n y))⁻¹ := by
  have g : GoodS rd vtSL w σv (fixNe (.atom (.mul (.n d) (.n x) (.n y)))) := vt_goodS rfl hs
  simp only [fixNe, GoodS, Good] at g
  rwa [ite_neg' (show ¬((V.n x).idx < (V.n d).idx ∧ (V.n y).idx < (V.n d).idx) from
    fun h' ↦ absurd h'.1 (by show ¬x < d; omega))] at g

theorem vt_ld {d p : V} {off : ℕ} (hs : Stmt.atom (.load d p off) ∈ vtPre)
    (hS : Atom.load d p off ∉ vtSL) {v : E} (h : LoadHolds rd (σv p) off v) : σv d = v :=
  (vtB_readM rfl hs hS h).1

theorem gen_div {a b : ℕ} (h : b ≤ a) : gen ^ a * (gen ^ b)⁻¹ = gen ^ (a - b) :=
  (pow_sub₀ _ gen_ne_zero h).symm

theorem vt_dims (I : VtIn H B w rd) : ∀ t < 6, LoadHolds rd (σv (.n 10)) (t + 1) (gen ^ H.τ t) := by
  intro t ht
  rw [vt_p (by norm_num), show (H.args B).getD 10 0 = ofK (gpow B.dims) from rfl]
  have mDims : TbReadsAt rd (ofK (gpow B.dims)) H.dimsW :=
    vt_lin_reads (q := (B.dims, H.dimsW)) I.hm (by simp [VtHonest.linL])
  have := tb_load_of mDims (k := t + 1) (by simp [VtHonest.dimsW, vtTauList]; omega)
  simpa [VtHonest.dimsW, vtTauList, List.getD_eq_getElem?_getD, ht] using this

theorem vt_bk (I : VtIn H B w rd) : ∀ b < 153, LoadHolds rd (σv (.n 12)) b (gen ^ H.κ b) := by
  intro b hb
  rw [vt_p (by norm_num), show (H.args B).getD 12 0 = ofK (gpow B.bk) from rfl]
  have mBk : TbReadsAt rd (ofK (gpow B.bk)) H.bkW :=
    vt_lin_reads (q := (B.bk, H.bkW)) I.hm (by simp [VtHonest.linL])
  have := tb_load_of mBk (k := b) (by simp [VtHonest.bkW, blockKappaWords]; omega)
  rwa [VtHonest.bkW, vt_kappa_word _ _ hb] at this

theorem vt_kap_fw : H.κ 0 = 0 ∧ H.κ 1 = H.lm ∧ H.κ 2 = 19 := by
  simp [VtHonest.κ, vtKap, blockKappaSrc, blockKappaAdj]

theorem vt_nμ (I : VtIn H B w rd) : H.n ≤ H.μ := by
  obtain ⟨t, ht, e⟩ := vt_n_ex I.hs.hr
  rw [← e]; exact I.hs.hτμ t ht

/-- **Table `t`'s `shared_len`**: `g^(μ - τ)`. -/
theorem vt_shLen (I : VtIn H B w rd) {t : ℕ} (ht : t < 6) :
    σv (.n (vtShLen t)) = gen ^ (H.μ - H.τ t) := by
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · have m0 := vt_mem_slice vtSh0_check (s := .atom (.load (.n 2771) (.n 10) 1)) (by simp [vtSh0T])
    have m1 := vt_mem_slice vtSh0_check (s := .atom (.mul (.n 9) (.n 2772) (.n 2771)))
      (by simp [vtSh0T])
    have m2 := vt_mem_slice vtSh0_check (s := .atom (.copy (.n 2773) (.n 2772))) (by simp [vtSh0T])
    have e0 : σv (.n 2771) = gen ^ H.τ 0 := vt_ld m0 (by decide +kernel) (vt_dims I 0 (by norm_num))
    rw [show vtShLen 0 = 2773 from rfl, vt_copy m2, vt_mulB m1 (by norm_num), e0, vt_s9,
      gen_div hτ]
  · have chk := vtSh_check t ht h0
    have m0 := vt_mem_slice chk (s := .atom (.load (.n (2781 + 14 * (t - 1))) (.n 10) (t + 1)))
      (by simp [vtShT])
    have m1 := vt_mem_slice chk (s := .atom (.mul (.n 9) (.n (2781 + 14 * (t - 1) + 1))
      (.n (2781 + 14 * (t - 1))))) (by simp [vtShT])
    have m2 := vt_mem_slice chk (s := .atom (.copy (.n (2781 + 14 * (t - 1) + 2))
      (.n (2781 + 14 * (t - 1) + 1)))) (by simp [vtShT])
    have e0 : σv (.n (2781 + 14 * (t - 1))) = gen ^ H.τ t :=
      vt_ld m0 (vt_sh_reads t ht h0) (vt_dims I t ht)
    rw [show vtShLen t = 2781 + 14 * (t - 1) + 2 by simp [vtShLen]; omega, vt_copy m2,
      vt_mulB m1 (by omega), e0, vt_s9, gen_div hτ]

/-! ## Each family -/

theorem vt_pw_up (I : VtIn H B w rd) {t : ℕ} (ht : t < 6)
    (h : VSH (coreProgram.Rel rd) rd σv (pwCall t)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (pwCall t) := by
  have hmem : Stmt.atom (.load (.n (2640 + 14 * t)) (.n 10) (t + 1)) ∈ vtPre := by
    rcases Nat.lt_or_ge t 5 with h5 | h5
    · exact vt_mem_slice (vtPad_check t h5) (by simp [vtPadT])
    · obtain rfl : t = 5 := by omega
      exact vt_mem_slice vtPad5_check (by simp [vtPad5T])
  have hx : σv (.n (2640 + 14 * t)) = gen ^ H.τ t := vt_ld hmem (vt_pw_reads t ht) (vt_dims I t ht)
  have h29 : H.τ t < 29 := I.hs.hτ29 t ht
  have hl : vtPadNames.length = 29 := by simp [vtPadNames]
  refine vsh_disp hx (by rw [hl]; exact h29) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtPadNames, List.getElem_map, List.getElem_range, List.map_cons, List.map_nil] at hc ⊢
  refine padding_weight_relIn h29 ?_ hc
  rw [vt_s8]
  exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) (I.hs.hτμ t ht)

theorem vt_por_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv porCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv porCall := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hl : plusOneRunNames.length = 34 := rfl
  have hm' : H.μ < plusOneRunNames.length := by rw [hl]; omega
  have e2767 : σv (.n 2767) = w 2767 := vt_alloc' (by unfold vtAllocVars; simp)
  refine vsh_disp vt_s9 hm' (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [List.map_cons, List.map_nil] at hc ⊢
  rw [← List.getD_eq_getElem _ "" hm'] at hc ⊢
  refine plus_one_run_relIn (by omega) ?_ ?_ hc
  · rw [e2767]
    exact ptr_own0 I.hw (j := 4) (by norm_num) (by decide) (le_of_eq rfl)
  · rw [vt_s8]
    exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) le_rfl

theorem vt_sh_up (I : VtIn H B w rd) {t : ℕ} (ht : t < 6)
    (h : VSH (coreProgram.Rel rd) rd σv (shCall t)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (shCall t) := by
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  have hμ : H.μ < 33 := I.hs.hμ33
  have hlen := vt_shLen I ht
  have e2769 : σv (.n 2769) = w 2769 := vt_alloc' (by unfold vtAllocVars; simp)
  have e2770 : σv (.n 2770) = w 2770 := vt_alloc' (by unfold vtAllocVars; simp)
  have e2767 : σv (.n 2767) = w 2767 := vt_alloc' (by unfold vtAllocVars; simp)
  -- the pointers, from `g^τ`
  have pz : ∀ v : E, v = gen ^ H.τ t →
      PtrIn (H.reg B) (σv (.n 8) * v) (H.μ - H.τ t) := fun v e ↦ by
    rw [vt_s8, e]
    exact ptr_lin (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) (by
      show H.τ t + (H.μ - H.τ t) ≤ H.μ; omega)
  have pz1 : ∀ v : E, v = gen ^ H.τ t →
      PtrIn (H.reg B) (σv (.n 2767) * v) (H.μ - H.τ t) := fun v e ↦ by
    rw [e2767, e]
    exact ptr_own I.hw (j := 4) (by norm_num) (by decide) (by
      show H.τ t + (H.μ - H.τ t) ≤ H.μ; omega)
  have pgs : ∀ v : E, v = gen ^ H.τ t →
      PtrIn (H.reg B) (σv (.n 13) * v) (H.μ - H.τ t) := fun v e ↦ by
    rw [vt_s13, e]
    exact ptr_lin (q := (B.sq, gSquaresList)) (by simp [VtHonest.linL]) (by
      show H.τ t + (H.μ - H.τ t) ≤ 34; omega)
  have peq : PtrIn (H.reg B) (w 2769 * gen ^ (288 * t)) (32 * ((H.μ - H.τ t + 3) / 4)) :=
    ptr_own I.hw (j := 5) (by norm_num) (by decide) (by
      show 288 * t + 32 * ((H.μ - H.τ t + 3) / 4) ≤ 1728; omega)
  have pgt : PtrIn (H.reg B) (w 2770 * gen ^ (144 * t)) (16 * ((H.μ - H.τ t + 3) / 4)) :=
    ptr_own I.hw (j := 6) (by norm_num) (by decide) (by
      show 144 * t + 16 * ((H.μ - H.τ t + 3) / 4) ≤ 864; omega)
  rcases Nat.eq_zero_or_pos t with rfl | h0
  · have mem : ∀ s ∈ vtSh0T, s ∈ vtPre := fun s hs ↦ vt_mem_slice vtSh0_check hs
    have e0 : σv (.n 2771) = gen ^ H.τ 0 :=
      vt_ld (mem _ (by simp [vtSh0T])) (by decide +kernel) (vt_dims I 0 (by norm_num))
    have e8 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n 2778) (.n 8) (.n 2771))) (by simp [vtSh0T])) (by norm_num) (by norm_num)
    have e9 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n 2779) (.n 2767) (.n 2771))) (by simp [vtSh0T])) (by norm_num)
      (by norm_num)
    have e10 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n 2780) (.n 13) (.n 2771))) (by simp [vtSh0T])) (by norm_num)
      (by norm_num)
    simp only [shCall, ↓reduceIte, vsh_call, List.map_cons, List.map_nil] at h ⊢
    rw [show vtShLen 0 = 2773 from rfl] at hlen
    rw [hlen] at h ⊢
    refine shared_selector_tables_relIn (by omega) ?_ ?_ ?_ ?_ ?_ h
    · rw [e2769]; simpa using peq
    · rw [e2770]; simpa using pgt
    · rw [e8]; exact pz _ e0
    · rw [e9]; exact pz1 _ e0
    · rw [e10]; exact pgs _ e0
  · have ht0 : t ≠ 0 := by omega
    simp only [shCall, ht0, ↓reduceIte, vsh_call, List.map_cons, List.map_nil] at h ⊢
    have chk := vtSh_check t ht h0
    set v := 2781 + 14 * (t - 1) with hv
    have mem : ∀ s ∈ vtShT v t, s ∈ vtPre := fun s hs ↦ vt_mem_slice chk hs
    have e0 : σv (.n v) = gen ^ H.τ t :=
      vt_ld (mem _ (by simp [vtShT, hv])) (vt_sh_reads t ht h0) (vt_dims I t ht)
    have c7 := vt_const (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.const (.n (v + 7)) (word (vtShC1.getD t 0) 0 0))) (by simp [vtShT]))
    have c9 := vt_const (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.const (.n (v + 9)) (word (vtShC2.getD t 0) 0 0))) (by simp [vtShT]))
    have e8 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n (v + 8)) (.n 2769) (.n (v + 7)))) (by simp [vtShT])) (by omega)
      (by omega)
    have e10 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n (v + 10)) (.n 2770) (.n (v + 9)))) (by simp [vtShT])) (by omega)
      (by omega)
    have e11 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n (v + 11)) (.n 8) (.n v))) (by simp [vtShT])) (by omega) (by omega)
    have e12 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n (v + 12)) (.n 2767) (.n v))) (by simp [vtShT])) (by omega) (by omega)
    have e13 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
      (mem (.atom (.mul (.n (v + 13)) (.n 13) (.n v))) (by simp [vtShT])) (by omega) (by omega)
    rw [show vtShLen t = v + 2 by simp [vtShLen, ht0, hv]] at hlen
    rw [hlen] at h ⊢
    refine shared_selector_tables_relIn (by omega) ?_ ?_ ?_ ?_ ?_ h
    · rw [e8, c7, vtShC1_word ht, e2769]; exact peq
    · rw [e10, c9, vtShC2_word ht, e2770]; exact pgt
    · rw [e11]; exact pz _ e0
    · rw [e12]; exact pz1 _ e0
    · rw [e13]; exact pgs _ e0

/-- Framework block `b`'s `g^κ`. -/
theorem vt_fw_kap (I : VtIn H B w rd) {b : ℕ} (hb : b < 3) :
    σv (.n (vtFwV.getD b 0)) = gen ^ H.κ b :=
  vt_ld (vt_mem_slice (vtFw_check b hb) (by simp [vtFwSelT])) (vtFw_reads b hb).1
    (vt_bk I b (by omega))

theorem vt_fw_kap_le (I : VtIn H B w rd) {b : ℕ} (hb : b < 3) : H.κ b ≤ H.μ := by
  obtain ⟨k0, k1, k2⟩ := vt_kap_fw (H := H)
  have h1 : H.lm ≤ H.μ := I.hs.hlmμ
  have h2 : 19 ≤ H.μ := I.hs.h19
  interval_cases b <;> omega

theorem vt_fw_up (I : VtIn H B w rd) {b : ℕ} (hb : b < 3)
    (h : VSH (coreProgram.Rel rd) rd σv (fwCall b)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (fwCall b) := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hκ := vt_fw_kap_le I hb
  have hwv : 2770 < vtFwV.getD b 0 := by interval_cases b <;> decide
  set v := vtFwV.getD b 0 with hv
  have mem : ∀ s ∈ vtFwSelT v b (vtFwPrev.getD b none), s ∈ vtPre :=
    fun s hs ↦ vt_mem_slice (vtFw_check b hb) hs
  have e0 := vt_fw_kap I hb
  rw [← hv] at e0
  have e8 : σv (.n (v + 8)) = gen ^ (H.μ - H.κ b) := by
    rw [vt_mulB (mem (.atom (.mul (.n 9) (.n (v + 8)) (.n v))) (by simp [vtFwSelT])) (by omega),
      vt_s9, e0, gen_div hκ]
  have e13 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 13)) (.n (v + 6)) (.n v))) (by simp [vtFwSelT])) (by omega)
    (by omega)
  have e14 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 14)) (.n 2767) (.n v))) (by simp [vtFwSelT])) (by omega) (by omega)
  have e15 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 15)) (.n 2732) (.n v))) (by simp [vtFwSelT])) (by omega) (by omega)
  have hjv : vtAllocVars.getD (8 + b) 0 = v + 6 := vtAllocVars_F b hb
  have a6 : σv (.n (v + 6)) = w (v + 6) := by
    rw [← hjv]; exact vt_alloc' (allocVars_mem (by omega))
  have a2767 : σv (.n 2767) = w 2767 := vt_alloc' (by unfold vtAllocVars; simp)
  have a2732 : σv (.n 2732) = w 2732 := vt_alloc' (by unfold vtAllocVars; simp)
  have hl : vtBsNames.length = 34 := by simp [vtBsNames]
  refine vsh_disp e8 (by rw [hl]; omega) (by rw [hl]; norm_num)
    (fun hc ↦ ?_) h
  simp only [← hv, vtBsNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine block_selector_relIn (by omega) ?_ ?_ ?_ hc
  · rw [e13, a6, e0]
    exact ptr_own I.hw (j := 8 + b) (by omega) hjv (by
      rw [sizes_bits H (by omega) (by omega)]; omega)
  · rw [e14, a2767, e0]
    exact ptr_own I.hw (j := 4) (by norm_num) (by decide) (by
      show H.κ b + (H.μ - H.κ b) ≤ H.μ; omega)
  · rw [e15, a2732, e0]
    exact ptr_own I.hw (j := 3) (by norm_num) (by decide) (by
      show H.κ b + (H.μ - H.κ b) ≤ 34; omega)

theorem vt_im_up (I : VtIn H B w rd) {b r : ℕ} (hb : b < 3)
    (h : VSH (coreProgram.Rel rd) rd σv (imCall b r)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (imCall b r) := by
  have hμ : H.μ < 33 := I.hs.hμ33
  have hκ := vt_fw_kap_le I hb
  have hl : vtImNames.length = 34 := by simp [vtImNames]
  refine vsh_disp (vt_fw_kap I hb) (by rw [hl]; omega) (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtImNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine index_mle_relIn (by omega) ?_ hc
  rw [vt_s8]
  exact ptr_lin0 (q := (B.zeta, H.point)) (by simp [VtHonest.linL]) hκ

theorem vt_sel_up (I : VtIn H B w rd) {x : ℕ × ℕ × ℕ × ℕ × Option ℕ} {j : ℕ}
    (hchk : tbStmtsEqb (vtSelT x.2.2.1 x.1 x.2.2.2.1 x.2.2.2.2)
      ((vtPre.drop x.2.1).take (vtSelT x.2.2.1 x.1 x.2.2.2.1 x.2.2.2.2).length) = true)
    (ht : x.2.2.2.1 < 6) (hw0 : 2770 < x.2.2.1)
    (hS : Atom.load (.n (x.2.2.1 + 8)) (.n 10) (x.2.2.2.1 + 1) ∉ vtSL)
    (hj : j < 110) (hjv : vtAllocVars.getD j 0 = x.2.2.1 + 6) (hsz : H.sizes.getD j 0 = 34)
    (h : VSH (coreProgram.Rel rd) rd σv (selCall x)) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv (selCall x) := by
  obtain ⟨b, pos, v, t, prev⟩ := x
  simp only at hchk ht hw0 hS hjv
  have hμ : H.μ < 33 := I.hs.hμ33
  have hτ : H.τ t ≤ H.μ := I.hs.hτμ t ht
  have mem : ∀ s ∈ vtSelT v b t prev, s ∈ vtPre := fun s hs ↦ vt_mem_slice hchk hs
  have e8 : σv (.n (v + 8)) = gen ^ H.τ t :=
    vt_ld (mem _ (by simp [vtSelT])) hS (vt_dims I t ht)
  have e9 := vt_mulF (H := H) (B := B) (w := w) (rd := rd)
    (mem (.atom (.mul (.n (v + 9)) (.n (v + 6)) (.n (v + 8)))) (by simp [vtSelT])) (by omega)
    (by omega)
  have a6 : σv (.n (v + 6)) = w (v + 6) := by
    rw [← hjv]; exact vt_alloc' (allocVars_mem (by omega))
  have e2769 : σv (.n 2769) = w 2769 := vt_alloc' (by unfold vtAllocVars; simp)
  have e2770 : σv (.n 2770) = w 2770 := vt_alloc' (by unfold vtAllocVars; simp)
  have eqt : σv (.n (if t = 0 then 2769 else v + 11)) = w 2769 * gen ^ (288 * t) := by
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp [e2769]
    · have ht0 : t ≠ 0 := by omega
      simp only [ht0, ↓reduceIte]
      rw [vt_mulF (mem (.atom (.mul (.n (v + 11)) (.n 2769) (.n (v + 10)))) (by simp [vtSelT, ht0]))
          (by omega) (by omega),
        vt_const (mem (.atom (.const (.n (v + 10)) (word (vtShC1.getD t 0) 0 0)))
          (by simp [vtSelT, ht0])), vtShC1_word ht, e2769]
  have egt : σv (.n (if t = 0 then 2770 else v + 13)) = w 2770 * gen ^ (144 * t) := by
    rcases Nat.eq_zero_or_pos t with rfl | h0
    · simp [e2770]
    · have ht0 : t ≠ 0 := by omega
      simp only [ht0, ↓reduceIte]
      rw [vt_mulF (mem (.atom (.mul (.n (v + 13)) (.n 2770) (.n (v + 12)))) (by simp [vtSelT, ht0]))
          (by omega) (by omega),
        vt_const (mem (.atom (.const (.n (v + 12)) (word (vtShC2.getD t 0) 0 0)))
          (by simp [vtSelT, ht0])), vtShC2_word ht, e2770]
  have hl : vtBstNames.length = 34 := by simp [vtBstNames]
  refine vsh_disp (vt_shLen I ht) (by rw [hl]; omega)
    (by rw [hl]; norm_num) (fun hc ↦ ?_) h
  simp only [vtBstNames, List.getElem_map, List.getElem_range, List.map_cons,
    List.map_nil] at hc ⊢
  refine block_selector_tab_relIn (by omega) ?_ ?_ ?_ hc
  · rw [e9, a6, e8]
    exact ptr_own I.hw hj hjv (by rw [hsz]; omega)
  · rw [eqt]
    exact ptr_own I.hw (j := 5) (by norm_num) (by decide) (by
      show 288 * t + 32 * btN (H.μ - H.τ t) ≤ 1728; simp only [btN]; omega)
  · rw [egt]
    exact ptr_own I.hw (j := 6) (by norm_num) (by decide) (by
      show 144 * t + 16 * btN (H.μ - H.τ t) ≤ 864; simp only [btN]; omega)

theorem vt_loop_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv loopCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv loopCall := by
  unfold loopCall at h ⊢
  refine ⟨h.1, fun hne ↦ ?_⟩
  have hc := h.2 hne
  have g5817 : GoodS rd vtSL w σv
      (fixNe (.atom (.hint (.witness "zc_tau_max" (.stack [.n 5817]))))) :=
    vt_goodS rfl (vt_mem_at 5152 _ (by decide +kernel))
  have e5817 : σv (.n 5817) = gen ^ H.n := by
    have := g5817 (.n 5817) (by simp)
    rw [this]; exact I.hw.w5817
  have e5920 : σv (.n 5920) = 1 + gen ^ H.n := by
    rw [vt_add (d := 5920) (x := 5919) (y := 5817) (vt_mem_at 5239 _ (by decide +kernel)),
      vt_const (vt_mem_at 5238 (.atom (.const (.n 5919) (word 1 0 0))) (by decide +kernel)),
      tb_word_one, e5817]
  have e5921 : σv (.n 5921) = gen ^ 0 := by
    rw [vt_const (vt_mem_at 5240 (.atom (.const (.n 5921) (word 1 0 0))) (by decide +kernel)),
      tb_word_one, pow_zero]
  have hK : 0 < H.n := by
    rcases Nat.eq_zero_or_pos H.n with h0 | h0
    · exact absurd (by rw [e5920, h0, pow_zero]; exact CharTwo.add_self_eq_zero 1) hne
    · exact h0
  have a5912 : σv (.n 5912) = w 5912 := vt_alloc' (by unfold vtAllocVars; simp)
  have a5915 : σv (.n 5915) = w 5915 := vt_alloc' (by unfold vtAllocVars; simp)
  simp only [List.map_cons, List.map_nil] at hc ⊢
  rw [e5921, e5817, a5912, a5915, vt_s18] at hc ⊢
  obtain ⟨d, hd⟩ := hc
  -- the rounds' cursor words
  have hR : TbReadsAt rd (w 5912)
      (zcRoundsW H.cap0 H.target (ofK (gpow B.cur) * gen ^ 5) H.xsR H.n) := by
    have := vt_own_reads I.hm I.hw (j := 107 + 0) (by norm_num)
    rw [ownW_getD_Z H B (k := 0) (by norm_num), show vtAllocVars.getD (107 + 0) 0 = 5912 by decide]
      at this
    exact this
  have hcur : ∀ k < H.n, ∀ c, LoadHolds rd (w 5912 * gen ^ (7 * k)) 5 c →
      PtrIn (H.reg B) c 3 := by
    intro k hk c hcl
    have r := zcRoundsW_reads (cap0_length H) hR k hk.le
    have hl5 := cap0_length H
    have l5 := tb_load_of r (k := 5) (by simp [zcRecW_len hl5])
    rw [zcRecW, List.getD_append_right _ _ _ _ (by simp [zcRec_len hl5]), zcRec_len hl5] at l5
    have e : c = ofK (gpow B.cur) * gen ^ (5 + 3 * k) := by
      rw [Option.some.inj (hcl.2.symm.trans l5.2)]
      simp [mul_assoc, pow_add]
    rw [e]
    have hcl' : 5 + 3 * k + 3 ≤ H.curW.length := by
      simp only [VtHonest.curW, List.length_append, I.ok.hx5, I.ok.hxR]; omega
    exact ptr_lin (q := (B.cur, H.curW)) (by simp [VtHonest.linL]) hcl'
  refine loop10_relIn hK ?_ ?_ ?_ hcur d 0 hK hd
  · exact ptr_own0 I.hw (j := 107) (by norm_num) (by decide) le_rfl
  · exact ptr_lin0 (q := (B.chi, H.chiW)) (by simp [VtHonest.linL]) (by
      simp [VtHonest.chiW, zcChis])
  · exact ptr_own0 I.hw (j := 108) (by norm_num) (by decide) le_rfl

theorem vt_epc_up (I : VtIn H B w rd) (h : VSH (coreProgram.Rel rd) rd σv epcCall) :
    VSH (coreProgram.RelIn rd (H.reg B)) rd σv epcCall := by
  have g5817 : GoodS rd vtSL w σv
      (fixNe (.atom (.hint (.witness "zc_tau_max" (.stack [.n 5817]))))) :=
    vt_goodS rfl (vt_mem_at 5152 _ (by decide +kernel))
  have e5817 : σv (.n 5817) = gen ^ H.n := by
    have := g5817 (.n 5817) (by simp)
    rw [this]; exact I.hw.w5817
  have a5936 : σv (.n 5936) = w 5936 := vt_alloc' (by unfold vtAllocVars; simp)
  have a2767 : σv (.n 2767) = w 2767 := vt_alloc' (by unfold vtAllocVars; simp)
  have hnμ := vt_nμ I
  have hμ : H.μ < 33 := I.hs.hμ33
  simp only [epcCall, vsh_call, List.map_cons, List.map_nil] at h ⊢
  rw [e5817] at h ⊢
  refine eq_prefix_chain_relIn (by omega) ?_ ?_ ?_ h
  · rw [a5936]; exact ptr_own0 I.hw (j := 109) (by norm_num) (by decide) le_rfl
  · rw [vt_s18]
    exact ptr_lin0 (q := (B.chi, H.chiW)) (by simp [VtHonest.linL]) (by
      simp [VtHonest.chiW, zcChis])
  · rw [a2767]; exact ptr_own0 I.hw (j := 4) (by norm_num) (by decide) hnμ

end

/-! ## Every statement -/

/-- **`verify_tables` is complete at the `RelIn` level**: under `vt_rel_complete`'s hypotheses,
every statement holds with its calls by relations loading from the caller's and the own buffers
only. -/
theorem vt_relIn_complete {H : VtHonest} (h : H.Ok) (hs : VtShape H) (B : VtBases) {w : ℕ → E}
    (hw : VtWOk H B w) {rd : Reader} (hlow : LowDefB 8 rd)
    (hm : MemLay rd (H.linL B ++ H.ownL B)) :
    ∀ s ∈ vtPre, VSH (coreProgram.RelIn rd (RegionL (H.linL B ++ H.ownL B))) rd
      (vtσ rd w (H.args B)) s := by
  have hV := (vt_rel_complete h hs B hw hlow hm).1
  have I : VtIn H B w rd := ⟨h, hs, hw, hm⟩
  intro s hs'
  have hv := hV s hs'
  cases hp : plainStB s
  · have hc := vt_call_mem hs' hp
    simp only [vtCalls, List.mem_append, List.mem_map, List.mem_range, List.mem_cons,
      List.not_mem_nil, or_false] at hc
    obtain ⟨hP, hC⟩ := vt_sel_shapes
    rcases hc with (((((⟨t, ht, rfl⟩ | rfl) | ⟨t, ht, rfl⟩) | (rfl | rfl | rfl | rfl | rfl)) |
      ⟨i, hi, rfl⟩) | ⟨i, hi, rfl⟩) | (rfl | rfl)
    · exact vt_pw_up I ht hv
    · exact vt_por_up I hv
    · exact vt_sh_up I ht hv
    · exact vt_fw_up I (by norm_num) hv
    · exact vt_fw_up I (by norm_num) hv
    · exact vt_im_up I (by norm_num) hv
    · exact vt_fw_up I (by norm_num) hv
    · exact vt_im_up I (by norm_num) hv
    · exact vt_sel_up I (x := vtPushSel.getD i default) (vtPushSel_check i (by rw [show vtPushSel.length = 51 from rfl]; exact hi))
        (hP i hi).1 (hP i hi).2 (vtPushSel_reads i hi).2.2.1 (j := 11 + i) (by omega)
        (vtAllocVars_P i hi) (sizes_bits H (by omega) (by omega)) hv
    · exact vt_sel_up I (x := vtCountSel.getD i default) (vtCountSel_check i (by rw [show vtCountSel.length = 45 from rfl]; exact hi))
        (hC i hi).1 (hC i hi).2 (vtCountSel_reads i hi).2.2.1 (j := 62 + i) (by omega)
        (vtAllocVars_C i hi) (sizes_bits H (by omega) (by omega)) hv
    · exact vt_loop_up I hv
    · exact vt_epc_up I hv
  · exact vsh_plain hp hv

end
end LeanVM.Guest.B1.Tables
