/-
  LeanVM.Guest.B1.Tables.VtC.AGlue

  What the honest valuation's equations give between `verify_tables`' ranges: the sponge after
  the framework words, `ξ`'s powers, the pull side's selectors.
-/

module

public import LeanVM.Guest.B1.Tables.VtC.ZSetup
public import LeanVM.Guest.B1.Tables.VtC.FFinal
public import LeanVM.Guest.B1.Tables.Vt.Fresh
public import LeanVM.Guest.B1.Tables.VtC.FData

/-!
# Between the ranges

`pack_good`: an `fs_pack` template whose hint is the honest one (the word's limbs) packs the
word's two rate cells, both canonical. `vt_fresh_good`: the sponge after the five framework words
is the five capacity cells the first permutation writes and the last word waiting, its rate cells
`σ4509`, `σ4511`, all canonical. `vt_xi_good`: `ξ`'s powers. `vt_pull_good`: the pull side's
selectors are the push side's.
-/

namespace LeanVM.Guest.B1.Tables

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Fwd

@[expose] public section

/-- **An honest `fs_pack`** packs the word's rate cells, canonical. -/
theorem pack_good {σ : Val} {x : V} {b t : ℕ}
    (hl : σ (.n (b + 2)) = limbAt (σ x) 2) (h3 : σ (.n (b + 3)) = word t 0 0)
    (h4 : σ (.n (b + 4)) = word 0 0 1)
    (h5 : σ (.n (b + 5)) = σ (.n (b + 4)) * σ (.n (b + 2)))
    (h6 : σ (.n (b + 6)) = σ x + σ (.n (b + 5))) (h7 : σ (.n (b + 7)) = word 0 t 0)
    (h8 : σ (.n (b + 8)) = σ (.n (b + 2)) + σ (.n (b + 7))) :
    σ (.n (b + 6)) = (Keccak.scalarCells (σ x) t).1 ∧
      σ (.n (b + 8)) = (Keccak.scalarCells (σ x) t).2 ∧
      IsCanonical128 (σ (.n (b + 6))) ∧ IsCanonical128 (σ (.n (b + 8))) := by
  have hl' : σ (.n (b + 2)) = ofK ((σ x).limb 2) := by rw [hl]; rfl
  have hok : FsPackOk σ x b t := ⟨h3, by rw [hl']; exact ofK_isInK _,
    by rw [h3, word_eOfNat]; exact eOfNat_isInK _, h4, h5, h6, h7, h8⟩
  have hcan : IsCanonical128 (σ (.n (b + 6))) := by
    rw [h6, h5, h4, hl', word_yy, top_pin_eq]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl
  have e := Prod.ext_iff.mp (fsPackT_cells hok hcan)
  obtain ⟨c1, c2⟩ := scalarCells_canonical (σ x) t
  have e1 : σ (.n (b + 6)) = (Keccak.scalarCells (σ x) t).1 := e.1
  have e2 : σ (.n (b + 8)) = (Keccak.scalarCells (σ x) t).2 := e.2
  exact ⟨e1, e2, by rw [e1]; exact c1, by rw [e2]; exact c2⟩

section
variable {rd : Reader} {w : ℕ → E} {args : List E}

/-- **A framework word's `fs_next`, honestly**: its two rate cells, canonical. -/
theorem vt_next_good (hl : args.length = 22) (cur : V) (pos k b : ℕ)
    (heq : tbStmtsEqb (fsNextT cur k b) ((vtPre.drop pos).take (fsNextT cur k b).length) =
      true) :
    vtσ rd w args (.n (b + 7)) = (Keccak.scalarCells (vtσ rd w args (.n b)) dsObserve).1 ∧
      vtσ rd w args (.n (b + 9)) = (Keccak.scalarCells (vtσ rd w args (.n b)) dsObserve).2 ∧
      IsCanonical128 (vtσ rd w args (.n (b + 7))) ∧ IsCanonical128 (vtσ rd w args (.n (b + 9))) := by
  have g := vt_goodL (rd := rd) (w := w) hl pos _ heq
  generalize vtσ rd w args = σ at g ⊢
  simp only [fsNextT, fsPackT, GoodL, GoodS, fixNe, Good, List.length_cons, List.length_nil,
    and_true] at g
  obtain ⟨-, gl, g3, -, g4, g5, g6, g7, g8⟩ := g
  have hl2 : σ (.n (b + 1 + 2)) = limbAt (σ (.n b)) 2 := gl 2 (by norm_num)
  have h5 : σ (.n (b + 1 + 5)) = σ (.n (b + 1 + 4)) * σ (.n (b + 1 + 2)) := by
    split_ifs at g5 with hc
    · exact g5
    · exact absurd ⟨by omega, by omega⟩ hc
  have := pack_good (σ := σ) (x := .n b) (b := b + 1) (t := dsObserve) hl2 g3 g4 h5 g6 g7 g8
  rwa [show b + 1 + 6 = b + 7 by omega, show b + 1 + 8 = b + 9 by omega] at this

theorem canon_zero' : IsCanonical128 (0 : E) := by
  rw [zero_eq_ofLimbs]; exact (isCanonical128_ofLimbs_iff _ _ _).mpr rfl

theorem good_keccak_cells {rd : Reader} {S : List Atom} {w : ℕ → E} {σ : Val} {ins : List V}
    {b : ℕ} (h : Good rd S w σ (.keccak ins (lyOuts b) false false)) :
    ∀ k (hk : k < 13), σ (.n (b + k)) = cellsOfState (permOf (ins.map σ)) false ⟨k, hk⟩ := by
  obtain ⟨-, -, hc⟩ := h
  intro k hk
  have := hc ⟨k, hk⟩
  simpa [cells13, lyOuts, List.getD_eq_getElem?_getD, hk, permOf] using this

set_option maxRecDepth 10000 in
/-- **The sponge after the framework words**, honestly: the first permutation's capacity and the
last word waiting, its rate cells canonical, the capacity canonical. -/
theorem vt_fresh_good (hl : args.length = 22) :
    vtFreshFs (vtσ rd w args) = ⟨(lyCap 4489).map (vtσ rd w args),
        [(vtσ rd w args (.n 4502), dsObserve)]⟩ ∧
      rateOf [(vtσ rd w args (.n 4502), dsObserve)] =
        [vtσ rd w args (.n 4509), vtσ rd w args (.n 4511), 0, 0, 0, 0, 0, 0] ∧
      AllCanonical ([vtσ rd w args (.n 4509), vtσ rd w args (.n 4511), 0, 0, 0, 0, 0, 0] ++
        (lyCap 4489).map (vtσ rd w args)) := by
  have p0 := vt_next_good (rd := rd) (w := w) hl (.n 5) 2462 0 2914 (by rw [vtPre_drop]; decide +kernel)
  have p1 := vt_next_good (rd := rd) (w := w) hl (.n 5) 2476 1 2927 (by rw [vtPre_drop]; decide +kernel)
  have p2 := vt_next_good (rd := rd) (w := w) hl (.n 5) 2490 2 2940 (by rw [vtPre_drop]; decide +kernel)
  have p3 := vt_next_good (rd := rd) (w := w) hl (.n 5) 3938 3 4444 (by rw [vtPre_drop]; decide +kernel)
  have p4 := vt_next_good (rd := rd) (w := w) hl (.n 5) 3983 4 4502 (by rw [vtPre_drop]; decide +kernel)
  have gc := vt_goodL (rd := rd) (w := w) hl 0 [.atom (.copy (.n 22) (.n 0)),
    .atom (.copy (.n 23) (.n 1)), .atom (.copy (.n 24) (.n 2)), .atom (.copy (.n 25) (.n 3)),
    .atom (.copy (.n 26) (.n 4))] (by rw [vtPre_drop]; decide +kernel)
  have gk := (vt_goodL (rd := rd) (w := w) hl 3982 [.atom (.keccak [.n 2921, .n 2923, .n 2934,
    .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22, .n 23, .n 24, .n 25, .n 26] (lyOuts 4489)
    false false)] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at p0 p1 p2 p3 p4 gc gk ⊢
  simp only [GoodL, GoodS, fixNe, Good, and_true] at gc
  obtain ⟨c22, c23, c24, c25, c26⟩ := gc
  have hk := good_keccak_cells (rd := rd) (S := vtSL) (w := w) gk
  simp only [Nat.reduceAdd] at p0 p1 p2 p3 p4
  set S4 : Fs := ⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], [(σ (.n 2914), dsObserve),
    (σ (.n 2927), dsObserve), (σ (.n 2940), dsObserve), (σ (.n 4444), dsObserve)]⟩ with hS4d
  have hS4 : (⟨[σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4)], []⟩ : Fs).absorbAll
      [σ (.n 2914), σ (.n 2927), σ (.n 2940), σ (.n 4444)] dsObserve = S4 := by
    rw [absorbAll_short _ _ _ (by simp)]; rfl
  have hin1 : ([.n 2921, .n 2923, .n 2934, .n 2936, .n 2947, .n 2949, .n 4451, .n 4453, .n 22,
      .n 23, .n 24, .n 25, .n 26] : List V).map σ = rateOf S4.pend ++ S4.cap := by
    rw [rateOf_eq_cells _ (by simp [hS4d])]
    simp only [hS4d, List.map_cons, List.map_nil, pendCells, List.flatMap_cons, List.flatMap_nil,
      List.length_cons, List.length_nil, List.cons_append, List.nil_append, List.append_nil,
      p0.1, p0.2.1, p1.1, p1.2.1, p2.1, p2.2.1, p3.1, p3.2.1, c22, c23, c24, c25, c26]
    rfl
  rw [hin1] at hk
  have hcap : (lyCap 4489).map σ = capOf S4.perm := by
    have e : (lyCap 4489).map σ =
        [σ (.n 4497), σ (.n 4498), σ (.n 4499), σ (.n 4500), σ (.n 4501)] := rfl
    have h8 : σ (.n 4497) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 8 :=
      hk 8 (by norm_num)
    have h9 : σ (.n 4498) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 9 :=
      hk 9 (by norm_num)
    have h10 : σ (.n 4499) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 10 :=
      hk 10 (by norm_num)
    have h11 : σ (.n 4500) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 11 :=
      hk 11 (by norm_num)
    have h12 : σ (.n 4501) = cellsOfState (permOf (rateOf S4.pend ++ S4.cap)) false 12 :=
      hk 12 (by norm_num)
    rw [e, h8, h9, h10, h11, h12]
    rfl
  have hS5 : vtFreshFs σ = ⟨(lyCap 4489).map σ, [(σ (.n 4502), dsObserve)]⟩ := by
    have hsplit : vtFreshWords σ = [σ (.n 2914), σ (.n 2927), σ (.n 2940), σ (.n 4444)] ++
        [σ (.n 4502)] := rfl
    rw [vtFreshFs, hsplit, vt_absorbAll_append, hS4, hcap]
    simp [Fs.absorbAll, Fs.absorb, rateScalars, hS4d]
  have hr : rateOf [(σ (.n 4502), dsObserve)] =
      [σ (.n 4509), σ (.n 4511), 0, 0, 0, 0, 0, 0] := by
    rw [rateOf_eq_cells _ (by simp)]
    simp [pendCells, p4.1, p4.2.1]
  refine ⟨hS5, hr, ?_⟩
  intro c hc
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false] at hc
  rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | hc
  · exact p4.2.2.1
  · exact p4.2.2.2
  all_goals first | exact canon_zero' | skip
  obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hc
  simp only [lyCap, List.mem_map, List.mem_range] at hv
  obtain ⟨k, hk5, rfl⟩ := hv
  have := hk (8 + k) (by omega)
  rw [show 4489 + 8 + k = 4489 + (8 + k) by omega, this]
  exact canon_cellsOfState _ _ _

set_option maxRecDepth 10000 in
/-- **The pull side's selectors are the push side's**, honestly. -/
theorem vt_pull_good (hl : args.length = 22) : VtPullSelsH (vtσ rd w args) := by
  have g4049 := (vt_goodL (rd := rd) (w := w) hl 4049 [.atom (.copy (.n 4569) (.n 3051))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4054 := (vt_goodL (rd := rd) (w := w) hl 4054 [.atom (.copy (.n 4576) (.n 3066))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4059 := (vt_goodL (rd := rd) (w := w) hl 4059 [.atom (.copy (.n 4583) (.n 3081))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4064 := (vt_goodL (rd := rd) (w := w) hl 4064 [.atom (.copy (.n 4590) (.n 3096))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4069 := (vt_goodL (rd := rd) (w := w) hl 4069 [.atom (.copy (.n 4597) (.n 3111))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4074 := (vt_goodL (rd := rd) (w := w) hl 4074 [.atom (.copy (.n 4604) (.n 3130))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4079 := (vt_goodL (rd := rd) (w := w) hl 4079 [.atom (.copy (.n 4611) (.n 3149))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4084 := (vt_goodL (rd := rd) (w := w) hl 4084 [.atom (.copy (.n 4618) (.n 3168))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4089 := (vt_goodL (rd := rd) (w := w) hl 4089 [.atom (.copy (.n 4625) (.n 3187))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4094 := (vt_goodL (rd := rd) (w := w) hl 4094 [.atom (.copy (.n 4632) (.n 3206))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4099 := (vt_goodL (rd := rd) (w := w) hl 4099 [.atom (.copy (.n 4639) (.n 3225))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4104 := (vt_goodL (rd := rd) (w := w) hl 4104 [.atom (.copy (.n 4646) (.n 3244))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4109 := (vt_goodL (rd := rd) (w := w) hl 4109 [.atom (.copy (.n 4653) (.n 3263))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4114 := (vt_goodL (rd := rd) (w := w) hl 4114 [.atom (.copy (.n 4660) (.n 3282))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4119 := (vt_goodL (rd := rd) (w := w) hl 4119 [.atom (.copy (.n 4667) (.n 3301))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4124 := (vt_goodL (rd := rd) (w := w) hl 4124 [.atom (.copy (.n 4674) (.n 3320))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4129 := (vt_goodL (rd := rd) (w := w) hl 4129 [.atom (.copy (.n 4681) (.n 3339))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4134 := (vt_goodL (rd := rd) (w := w) hl 4134 [.atom (.copy (.n 4688) (.n 3358))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4139 := (vt_goodL (rd := rd) (w := w) hl 4139 [.atom (.copy (.n 4695) (.n 3377))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4144 := (vt_goodL (rd := rd) (w := w) hl 4144 [.atom (.copy (.n 4702) (.n 3396))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4149 := (vt_goodL (rd := rd) (w := w) hl 4149 [.atom (.copy (.n 4709) (.n 3415))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4154 := (vt_goodL (rd := rd) (w := w) hl 4154 [.atom (.copy (.n 4716) (.n 3434))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4159 := (vt_goodL (rd := rd) (w := w) hl 4159 [.atom (.copy (.n 4723) (.n 3453))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4164 := (vt_goodL (rd := rd) (w := w) hl 4164 [.atom (.copy (.n 4730) (.n 3472))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4169 := (vt_goodL (rd := rd) (w := w) hl 4169 [.atom (.copy (.n 4737) (.n 3491))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4174 := (vt_goodL (rd := rd) (w := w) hl 4174 [.atom (.copy (.n 4744) (.n 3510))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4179 := (vt_goodL (rd := rd) (w := w) hl 4179 [.atom (.copy (.n 4751) (.n 3529))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4184 := (vt_goodL (rd := rd) (w := w) hl 4184 [.atom (.copy (.n 4758) (.n 3548))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4189 := (vt_goodL (rd := rd) (w := w) hl 4189 [.atom (.copy (.n 4765) (.n 3567))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4194 := (vt_goodL (rd := rd) (w := w) hl 4194 [.atom (.copy (.n 4772) (.n 3586))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4199 := (vt_goodL (rd := rd) (w := w) hl 4199 [.atom (.copy (.n 4779) (.n 3605))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4204 := (vt_goodL (rd := rd) (w := w) hl 4204 [.atom (.copy (.n 4786) (.n 3624))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4209 := (vt_goodL (rd := rd) (w := w) hl 4209 [.atom (.copy (.n 4793) (.n 3643))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4214 := (vt_goodL (rd := rd) (w := w) hl 4214 [.atom (.copy (.n 4800) (.n 3662))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4219 := (vt_goodL (rd := rd) (w := w) hl 4219 [.atom (.copy (.n 4807) (.n 3681))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4224 := (vt_goodL (rd := rd) (w := w) hl 4224 [.atom (.copy (.n 4814) (.n 3700))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4229 := (vt_goodL (rd := rd) (w := w) hl 4229 [.atom (.copy (.n 4821) (.n 3719))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4234 := (vt_goodL (rd := rd) (w := w) hl 4234 [.atom (.copy (.n 4828) (.n 3738))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4239 := (vt_goodL (rd := rd) (w := w) hl 4239 [.atom (.copy (.n 4835) (.n 3757))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4244 := (vt_goodL (rd := rd) (w := w) hl 4244 [.atom (.copy (.n 4842) (.n 3776))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4249 := (vt_goodL (rd := rd) (w := w) hl 4249 [.atom (.copy (.n 4849) (.n 3795))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4254 := (vt_goodL (rd := rd) (w := w) hl 4254 [.atom (.copy (.n 4856) (.n 3814))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4259 := (vt_goodL (rd := rd) (w := w) hl 4259 [.atom (.copy (.n 4863) (.n 3833))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4264 := (vt_goodL (rd := rd) (w := w) hl 4264 [.atom (.copy (.n 4870) (.n 3852))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4269 := (vt_goodL (rd := rd) (w := w) hl 4269 [.atom (.copy (.n 4877) (.n 3871))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4274 := (vt_goodL (rd := rd) (w := w) hl 4274 [.atom (.copy (.n 4884) (.n 3890))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4279 := (vt_goodL (rd := rd) (w := w) hl 4279 [.atom (.copy (.n 4891) (.n 3909))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4284 := (vt_goodL (rd := rd) (w := w) hl 4284 [.atom (.copy (.n 4898) (.n 3928))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4289 := (vt_goodL (rd := rd) (w := w) hl 4289 [.atom (.copy (.n 4905) (.n 3947))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4294 := (vt_goodL (rd := rd) (w := w) hl 4294 [.atom (.copy (.n 4912) (.n 3966))] (by rw [vtPre_drop]; decide +kernel)).1
  have g4299 := (vt_goodL (rd := rd) (w := w) hl 4299 [.atom (.copy (.n 4919) (.n 3985))] (by rw [vtPre_drop]; decide +kernel)).1
  generalize vtσ rd w args = σ at g4049 g4054 g4059 g4064 g4069 g4074 g4079 g4084 g4089 g4094 g4099 g4104 g4109 g4114 g4119 g4124 g4129 g4134 g4139 g4144 g4149 g4154 g4159 g4164 g4169 g4174 g4179 g4184 g4189 g4194 g4199 g4204 g4209 g4214 g4219 g4224 g4229 g4234 g4239 g4244 g4249 g4254 g4259 g4264 g4269 g4274 g4279 g4284 g4289 g4294 g4299 ⊢
  simp only [GoodS, fixNe, Good] at g4049 g4054 g4059 g4064 g4069 g4074 g4079 g4084 g4089 g4094 g4099 g4104 g4109 g4114 g4119 g4124 g4129 g4134 g4139 g4144 g4149 g4154 g4159 g4164 g4169 g4174 g4179 g4184 g4189 g4194 g4199 g4204 g4209 g4214 g4219 g4224 g4229 g4234 g4239 g4244 g4249 g4254 g4259 g4264 g4269 g4274 g4279 g4284 g4289 g4294 g4299
  simp only [VtPullSelsH, g4049, g4054, g4059, g4064, g4069, g4074, g4079, g4084, g4089, g4094, g4099, g4104, g4109, g4114, g4119, g4124, g4129, g4134, g4139, g4144, g4149, g4154, g4159, g4164, g4169, g4174, g4179, g4184, g4189, g4194, g4199, g4204, g4209, g4214, g4219, g4224, g4229, g4234, g4239, g4244, g4249, g4254, g4259, g4264, g4269, g4274, g4279, g4284, g4289, g4294, g4299, and_self]

/-- **`ξ`'s powers**, honestly. -/
theorem vt_xi_good (hl : args.length = 22) :
    vtσ rd w args (.n 5896) = 1 ∧ vtσ rd w args (.n 5897) = vtσ rd w args (.n 5895) ∧
      vtσ rd w args (.n 5898) = vtσ rd w args (.n 5895) ^ 2 ∧
      vtσ rd w args (.n 5899) = vtσ rd w args (.n 5895) ^ 3 ∧
      vtσ rd w args (.n 5900) = vtσ rd w args (.n 5895) ^ 4 := by
  have g := vt_goodL (rd := rd) (w := w) hl 5207 [.atom (.const (.n 5896) (word 1 0 0)),
    .atom (.mul (.n 5897) (.n 5896) (.n 5895)), .atom (.mul (.n 5898) (.n 5897) (.n 5895)),
    .atom (.mul (.n 5899) (.n 5898) (.n 5895)), .atom (.mul (.n 5900) (.n 5899) (.n 5895))]
    (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at g ⊢
  simp only [GoodL, GoodS, fixNe, Good, Nat.reduceLT, and_self, ↓reduceIte, and_true] at g
  obtain ⟨g0, g1, g2, g3, g4⟩ := g
  rw [tb_word_one] at g0
  refine ⟨g0, ?_, ?_, ?_, ?_⟩
  · rw [g1, g0, one_mul]
  · rw [g2, g1, g0, one_mul, sq]
  · rw [g3, g2, g1, g0, one_mul]; ring
  · rw [g4, g3, g2, g1, g0, one_mul]; ring

theorem vtPermCap_39 : vtPermCap 39 = [.n 9404, .n 9405, .n 9406, .n 9407, .n 9408] := by
  decide +kernel

set_option maxRecDepth 10000 in
/-- **The sponge after the evaluations**, from the evaluations' sponge facts: the last
permutation's capacity and the last evaluation waiting, its rate cells canonical. -/
theorem vt_evalFs_good (hl : args.length = 22)
    (hF : ∀ j < 39, (⟨vtCapV (vtσ rd w args) 0, []⟩ : Fs).absorbAll
        ((vtEvs (vtσ rd w args)).take (4 * (j + 1))) dsObserve =
      ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩ ∧
      vtCapV (vtσ rd w args) (j + 1) = capOf (Fs.perm ⟨vtCapV (vtσ rd w args) j,
        (((vtEvs (vtσ rd w args)).drop (4 * j)).take 4).map (·, dsObserve)⟩)) :
    vtEvalFs (vtσ rd w args) = ⟨vtCapV (vtσ rd w args) 39,
        [(vtσ rd w args (.n 9409), dsObserve)]⟩ ∧
      rateOf (vtEvalFs (vtσ rd w args)).pend =
        [vtσ rd w args (.n 9416), vtσ rd w args (.n 9418), 0, 0, 0, 0, 0, 0] ∧
      (vtEvalFs (vtσ rd w args)).cap = [vtσ rd w args (.n 9404), vtσ rd w args (.n 9405),
        vtσ rd w args (.n 9406), vtσ rd w args (.n 9407), vtσ rd w args (.n 9408)] ∧
      AllCanonical (rateOf (vtEvalFs (vtσ rd w args)).pend ++ (vtEvalFs (vtσ rd w args)).cap) := by
  have p := vt_next_good (rd := rd) (w := w) hl (.n 5932) 8418 156 9409 (by rw [vtPre_drop]; decide +kernel)
  generalize vtσ rd w args = σ at hF p ⊢
  have he : vtEvB 156 = 9409 := by decide
  obtain ⟨h38, hp38⟩ := hF 38 (by norm_num)
  have hr : vtEvs σ = (List.range 156).map (fun k ↦ σ (.n (vtEvB k))) ++
      [σ (.n (vtEvB 156))] := by
    show (List.range (156 + 1)).map _ = _
    rw [List.range_succ, List.map_append, List.map_singleton]
  have ht : (vtEvs σ).take (4 * (38 + 1)) = (List.range 156).map fun k ↦ σ (.n (vtEvB k)) := by
    rw [hr, List.take_left' (by simp)]
  rw [ht] at h38
  have hS : vtEvalFs σ = ⟨vtCapV σ 39, [(σ (.n 9409), dsObserve)]⟩ := by
    rw [vtEvalFs, hr, fs_absorbAll_append, h38, tb_absorbAll_full' _ (by simp [vtEvs]) _
      (by simp) (by simp), ← hp38, he]
    rfl
  have hcap : vtCapV σ 39 = [σ (.n 9404), σ (.n 9405), σ (.n 9406), σ (.n 9407), σ (.n 9408)] := by
    simp [vtCapV, vtPermCap_39]
  have hrate : rateOf [(σ (.n 9409), dsObserve)] = [σ (.n 9416), σ (.n 9418), 0, 0, 0, 0, 0, 0] := by
    rw [rateOf_eq_cells _ (by simp)]
    simp [pendCells, p.1, p.2.1]
  refine ⟨hS, by rw [hS]; exact hrate, by rw [hS]; exact hcap, ?_⟩
  rw [hS]
  intro c hc
  simp only [List.mem_append] at hc
  rcases hc with hc | hc
  · rw [hrate] at hc
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact p.2.2.1
    · exact p.2.2.2
    all_goals exact canon_zero'
  · rw [hp38] at hc
    simp only [capOf, List.mem_cons, List.mem_nil_iff, or_false] at hc
    rcases hc with rfl | rfl | rfl | rfl | rfl <;> exact canon_cellsOfState _ _ _

theorem vt_evLoad_at : ∀ k < 157, tbStmtsEqb [.atom (.load (.n (vtEvB k)) (.n 5932) k)]
    ((vtPre.drop (vtEvalData.getD k (0, 0, 0)).1).take 1) = true := by
      simp only [vtPre_drop]; decide +kernel

theorem vt_evLoad_read : ∀ k < 157, Atom.load (.n (vtEvB k)) (.n 5932) k ∉ vtSL :=
  fun _ _ ↦ not_mem_vtSL vtF_noStore.2.1 _ _

/-- **The evaluations are the words at the cursor.** -/
theorem vt_evs_good (hl : args.length = 22) {evs : List E}
    (hm : TbReadsAt rd (vtσ rd w args (.n 5932)) evs) (hlen : evs.length = 157) :
    vtEvs (vtσ rd w args) = evs := by
  apply List.ext_getElem (by simp [vtEvs, hlen])
  intro k h1 h2
  have hk : k < 157 := by simpa [vtEvs] using h1
  simp only [vtEvs, List.getElem_map, List.getElem_range]
  rw [vt_read hl _ (vt_evLoad_at k hk) (vt_evLoad_read k hk), rdAt, (hm k h2).2]
  rfl

end

end
end LeanVM.Guest.B1.Tables
