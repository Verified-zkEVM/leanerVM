/-
  LeanVM.Guest.B1.Comp.Tables.FlockAtL

  `verify_flock` placed over a completeness model, its tree loading the stream words it reads.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.FlockAtC
public import LeanVM.Guest.B1.Comp.Tables.ShapesWST
public import LeanVM.Guest.B1.Comp.VerifySub.PlacedEq

/-!
# `verify_flock`, placed, loading what it reads

`verify_flock` reads the stream `xs` at `g^c`: its body loads the first `78` words (round 1 and
the first seven rounds) through the cursor and the last `82` (the lincheck and the slices) past
the rounds; `__loop82` loads rounds `7 ..< τ + 8`, two words each, through the cursors its rows
hold (`l82_loads`, over every valid tree, from `loopStdS_loads`). `verify_flock_completeAtWCL`:
`CompleteFlockAtWCL`, `verify_flock_completeAtWC`'s proof with `completeAtS_straightWT`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## `mul_range` loops' loads -/

section
variable {S : BlakeSem}

/-- **A `mul_range` loop ending in the standard step loads what its iterations load**
(`loopS_loads` at `loopTail`'s step). -/
theorem loopStdS_loads {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre0 : List Stmt} {P : List V} {a b c a' d : ℕ} (hpar : fn.params = .n 0 :: .n 1 :: P)
    (hb : fn.body = (pre0 ++ loopTail a b c a' d) ++ [.callIf (.n c) f (.n d :: .n 1 :: P), .ret []])
    (hst : (pre0 ++ loopTail a b c a' d).all Main.Stmt.straight = true)
    (rd : Reader) {m : ℕ} (hm : m < 2 ^ 63) (rest : List E) (A : ℕ → K × E → Prop)
    (hstep : ∀ σ j, j < m → fn.params.map σ = gen ^ j :: gen ^ m :: rest →
      (∀ e ∈ (pre0 ++ loopTail a b c a' d).flatMap (Main.slEvs σ), e.HoldsB S rd σ) →
      ∀ kids, Tree.KidsValidB S coreProgram rd σ
        (((pre0 ++ loopTail a b c a' d).filterMap Main.Stmt.callS).map (Main.mkCall σ)) kids →
        ∀ q, A j q → q ∈ evLoadEqns σ ((pre0 ++ loopTail a b c a' d).flatMap (Main.slEvs σ)) ∨
          q ∈ Tree.loadEqnsKids coreProgram kids)
    {j : ℕ} {t : Tree} {rets : List E} (hj : j < m) (hn : t.name = f)
    (hv : t.ValidB S coreProgram rd (gen ^ j :: gen ^ m :: rest) rets) :
    ∀ j', j ≤ j' → j' < m → ∀ q, A j' q → q ∈ t.loadEqns coreProgram := by
  refine loopS_loads hf hb hst rd m hm rest A (fun σ j' hj' hp hes => ?_) (m - j) j t rets
    (by omega) hj hn hv
  rw [hpar] at hp
  simp only [List.map_cons, List.cons.injEq] at hp
  obtain ⟨h0, h1, hr⟩ := hp
  have mem : ∀ s ∈ loopTail a b c a' d, s ∈ pre0 ++ loopTail a b c a' d :=
    fun s hs => List.mem_append_right _ hs
  have a1 := vtcS_atom hes (mem (.atom (.const (.n a) (word 2 0 0))) (by simp [loopTail]))
  have a2 := vtcS_atom hes (mem (.atom (.mul (.n b) (.n 0) (.n a))) (by simp [loopTail]))
  have a3 := vtcS_atom hes (mem (.atom (.add (.n c) (.n b) (.n 1))) (by simp [loopTail]))
  have a4 := vtcS_atom hes (mem (.atom (.const (.n a') (word 2 0 0))) (by simp [loopTail]))
  have a5 := vtcS_atom hes (mem (.atom (.mul (.n d) (.n 0) (.n a'))) (by simp [loopTail]))
  simp only [Atom.HoldsB, word_gen] at a1 a2 a3 a4 a5
  refine ⟨by rw [a3, a2, a1, h0, h1], by simp [a5, a4, h0, h1, hr], fun kids hk q hq => ?_⟩
  exact hstep σ j' hj' (by rw [hpar]; simp [h0, h1, hr]) hes kids hk q hq

end

/-! ## `__loop82`'s loads -/

/-- **`__loop82`'s tree loads rounds `7 ..< τ + 8`**: words `64 + 2j`, `64 + 2j + 1` of the stream
at `g^c`. -/
def L82Loads (τ c : ℕ) (xs : List E) (t : Tree) : Prop :=
  ∀ j, 7 ≤ j → j < τ + 8 →
    (Parameters.gpow (c + (64 + 2 * j)), xs.getD (64 + 2 * j) 0) ∈ t.loadEqns coreProgram ∧
      (Parameters.gpow (c + (64 + 2 * j + 1)), xs.getD (64 + 2 * j + 1) 0) ∈ t.loadEqns coreProgram

theorem l82_mem {i : ℕ} {s : Stmt} (h : (l82Body.take 64)[i]? = some s) :
    s ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 :=
  List.mem_append_left _ (by rw [core141_body]; exact List.mem_of_getElem? h)

theorem l82_loadAtoms :
    Stmt.atom (.mul (.n 5) (.n 0) (.n 0)) ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 ∧
    Stmt.atom (.mul (.n 6) (.n 5) (.n 5)) ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 ∧
    Stmt.atom (.mul (.n 7) (.n 2) (.n 6)) ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 ∧
    Stmt.atom (.load (.n 12) (.n 7) 2) ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 ∧
    Stmt.atom (.load (.n 13) (.n 12) 0) ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 ∧
    Stmt.atom (.load (.n 28) (.n 12) 1) ∈ (Fn.body Data.core141).take 64 ++ loopTail 68 69 70 71 72 :=
  ⟨l82_mem (i := 0) rfl, l82_mem (i := 1) rfl, l82_mem (i := 2) rfl, l82_mem (i := 7) rfl,
    l82_mem (i := 8) rfl, l82_mem (i := 21) rfl⟩

/-- **Every valid tree of `__loop82` from `g^7` to `g^(τ+8)` loads its rounds' words**, on a memory
holding the stream at `g^c` and the rounds' cursors in its rows. -/
theorem l82_loads {S : BlakeSem} {rd : Reader} {τ c : ℕ} {xs : List E} {rnd zr chis : E}
    (hτ : τ < 29) (hlen : xs.length = flLen τ) (hx : ReadsAt rd (ofK (Parameters.gpow c)) xs)
    (hrow : ∀ j, 7 ≤ j → j ≤ τ + 8 →
      LoadHolds rd rnd (4 * j + 2) (ofK (Parameters.gpow c) * gen ^ (64 + 2 * j)))
    {t : Tree} {rets : List E} (hn : t.name = "__loop82")
    (hv : t.ValidB S coreProgram rd [gen ^ 7, gen ^ (τ + 8), rnd, zr, chis] rets) :
    L82Loads τ c xs t := by
  obtain ⟨m5, m6, m7, l12, l13, l28⟩ := l82_loadAtoms
  have h := loopStdS_loads (S := S) find_loop82 rfl l82_shape l82_ck.1 rd (m := τ + 8) (by omega)
    [rnd, zr, chis]
    (fun j q => 7 ≤ j ∧ (q = (Parameters.gpow (c + (64 + 2 * j)), xs.getD (64 + 2 * j) 0) ∨
      q = (Parameters.gpow (c + (64 + 2 * j + 1)), xs.getD (64 + 2 * j + 1) 0)))
    (fun σ j hj hp hes kids _ q hq => ?_) (j := 7) (by omega) hn hv
  · intro j h7 hj
    exact ⟨h j h7 hj _ ⟨h7, Or.inl rfl⟩, h j h7 hj _ ⟨h7, Or.inr rfl⟩⟩
  · simp only [show Fn.params Data.core141 = [.n 0, .n 1, .n 2, .n 3, .n 4] from rfl, List.map_cons,
      List.map_nil, List.cons.injEq] at hp
    obtain ⟨h0, -, h2, -, -, -⟩ := hp
    obtain ⟨h7, hq⟩ := hq
    have a5 := vtcS_atom hes m5
    have a6 := vtcS_atom hes m6
    have a7 := vtcS_atom hes m7
    have a12 : LoadHolds rd (σ (.n 7)) 2 (σ (.n 12)) := vtcS_atom hes l12
    simp only [Atom.HoldsB] at a5 a6 a7
    rw [a7, a6, a5, h0, h2, ← pow_add, ← pow_add, loadHolds_mul_gen_pow] at a12
    have e12 : σ (.n 12) = ofK (Parameters.gpow c) * gen ^ (64 + 2 * j) :=
      loadHolds_unique a12 (by rw [show j + j + (j + j) + 2 = 4 * j + 2 by omega]; exact hrow j h7 (by omega))
    have hk0 : 64 + 2 * j < xs.length := by rw [hlen]; unfold flLen; omega
    have hk1 : 64 + 2 * j + 1 < xs.length := by rw [hlen]; unfold flLen; omega
    left
    rcases hq with rfl | rfl
    · rw [List.getD_eq_getElem _ _ hk0]
      exact loadEq_of_event hes (mem_slEvs_of l13) hx hk0 (by rw [e12, addr_gen, Nat.add_zero])
    · rw [List.getD_eq_getElem _ _ hk1]
      exact loadEq_of_event hes (mem_slEvs_of l28) hx hk1 (by rw [e12, addr_gen]; rfl)

set_option maxRecDepth 100000 in
theorem fl_load2 : ∀ k < 78, ((.n 2 : V), k) ∈ flSegs.flatten.filterMap Stmt.loadS := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem fl_load2240 : ∀ k < 82, ((.n 2240 : V), k) ∈ flSegs.flatten.filterMap Stmt.loadS := by
  decide +kernel

/-! ## `verify_flock`, placed, loading what it reads -/

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
/-- **`verify_flock` is complete, placed, by a bounded tree within weights** (TRIAGE #40):
`CompleteFlockAtW` at its frame, its `HeapBuf`s and its two loops at `τ < 29`. -/
theorem verify_flock_completeAtWCL (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ)
    {Θ : Type} (w : Θ → String → ℕ) (κ : ℕ) :
    VerifySub.CompleteFlockAtWCL CM fs cert κ w (flockBound fs) fun θ => flockBoundW (w θ) := by
  intro τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin hτ hcl hrl hsl hrun hLin
  obtain ⟨hlen, hz, ha, hchiE, hrcE, hsE, hterm, hcv', hA⟩ :=
    flock_invC (hrun _ (flockEv_atM CM.hm alpha zSkip (chi.take 8) rcs.reverse s mv))
  refine CompleteAtWST.bmono ?_ (show fs "verify_flock" + (flSizes τ).sum + 2 * flLoopsBound fs ≤
    flockBound fs by simp only [flSizes, flockBound, List.sum_cons, List.sum_nil]; omega)
  refine completeAtS_straightWT (S := CM.sem) find_verify_flock fl_not_loop κ Lin _ _ fl_body fl_straight fl_addrs
    (flSizes τ) (fun _ => flOwnT CM.hm τ cv xs (ofK (Parameters.gpow c))) (fun _ => flOwnT_fit _ _ _ _ _)
    (fun fp => flKidsT CM.hm τ cv xs (ofK (Parameters.gpow c)) (ofK (Parameters.gpow zc)) Lin
      (fp + fs "verify_flock")) (fun _ => flLoopsBound fs) (fun _ θ => flLoopsBound (w θ))
    (2 * flLoopsBound fs) (fun θ => 2 * flLoopsBound (w θ))
    (fun k _ _ t => k.f = "__loop82" → L82Loads τ c xs t) (fun _ _ t => LoadsWords t c xs) ?_
    (fun fp => by simp [kidsBound, flKidsT]; omega) (fun fp θ => by simp [Main.kidsBoundW, flKidsT]; omega) ?_ ?_ ?_
  · intro fp k hk _
    simp only [flKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine CompleteAtWST.mono (CompleteAtWS.toWST (vtcS_completeAt_of_rel_lowW (S := CM.sem)
        (B := fun fs' => flLoopsBound fs') pure81 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) fun fs' rd _ t rets' hn hv hbo => ?_))
        fun _ _ _ _ h => absurd h (by simp)
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hM := flMemC_of (M := CM.hm) hLin hlen hchiE hrcE hsE hlow hL1 hL2 hag
        rw [word_g13, word_g14, ← pow_add]
        exact loop81_completeC hτ hM hA
      · rw [word_g13, word_g14, ← pow_add] at hv
        have := l81S_total (S := CM.sem) (fs := fs') (j := 13) (m := τ + 14) (by omega) hn hv hbo
        have : (τ + 14 - 13) * fs' "__loop81" ≤ 29 * fs' "__loop81" := Nat.mul_le_mul_right _ (by omega)
        simp only [flLoopsBound]; omega
    · refine CompleteAtWS.toWST_of_valid (vtcS_completeAt_of_rel_lowW (S := CM.sem)
        (B := fun fs' => flLoopsBound fs') pure82 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) fun fs' rd _ t rets' hn hv hbo => ?_)
        (fun fp' rd hlow hL t rets' hn hv _ => ?_)
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hM := flMemC_of (M := CM.hm) hLin hlen hchiE hrcE hsE hlow hL1 hL2 hag
        rw [word_g7, word_g8, ← pow_add]
        exact loop82_completeC hτ hM hA
      · rw [word_g7, word_g8, ← pow_add] at hv
        have := l82S_total (S := CM.sem) (fs := fs') (j := 7) (m := τ + 8) (by omega) hn hv hbo
        have : (τ + 8 - 7) * fs' "__loop82" ≤ 29 * fs' "__loop82" := Nat.mul_le_mul_right _ (by omega)
        simp only [flLoopsBound]; omega
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hB := flBufsC_of (M := CM.hm) hL2
        rw [word_g7, word_g8, ← pow_add] at hv
        exact l82_loads hτ hlen ((hLin rd hlow hL1).1) (fun j h1 h2 => (hB.rnd j h1 h2).2.2.1) hn hv
  · intro fp k hk _ i hi
    simp only [flKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact regionL_append.mp hi
  · intro fp rd hB hL k hk
    simp only [flKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact Main.memL_append.mpr ⟨hL, hB⟩
  · intro fp outs ho rd hlow hB hL
    have hM := flMemC_of (M := CM.hm) hLin hlen hchiE hrcE hsE hlow hL hB (rd' := rd) (fun _ _ => rfl)
    obtain ⟨σ, he, ⟨hret, F0, F7⟩, hh⟩ := flock_body_completeC hτ hM hA hlen hterm
      (Val.ofArgs [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c), gen ^ τ,
        ofK (Parameters.gpow zc), ofK (Parameters.gpow lr), ofK (Parameters.gpow zp)]) (by
        intro p hp
        simp only [flArgs, List.mem_cons, List.mem_nil_iff, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> rfl)
    have ag : ∀ i < 7, σ (.n i) = [(digestScalars cv).1, (digestScalars cv).2, ofK (Parameters.gpow c),
        gen ^ τ, ofK (Parameters.gpow zc), ofK (Parameters.gpow lr), ofK (Parameters.gpow zp)].getD i 0 :=
      fun i hi => by rw [he.apply (Or.inl hi)]; rfl
    set b := fp + fs "verify_flock"
    have f10 : σ (.n 10) = gen ^ τ * word 16384 0 0 := F0.get (by simp [flP0OutC])
    have f11 : σ (.n 11) = ofK (Parameters.gpow b) := F0.get (by simp [flP0OutC])
    have f23 : σ (.n 23) = gen ^ τ * word 16384 0 0 * word 4 0 0 * (gen ^ τ * word 16384 0 0 * word 4 0 0) :=
      F0.get (by simp [flP0OutC])
    have f24 : σ (.n 24) = ofK (Parameters.gpow (b + (τ + 14))) := F0.get (by simp [flP0OutC])
    have f26 : σ (.n 26) = ofK (Parameters.gpow (b + (τ + 14))) * word 67108864 0 0 :=
      F0.get (by simp [flP0OutC])
    have f30 : σ (.n 30) = word 8192 0 0 + gen ^ τ * word 16384 0 0 := F0.get (by simp [flP0OutC])
    have f31 : σ (.n 31) = word 8192 0 0 := F0.get (by simp [flP0OutC])
    have f33 : σ (.n 33) = gen ^ τ * word 16384 0 0 := F0.get (by simp [flP0OutC])
    have f37 : σ (.n 37) = ofK (Parameters.gpow (b + (τ + 14))) *
        (gen ^ τ * word 16384 0 0 * (gen ^ τ * word 16384 0 0)) := F0.get (by simp [flP0OutC])
    have f40 : σ (.n 40) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32))) := F0.get (by simp [flP0OutC])
    have f2219 : σ (.n 2219) =
        gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0 *
          (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0) *
        (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0 *
          (gen ^ τ * word 16384 0 0 * word 2017612633061982209 0 0 * word 4 0 0)) :=
      F7.get (by simp [flP7OutC])
    have f2220 : σ (.n 2220) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)) :=
      F7.get (by simp [flP7OutC])
    have f2222 : σ (.n 2222) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)) *
        word 268435456 0 0 := F7.get (by simp [flP7OutC])
    have f2228 : σ (.n 2228) = word 128 0 0 + gen ^ τ * word 256 0 0 := F7.get (by simp [flP7OutC])
    have f2229 : σ (.n 2229) = word 128 0 0 := F7.get (by simp [flP7OutC])
    have f2231 : σ (.n 2231) = gen ^ τ * word 256 0 0 := F7.get (by simp [flP7OutC])
    have f2236 : σ (.n 2236) = ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)) *
        (gen ^ τ * word 256 0 0 * (gen ^ τ * word 256 0 0) *
          (gen ^ τ * word 256 0 0 * (gen ^ τ * word 256 0 0))) := F7.get (by simp [flP7OutC])
    have f2240 : σ (.n 2240) = ofK (Parameters.gpow c) * gen ^ (64 + 2 * (τ + 8)) :=
      F7.get (by simp [flP7OutC])
    have h4 : word 4 0 0 = gen ^ 2 := word_four'
    obtain ⟨o1, o2, rfl⟩ : ∃ o1 o2, outs = [o1, o2] := by
      match outs, ho.length with
      | [o1, o2], _ => exact ⟨o1, o2, rfl⟩
    have ho1 : o1.1 = [] := (ho.1 rfl).1
    have ho2 : o2.1 = [] := (ho.2.1 rfl).1
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [core12_params]
      simp only [List.map_cons, List.map_nil]
      rw [ag 0 (by omega), ag 1 (by omega), ag 2 (by omega), ag 3 (by omega), ag 4 (by omega),
        ag 5 (by omega), ag 6 (by omega)]
      rfl
    · rw [fl_body, holdsListB_append]
      refine hh _ _ ?_
      simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_cons, List.map_nil]
      rw [hret, hcv', hz, ha, hlen, mul_assoc, ← pow_add,
        show 64 + 2 * (τ + 8) + 82 = flLen τ by unfold flLen; omega]
    · rw [fl_allocs]
      simp only [List.map_cons, List.map_nil, Sum.elim_inr, Sum.elim_inl, id]
      rw [f10, f23, f2219, fl_v1851, word_g14, h4]
      simp only [← pow_add]
      rw [logG_g _ (by omega), logG_g _ (by omega), logG_g _ (by omega), flSizes]
      congr 2
      · omega
      · congr 2; omega
    · rw [fl_allocs]
      simp only [List.map_cons, List.map_nil, flBases]
      rw [f11, f24, f40, f2220]
    · rw [fl_calls]
      simp only [List.map_cons, List.map_nil, Main.mkCall, flKidsT]
      refine ⟨rfl, ?_, fun _ => ⟨?_, by rw [ho1]; rfl⟩, rfl, ?_, fun _ => ⟨?_, by rw [ho2]; rfl⟩,
        trivial⟩
      · rw [f30, word_g13, word_g14, ← pow_add]
        simpa using gen_pow_ne_of_lt (a := 13) (b := τ + 14) (by omega) (by omega)
      · simp only [List.map_cons, List.map_nil]; rw [f31, f33, f24, f11]
      · rw [f2228, word_g7, word_g8, ← pow_add]
        simpa using gen_pow_ne_of_lt (a := 7) (b := τ + 8) (by omega) (by omega)
      · simp only [List.map_cons, List.map_nil]; rw [f2229, f2231, f2220, f11, ag 4 (by omega)]; rfl
    · intro q hq
      have hb := List.all_eq_true.mp fl_loads q hq
      obtain ⟨t, ht, htq⟩ := List.any_eq_true.mp hb
      obtain ⟨p, off⟩ := q
      simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at htq
      obtain ⟨⟨hp, hlo⟩, hhi⟩ := htq
      simp only [flLoadT, List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        (dsimp only at hp hlo hhi ⊢; subst hp)
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL (j := off) (by rw [hlen]; unfold flLen; omega)
        exact ⟨i, by rw [ag 2 (by omega)]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).1) hlow hL
          (j := 64 + 2 * (τ + 8) + off) (by rw [hlen]; unfold flLen; omega)
        refine ⟨i, ?_, Or.inl hr⟩
        rw [f2240, addr_gen, ← hi, addr_k, Nat.add_assoc]
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).2.1) hlow hL (j := off) (by rw [hcl]; omega)
        exact ⟨i, by rw [ag 4 (by omega)]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).2.2.1) hlow hL (j := off) (by rw [hrl]; omega)
        exact ⟨i, by rw [ag 5 (by omega)]; exact hi, Or.inl hr⟩
      · obtain ⟨i, hi, hr⟩ := addr_in_region (fun rd h1 h2 => (hLin rd h1 h2).2.2.2) hlow hL (j := off) (by rw [hsl]; omega)
        exact ⟨i, by rw [ag 6 (by omega)]; exact hi, Or.inl hr⟩
      · exact ⟨b + off, by rw [f11, addr_k], Or.inr (region_buf (w := flW11T CM.hm τ cv)
          (by simp [bufL, flBases, flOwnT]) (by simp [flW11T]; omega))⟩
      · refine ⟨b + (τ + 14) + (26 + off), by rw [f26, word_g26, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW24T CM.hm τ cv) (by simp [bufL, flBases, flOwnT]) (by simp [flW24T]; omega))⟩
      · refine ⟨b + (τ + 14) + (τ + 14 + (τ + 14) + off), by
          rw [f37, word_g14, ← pow_add, ← pow_add, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW24T CM.hm τ cv) (by simp [bufL, flBases, flOwnT]) (by simp [flW24T]; omega))⟩
      · exact ⟨b + (τ + 14) + (2 * τ + 32) + off, by rw [f40, addr_k], Or.inr (region_buf (w := flW40 xs)
          (by simp [bufL, flBases, flOwnT]) (by simp [flW40]; omega))⟩
      · refine ⟨b + (τ + 14) + (2 * τ + 32) + 64 + (28 + off), by
          rw [f2222, LeanVM.Guest.B1.word_g28, addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW2220T CM.hm τ cv xs (ofK (Parameters.gpow c)))
            (by simp [bufL, flBases, flOwnT]) (by simp [flW2220T]; omega))⟩
      · refine ⟨b + (τ + 14) + (2 * τ + 32) + 64 + (τ + 8 + (τ + 8) + (τ + 8 + (τ + 8)) + off), by
          rw [f2236, word_g8, ← pow_add]
          simp only [← pow_add]
          rw [addr_gen, Nat.add_assoc],
          Or.inr (region_buf (w := flW2220T CM.hm τ cv xs (ofK (Parameters.gpow c)))
            (by simp [bufL, flBases, flOwnT]) (by simp [flW2220T]; omega))⟩
    · intro es hw hes ks hkv hks
      have hwS := Main.walk_straight σ [.n 4369, .n 4370, .n 4373, .n 4374, .n 4375, .n 4376]
        flSegs.flatten fl_straight
      rw [← fl_body, hw] at hwS
      injection hwS with hes_eq
      subst hes_eq
      have hx := (hLin rd hlow hL).1
      obtain ⟨-, -, -, i4⟩ := Main.straight_parts σ flSegs.flatten fl_straight
      have hkl := kidsValidB_length hkv
      rw [i4, fl_calls] at hkv hks hkl
      intro k hk
      have hk' : k < flLen τ := hlen ▸ hk
      unfold flLen at hk'
      by_cases h78 : k < 78
      · obtain ⟨d, hd⟩ := exists_load_of_loadS (fl_load2 k h78)
        exact mem_loadEqns_node find_verify_flock hw
          (loadEq_of_event hes (mem_slEvs_of hd) hx hk (by rw [ag 2 (by omega)]; exact addr_k c k))
      by_cases hhi : 64 + 2 * (τ + 8) ≤ k
      · obtain ⟨d, hd⟩ := exists_load_of_loadS (fl_load2240 (k - (64 + 2 * (τ + 8))) (by omega))
        refine mem_loadEqns_node find_verify_flock hw
          (loadEq_of_event hes (mem_slEvs_of hd) hx hk ?_)
        rw [f2240, addr_gen]
        congr 1
        omega
      · have ht : decide (σ (.n 2228) ≠ 0) = true := by
          rw [f2228, word_g7, word_g8, ← pow_add]
          simpa using gen_pow_ne_of_lt (a := 7) (b := τ + 8) (by omega) (by omega)
        obtain ⟨kt, hkm, hq, -⟩ := kidsSat_get 1 hkv hks (by simp) (by simp [flKidsT])
          (by rw [VerifySub.vt_length_bases, List.length_map, ← hkl]; simp) (by simpa [Main.mkCall] using ht)
        have h82 := hq rfl
        obtain ⟨h0, h1⟩ := h82 ((k - 64) / 2) (by omega) (by omega)
        refine mem_loadEqns_kid hkm ?_
        rw [← List.getD_eq_getElem xs 0 hk]
        rcases Nat.mod_two_eq_zero_or_one (k - 64) with he | ho
        · rwa [show 64 + 2 * ((k - 64) / 2) = k by omega] at h0
        · rwa [show 64 + 2 * ((k - 64) / 2) + 1 = k by omega] at h1

end
end LeanVM.Guest.B1
