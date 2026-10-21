/-
  LeanVM.Guest.B1.Comp.Tables.FlockAtC

  `verify_flock` complete in the placed form over a completeness model, by a bounded tree within
  weights, and the deployed placed completeness recovered at `CompModel.deployed`.
-/

module

public import LeanVM.Guest.B1.Comp.Tables.FlockAllC
public import LeanVM.Guest.B1.Comp.Tables.IfaceC
public import LeanVM.Guest.B1.Tables.FlockAtB
public import LeanVM.Guest.B1.Tables.LoopSize
public import LeanVM.Guest.B1.Tables.VtCSizeS

/-!
# `verify_flock`, placed, over a completeness model

`Tables/FlockAt.lean` and `Tables/FlockAtB.lean` over a `CompModel`:

* the buffers' honest words at the model's total hash (`flOwnT`), read back (`flBufsC_of`) into
  `verify_flock`'s honest memory over the model (`flMemC_of`);
* the two loops' valid trees under any semantics (`l81S_total`, `l82S_total`, from
  `loopStdS_total`);
* `verify_flock_completeAtWC`: `CompleteFlockAtWC` at its frame, its `HeapBuf`s and its two loops,
  from the answered run (`flock_invC`), the body over the model (`flock_body_completeC`) and the
  loops over the model (`loop81_completeC`, `loop82_completeC`), by `completeAtS_straightW`.

At `CompModel.deployed` it is the deployed `verify_flock_completeAtW`
(`verify_flock_completeAtW_of_comp`).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub LeanVM.Guest.B1.Sig LeanVM.E2E.Complete
open LeanVM.Guest.B1.Main (Layout MemL RegionL)

@[expose] public section

/-! ## The buffers over a hash model -/

/-- `zerocheck_r`: the coordinates from offset 6. -/
def flW11T (M : HashModel) (τ : ℕ) (cv : Digest) : List E :=
  (List.range (τ + 14)).map fun j => if j < 6 then 0 else flET M τ cv (j - 6)

/-- `flock_pts`: the squeezes' states from row 13. -/
def flW24T (M : HashModel) (τ : ℕ) (cv : Digest) : List E :=
  (List.range (2 * τ + 32)).map fun i => if 26 ≤ i ∧ i < 2 * τ + 30 then
    (if i % 2 = 0 then (digestScalars ((sqCvT M)^[(i - 26) / 2] cv)).1
      else (digestScalars ((sqCvT M)^[(i - 26) / 2] cv)).2) else 0

/-- A word of `flock_rounds`' row `i / 4`. -/
def flRowT (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) (i : ℕ) : E :=
  if i % 4 = 0 then (digestScalars (flScAtT M τ cv xs (i / 4)).2).1
  else if i % 4 = 1 then (digestScalars (flScAtT M τ cv xs (i / 4)).2).2
  else if i % 4 = 2 then cur * gen ^ (64 + 2 * (i / 4)) else (flScAtT M τ cv xs (i / 4)).1

/-- `flock_rounds`: the rows from row 7. -/
def flW2220T (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) : List E :=
  (List.range (4 * τ + 40)).map fun i => if 28 ≤ i ∧ i < 4 * τ + 36 then flRowT M τ cv xs cur i else 0

/-- The four buffers' words. -/
def flOwnT (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) : List (List E) :=
  [flW11T M τ cv, flW24T M τ cv, flW40 xs, flW2220T M τ cv xs cur]

theorem flOwnT_fit (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur : E) :
    List.Forall₂ (fun c s => c.length ≤ s) (flOwnT M τ cv xs cur) (flSizes τ) := by
  simp [flOwnT, flSizes, flW11T, flW24T, flW40, flW2220T]


section
variable {rd : Reader}

/-- **The buffers' words**, read off a memory holding their layout. -/
theorem flBufsC_of {M : HashModel} {τ : ℕ} {cv : Digest} {xs : List E} {cur : E} {b : ℕ}
    (h : MemL rd (bufL b (flSizes τ) (flOwnT M τ cv xs cur))) :
    FlBufsC M rd τ cv xs cur (ofK (gpow b)) (ofK (gpow (b + (τ + 14))))
      (ofK (gpow (b + (τ + 14) + (2 * τ + 32)))) (ofK (gpow (b + (τ + 14) + (2 * τ + 32) + 64))) := by
  simp only [bufL, flBases, flOwnT, List.zip_cons_cons, List.zip_nil_right] at h
  have h0 := h (b, flW11T M τ cv) (by simp)
  have h1 := h (b + (τ + 14), flW24T M τ cv) (by simp)
  have h2 := h (b + (τ + 14) + (2 * τ + 32), flW40 xs) (by simp)
  have h3 := h (b + (τ + 14) + (2 * τ + 32) + 64, flW2220T M τ cv xs cur) (by simp)
  simp only at h0 h1 h2 h3
  refine ⟨fun j hj => ?_, fun t ht => ⟨?_, ?_⟩, fun i hi => ?_, fun j h7 hj => ⟨?_, ?_, ?_, ?_⟩⟩
  · have := readsAt_get h0 (k := 6 + j) (by simp [flW11T]; omega)
    rwa [flW11T, getD_map_range _ _ (by omega), ite_neg' (by omega), Nat.add_sub_cancel_left] at this
  · have := readsAt_get h1 (k := 26 + 2 * t) (by simp [flW24T]; omega)
    rwa [flW24T, getD_map_range _ _ (by omega), ite_pos' (by omega), ite_pos' (by omega),
      show (26 + 2 * t - 26) / 2 = t by omega] at this
  · have := readsAt_get h1 (k := 27 + 2 * t) (by simp [flW24T]; omega)
    rwa [flW24T, getD_map_range _ _ (by omega), ite_pos' (by omega), ite_neg' (by omega),
      show (27 + 2 * t - 26) / 2 = t by omega] at this
  · have := readsAt_get h2 (k := i) (by simp [flW40]; omega)
    rwa [flW40, getD_map_range _ _ hi] at this
  · have := readsAt_get h3 (k := 4 * j) (by simp [flW2220T]; omega)
    rwa [flW2220T, getD_map_range _ _ (by omega), ite_pos' (by omega), flRowT,
      ite_pos' (by omega), show 4 * j / 4 = j by omega] at this
  · have := readsAt_get h3 (k := 4 * j + 1) (by simp [flW2220T]; omega)
    rwa [flW2220T, getD_map_range _ _ (by omega), ite_pos' (by omega), flRowT,
      ite_neg' (by omega), ite_pos' (by omega), show (4 * j + 1) / 4 = j by omega] at this
  · have := readsAt_get h3 (k := 4 * j + 2) (by simp [flW2220T]; omega)
    rwa [flW2220T, getD_map_range _ _ (by omega), ite_pos' (by omega), flRowT,
      ite_neg' (by omega), ite_neg' (by omega), ite_pos' (by omega),
      show (4 * j + 2) / 4 = j by omega] at this
  · have := readsAt_get h3 (k := 4 * j + 3) (by simp [flW2220T]; omega)
    rwa [flW2220T, getD_map_range _ _ (by omega), ite_pos' (by omega), flRowT,
      ite_neg' (by omega), ite_neg' (by omega), ite_neg' (by omega),
      show (4 * j + 3) / 4 = j by omega] at this

/-- **`verify_flock`'s honest memory** on a memory holding its buffers and the caller's words,
and on any memory agreeing with it there. -/
theorem flMemC_of {M : HashModel} {κ : ℕ} {Lin : Main.Layout} {τ : ℕ} {cv : Digest} {xs chi rcs s : List E}
    {c zc lr zp b : ℕ}
    (hall : ∀ rd, LowDef κ rd → MemL rd Lin →
      ReadsAt rd (ofK (gpow c)) xs ∧ ReadsAt rd (ofK (gpow zc)) chi ∧
        ReadsAt rd (ofK (gpow lr)) rcs ∧ ReadsAt rd (ofK (gpow zp)) s)
    (hlen : xs.length = flLen τ) (hchiE : chi = flChiT M τ cv xs) (hrcE : rcs = flRcT M τ cv xs)
    (hsE : s = flS τ xs) (hlow : LowDef κ rd) (hL : MemL rd Lin)
    (hB : MemL rd (bufL b (flSizes τ) (flOwnT M τ cv xs (ofK (gpow c))))) {rd' : Reader}
    (hag : ∀ i, RegionL (Lin ++ bufL b (flSizes τ) (flOwnT M τ cv xs (ofK (gpow c)))) i →
      rd' (gpow i) = rd (gpow i)) :
    FlMemC M rd' τ cv xs (ofK (gpow c)) (ofK (gpow zc)) (ofK (gpow lr)) (ofK (gpow zp))
      (ofK (gpow b)) (ofK (gpow (b + (τ + 14)))) (ofK (gpow (b + (τ + 14) + (2 * τ + 32))))
      (ofK (gpow (b + (τ + 14) + (2 * τ + 32) + 64))) := by
  have hagL : ∀ i, RegionL Lin i → rd' (gpow i) = rd (gpow i) := fun i hi =>
    hag i (regionL_append.mpr (Or.inl hi))
  have hB' := flBufsC_of (memL_of_agree hB fun i hi => hag i (regionL_append.mpr (Or.inr hi)))
  have r0 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).1) hlow hL hagL
  have r1 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).2.1) hlow hL hagL
  have r2 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).2.2.1) hlow hL hagL
  have r3 := readsAt_transfer (fun rd h1 h2 => (hall rd h1 h2).2.2.2) hlow hL hagL
  subst hchiE hrcE hsE
  refine ⟨fun k hk => readsAt_get r0 (by omega), hB'.zr, hB'.pts, hB'.p1, hB'.rnd, fun j hj => ?_,
    fun j hj => ?_, fun i hi => ?_⟩
  · have := readsAt_get r1 (k := j) (by simp [flChiT]; omega)
    rwa [flChiT, getD_map_range _ _ hj] at this
  · have := readsAt_get r2 (k := j) (by simp [flRcT]; omega)
    rwa [flRcT, getD_map_range _ _ hj] at this
  · have := readsAt_get r3 (k := i) (by simp [flS]; unfold flLen at hlen; omega)
    rwa [flS_getD τ xs hi] at this

/-- The two loops' frames: on the caller's words and `verify_flock`'s buffers from `b`. -/
def flKidsT (M : HashModel) (τ : ℕ) (cv : Digest) (xs : List E) (cur zchis : E) (Lin : Main.Layout) (b : ℕ) :
    List Kid :=
  [⟨"__loop81", true, [word 8192 0 0, gen ^ τ * word 16384 0 0, ofK (Parameters.gpow (b + (τ + 14))),
      ofK (Parameters.gpow b)], Lin ++ bufL b (flSizes τ) (flOwnT M τ cv xs cur), Returns []⟩,
    ⟨"__loop82", true, [word 128 0 0, gen ^ τ * word 256 0 0,
      ofK (Parameters.gpow (b + (τ + 14) + (2 * τ + 32) + 64)), ofK (Parameters.gpow b), zchis],
      Lin ++ bufL b (flSizes τ) (flOwnT M τ cv xs cur), Returns []⟩]


end

/-! ## The loops' trees under any semantics -/

section
variable {S : BlakeSem} {fs : String → ℕ}

/-- **A `mul_range` loop's valid trees** from `g^j` to `g^m`: at most `m - j` frames and the
skipped tail's. -/
theorem loopStdS_total {f : String} {fn : Fn} (hf : coreProgram.find? f = some fn)
    {pre0 : List Stmt} {P : List V} {a b c a' d : ℕ} (hpar : fn.params = .n 0 :: .n 1 :: P)
    (hb : fn.body = (pre0 ++ loopTail a b c a' d) ++ [.callIf (.n c) f (.n d :: .n 1 :: P), .ret []])
    (hck : (pre0 ++ loopTail a b c a' d).all Main.Stmt.straight = true ∧
      (pre0 ++ loopTail a b c a' d).filterMap Main.Stmt.allocSz = [] ∧
      (pre0 ++ loopTail a b c a' d).filterMap Main.Stmt.callS = [])
    {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = f) (hv : t.ValidB S coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs f + fs f := by
  have := vtcS_loop_total (S := S) (fs := fs) hf hb hck.1 hck.2.1 rd m rest 0 ?_ (m - j) j t rets (by omega) hj
    hn hv hbo
  · simpa using this
  intro σ j' _ hp hes
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
  refine ⟨by rw [a3, a2, a1, h0, h1], by simp [a5, a4, h0, h1, hr], fun kids hk _ => ?_⟩
  rw [hck.2.2] at hk
  match kids, hk with
  | [], _ => simp [Tree.totalKids]


/-- **`__loop81`'s valid trees** from `g^j` to `g^m`. -/
theorem l81S_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop81") (hv : t.ValidB S coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop81" + fs "__loop81" :=
  loopStdS_total find_loop81 rfl l81_shape l81_ck hj hn hv hbo

/-- **`__loop82`'s valid trees** from `g^j` to `g^m`. -/
theorem l82S_total {rd : Reader} {j m : ℕ} {rest : List E} {t : Tree} {rets : List E} (hj : j < m)
    (hn : t.name = "__loop82") (hv : t.ValidB S coreProgram rd (gen ^ j :: gen ^ m :: rest) rets)
    (hbo : t.BufsOk coreProgram) : t.total fs ≤ (m - j) * fs "__loop82" + fs "__loop82" :=
  loopStdS_total find_loop82 rfl l82_shape l82_ck hj hn hv hbo

end

/-! ## `verify_flock`, placed -/

set_option maxHeartbeats 4000000 in
/-- **`verify_flock` is complete, placed, by a bounded tree within weights** (TRIAGE #40):
`CompleteFlockAtW` at its frame, its `HeapBuf`s and its two loops at `τ < 29`. -/
theorem verify_flock_completeAtWC (CM : CompModel) (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type}
    (w : Θ → String → ℕ) (κ : ℕ) :
    VerifySub.CompleteFlockAtWC CM fs cert κ w (flockBound fs) fun θ => flockBoundW (w θ) := by
  intro τ cv xs cv' zSkip alpha mv chi rcs s c zc lr zp Lin hτ hcl hrl hsl hrun hLin
  obtain ⟨hlen, hz, ha, hchiE, hrcE, hsE, hterm, hcv', hA⟩ :=
    flock_invC (hrun _ (flockEv_atM CM.hm alpha zSkip (chi.take 8) rcs.reverse s mv))
  refine Main.CompleteAtWS.bmono ?_ (show fs "verify_flock" + (flSizes τ).sum + 2 * flLoopsBound fs ≤
    flockBound fs by simp only [flSizes, flockBound, List.sum_cons, List.sum_nil]; omega)
  refine completeAtS_straightW (S := CM.sem) find_verify_flock fl_not_loop κ Lin _ _ fl_body fl_straight fl_addrs
    (flSizes τ) (fun _ => flOwnT CM.hm τ cv xs (ofK (Parameters.gpow c))) (fun _ => flOwnT_fit _ _ _ _ _)
    (fun fp => flKidsT CM.hm τ cv xs (ofK (Parameters.gpow c)) (ofK (Parameters.gpow zc)) Lin
      (fp + fs "verify_flock")) (fun _ => flLoopsBound fs) (fun _ θ => flLoopsBound (w θ))
    (2 * flLoopsBound fs) (fun θ => 2 * flLoopsBound (w θ)) ?_
    (fun fp => by simp [kidsBound, flKidsT]; omega) (fun fp θ => by simp [Main.kidsBoundW, flKidsT]; omega) ?_ ?_ ?_
  · intro fp k hk _
    simp only [flKidsT, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl
    · refine vtcS_completeAt_of_rel_lowW (S := CM.sem) (B := fun fs' => flLoopsBound fs') pure81 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) fun fs' rd _ t rets' hn hv hbo => ?_
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hM := flMemC_of (M := CM.hm) hLin hlen hchiE hrcE hsE hlow hL1 hL2 hag
        rw [word_g13, word_g14, ← pow_add]
        exact loop81_completeC hτ hM hA
      · rw [word_g13, word_g14, ← pow_add] at hv
        have := l81S_total (S := CM.sem) (fs := fs') (j := 13) (m := τ + 14) (by omega) hn hv hbo
        have : (τ + 14 - 13) * fs' "__loop81" ≤ 29 * fs' "__loop81" := Nat.mul_le_mul_right _ (by omega)
        simp only [flLoopsBound]; omega
    · refine vtcS_completeAt_of_rel_lowW (S := CM.sem) (B := fun fs' => flLoopsBound fs') pure82 (by simp) κ
        (fun rd hlow hL rd' hag => ?_) fun fs' rd _ t rets' hn hv hbo => ?_
      · obtain ⟨hL1, hL2⟩ := Main.memL_append.mp hL
        have hM := flMemC_of (M := CM.hm) hLin hlen hchiE hrcE hsE hlow hL1 hL2 hag
        rw [word_g7, word_g8, ← pow_add]
        exact loop82_completeC hτ hM hA
      · rw [word_g7, word_g8, ← pow_add] at hv
        have := l82S_total (S := CM.sem) (fs := fs') (j := 7) (m := τ + 8) (by omega) hn hv hbo
        have : (τ + 8 - 7) * fs' "__loop82" ≤ 29 * fs' "__loop82" := Nat.mul_le_mul_right _ (by omega)
        simp only [flLoopsBound]; omega
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
    refine ⟨σ, ?_, ?_, ?_, ?_, ?_, ?_⟩
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



/-- **The deployed `verify_flock_completeAtW`**, from the model's at `CompModel.deployed`. -/
theorem verify_flock_completeAtW_of_comp (fs : String → ℕ) (cert : String → V → ℕ) {Θ : Type}
    (w : Θ → String → ℕ) (κ : ℕ) :
    CompleteFlockAtW fs cert κ w (flockBound fs) fun θ => flockBoundW (w θ) :=
  (verify_flock_completeAtWC CompModel.deployed fs cert w κ).toDeployed

end
end LeanVM.Guest.B1
