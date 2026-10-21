/-
  LeanVM.Guest.B1.Tables.FlockM

  B1 for `verify_flock` over a hash model: soundness in `verify_sub`'s shape (`SoundFlockM`).
-/

module

public import LeanVM.Guest.B1.Tables.Flock
public import LeanVM.Guest.B1.Tables.FlockSpecM
public import LeanVM.Guest.B1.VerifySub.InterfaceM

/-!
# `verify_flock` over a hash model

`Flock.lean` over a hash model `M`. `verify_flock`'s body holds under `M.sem`
(`verify_flock_holdsB`); its segments with no `BLAKE2S` atom (the prelude, the interpolation, the
numerators, the pin term, the points' equality, the slices' sum, the final check) hold as
deployed at the same call relation (`holdsListB_iff_of_noBlake`), so `Flock.lean`'s lemmas about
them apply unchanged; the segments that hash are read over the model:

* `fl_sampledM`: `__loop81`'s squeezes, answered at every iterate of the total `sqCvT`;
* `fsNext_runM`, `fl_round1M`, `fl_slicesM`: runs of `fs_next`, the state the model's answer
  (`obsAllM`);
* `frBlk_stepM`, `lcBlk_stepM`, `fl_roundsM`, `fl_lincheckM`: the sumchecks' rounds, each
  answered (`RoundOk`), over the total hash (`scStT`, `lcStT`);
* `fl_s8M`, `fl_s10M`: the final evaluations and `alpha`.

`verify_flock_model` assembles them by `runs_verifyFlockM`: `SoundFlockM M rd` for every reader
(`soundFlockM_model`, the hypothesis `verify_sub_model` takes).
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.VerifySub

@[expose] public section

variable {M : HashModel}

/-! ## The body under any semantics -/

section
variable {S : BlakeSem} {C : CallRel} {rd : Reader} {σ : Val}

/-- Blocks without `ret`, flattened, under `S` (`holdsList_flatten_noRet`). -/
theorem holdsListB_flatten_noRet : ∀ (ss : List (List Stmt)),
    (∀ s ∈ ss, Stmt.noRetList s = true) → ∀ (next : Prop) (kret : List E → Prop),
    Stmt.HoldsListB S C rd σ ss.flatten next kret ↔
      (∀ s ∈ ss, Stmt.HoldsListB S C rd σ s True kret) ∧ next
  | [], _, _, _ => by simp [Stmt.HoldsListB]
  | s :: ss, h, next, kret => by
    rw [List.flatten_cons, holdsListB_append, holdsListB_noRet s (h s (by simp)),
      holdsListB_flatten_noRet ss (fun t ht => h t (by simp [ht]))]
    simp only [List.mem_cons, forall_eq_or_imp]
    tauto

/-- Two blocks, the first without `ret`, under `S` (`hl_app`). -/
theorem hl_appB {a b : List Stmt} {kret : List E → Prop} (ha : Stmt.noRetList a = true) :
    Stmt.HoldsListB S C rd σ (a ++ b) True kret ↔
      Stmt.HoldsListB S C rd σ a True kret ∧ Stmt.HoldsListB S C rd σ b True kret := by
  rw [holdsListB_append, holdsListB_noRet _ ha]

end

/-- **`verify_flock`'s relation under any semantics** (`verify_flock_holds`). -/
theorem verify_flock_holdsB {S : BlakeSem} {rd : Reader} {args rets : List E}
    (h : coreProgram.RelB S rd "verify_flock" args rets) :
    ∃ σ : Val, [σ (.n 0), σ (.n 1), σ (.n 2), σ (.n 3), σ (.n 4), σ (.n 5), σ (.n 6)] = args ∧
      (∀ s ∈ flSegs, Stmt.HoldsListB S (coreProgram.RelB S rd) rd σ s True fun rs => rs = rets) ∧
      [σ (.n 4369), σ (.n 4370), σ (.n 4373), σ (.n 4374), σ (.n 4375), σ (.n 4376)] = rets := by
  rw [relB_iff_sem find_verify_flock, core12_body, core12_params] at h
  obtain ⟨σ, hp, hb⟩ := h
  rw [holdsListB_append, holdsListB_flatten_noRet _ flSegs_noRet] at hb
  exact ⟨σ, hp, hb.1, by simpa [flRet, Stmt.HoldsListB, Stmt.HoldsB] using hb.2⟩

/-! ## The segments with no `BLAKE2S` atom -/

/-- The prelude has no `BLAKE2S` atom. -/
theorem flP0_noBlake : Stmt.noBlakeList flP0 = true := by decide +kernel
/-- The interpolation's tail has no `BLAKE2S` atom. -/
theorem flP5_noBlake : Stmt.noBlakeList flP5 = true := by decide +kernel
/-- The sampled rounds' setup has no `BLAKE2S` atom. -/
theorem flP7_noBlake : Stmt.noBlakeList flP7 = true := by decide +kernel
/-- The pin term has no `BLAKE2S` atom. -/
theorem flP13_noBlake : Stmt.noBlakeList flP13 = true := by decide +kernel
/-- The final check has no `BLAKE2S` atom. -/
theorem flPEnd_noBlake : Stmt.noBlakeList flPEnd = true := by decide +kernel
/-- The upper numerators have no `BLAKE2S` atom. -/
theorem lag64_hi_noBlake : Stmt.noBlakeList (lag64T (.n 1014) (phi8From 64) 1015) = true := by
  decide +kernel
/-- The lower numerators have no `BLAKE2S` atom. -/
theorem lag64_lo_noBlake : Stmt.noBlakeList (lag64T (.n 1014) (phi8From 0) 2273) = true := by
  decide +kernel
/-- An interpolation term has no `BLAKE2S` atom. -/
theorem ipBlk_noBlake (i : ℕ) : Stmt.noBlakeList (ipBlk i) = true := by
  unfold ipBlk; split <;> rfl
/-- A factor of the points' equality has no `BLAKE2S` atom. -/
theorem cpeBlk_noBlake (t : ℕ) : Stmt.noBlakeList (cpeBlk t) = true := by
  unfold cpeBlk; split <;> rfl
/-- A term of the slices' sum has no `BLAKE2S` atom. -/
theorem csBlk_noBlake (i : ℕ) : Stmt.noBlakeList (csBlk i) = true := by
  unfold csBlk; split <;> rfl

/-! ## The sampled coordinates over the model -/

/-- **The sampled coordinates over the model** (`fl_sampled`): from the state `cv0` in row `13`
of `pts`, the loop leaves challenge `t` of the iterates of the total `sqCvT` at `zr[13 + t]`, each
squeeze answered, and its final state in row `τ + 14`. -/
theorem fl_sampledM {rd : Reader} {τ : ℕ} (hτ : τ < 29) {pts zr : E} {cv0 : Digest}
    (l0 : LoadHolds rd pts 26 (digestScalars cv0).1)
    (l1 : LoadHolds rd pts 27 (digestScalars cv0).2)
    (hloop : coreProgram.RelB M.sem rd "__loop81" [gen ^ 13, gen ^ (τ + 14), pts, zr] []) :
    (∀ t ≤ τ, LoadHolds rd zr (13 + t) (challengeOf (sqCvT M ((sqCvT M)^[t] cv0))) ∧
        sqCvM M ((sqCvT M)^[t] cv0) = some ((sqCvT M)^[t + 1] cv0)) ∧
      LoadHolds rd pts (2 * (τ + 14)) (digestScalars ((sqCvT M)^[τ + 1] cv0)).1 ∧
      LoadHolds rd pts (2 * (τ + 14) + 1) (digestScalars ((sqCvT M)^[τ + 1] cv0)).2 := by
  obtain ⟨m, hm, hN, hfirst, hall⟩ :=
    loopB_sound (loop81_stepM rd (gen ^ (τ + 14)) pts zr) 13 hloop
  have hm' : m = τ + 14 := by
    rcases Nat.lt_or_ge (τ + 14) m with h | h
    · exact absurd rfl (hfirst (τ + 14) (by omega) h)
    · exact (gen_pow_inj' (by omega) (by omega) hN).symm
  subst hm'
  have key : ∀ t ≤ τ + 1,
      LoadHolds rd pts (2 * (13 + t)) (digestScalars ((sqCvT M)^[t] cv0)).1 ∧
      LoadHolds rd pts (2 * (13 + t) + 1) (digestScalars ((sqCvT M)^[t] cv0)).2 ∧
      (t ≤ τ → LoadHolds rd zr (13 + t) (challengeOf (sqCvT M ((sqCvT M)^[t] cv0))) ∧
        sqCvM M ((sqCvT M)^[t] cv0) = some ((sqCvT M)^[t + 1] cv0)) := by
    intro t ht
    induction t with
    | zero =>
      refine ⟨l0, l1, fun _ => ?_⟩
      obtain ⟨cv, a0, a1, hq, a2, -, -⟩ := hall 13 le_rfl (by omega)
      rw [gen_pow_sq] at a0 a1
      have e0 := loadHolds_unique (lh_off0 a0) l0
      have e1 := loadHolds_unique (lh_off1 a1) l1
      obtain rfl := digestScalars_injective (Prod.ext e0 e1)
      exact ⟨lh_off0 a2, hq⟩
    | succ t ih =>
      obtain ⟨i0, i1, -⟩ := ih (by omega)
      obtain ⟨cv, a0, a1, -, -, a3, a4⟩ := hall (13 + t) (by omega) (by omega)
      rw [gen_pow_sq] at a0 a1 a3 a4
      obtain rfl := digestScalars_injective
        (Prod.ext (loadHolds_unique (lh_off0 a0) i0) (loadHolds_unique (lh_off1 a1) i1))
      have a3' := lh_off a3
      have a4' := lh_off a4
      rw [show 2 * (13 + t) + 2 = 2 * (13 + (t + 1)) by omega,
        ← Function.iterate_succ_apply' (sqCvT M) t cv0] at a3'
      rw [show 2 * (13 + t) + 3 = 2 * (13 + (t + 1)) + 1 by omega,
        ← Function.iterate_succ_apply' (sqCvT M) t cv0] at a4'
      refine ⟨a3', a4', fun ht' => ?_⟩
      obtain ⟨cv', b0, b1, hq', b2, -, -⟩ := hall (13 + (t + 1)) (by omega) (by omega)
      rw [gen_pow_sq] at b0 b1
      obtain rfl := digestScalars_injective
        (Prod.ext (loadHolds_unique (lh_off0 b0) a3') (loadHolds_unique (lh_off1 b1) a4'))
      rw [Function.iterate_succ_apply' (sqCvT M) (t + 1) cv0]
      exact ⟨lh_off0 b2, hq'⟩
  obtain ⟨k0, k1, -⟩ := key (τ + 1) le_rfl
  refine ⟨fun t ht => (key t (by omega)).2.2 ht, ?_, ?_⟩
  · rw [show 2 * (13 + (τ + 1)) = 2 * (τ + 14) by omega] at k0; exact k0
  · rw [show 2 * (13 + (τ + 1)) = 2 * (τ + 14) by omega] at k1; exact k1

/-! ## Runs of `fs_next` blocks over the model -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **A run of `fs_next` blocks over the model** (`fsNext_run`): the words read, and the chain
the model's answer on them. -/
theorem fsNext_runM (sIdx bIdx off : ℕ → ℕ) (cur : V) (extra : ℕ → List Stmt) {n : ℕ}
    (hblk : ∀ i < n, Stmt.HoldsListB M.sem C rd σ
      (fsNextT (.n (sIdx i)) (.n (sIdx i + 1)) cur (off i) (bIdx i) ++ extra i) True kret)
    (hs : ∀ i, sIdx (i + 1) = bIdx i + 13) {cv : Digest}
    (h0 : (σ (.n (sIdx 0)), σ (.n (sIdx 0 + 1))) = digestScalars cv) :
    (∀ i < n, LoadHolds rd (σ cur) (off i) (σ (.n (bIdx i))) ∧
      Stmt.HoldsListB M.sem C rd σ (extra i) True kret) ∧
      ∃ d, obsAllM M cv ((List.range n).map fun i => σ (.n (bIdx i))) = some d ∧
        (σ (.n (sIdx n)), σ (.n (sIdx n + 1))) = digestScalars d := by
  induction n with
  | zero => exact ⟨fun i hi => absurd hi (by omega), cv, rfl, h0⟩
  | succ n ih =>
    obtain ⟨h1, d, hd, h2⟩ := ih fun i hi => hblk i (by omega)
    have hb := hblk n (by omega)
    rw [holdsListB_append, holdsListB_noRet _ rfl] at hb
    obtain ⟨l, d', hd', hc⟩ := fsNext_chainM hb.1 h2
    refine ⟨fun i hi => ?_, d', ?_, ?_⟩
    · rcases Nat.lt_or_ge i n with h | h
      · exact h1 i h
      · obtain rfl : i = n := by omega
        exact ⟨l, hb.2⟩
    · rw [List.range_succ, List.map_append, List.map_singleton, obsAllM_snoc, hd, Option.bind_some,
        hd']
    · rw [hs]; exact hc

/-- Round 1's words over the model (`fl_round1`). -/
theorem fl_round1M (h : ∀ i < 64, Stmt.HoldsListB M.sem C rd σ (rd1Blk i) True kret)
    {cv1 : Digest} (hcv : (σ (.n 38), σ (.n 39)) = digestScalars cv1) :
    (∀ i < 64, LoadHolds rd (σ (.n 2)) i (σ (.n (41 + 15 * i))) ∧
      LoadHolds rd (σ (.n 40)) i (σ (.n (41 + 15 * i)))) ∧
      ∃ d, obsAllM M cv1 ((List.range 64).map fun i => σ (.n (41 + 15 * i))) = some d ∧
        (σ (.n 999), σ (.n 1000)) = digestScalars d := by
  obtain ⟨h1, h2⟩ := fsNext_runM rd1S (fun i => 41 + 15 * i) (fun i => i) (.n 2)
    (fun i => [.atom (.load (.n (41 + 15 * i)) (.n 40) i)]) (n := 64) h
    (fun i => by simp only [rd1S, Nat.add_one_ne_zero, ↓reduceIte]; omega) hcv
  refine ⟨fun i hi => ⟨(h1 i hi).1, ?_⟩, h2⟩
  have := (h1 i hi).2
  simpa [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] using this

/-- The slices over the model (`fl_slices`). -/
theorem fl_slicesM (h : ∀ i < 64, Stmt.HoldsListB M.sem C rd σ (zpBlk i) True kret)
    {cv : Digest} (hcv : (σ (.n 3120), σ (.n 3121)) = digestScalars cv) :
    (∀ i < 64, LoadHolds rd (σ (.n 2240)) (18 + i) (σ (.n (3133 + 15 * i))) ∧
      LoadHolds rd (σ (.n 6)) i (σ (.n (3133 + 15 * i)))) ∧
      ∃ d, obsAllM M cv ((List.range 64).map fun i => σ (.n (3133 + 15 * i))) = some d ∧
        (σ (.n 4091), σ (.n 4092)) = digestScalars d := by
  obtain ⟨h1, h2⟩ := fsNext_runM zpS (fun i => 3133 + 15 * i) (fun i => 18 + i) (.n 2240)
    (fun i => [.atom (.load (.n (3133 + 15 * i)) (.n 6) i)]) (n := 64) h
    (fun i => by simp only [zpS, Nat.add_one_ne_zero, ↓reduceIte]; omega) hcv
  refine ⟨fun i hi => ⟨(h1 i hi).1, ?_⟩, h2⟩
  have := (h1 i hi).2
  simpa [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB] using this

end

/-! ## The rounds over the model -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **Fixed round `i` over the model** (`frBlk_step`): its round answered (`RoundOk`), and
`scStepT`'s challenge, claim and state. -/
theorem frBlk_stepM (i : ℕ) (h : Stmt.HoldsListB M.sem C rd σ (frBlk i) True kret) {cv : Digest}
    (hcv : (σ (.n (frS i)), σ (.n (frS i + 1))) = digestScalars cv) :
    LoadHolds rd (σ (.n 11)) (6 + i) (σ (.n (frB i))) ∧
      LoadHolds rd (σ (.n 2)) (64 + 2 * i) (σ (.n (frB i + 1))) ∧
      LoadHolds rd (σ (.n 2)) (65 + 2 * i) (σ (.n (frB i + 16))) ∧
      RoundOk M (σ (.n (frB i + 1)), σ (.n (frB i + 16))) cv ∧
      LoadHolds rd (σ (.n 4)) i (scStepT M (σ (.n (frB i)))
        (σ (.n (frB i + 1)), σ (.n (frB i + 16))) (σ (.n (frC i)), cv)).1 ∧
      σ (.n (frB i + 51)) = (scStepT M (σ (.n (frB i)))
        (σ (.n (frB i + 1)), σ (.n (frB i + 16))) (σ (.n (frC i)), cv)).2.1 ∧
      (σ (.n (frB i + 39)), σ (.n (frB i + 40))) = digestScalars (scStepT M (σ (.n (frB i)))
        (σ (.n (frB i + 1)), σ (.n (frB i + 16))) (σ (.n (frC i)), cv)).2.2 := by
  simp only [frBlk, holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  obtain ⟨lB, g1l, f1⟩ := h
  obtain ⟨⟨cv1, d1, hcv1, hd1, e1⟩, f2⟩ := holdsB_fsCompressT _ _ _ _ (by decide) f1
  obtain ⟨⟨g2l, cv2, d2, hcv2, hd2, e2⟩, a31, m32, a33, sq⟩ := holdsB_fsNextT _ _ _ _ _ f2
  obtain ⟨⟨cv3, d3, hcv3, hd3, e3⟩, l47, m48, a49, m50, a51⟩ := holdsB_squeezeT _ _ _ sq
  have q1 : cv1 = cv := digestScalars_injective (hcv1.symm.trans hcv)
  subst cv1
  have c1 : (σ (.n (frB i + 14)), σ (.n (frB i + 15))) = digestScalars d1 := by
    have a := e1 12 (by omega) (by omega)
    have b := e1 13 (by omega) (by omega)
    rw [show frB i + 1 + 1 + 12 = frB i + 14 by omega] at a
    rw [show frB i + 1 + 1 + 13 = frB i + 15 by omega] at b
    exact Prod.ext a b
  have q2 : cv2 = d1 := digestScalars_injective (hcv2.symm.trans c1)
  subst cv2
  have c2 : (σ (.n (frB i + 29)), σ (.n (frB i + 30))) = digestScalars d2 := by
    have a := e2 12 (by omega) (by omega)
    have b := e2 13 (by omega) (by omega)
    rw [show frB i + 16 + 1 + 12 = frB i + 29 by omega] at a
    rw [show frB i + 16 + 1 + 13 = frB i + 30 by omega] at b
    exact Prod.ext a b
  have q3 : cv3 = d2 := digestScalars_injective (hcv3.symm.trans c2)
  subst cv3
  obtain ⟨hok, rfl, rfl, rfl⟩ :=
    roundOk_of (M := M) (g := (σ (.n (frB i + 1)), σ (.n (frB i + 16)))) hd1 hd2 hd3
  have c3 : (σ (.n (frB i + 39)), σ (.n (frB i + 40))) = digestScalars
      (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) := by
    have a := e3 5 (by omega)
    have b := e3 6 (by omega)
    rw [show frB i + 34 + 5 = frB i + 39 by omega] at a
    rw [show frB i + 34 + 6 = frB i + 40 by omega] at b
    exact Prod.ext a b
  have ch : σ (.n (frB i + 47)) =
      challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) := by
    have a := e3 13 (by omega)
    rw [show frB i + 34 + 13 = frB i + 47 by omega] at a
    exact a
  refine ⟨lB, g1l, g2l, hok, ?_, ?_, c3⟩
  · show LoadHolds rd (σ (.n 4)) i
      (challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))))
    rw [← ch]; exact l47
  · show σ (.n (frB i + 51)) = σ (.n (frC i)) + σ (.n (frB i)) * (σ (.n (frB i + 1)) +
      σ (.n (frB i + 16))) +
      challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) *
        (σ (.n (frB i + 1)) +
          challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (frB i + 1)))) (σ (.n (frB i + 16))))) *
            σ (.n (frB i + 16)))
    rw [← ch, a51, m50, a49, m48, a33, m32, a31]

/-- **Lincheck round `i` over the model** (`lcBlk_step`). -/
theorem lcBlk_stepM (i : ℕ) (h : Stmt.HoldsListB M.sem C rd σ (lcBlk i) True kret) {cv : Digest}
    (hcv : (σ (.n (lcS i)), σ (.n (lcS i + 1))) = digestScalars cv) :
    LoadHolds rd (σ (.n 2240)) (2 + 2 * i) (σ (.n (lcB i))) ∧
      LoadHolds rd (σ (.n 2240)) (3 + 2 * i) (σ (.n (lcB i + 15))) ∧
      RoundOk M (σ (.n (lcB i)), σ (.n (lcB i + 15))) cv ∧
      LoadHolds rd (σ (.n 5)) i
        (lcStepT M (σ (.n (lcB i)), σ (.n (lcB i + 15))) (σ (.n (lcC i)), cv)).1 ∧
      σ (.n (lcB i + 48)) =
        (lcStepT M (σ (.n (lcB i)), σ (.n (lcB i + 15))) (σ (.n (lcC i)), cv)).2.1 ∧
      (σ (.n (lcB i + 36)), σ (.n (lcB i + 37))) = digestScalars
        (lcStepT M (σ (.n (lcB i)), σ (.n (lcB i + 15))) (σ (.n (lcC i)), cv)).2.2 := by
  simp only [lcBlk, holdsListB_append, Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  obtain ⟨g1l, f1⟩ := h
  obtain ⟨⟨cv1, d1, hcv1, hd1, e1⟩, f2⟩ := holdsB_fsCompressT _ _ _ _ (by decide) f1
  obtain ⟨⟨g2l, cv2, d2, hcv2, hd2, e2⟩, a30, sq⟩ := holdsB_fsNextT _ _ _ _ _ f2
  obtain ⟨⟨cv3, d3, hcv3, hd3, e3⟩, l44, m45, a46, m47, a48⟩ := holdsB_squeezeT _ _ _ sq
  have q1 : cv1 = cv := digestScalars_injective (hcv1.symm.trans hcv)
  subst cv1
  have c1 : (σ (.n (lcB i + 13)), σ (.n (lcB i + 14))) = digestScalars d1 := by
    have a := e1 12 (by omega) (by omega)
    have b := e1 13 (by omega) (by omega)
    rw [show lcB i + 1 + 12 = lcB i + 13 by omega] at a
    rw [show lcB i + 1 + 13 = lcB i + 14 by omega] at b
    exact Prod.ext a b
  have q2 : cv2 = d1 := digestScalars_injective (hcv2.symm.trans c1)
  subst cv2
  have c2 : (σ (.n (lcB i + 28)), σ (.n (lcB i + 29))) = digestScalars d2 := by
    have a := e2 12 (by omega) (by omega)
    have b := e2 13 (by omega) (by omega)
    rw [show lcB i + 15 + 1 + 12 = lcB i + 28 by omega] at a
    rw [show lcB i + 15 + 1 + 13 = lcB i + 29 by omega] at b
    exact Prod.ext a b
  have q3 : cv3 = d2 := digestScalars_injective (hcv3.symm.trans c2)
  subst cv3
  obtain ⟨hok, rfl, rfl, rfl⟩ :=
    roundOk_of (M := M) (g := (σ (.n (lcB i)), σ (.n (lcB i + 15)))) hd1 hd2 hd3
  have c3 : (σ (.n (lcB i + 36)), σ (.n (lcB i + 37))) = digestScalars
      (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) := by
    have a := e3 5 (by omega)
    have b := e3 6 (by omega)
    rw [show lcB i + 31 + 5 = lcB i + 36 by omega] at a
    rw [show lcB i + 31 + 6 = lcB i + 37 by omega] at b
    exact Prod.ext a b
  have ch : σ (.n (lcB i + 44)) =
      challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) := by
    have a := e3 13 (by omega)
    rw [show lcB i + 31 + 13 = lcB i + 44 by omega] at a
    exact a
  refine ⟨g1l, g2l, hok, ?_, ?_, c3⟩
  · show LoadHolds rd (σ (.n 5)) i
      (challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))))
    rw [← ch]; exact l44
  · show σ (.n (lcB i + 48)) = σ (.n (lcB i)) +
      challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) *
        (σ (.n (lcC i)) + σ (.n (lcB i + 15)) +
          challengeOf (sqCvT M (obsCvT M (obsCvT M cv (σ (.n (lcB i)))) (σ (.n (lcB i + 15))))) *
            σ (.n (lcB i + 15)))
    rw [← ch, a48, m47, a46, m45, a30]

end

/-- **The zerocheck's rounds over the model** (`fl_rounds`): the seven fixed rounds then
`__loop82`'s `τ + 1`, each a round of `scStT` with its hashes answered. -/
theorem fl_roundsM {rd : Reader} {σ : Val} {kret : List E → Prop} {τ : ℕ} (hτ : τ < 29)
    (e : ℕ → E) (st0 : E × Digest)
    (hfr : ∀ i < 7, Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (frBlk i) True kret)
    (he : ∀ j < τ + 8, LoadHolds rd (σ (.n 11)) (6 + j) (e j))
    (h0 : σ (.n 1847) = st0.1) (hs0 : (σ (.n 1006), σ (.n 1007)) = digestScalars st0.2)
    (l28 : LoadHolds rd (σ (.n 2220)) 28 (σ (.n 2203)))
    (l29 : LoadHolds rd (σ (.n 2220)) 29 (σ (.n 2204)))
    (l30 : LoadHolds rd (σ (.n 2220)) 30 (σ (.n 2) * gen ^ 78))
    (l31 : LoadHolds rd (σ (.n 2220)) 31 (σ (.n 2215)))
    (hloop : coreProgram.RelB M.sem rd "__loop82"
      [gen ^ 7, gen ^ (τ + 8), σ (.n 2220), σ (.n 11), σ (.n 4)] [])
    (lE0 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8)) (σ (.n 2237)))
    (lE1 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 1) (σ (.n 2238)))
    (lE3 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 3) (σ (.n 2239)))
    (lE2 : LoadHolds rd (σ (.n 2220)) (4 * (τ + 8) + 2) (σ (.n 2240))) :
    ∃ g : ℕ → E × E,
      (∀ j < τ + 8, LoadHolds rd (σ (.n 2)) (64 + 2 * j) (g j).1 ∧
        LoadHolds rd (σ (.n 2)) (65 + 2 * j) (g j).2 ∧
        LoadHolds rd (σ (.n 4)) j (scChT M e g st0 j) ∧ RoundOk M (g j) (scStT M e g st0 j).2) ∧
      σ (.n 2239) = (scStT M e g st0 (τ + 8)).1 ∧
      (σ (.n 2237), σ (.n 2238)) = digestScalars (scStT M e g st0 (τ + 8)).2 ∧
      σ (.n 2240) = σ (.n 2) * gen ^ (64 + 2 * (τ + 8)) := by
  -- the loop's iterations
  obtain ⟨m, hm, hN, hfirst, hall⟩ :=
    loopB_sound (loop82_stepM rd (gen ^ (τ + 8)) (σ (.n 2220)) (σ (.n 11)) (σ (.n 4))) 7 hloop
  have hm' : m = τ + 8 := by
    rcases Nat.lt_or_ge (τ + 8) m with h | h
    · exact absurd rfl (hfirst (τ + 8) (by omega) h)
    · exact (gen_pow_inj' (by omega) (by omega) hN).symm
  subst hm'
  obtain ⟨F, hF⟩ := exists_fun_of_forall (n := τ + 8) (α := Digest × E × E × E × E × E)
    (P := fun j x => 7 ≤ j →
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 0 (digestScalars x.1).1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 1 (digestScalars x.1).2 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 2 x.2.1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 3 x.2.2.1 ∧
      LoadHolds rd (σ (.n 11) * gen ^ j) 6 x.2.2.2.1 ∧ LoadHolds rd x.2.1 0 x.2.2.2.2.1 ∧
      LoadHolds rd x.2.1 1 x.2.2.2.2.2 ∧
      RoundOk M (x.2.2.2.2.1, x.2.2.2.2.2) x.1 ∧
      LoadHolds rd (σ (.n 4) * gen ^ j) 0
        (scStepT M x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 4
        (digestScalars (scStepT M x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).2.2).1 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 5
        (digestScalars (scStepT M x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).2.2).2 ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 6 (x.2.1 * gen ^ 2) ∧
      LoadHolds rd (σ (.n 2220) * gen ^ (4 * j)) 7
        (scStepT M x.2.2.2.1 (x.2.2.2.2.1, x.2.2.2.2.2) (x.2.2.1, x.1)).2.1) fun j hj => by
    by_cases h7 : 7 ≤ j
    · obtain ⟨cv, cur, claim, e', g1, g2, a0, a1, a2, a3, a4, a5, a6, hok, a7, a8, a9, a10,
        a11⟩ := hall j h7 hj
      rw [gen_pow_quad] at a0 a1 a2 a3 a8 a9 a10 a11
      exact ⟨(cv, cur, claim, e', g1, g2), fun _ => ⟨a0, a1, a2, a3, a4, a5, a6, hok, a7, a8, a9,
        a10, a11⟩⟩
    · exact ⟨default, fun h => absurd h h7⟩
  set g : ℕ → E × E := fun j => if j < 7 then (σ (.n (frB j + 1)), σ (.n (frB j + 16)))
    else ((F j).2.2.2.2.1, (F j).2.2.2.2.2) with hg
  refine ⟨g, ?_⟩
  -- the fixed rounds
  have fixed : ∀ i ≤ 7, σ (.n (frC i)) = (scStT M e g st0 i).1 ∧
      (σ (.n (frS i)), σ (.n (frS i + 1))) = digestScalars (scStT M e g st0 i).2 ∧
      (∀ j < i, LoadHolds rd (σ (.n 2)) (64 + 2 * j) (g j).1 ∧
        LoadHolds rd (σ (.n 2)) (65 + 2 * j) (g j).2 ∧
        LoadHolds rd (σ (.n 4)) j (scChT M e g st0 j) ∧ RoundOk M (g j) (scStT M e g st0 j).2) := by
    intro i hi
    induction i with
    | zero => exact ⟨h0, hs0, fun j hj => absurd hj (by omega)⟩
    | succ i ih =>
      obtain ⟨c, sv, prev⟩ := ih (by omega)
      obtain ⟨lB, g1l, g2l, hok, lch, hc, hsv⟩ := frBlk_stepM i (hfr i (by omega)) sv
      have eB : σ (.n (frB i)) = e i := loadHolds_unique lB (he i (by omega))
      have eg : (σ (.n (frB i + 1)), σ (.n (frB i + 16))) = g i := by
        simp only [hg, show i < 7 by omega, ↓reduceIte]
      rw [eB, eg, c, Prod.mk.eta] at lch hc hsv
      rw [eg] at hok
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · rw [show frC (i + 1) = frB i + 51 by
          simp only [frC, frB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hc
      · rw [show frS (i + 1) = frB i + 39 by
          simp only [frS, frB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hsv
      · rcases Nat.lt_or_ge j i with h | h
        · exact prev j h
        · obtain rfl : j = i := by omega
          rw [← eg]
          exact ⟨g1l, g2l, lch, by rw [eg]; exact hok⟩
  -- the sampled rounds
  obtain ⟨c7, sv7, prev7⟩ := fixed 7 le_rfl
  have hrow : ∀ j, 7 ≤ j → j ≤ τ + 8 →
      LoadHolds rd (σ (.n 2220)) (4 * j) (digestScalars (scStT M e g st0 j).2).1 ∧
      LoadHolds rd (σ (.n 2220)) (4 * j + 1) (digestScalars (scStT M e g st0 j).2).2 ∧
      LoadHolds rd (σ (.n 2220)) (4 * j + 2) (σ (.n 2) * gen ^ (64 + 2 * j)) ∧
      LoadHolds rd (σ (.n 2220)) (4 * j + 3) (scStT M e g st0 j).1 ∧
      (∀ i < j, LoadHolds rd (σ (.n 2)) (64 + 2 * i) (g i).1 ∧
        LoadHolds rd (σ (.n 2)) (65 + 2 * i) (g i).2 ∧
        LoadHolds rd (σ (.n 4)) i (scChT M e g st0 i) ∧ RoundOk M (g i) (scStT M e g st0 i).2) := by
    intro j h7 hj
    induction j, h7 using Nat.le_induction with
    | base =>
      have s1 : σ (.n 2203) = (digestScalars (scStT M e g st0 7).2).1 := congrArg Prod.fst sv7
      have s2 : σ (.n 2204) = (digestScalars (scStT M e g st0 7).2).2 := congrArg Prod.snd sv7
      rw [← s1, ← s2, ← c7]
      exact ⟨l28, l29, l30, l31, prev7⟩
    | succ j h7 ih =>
      obtain ⟨r0, r1, r2, r3, prev⟩ := ih (by omega)
      obtain ⟨a0, a1, a2, a3, a4, a5, a6, hok, a7, a8, a9, a10, a11⟩ := hF j (by omega) h7
      have ecv : (F j).1 = (scStT M e g st0 j).2 := digestScalars_injective
        (Prod.ext (loadHolds_unique (lh_at a0 rfl) r0) (loadHolds_unique (lh_at a1 rfl) r1))
      have ecur : (F j).2.1 = σ (.n 2) * gen ^ (64 + 2 * j) := loadHolds_unique (lh_at a2 rfl) r2
      have ecl : (F j).2.2.1 = (scStT M e g st0 j).1 := loadHolds_unique (lh_at a3 rfl) r3
      have ee : (F j).2.2.2.1 = e j := loadHolds_unique (lh_at a4 (by omega)) (he j (by omega))
      have eg : ((F j).2.2.2.2.1, (F j).2.2.2.2.2) = g j := by
        simp only [hg, show ¬ j < 7 by omega, ↓reduceIte]
      rw [ecv, ecl, ee, eg, Prod.mk.eta] at a7 a8 a9 a11
      rw [ecv, eg] at hok
      rw [ecur] at a5 a6 a10
      refine ⟨lh_at a8 (by ring), lh_at a9 (by ring), ?_, lh_at a11 (by ring), fun i hi => ?_⟩
      · have := lh_at a10 (show 4 * j + 6 = 4 * (j + 1) + 2 by ring)
        rwa [mul_assoc, ← pow_add, show 64 + 2 * j + 2 = 64 + 2 * (j + 1) by ring] at this
      · rcases Nat.lt_or_ge i j with h | h
        · exact prev i h
        · obtain rfl : i = j := by omega
          rw [← eg]
          refine ⟨?_, ?_, lh_at a7 (by ring), by rw [eg]; exact hok⟩
          · have := lh_off a5
            rw [show 64 + 2 * i + 0 = 64 + 2 * i by ring] at this; exact this
          · have := lh_off a6
            rw [show 64 + 2 * i + 1 = 65 + 2 * i by ring] at this; exact this
  obtain ⟨r0, r1, r2, r3, words⟩ := hrow (τ + 8) (by omega) le_rfl
  refine ⟨words, loadHolds_unique lE3 r3, Prod.ext (loadHolds_unique lE0 r0)
    (loadHolds_unique lE1 r1), loadHolds_unique lE2 r2⟩

/-! ## The final evaluations, `alpha` and the lincheck over the model -/

section
variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- The final evaluations over the model (`fl_s8`). -/
theorem fl_s8M (h : Stmt.HoldsListB M.sem C rd σ flS8 True kret) {cv : Digest}
    (hcv : (σ (.n 2237), σ (.n 2238)) = digestScalars cv) :
    LoadHolds rd (σ (.n 2240)) 0 (σ (.n 2241)) ∧ LoadHolds rd (σ (.n 2240)) 1 (σ (.n 2256)) ∧
      ∃ d1 d2, obsCvM M cv (σ (.n 2241)) = some d1 ∧ obsCvM M d1 (σ (.n 2256)) = some d2 ∧
        (σ (.n 2269), σ (.n 2270)) = digestScalars d2 ∧
        σ (.n 2272) = σ (.n 2239) + σ (.n 2241) * σ (.n 2256) := by
  simp only [flS8] at h
  rw [hl_appB rfl, hl_appB rfl] at h
  obtain ⟨⟨f1, f2⟩, h⟩ := h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  obtain ⟨m, a⟩ := h
  obtain ⟨l1, d1, hd1, c1⟩ := fsNext_chainM f1 hcv
  obtain ⟨l2, d2, hd2, c2⟩ := fsNext_chainM f2 c1
  exact ⟨l1, l2, d1, d2, hd1, hd2, c2, by rw [a, m]⟩

/-- `alpha` and the lincheck's claim over the model (`fl_s10`). -/
theorem fl_s10M (h : Stmt.HoldsListB M.sem C rd σ flS10 True kret) {cv : Digest}
    (hcv : (σ (.n 2269), σ (.n 2270)) = digestScalars cv) :
    ∃ d, sqCvM M cv = some d ∧ σ (.n 2733) = challengeOf d ∧
      (σ (.n 2725), σ (.n 2726)) = digestScalars d ∧
      σ (.n 2734) = σ (.n 2733) ^ 2 ∧ σ (.n 2735) = σ (.n 2733) ^ 3 ∧
      σ (.n 2740) = σ (.n 2241) + σ (.n 2733) * σ (.n 2256) + σ (.n 2733) ^ 2 * σ (.n 2272) +
        σ (.n 2733) ^ 3 := by
  simp only [flS10] at h
  rw [hl_appB rfl] at h
  obtain ⟨⟨-, hsq⟩, h⟩ := h
  simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at h
  obtain ⟨m34, m35, m36, a37, m38, a39, a40⟩ := h
  obtain ⟨d, hd, c, ch⟩ := squeeze_chainM hsq hcv
  have e2 : σ (.n 2734) = σ (.n 2733) ^ 2 := by rw [m34, sq]
  have e3 : σ (.n 2735) = σ (.n 2733) ^ 3 := by rw [m35, e2]; ring
  exact ⟨d, hd, ch, c, e2, e3, by rw [a40, a39, a37, m38, m36, e2, e3]⟩

/-- **The lincheck's eight rounds over the model** (`fl_lincheck`): `lcStT`, each round
answered. -/
theorem fl_lincheckM (h : ∀ i < 8, Stmt.HoldsListB M.sem C rd σ (lcBlk i) True kret)
    {cv : Digest} (hcv : (σ (.n 2725), σ (.n 2726)) = digestScalars cv) :
    (∀ i < 8, LoadHolds rd (σ (.n 2240)) (2 + 2 * i) (σ (.n (lcB i))) ∧
      LoadHolds rd (σ (.n 2240)) (3 + 2 * i) (σ (.n (lcB i + 15))) ∧
      LoadHolds rd (σ (.n 5)) i
        (lcChT M (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) i) ∧
      RoundOk M (σ (.n (lcB i)), σ (.n (lcB i + 15)))
        (lcStT M (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) i).2) ∧
      σ (.n 3132) =
        (lcStT M (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) 8).1 ∧
      (σ (.n 3120), σ (.n 3121)) = digestScalars
        (lcStT M (fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))) (σ (.n 2740), cv) 8).2 := by
  set g : ℕ → E × E := fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15)))
  have key : ∀ i ≤ 8, σ (.n (lcC i)) = (lcStT M g (σ (.n 2740), cv) i).1 ∧
      (σ (.n (lcS i)), σ (.n (lcS i + 1))) = digestScalars (lcStT M g (σ (.n 2740), cv) i).2 ∧
      (∀ j < i, LoadHolds rd (σ (.n 2240)) (2 + 2 * j) (σ (.n (lcB j))) ∧
        LoadHolds rd (σ (.n 2240)) (3 + 2 * j) (σ (.n (lcB j + 15))) ∧
        LoadHolds rd (σ (.n 5)) j (lcChT M g (σ (.n 2740), cv) j) ∧
        RoundOk M (g j) (lcStT M g (σ (.n 2740), cv) j).2) := by
    intro i hi
    induction i with
    | zero => exact ⟨rfl, hcv, fun j hj => absurd hj (by omega)⟩
    | succ i ih =>
      obtain ⟨c, sv, prev⟩ := ih (by omega)
      obtain ⟨g1l, g2l, hok, lch, hc, hsv⟩ := lcBlk_stepM i (h i (by omega)) sv
      rw [c, Prod.mk.eta] at lch hc hsv
      refine ⟨?_, ?_, fun j hj => ?_⟩
      · rw [show lcC (i + 1) = lcB i + 48 by
          simp only [lcC, lcB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hc
      · rw [show lcS (i + 1) = lcB i + 36 by
          simp only [lcS, lcB, Nat.add_one_ne_zero, ↓reduceIte]; omega]; exact hsv
      · rcases Nat.lt_or_ge j i with hlt | hge
        · exact prev j hlt
        · obtain rfl : j = i := by omega
          exact ⟨g1l, g2l, lch, hok⟩
  obtain ⟨c8, s8, words⟩ := key 8 le_rfl
  exact ⟨words, c8, s8⟩

end

/-! ## Soundness over the model -/

set_option maxHeartbeats 2000000 in
/-- **`verify_flock` is sound over the model** (`verify_flock_sound`): `SoundFlockM`. -/
theorem verify_flock_model (rd : Reader) : SoundFlockM M rd := by
  intro τ fs0 fs1 cur zchis lrs zpart rets hτ h
  obtain ⟨σ, hp, hseg, hret⟩ := verify_flock_holdsB h
  simp only [List.cons.injEq, and_true] at hp
  obtain ⟨e0, e1, e2, e3, e4, e5, e6⟩ := hp
  simp only [flSegs, List.forall_mem_cons] at hseg
  obtain ⟨g0, g1, g2, g3, g4, g5, g6, g7, g8, g9, g10, g11, g12, g13, g14, g15, g16, -⟩ := hseg
  rw [holdsListB_flatten_range 64 rd1Blk (fun _ => rfl), and_true] at g1
  rw [holdsListB_iff_of_noBlake lag64_hi_noBlake, holds_lag64T, and_true] at g3
  rw [holdsListB_iff_of_noBlake lag64_lo_noBlake, holds_lag64T, and_true] at g9
  rw [holdsListB_flatten_range 64 ipBlk (fun i => by unfold ipBlk; split <;> rfl), and_true] at g4
  rw [holdsListB_flatten_range 7 frBlk (fun _ => rfl), and_true] at g6
  rw [holdsListB_flatten_range 8 lcBlk (fun _ => rfl), and_true] at g11
  rw [holdsListB_flatten_range 64 zpBlk (fun _ => rfl), and_true] at g12
  rw [holdsListB_flatten_range 8 cpeBlk (fun i => by unfold cpeBlk; split <;> rfl),
    and_true] at g14
  rw [holdsListB_flatten_range 64 csBlk (fun i => by unfold csBlk; split <;> rfl),
    and_true] at g15
  rw [holdsListB_iff_of_noBlake flP0_noBlake] at g0
  rw [holdsListB_iff_of_noBlake flP5_noBlake] at g5
  rw [holdsListB_iff_of_noBlake flP7_noBlake] at g7
  rw [holdsListB_iff_of_noBlake flP13_noBlake] at g13
  rw [holdsListB_iff_of_noBlake flPEnd_noBlake] at g16
  have g4' := fun i hi => (holdsListB_iff_of_noBlake (ipBlk_noBlake i) _ _).mp (g4 i hi)
  have g14' := fun t ht => (holdsListB_iff_of_noBlake (cpeBlk_noBlake t) _ _).mp (g14 t ht)
  have g15' := fun i hi => (holdsListB_iff_of_noBlake (csBlk_noBlake i) _ _).mp (g15 i hi)
  -- the prelude and the sampled coordinates
  obtain ⟨h7, h8, hzr, l26, l27, hc81, l38, l39⟩ := fl_p0 e3 g0
  have hloop81 := hc81 (gen_pow_ne_of_lt (by omega) (by omega))
  obtain ⟨cv0, hcv0⟩ : ∃ cv0, (σ (.n 0), σ (.n 1)) = digestScalars cv0 := by
    obtain ⟨m, hm, -, -, hall⟩ := loopB_sound (loop81_stepM rd _ _ _) 13 hloop81
    obtain ⟨cv, a0, a1, -⟩ := hall 13 le_rfl hm
    rw [gen_pow_sq] at a0 a1
    exact ⟨cv, Prod.ext (by rw [← h7]; exact loadHolds_unique l26 (lh_at a0 rfl))
      (by rw [← h8]; exact loadHolds_unique l27 (lh_at a1 rfl))⟩
  have l0 : LoadHolds rd (σ (.n 24)) 26 (digestScalars cv0).1 := by
    rw [← congrArg Prod.fst hcv0, ← h7]; exact l26
  have l1 : LoadHolds rd (σ (.n 24)) 27 (digestScalars cv0).2 := by
    rw [← congrArg Prod.snd hcv0, ← h8]; exact l27
  obtain ⟨hsam, k0, k1⟩ := fl_sampledM (M := M) hτ l0 l1 hloop81
  have hcv1 : (σ (.n 38), σ (.n 39)) = digestScalars ((sqCvT M)^[τ + 1] cv0) :=
    Prod.ext (loadHolds_unique l38 k0) (loadHolds_unique l39 k1)
  have hsamM := sqAllM_iter (τ + 1) cv0 (fun t ht => (hsam t (by omega)).2)
  set sam := (List.range (τ + 1)).map fun t => challengeOf (sqCvT M ((sqCvT M)^[t] cv0))
    with hsamdef
  -- round 1, the skip challenge, the interpolation
  obtain ⟨hr1, cvP, hP, hcv2⟩ := fl_round1M g1 hcv1
  set p := (List.range 64).map fun i => σ (.n (41 + 15 * i)) with hpdef
  have hpl : p.length = 64 := by simp [p]
  obtain ⟨cz, hzq, hcv3, hz⟩ := squeeze_chainM g2 hcv2
  set z := challengeOf cz with hzdef
  have hz' : σ (.n 1014) = z := hz
  have hnum := lag64_phi (σ := σ) (b := 64) (by norm_num) g3
  rw [lgOut_hi] at hnum
  obtain ⟨hsh, hsum⟩ := fl_interp g4' (p := fun i => σ (.n (41 + 15 * i)))
    (fun i hi => (hr1 i hi).2)
  simp only [flP5, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at g5
  obtain ⟨c1845, m1846, m1847, -, -, -, -⟩ := g5
  have hvP : σ (.n 1847) = lagrangeInterpolate 128 (List.replicate 64 0 ++ p) z := by
    rw [interp_eq _ p hpl, m1847, m1846, c1845, hsh, hsum, hz']
    refine congrArg (fun x => x * _) (Finset.sum_congr rfl fun i hi => ?_)
    rw [hnum i (Finset.mem_range.mp hi), hz', getD_map_range _ _ (Finset.mem_range.mp hi)]
  -- the rounds
  obtain ⟨l28, l29, l30, l31, hc82, lE0, lE1, lE3, lE2⟩ := fl_p7 e3 g7
  have hloop82 := hc82 (gen_pow_ne_of_lt (by omega) (by omega))
  set e : ℕ → E := fun j => (fixedChallenges ++ sam).getD j 0 with hedef
  set st0 : E × Digest := (lagrangeInterpolate 128 (List.replicate 64 0 ++ p) z, cz) with hst0
  have he : ∀ j < τ + 8, LoadHolds rd (σ (.n 11)) (6 + j) (e j) := by
    intro j hj
    rcases Nat.lt_or_ge j 7 with h7' | h7'
    · have := hzr j h7'
      rw [fixed_words] at this
      simp only [e]
      rw [getD_append_lt (by rw [fixedChallenges_length]; exact h7')]
      exact this
    · obtain ⟨t, rfl⟩ : ∃ t, j = 7 + t := ⟨j - 7, by omega⟩
      have := (hsam t (by omega)).1
      simp only [e]
      rw [show 7 + t = fixedChallenges.length + t by rw [fixedChallenges_length], getD_append_ge,
        hsamdef, getD_map_range _ _ (by omega),
        show 6 + (fixedChallenges.length + t) = 13 + t by rw [fixedChallenges_length]; omega]
      exact this
  obtain ⟨g, hwords, hclaim, hst, hcur⟩ := fl_roundsM hτ e st0 g6 he (by rw [hvP])
    (by exact hcv3) l28 l29 l30 l31 hloop82 lE0 lE1 lE3 lE2
  -- the final evaluations, alpha, the lincheck, the slices
  obtain ⟨la, lb, ca, cb, hca, hcb, hcv5, hc⟩ := fl_s8M g8 hst
  have hcn := lag64_phi (σ := σ) (b := 0) (by norm_num) g9
  rw [lgOut_lo] at hcn
  obtain ⟨cα, hcα, hα, hcv6, h2734, h2735, h2740⟩ := fl_s10M g10 hcv5
  obtain ⟨hlc, hrlc, hcv7⟩ := fl_lincheckM g11 hcv6
  set g' : ℕ → E × E := fun i => (σ (.n (lcB i)), σ (.n (lcB i + 15))) with hg'
  set st0' : E × Digest := (σ (.n 2740), cα) with hst0'
  obtain ⟨hsl, cv8, hS, hcv8⟩ := fl_slicesM g12 hcv7
  have hpin := fl_p13 g13 (rc := lcChT M g' st0') (fun j hj => (hlc j hj).2.2.1)
    (hsl 0 (by omega)).2
  have hcpe := fl_cpe g14' (chi := scChT M e g st0) (rc := lcChT M g' st0')
    (fun t ht => (hwords t (by omega)).2.2.1) (fun j hj => (hlc j hj).2.2.1)
  have hcs := fl_cs g15' (s := fun i => σ (.n (3133 + 15 * i))) (fun i hi => (hsl i hi).2)
  obtain ⟨hfin, r69, r70, r73, r74, r75, r76⟩ := fl_end g16
  -- the outcome
  set chi := (List.range (τ + 8)).map (scChT M e g st0) with hchi
  set rcs := (List.range 8).map (lcChT M g' st0') with hrcs
  set sl := (List.range 64).map fun i => σ (.n (3133 + 15 * i)) with hsl'
  set ys := roundWords g (τ + 8) 0 with hys
  set zs := roundWords g' 8 0 with hzs
  have hchil : chi.length = τ + 8 := by simp [chi]
  have hrcsl : rcs.length = 8 := by simp [rcs]
  have hsll : sl.length = 64 := by simp [sl]
  have hysl : ys.length = 2 * (τ + 8) := roundWords_length _ _ _
  have hzsl : zs.length = 2 * 8 := roundWords_length _ _ _
  have h2240 : σ (.n 2240) = cur * gen ^ (64 + 2 * (τ + 8)) := by rw [hcur, e2]
  have h2739 : σ (.n 2239) = (scStT M e g st0 (τ + 8)).1 := hclaim
  have hα' : σ (.n 2733) = challengeOf cα := hα
  have h2740' : σ (.n 2740) = σ (.n 2241) + challengeOf cα * σ (.n 2256) +
      challengeOf cα ^ 2 * ((scStT M e g st0 (τ + 8)).1 + σ (.n 2241) * σ (.n 2256)) +
      challengeOf cα ^ 3 := by
    rw [h2740, hc, h2739, hα']
  refine ⟨cv0, p ++ ys ++ [σ (.n 2241), σ (.n 2256)] ++ zs ++ sl, cv8, z,
    σ (.n 2733), σ (.n 2719), chi, rcs, sl, by rw [← e0, ← e1]; exact hcv0, ?_,
    by rw [hchil]; omega, hrcsl, hsll, ?_, ?_, ?_, fun ev hmv => ?_, ?_⟩
  · -- the words at the cursor
    rw [readsAt_append_iff, readsAt_append_iff, readsAt_append_iff, readsAt_append_iff]
    refine ⟨⟨⟨⟨?_, fun k hk => ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩, fun k hk => ?_⟩
    · refine readsAt_iff_getD.mpr fun k hk => ?_
      rw [hpl] at hk
      rw [← e2, getD_map_range _ _ hk]
      exact (hr1 k hk).1
    · rw [hysl] at hk
      rw [roundWords_getD g _ _ _ hk, ← e2, hpl]
      obtain ⟨w1, w2, -⟩ := hwords (k / 2) (by omega)
      split_ifs with h2
      · rw [show 64 + k = 64 + 2 * (k / 2) by omega]; simpa using w1
      · rw [show 64 + k = 65 + 2 * (k / 2) by omega]; simpa using w2
    · have hk' : k < 2 := by simpa using hk
      rw [List.length_append, hpl, hysl]
      have l2 := lh_at (h2240 ▸ la) (show 64 + 2 * (τ + 8) + 0 = 64 + 2 * (τ + 8) + k - k by omega)
      have l3 := lh_at (h2240 ▸ lb) rfl
      interval_cases k
      · simpa using l2
      · exact l3
    · rw [hzsl] at hk
      rw [List.length_append, List.length_append, hpl, hysl, roundWords_getD g' _ _ _ hk,
        List.length_cons, List.length_cons, List.length_nil, Nat.zero_add]
      obtain ⟨w1, w2, -⟩ := hlc (k / 2) (by omega)
      rw [h2240] at w1 w2
      have w1' := lh_off w1
      have w2' := lh_off w2
      split_ifs with h2
      · simp only [Nat.zero_add]; exact lh_eq w1' (by omega)
      · simp only [Nat.zero_add]; exact lh_eq w2' (by omega)
    · rw [hsll] at hk
      rw [List.length_append, List.length_append, List.length_append, hpl, hysl, hzsl,
        getD_map_range _ _ hk, List.length_cons, List.length_cons, List.length_nil]
      have w := (hsl k hk).1
      rw [h2240] at w
      exact lh_eq (lh_off w) (by omega)
  · -- the zerocheck's point
    rw [← e4]
    refine readsAt_iff_getD.mpr fun k hk => ?_
    rw [hchil] at hk
    rw [getD_map_range _ _ hk]
    exact (hwords k hk).2.2.1
  · -- the lincheck's challenges
    rw [← e5]
    refine readsAt_iff_getD.mpr fun k hk => ?_
    rw [hrcsl] at hk
    rw [getD_map_range _ _ hk]
    exact (hlc k hk).2.2.1
  · -- the slices
    rw [← e6]
    refine readsAt_iff_getD.mpr fun k hk => ?_
    rw [hsll] at hk
    rw [getD_map_range _ _ hk]
    exact (hsl k hk).2
  · -- the run
    have hlen : (fixedChallenges ++ sam).length = τ + 8 := by
      rw [List.length_append, fixedChallenges_length, hsamdef]; simp; omega
    refine runs_verifyFlockM ev τ cv0 sam _ hsamM p hpl cvP hP cz hzq ys chi
      (scStT M e g st0 (τ + 8)).1 (scStT M e g st0 (τ + 8)).2
      (fun rest os roots => ?_) (σ (.n 2241)) (σ (.n 2256)) ca cb cα hca hcb hcα zs rcs
      (lcStT M g' st0' 8).1 (lcStT M g' st0' 8).2 (fun rest os roots => ?_) sl hsll cv8 hS
      (σ (.n 2719)) ?_ ?_
    · have := runs_sumcheck_eqM e g st0 (τ + 8) 0 rest os roots
        (fun j hj => by rw [Nat.zero_add]; exact (hwords j hj).2.2.2)
      simp only [Nat.zero_add] at this
      rw [map_some_range, hlen]
      exact this
    · have := runs_sumcheck_plainM g' st0' 8 0 rest os roots
        (fun j hj => by rw [Nat.zero_add]; exact (hlc j hj).2.2.2)
      simp only [Nat.zero_add] at this
      rw [← h2740', show List.replicate 8 (none : Option E) = (List.range 8).map (fun _ => none)
        from rfl]
      exact this
    · rw [hα'] at hmv; exact hmv
    · have hdot : σ (.n 4362) * word 11666641484232641359 0 0 = dot (lagrangeWeights 64 z) sl := by
        rw [hcs, ← cslice_eq z sl hsll]
        refine congrArg (fun x => x * _) (Finset.sum_congr rfl fun i hi => ?_)
        rw [hcn i (Finset.mem_range.mp hi), hz', getD_map_range _ _ (Finset.mem_range.mp hi)]
        simp only [Nat.zero_add]
      have heq : eqEval (chi.take 8) rcs.reverse =
          ∏ t ∈ Finset.range 8, (1 + scChT M e g st0 t + lcChT M g' st0' (7 - t)) := by
        rw [Main.eqEval_prod _ _ 8 (by simp [hchil]) (by simp [hrcsl])]
        refine Finset.prod_congr rfl fun t ht => ?_
        have ht' := Finset.mem_range.mp ht
        rw [List.getD_eq_getElem?_getD, List.getElem?_take, ite_pos' ht',
          ← List.getD_eq_getElem?_getD,
          getD_map_range _ _ (by omega), List.getD_eq_getElem?_getD,
          List.getElem?_reverse (by omega), hrcsl, ← List.getD_eq_getElem?_getD,
          getD_map_range _ _ (by omega), show 8 - 1 - t = 7 - t by omega]
      rw [← hα', ← hrlc, hfin, hpin, hcpe, h2735, h2734, hdot, heq,
        colWeight_pin rcs sl hrcsl hsll]
      simp only [hrcs, hsl', getD_map_range _ _ (show 0 < 8 by omega),
        getD_map_range _ _ (show 1 < 8 by omega), getD_map_range _ _ (show 2 < 8 by omega),
        getD_map_range _ _ (show 3 < 8 by omega), getD_map_range _ _ (show 4 < 8 by omega),
        getD_map_range _ _ (show 5 < 8 by omega), getD_map_range _ _ (show 6 < 8 by omega),
        getD_map_range _ _ (show 7 < 8 by omega), getD_map_range _ _ (show 0 < 64 by omega)]
      ring
  · -- the returns
    rw [← hret, r69, r70, r73, r74, r75, r76, hz', h2240]
    simp only [List.cons.injEq, and_true]
    refine ⟨congrArg Prod.fst hcv8, congrArg Prod.snd hcv8, ?_⟩
    rw [mul_assoc, ← pow_add]
    refine congrArg (fun n => cur * gen ^ n) ?_
    simp only [List.length_append, hpl, hysl, hzsl, hsll, List.length_cons, List.length_nil]

/-- **`verify_flock` is sound over every hash model**, on every reader: the hypothesis
`verify_sub_model` takes. -/
theorem soundFlockM_model (M : HashModel) (rd : Reader) : SoundFlockM M rd :=
  verify_flock_model rd

end
end LeanVM.Guest.B1
