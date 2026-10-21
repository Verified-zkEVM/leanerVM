/-
  LeanVM.Guest.B1.Tables.VerifyTablesHashM

  `verify_tables`' reads and squeezes over a hash model: the framework claims, the table
  sumcheck, the column evaluations, the public input's challenge.
-/

module

public import LeanVM.Guest.B1.Tables.VerifyTablesFreeB
public import LeanVM.Guest.B1.Tables.VerifyTablesRunM

/-!
# `verify_tables`' Fiat-Shamir steps over a hash model

The lemmas of `VerifyTablesZc`, `Front`, `Reads` and `Tail` whose runs hash, over a hash model `M`
(`VtHoldsB M.sem`): every chain step is the model's answer.

* `ZcRoundM`, `loop79_stepM`, `ZcAtM`, `zc_roundsM`, `vt_zcM`: the table sumcheck's rounds run
  `sumcheck_round4` over the model (`sumcheck_round4_model`), `ξ` the model's squeeze;
* `vt_freshM`, `vt_evalsM`: the framework values and the column evaluations absorbed, the chain
  the model's answer (`obsAllM`);
* `vt_piM`: `rm` the model's squeeze.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier

@[expose] public section

/-- The round count's checks are free of `BLAKE2S`. -/
theorem zc_tau_free : ∀ t < 5, Stmt.freeInList vtFree (vtZcTau (t + 1)) = true := by
  decide +kernel

/-- The public input's limbs are free of `BLAKE2S`. -/
theorem pi_free : Stmt.freeInList vtFree (canonicalLimbsT (.n 3) 8154) = true ∧
    Stmt.freeInList vtFree (canonicalLimbsT (.n 4) 8159) = true := by decide +kernel

variable {M : HashModel}

/-! ## The table sumcheck -/

variable (M) in
/-- **Round `x` of the table sumcheck** (G:1727-1736): the slot at `rounds·x⁴` holds the state of
`cv`, the cursor and the claim; the three words at the cursor run `roundPoly 4` to `claim'` and the
challenge `rk`, stored at `chi[q]` with `q·x = g^n·g⁻¹`; the next slot holds the new state, the
cursor three words on and `claim'`; and `cprod[x·g] = cprod[x]·rk`. -/
def ZcRoundM (rd : Reader) (rounds chi gn cprod x : E) : Prop :=
  ∃ (cv : Digest) (cur claim c0 c2 c3 claim' rk : E) (cv' : Digest) (q c : E),
    LoadHolds rd (rounds * x ^ 4) 0 (digestScalars cv).1 ∧
    LoadHolds rd (rounds * x ^ 4) 1 (digestScalars cv).2 ∧
    LoadHolds rd (rounds * x ^ 4) 2 cur ∧ LoadHolds rd (rounds * x ^ 4) 3 claim ∧
    ReadsAt rd cur [c0, c2, c3] ∧ RunsToM M (roundPoly 4 claim none) cv [c0, c2, c3] (claim', rk) cv' ∧
    gn * wInvG = q * x ∧ LoadHolds rd (chi * q) 0 rk ∧
    LoadHolds rd (rounds * x ^ 4) 4 (digestScalars cv').1 ∧
    LoadHolds rd (rounds * x ^ 4) 5 (digestScalars cv').2 ∧
    LoadHolds rd (rounds * x ^ 4) 6 (cur * gen ^ 3) ∧ LoadHolds rd (rounds * x ^ 4) 7 claim' ∧
    LoadHolds rd (cprod * x) 0 c ∧ LoadHolds rd (cprod * x) 1 (c * rk)

/-- **`__loop79`**, one iteration: the round, then the loop at `x·g` while `x·g ≠ g^n`. -/
theorem loop79_stepM {rd : Reader} {N rounds chi gn cprod x : E}
    (h : coreProgram.RelB M.sem rd "__loop79" [x, N, rounds, chi, gn, cprod] []) :
    ZcRoundM M rd rounds chi gn cprod x ∧
      (x * gen + N ≠ 0 →
        coreProgram.RelB M.sem rd "__loop79" [x * gen, N, rounds, chi, gn, cprod] []) := by
  obtain ⟨σ, hp, hb, -⟩ := relB_pre find_loop79 core138_body l79Pre_noRet h
  simp only [show Fn.params Data.core138 = [.n 0, .n 1, .n 2, .n 3, .n 4, .n 5] from rfl,
    List.map_cons, List.map_nil, List.cons.injEq] at hp
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, -⟩ := hp
  have hnr := l79Pre_noRet
  have a6 := holdsB_atom hnr hb 0 (.mul (.n 6) (.n 0) (.n 0)) (by decide +kernel)
  have a7 := holdsB_atom hnr hb 1 (.mul (.n 7) (.n 6) (.n 6)) (by decide +kernel)
  have a8 := holdsB_atom hnr hb 2 (.mul (.n 8) (.n 2) (.n 7)) (by decide +kernel)
  have l9 := holdsB_atom hnr hb 3 (.load (.n 9) (.n 8) 0) (by decide +kernel)
  have l10 := holdsB_atom hnr hb 4 (.load (.n 10) (.n 8) 1) (by decide +kernel)
  have l11 := holdsB_atom hnr hb 5 (.load (.n 11) (.n 8) 2) (by decide +kernel)
  have l12 := holdsB_atom hnr hb 6 (.load (.n 12) (.n 8) 3) (by decide +kernel)
  have c7 := holdsB_call hnr hb 7 "sumcheck_round4" [.n 9, .n 10, .n 11, .n 12]
    [.n 13, .n 14, .n 15, .n 16, .n 17] (by decide +kernel)
  have a18 := holdsB_atom hnr hb 8 (.const (.n 18) wInvG) (by decide +kernel)
  have a19 := holdsB_atom hnr hb 9 (.mul (.n 19) (.n 4) (.n 18)) (by decide +kernel)
  have a19' := holdsB_atom hnr hb 10 (.mul (.n 19) (.n 20) (.n 0)) (by decide +kernel)
  have a21 := holdsB_atom hnr hb 11 (.mul (.n 21) (.n 3) (.n 20)) (by decide +kernel)
  have l17 := holdsB_atom hnr hb 12 (.load (.n 17) (.n 21) 0) (by decide +kernel)
  have l13 := holdsB_atom hnr hb 13 (.load (.n 13) (.n 8) 4) (by decide +kernel)
  have l14 := holdsB_atom hnr hb 14 (.load (.n 14) (.n 8) 5) (by decide +kernel)
  have l15 := holdsB_atom hnr hb 15 (.load (.n 15) (.n 8) 6) (by decide +kernel)
  have l16 := holdsB_atom hnr hb 16 (.load (.n 16) (.n 8) 7) (by decide +kernel)
  have a22 := holdsB_atom hnr hb 17 (.mul (.n 22) (.n 5) (.n 0)) (by decide +kernel)
  have l23 := holdsB_atom hnr hb 18 (.load (.n 23) (.n 22) 0) (by decide +kernel)
  have a24 := holdsB_atom hnr hb 19 (.mul (.n 24) (.n 23) (.n 17)) (by decide +kernel)
  have a25 := holdsB_atom hnr hb 20 (.mul (.n 25) (.n 5) (.n 0)) (by decide +kernel)
  have l24 := holdsB_atom hnr hb 21 (.load (.n 24) (.n 25) 1) (by decide +kernel)
  have a26 := holdsB_atom hnr hb 22 (.const (.n 26) (word 2 0 0)) (by decide +kernel)
  have a27 := holdsB_atom hnr hb 23 (.mul (.n 27) (.n 0) (.n 26)) (by decide +kernel)
  have a28 := holdsB_atom hnr hb 24 (.add (.n 28) (.n 27) (.n 1)) (by decide +kernel)
  have a29 := holdsB_atom hnr hb 25 (.const (.n 29) (word 2 0 0)) (by decide +kernel)
  have a30 := holdsB_atom hnr hb 26 (.mul (.n 30) (.n 0) (.n 29)) (by decide +kernel)
  have hc := holdsB_callIf hnr hb 27 (.n 28) "__loop79" [.n 30, .n 1, .n 2, .n 3, .n 4, .n 5]
    (by decide +kernel)
  simp only [Atom.Holds, word_gen, List.map_cons, List.map_nil] at *
  obtain ⟨cv, c0, c2, c3, claim', r, cv', hcv, hrd, hrun, hret⟩ :=
    sumcheck_round4_model rd _ _ c7
  simp only [List.cons.injEq] at hret
  obtain ⟨e13, e14, e15, e16, e17, -⟩ := hret
  have hq : σ (.n 8) = σ (.n 2) * σ (.n 0) ^ 4 := by rw [a8, a7, a6]; ring
  rw [hq] at l9 l10 l11 l12 l13 l14 l15 l16
  refine ⟨⟨cv, σ (.n 11), σ (.n 12), c0, c2, c3, claim', r, cv', σ (.n 20), σ (.n 23), ?_, ?_, l11,
    l12, hrd, hrun, by rw [← a19', a19, a18], ?_, ?_, ?_, ?_, ?_, by rw [← a22]; exact l23, ?_⟩,
    fun hne => ?_⟩
  · have e9 : σ (.n 9) = (digestScalars cv).1 := congrArg Prod.fst hcv
    rw [← e9]; exact l9
  · have e10 : σ (.n 10) = (digestScalars cv).2 := congrArg Prod.snd hcv
    rw [← e10]; exact l10
  · rw [← e17, ← a21]; exact l17
  · rw [← e13]; exact l13
  · rw [← e14]; exact l14
  · rw [← e15]; exact l15
  · rw [← e16]; exact l16
  · rw [← e17, ← a24, ← a25]; exact l24
  · have := hc (by rw [a28, a27, a26]; exact hne)
    rw [a30, a29] at this
    exact this

variable (M) in
/-- Round `j` with its pointers resolved: slot `j` of `rounds`, `chi[n - 1 - j]`, `cprod[j]`. -/
def ZcAtM (rd : Reader) (rounds chi cprod : E) (n j : ℕ) : Prop :=
  ∃ (cv : Digest) (cur claim c0 c2 c3 claim' rk : E) (cv' : Digest) (c : E),
    LoadHolds rd rounds (4 * j) (digestScalars cv).1 ∧
    LoadHolds rd rounds (4 * j + 1) (digestScalars cv).2 ∧
    LoadHolds rd rounds (4 * j + 2) cur ∧ LoadHolds rd rounds (4 * j + 3) claim ∧
    ReadsAt rd cur [c0, c2, c3] ∧ RunsToM M (roundPoly 4 claim none) cv [c0, c2, c3] (claim', rk) cv' ∧
    LoadHolds rd chi (n - 1 - j) rk ∧
    LoadHolds rd rounds (4 * j + 4) (digestScalars cv').1 ∧
    LoadHolds rd rounds (4 * j + 5) (digestScalars cv').2 ∧
    LoadHolds rd rounds (4 * j + 6) (cur * gen ^ 3) ∧ LoadHolds rd rounds (4 * j + 7) claim' ∧
    LoadHolds rd cprod j c ∧ LoadHolds rd cprod (j + 1) (c * rk)

/-- Round `j` with its pointers resolved, over the model (`zcAt_of_round`). -/
theorem zcAt_of_roundM {rd : Reader} {rounds chi cprod : E} {n j : ℕ} (hj : j < n)
    (h : ZcRoundM M rd rounds chi (gen ^ n) cprod (gen ^ j)) : ZcAtM M rd rounds chi cprod n j := by
  obtain ⟨cv, cur, claim, c0, c2, c3, claim', rk, cv', q, c, i0, i1, i2, i3, hrd, hrun, hq, hchi,
    o4, o5, o6, o7, hc0, hc1⟩ := h
  have hr : ∀ k w, LoadHolds rd (rounds * (gen ^ j) ^ 4) k w ↔ LoadHolds rd rounds (4 * j + k) w := by
    intro k w; rw [← pow_mul, show j * 4 = 4 * j by ring, loadHolds_gen_pow_mul]
  rw [chi_slot hj hq, loadHolds_gen_pow_mul, Nat.add_zero] at hchi
  rw [loadHolds_gen_pow_mul, Nat.add_zero] at hc0
  rw [loadHolds_gen_pow_mul] at hc1
  rw [hr] at i0 i1 i2 i3 o4 o5 o6 o7
  rw [Nat.add_zero] at i0
  exact ⟨cv, cur, claim, c0, c2, c3, claim', rk, cv', c, i0, i1, i2, i3, hrd, hrun, hchi, o4, o5,
    o6, o7, hc0, hc1⟩

/-- **The table sumcheck's rounds, chained**: from slot `b` (the state of `cv0`, the cursor, the
claim) and `cprod[b] = c0`, the words `ws` at the cursor run `L` plain rounds to the challenges `rs`
and the claim `cl`; `rs[j]` is at `chi[n - 1 - (b + j)]`, the challenges' prefix products times `c0`
are in `cprod`, and slot `b + L` holds the final state, the cursor `3L` words on and `cl`. -/
theorem zc_roundsM {rd : Reader} {rounds chi cprod : E} {n : ℕ} : ∀ (L b : ℕ) (cv0 : Digest)
    (cur claim0 c0 : E), (∀ j < L, ZcAtM M rd rounds chi cprod n (b + j)) →
    LoadHolds rd rounds (4 * b) (digestScalars cv0).1 →
    LoadHolds rd rounds (4 * b + 1) (digestScalars cv0).2 →
    LoadHolds rd rounds (4 * b + 2) cur → LoadHolds rd rounds (4 * b + 3) claim0 →
    LoadHolds rd cprod b c0 →
    ∃ (ws rs : List E) (cl : E) (cvS : Digest), ws.length = 3 * L ∧ ReadsAt rd cur ws ∧
      rs.length = L ∧ RunsToM M (sumcheck claim0 4 (List.replicate L none)) cv0 ws (rs, cl) cvS ∧
      (∀ j (hj : j < rs.length), LoadHolds rd chi (n - 1 - (b + j)) rs[j]) ∧
      (∀ j ≤ L, LoadHolds rd cprod (b + j) (c0 * prodE (rs.take j))) ∧
      LoadHolds rd rounds (4 * (b + L)) (digestScalars cvS).1 ∧
      LoadHolds rd rounds (4 * (b + L) + 1) (digestScalars cvS).2 ∧
      LoadHolds rd rounds (4 * (b + L) + 2) (cur * gen ^ (3 * L)) ∧
      LoadHolds rd rounds (4 * (b + L) + 3) cl := by
  intro L
  induction L with
  | zero =>
    intro b cv0 cur claim0 c0 _ h0 h1 h2 h3 hc
    refine ⟨[], [], claim0, cv0, rfl, readsAt_nil _ _, rfl, runsToM_ret _ _,
      fun j hj => absurd hj (by simp), fun j hj => ?_, h0, h1, ?_, h3⟩
    · obtain rfl : j = 0 := by omega
      simpa [prodE] using hc
    · rw [Nat.mul_zero, pow_zero, mul_one]; exact h2
  | succ L ih =>
    intro b cv0 cur claim0 c0 hR h0 h1 h2 h3 hc
    obtain ⟨cv, cur', claim', a0, a2, a3, claim'', rk, cv', c, i0, i1, i2, i3, hrd, hrun, hchi,
      o4, o5, o6, o7, hc0, hc1⟩ := hR 0 (by omega)
    simp only [Nat.add_zero] at i0 i1 i2 i3 hchi o4 o5 o6 o7 hc0 hc1
    have ecv : cv0 = cv := digestScalars_injective (Prod.ext (loadHolds_unique h0 i0)
      (loadHolds_unique h1 i1))
    have ecur : cur = cur' := loadHolds_unique h2 i2
    have ecl : claim0 = claim' := loadHolds_unique h3 i3
    have ec : c0 = c := loadHolds_unique hc hc0
    subst ecv ecur ecl ec
    obtain ⟨ws', rs', cl, cvS, hwl', hws', hrl', hrun', hchi', hcp', t0, t1, t2, t3⟩ :=
      ih (b + 1) cv' (cur * gen ^ 3) claim'' (c0 * rk)
        (fun j hj => by rw [show b + 1 + j = b + (j + 1) by ring]; exact hR (j + 1) (by omega))
        (by rw [show 4 * (b + 1) = 4 * b + 4 by ring]; exact o4)
        (by rw [show 4 * (b + 1) + 1 = 4 * b + 5 by ring]; exact o5)
        (by rw [show 4 * (b + 1) + 2 = 4 * b + 6 by ring]; exact o6)
        (by rw [show 4 * (b + 1) + 3 = 4 * b + 7 by ring]; exact o7) hc1
    refine ⟨[a0, a2, a3] ++ ws', rk :: rs', cl, cvS, by simp [hwl']; ring,
      readsAt_append_pow hrd (by simp only [List.length_cons, List.length_nil]; exact hws'),
      by simp [hrl'], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact RunsToM.sumcheck_cons hrun hrun'
    · intro j hj
      cases j with
      | zero => simpa using hchi
      | succ j =>
        have := hchi' j (by simp at hj; omega)
        rw [show b + 1 + j = b + (j + 1) by ring] at this
        simpa using this
    · intro j hj
      cases j with
      | zero => simpa [prodE] using hc0
      | succ j =>
        have := hcp' j (by omega)
        rw [show b + 1 + j = b + (j + 1) by ring] at this
        rw [List.take_succ_cons, vt_prodE_eq, List.prod_cons, ← mul_assoc, ← vt_prodE_eq]
        exact this
    · rw [show b + (L + 1) = b + 1 + L by ring]; exact t0
    · rw [show b + (L + 1) = b + 1 + L by ring]; exact t1
    · rw [show b + (L + 1) = b + 1 + L by ring, mul_assoc, ← pow_add,
        show 3 + 3 * L = 3 * (L + 1) by ring] at *
      exact t2
    · rw [show b + (L + 1) = b + 1 + L by ring]; exact t3

set_option maxHeartbeats 4000000 in
/-- **The table sumcheck** (G:1706-1745): with `dims_g[t + 1] = g^(τ t)`, `τ t < 29`, the bus point
at `zeta` with `g_bus_mu = g^|point|`, and the chain at `(3422, 3423)` the state of `cvB`: the
round count is `n = max τ ≤ |point|`; `ξ` is squeezed from `cvB`; the words at the cursor (five
words on) run the `n` plain rounds from the bus target to the challenges `rs` and the claim `cl`;
`chi` holds `rs` reversed; `cprod[j]` and `peq[k]` are the prefix products; and the chain, the
cursor and the claim the phase leaves are the rounds'. -/
theorem vt_zcM {κ : ℕ} (hκ : κ ≤ 32) (Lm : MemImage κ) {σ : Val} (h : VtHoldsB M.sem Lm.read σ)
    (τ : ℕ → ℕ) (hτ : ∀ t < 6, τ t < 29)
    (hdims : ∀ t < 6, LoadHolds Lm.read (σ (.n 7)) (t + 1) (gen ^ τ t))
    {point : List E} (hz : ReadsAt Lm.read (σ (.n 5)) point) (hmu : σ (.n 6) = gen ^ point.length)
    (hml : point.length < 33) {cvB : Digest} (hst : (σ (.n 3422), σ (.n 3423)) = digestScalars cvB) :
    ∃ (n : ℕ) (ws rs : List E) (cl : E) (cvS cX : Digest),
      n = ((List.range 6).map τ).foldl max 0 ∧ n ≤ point.length ∧ σ (.n 4554) = gen ^ n ∧
      sqCvM M cvB = some cX ∧
      σ (.n 4621) = challengeOf cX ∧ σ (.n 4622) = 1 ∧
      σ (.n 4623) = challengeOf cX ∧ σ (.n 4624) = challengeOf cX ^ 2 ∧
      σ (.n 4625) = challengeOf cX ^ 3 ∧ σ (.n 4626) = challengeOf cX ^ 4 ∧
      ws.length = 3 * n ∧ ReadsAt Lm.read (σ (.n 2) * gen ^ 5) ws ∧ rs.length = n ∧
      RunsToM M (sumcheck (σ (.n 4631)) 4 (List.replicate n none)) cX ws (rs, cl) cvS ∧
      ReadsAt Lm.read (σ (.n 15)) rs.reverse ∧
      (∀ j ≤ n, LoadHolds Lm.read (σ (.n 4639)) j (prodE (rs.take j))) ∧
      (∀ k ≤ n, LoadHolds Lm.read (σ (.n 4655)) k (eqEval (point.take k) (rs.reverse.take k))) ∧
      (σ (.n 4649), σ (.n 4650)) = digestScalars cvS ∧
      σ (.n 4651) = σ (.n 2) * gen ^ 5 * gen ^ (3 * n) ∧ σ (.n 4652) = cl := by
  -- the round count
  have a4554 := h.atom 4276 (.mul (.n 4554) (.n 4557) (.n 4555)) (by decide +kernel)
  have l4555 := h.atom 4274 (.load (.n 4555) (.n 7) 1) (by decide +kernel)
  have c4556 := h.atom 4275 (.const (.n 4556) (word 4294967296 0 0)) (by decide +kernel)
  have rc0 := h.atom 4277 (.rangeCheck (.n 4557) (.n 4558) (.n 4559) (.n 4560) (.n 4556))
    (by decide +kernel)
  have a4561 := h.atom 4278 (.add (.n 4561) (.n 4554) (.n 4555)) (by decide +kernel)
  simp only [Atom.Holds] at a4554 l4555 c4556 rc0 a4561
  have e4555 : σ (.n 4555) = gen ^ τ 0 := loadHolds_unique l4555 (hdims 0 (by omega))
  obtain ⟨e0, he0, he0'⟩ := rc_sound' hκ Lm (K := 33) (by omega) (by decide)
    (by rw [c4556]; exact word_g32') rc0.1 rc0.2.1 rc0.2.2
  set n := e0 + τ 0 with hn
  have hgn : σ (.n 4554) = gen ^ n := by rw [a4554, he0', e4555, ← pow_add]
  have hτ0 := hτ 0 (by omega)
  -- each height is at most `n`
  have htau : ∀ t, t < 5 → ∃ e < 33, n = e + τ (t + 1) ∧
      σ (.n (4562 + 8 * t + 6)) = gen ^ n + gen ^ τ (t + 1) ∧
      σ (.n (4562 + 8 * t + 7)) =
        σ (.n (if t + 1 = 1 then 4561 else 4562 + 8 * t - 1)) * σ (.n (4562 + 8 * t + 6)) := by
    intro t ht
    obtain ⟨k, hb⟩ := h.slice _ _ (vt_zc_taus t ht) (zc_tau_free t ht)
    simp only [vtZcTau, Nat.add_sub_cancel, Stmt.HoldsList, Stmt.Holds, Atom.Holds, and_true] at hb
    obtain ⟨l0, c1, m2, rc, a6, a7⟩ := hb
    have ev := loadHolds_unique l0 (hdims (t + 1) (by omega))
    obtain ⟨e, he, he'⟩ := rc_sound' hκ Lm (K := 33) (by omega) (by decide)
      (by rw [c1]; exact word_g32') rc.1 rc.2.1 rc.2.2
    rw [hgn, he', ev, ← pow_add] at m2
    refine ⟨e, he, gen_pow_inj' (by omega) (by have := hτ (t + 1) (by omega); omega) m2, ?_, a7⟩
    rw [a6, hgn, ev]
  obtain ⟨f1, hf1, hn1, s1, p1⟩ := htau 0 (by omega)
  obtain ⟨f2, hf2, hn2, s2, p2⟩ := htau 1 (by omega)
  obtain ⟨f3, hf3, hn3, s3, p3⟩ := htau 2 (by omega)
  obtain ⟨f4, hf4, hn4, s4, p4⟩ := htau 3 (by omega)
  obtain ⟨f5, hf5, hn5, s5, p5⟩ := htau 4 (by omega)
  simp only [Nat.reduceMul, Nat.reduceAdd, Nat.reduceSub, ↓reduceIte,
    OfNat.ofNat_ne_one] at s1 s2 s3 s4 s5 p1 p2 p3 p4 p5
  simp only [Nat.reduceAdd] at hn1 hn2 hn3 hn4 hn5
  have c4602 := h.atom 4309 (.const (.n 4602) (word 0 0 0)) (by decide +kernel)
  have ae := h.atom 4310 (.assertEq (.n 4601) (.n 4602)) (by decide +kernel)
  simp only [Atom.Holds, word_zero] at c4602 ae
  rw [c4602, add_zero] at ae
  have hmax : ∃ t < 6, τ t = n := by
    rw [p5, p4, p3, p2, p1, a4561, s1, s2, s3, s4, s5, hgn, e4555] at ae
    simp only [mul_eq_zero, e_add_eq_zero_iff] at ae
    have hinj : ∀ t < 6, gen ^ n = gen ^ τ t → τ t = n := fun t ht he =>
      (gen_pow_inj' (by omega) (by have := hτ t ht; omega) he).symm
    rcases ae with ((((h0 | h1) | h2) | h3) | h4) | h5
    · exact ⟨0, by omega, hinj 0 (by omega) h0⟩
    · exact ⟨1, by omega, hinj 1 (by omega) h1⟩
    · exact ⟨2, by omega, hinj 2 (by omega) h2⟩
    · exact ⟨3, by omega, hinj 3 (by omega) h3⟩
    · exact ⟨4, by omega, hinj 4 (by omega) h4⟩
    · exact ⟨5, by omega, hinj 5 (by omega) h5⟩
  have hnmax : n = ((List.range 6).map τ).foldl max 0 := by
    obtain ⟨t0, ht0, hτt0⟩ := hmax
    refine (foldl_max_eq (fun x hx => ?_) ?_).symm
    · simp only [List.mem_map, List.mem_range] at hx
      obtain ⟨t, ht, rfl⟩ := hx
      interval_cases t <;> omega
    · exact List.mem_map.mpr ⟨t0, List.mem_range.mpr ht0, hτt0⟩
  -- the bus point's length bounds it
  have c4603 := h.atom 4311 (.const (.n 4603) (word 4294967296 0 0)) (by decide +kernel)
  have m6 := h.atom 4312 (.mul (.n 6) (.n 4604) (.n 4554)) (by decide +kernel)
  have rcm := h.atom 4313 (.rangeCheck (.n 4604) (.n 4605) (.n 4606) (.n 4607) (.n 4603))
    (by decide +kernel)
  simp only [Atom.Holds] at c4603 m6 rcm
  obtain ⟨em, hem, hem'⟩ := rc_sound' hκ Lm (K := 33) (by omega) (by decide)
    (by rw [c4603]; exact word_g32') rcm.1 rcm.2.1 rcm.2.2
  rw [hmu, hem', hgn, ← pow_add] at m6
  have hnmu : n ≤ point.length := by
    have := gen_pow_inj' (by omega) (by omega) m6; omega
  -- `ξ` and its powers
  obtain ⟨cv0, cX, hcv0, hX, hsq, hxi⟩ :=
    h.squeeze 4314 (.n 3422) (.n 3423) 4608 (by decide +kernel)
  rw [hst] at hcv0
  obtain rfl := (digestScalars_injective hcv0).symm
  have c4622 := h.atom 4328 (.const (.n 4622) (word 1 0 0)) (by decide +kernel)
  have m4623 := h.atom 4329 (.mul (.n 4623) (.n 4622) (.n 4621)) (by decide +kernel)
  have m4624 := h.atom 4330 (.mul (.n 4624) (.n 4623) (.n 4621)) (by decide +kernel)
  have m4625 := h.atom 4331 (.mul (.n 4625) (.n 4624) (.n 4621)) (by decide +kernel)
  have m4626 := h.atom 4332 (.mul (.n 4626) (.n 4625) (.n 4621)) (by decide +kernel)
  simp only [Atom.Holds, word_one] at c4622 m4623 m4624 m4625 m4626
  rw [c4622, one_mul, hxi] at m4623
  rw [m4623, hxi, ← pow_two] at m4624
  rw [m4624, hxi, ← pow_succ] at m4625
  rw [m4625, hxi, ← pow_succ] at m4626
  -- the rounds' first slot and `cprod[0]`
  have s0 := h.atom 4346 (.load (.n 4613) (.n 4636) 0) (by decide +kernel)
  have s1 := h.atom 4347 (.load (.n 4614) (.n 4636) 1) (by decide +kernel)
  have c4640 := h.atom 4348 (.const (.n 4640) (word 32 0 0)) (by decide +kernel)
  have m4641 := h.atom 4349 (.mul (.n 4641) (.n 2) (.n 4640)) (by decide +kernel)
  have s2 := h.atom 4350 (.load (.n 4641) (.n 4636) 2) (by decide +kernel)
  have s3 := h.atom 4351 (.load (.n 4631) (.n 4636) 3) (by decide +kernel)
  have c4642 := h.atom 4352 (.const (.n 4642) (word 1 0 0)) (by decide +kernel)
  have sc := h.atom 4353 (.load (.n 4642) (.n 4639) 0) (by decide +kernel)
  have c4643 := h.atom 4354 (.const (.n 4643) (word 1 0 0)) (by decide +kernel)
  have a4644 := h.atom 4355 (.add (.n 4644) (.n 4643) (.n 4554)) (by decide +kernel)
  have c4645 := h.atom 4356 (.const (.n 4645) (word 1 0 0)) (by decide +kernel)
  have c79 := h.callIfB 4357 (.n 4644) "__loop79" [.n 4645, .n 4554, .n 4636, .n 15, .n 4554,
    .n 4639]
    (by decide +kernel)
  simp only [Atom.Holds] at s0 s1 c4640 m4641 s2 s3 sc a4644
  simp only [Atom.Holds, word_one, List.map_cons, List.map_nil] at c4642 c4643 c4645 c79
  rw [m4641, c4640, show (32 : ℕ) = 2 ^ 5 by norm_num, word_two_pow (by decide)] at s2
  rw [c4642] at sc
  have e4613 : σ (.n 4613) = (digestScalars cX).1 := congrArg Prod.fst hsq
  have e4614 : σ (.n 4614) = (digestScalars cX).2 := congrArg Prod.snd hsq
  rw [e4613] at s0
  rw [e4614] at s1
  have hR : ∀ j < n, ZcRoundM M Lm.read (σ (.n 4636)) (σ (.n 15)) (σ (.n 4554)) (σ (.n 4639)) (gen ^ j) :=
    loop_soundB (ps := [σ (.n 4554), σ (.n 4636), σ (.n 15), σ (.n 4554), σ (.n 4639)])
      (N := σ (.n 4554)) (by unfold ordG; omega) hgn (fun x hx => loop79_stepM hx) (fun hne => by
        have := c79 (by rw [a4644, c4643]; exact hne)
        rw [c4645] at this
        exact this)
  rw [hgn] at hR
  obtain ⟨ws, rs, cl, cvS, hwl, hws, hrl, hrun, hchi, hcp, t0, t1, t2, t3⟩ :=
    zc_roundsM (rounds := σ (.n 4636)) (chi := σ (.n 15)) (cprod := σ (.n 4639)) n 0 cX
      (σ (.n 2) * gen ^ 5) (σ (.n 4631)) 1
      (fun j hj => by rw [Nat.zero_add]; exact zcAt_of_roundM hj (hR j hj)) s0 s1 s2 s3 sc
  simp only [Nat.zero_add, one_mul] at hchi hcp t0 t1 t2 t3
  -- the last slot
  have m4646 := h.atom 4358 (.mul (.n 4646) (.n 4554) (.n 4554)) (by decide +kernel)
  have m4647 := h.atom 4359 (.mul (.n 4647) (.n 4646) (.n 4646)) (by decide +kernel)
  have m4648 := h.atom 4360 (.mul (.n 4648) (.n 4636) (.n 4647)) (by decide +kernel)
  have l4649 := h.atom 4361 (.load (.n 4649) (.n 4648) 0) (by decide +kernel)
  have l4650 := h.atom 4362 (.load (.n 4650) (.n 4648) 1) (by decide +kernel)
  have l4651 := h.atom 4363 (.load (.n 4651) (.n 4648) 2) (by decide +kernel)
  have l4652 := h.atom 4364 (.load (.n 4652) (.n 4648) 3) (by decide +kernel)
  simp only [Atom.Holds] at m4646 m4647 m4648 l4649 l4650 l4651 l4652
  have e4648 : σ (.n 4648) = σ (.n 4636) * gen ^ (4 * n) := by
    rw [m4648, m4647, m4646, hgn]; ring
  rw [e4648, loadHolds_gen_pow_mul] at l4649 l4650 l4651 l4652
  -- `zc_peq`
  have c4656 := h.atom 4368 (.const (.n 4656) (word 1 0 0)) (by decide +kernel)
  have sp := h.atom 4369 (.load (.n 4656) (.n 4655) 0) (by decide +kernel)
  have c4657 := h.atom 4370 (.const (.n 4657) (word 1 0 0)) (by decide +kernel)
  have a4658 := h.atom 4371 (.add (.n 4658) (.n 4657) (.n 4554)) (by decide +kernel)
  have c4659 := h.atom 4372 (.const (.n 4659) (word 1 0 0)) (by decide +kernel)
  have c80 := h.callIf 4373 (.n 4658) "__loop80" [.n 4659, .n 4554, .n 4655, .n 5, .n 15]
    (by decide +kernel)
  simp only [Atom.Holds, word_one, List.map_cons, List.map_nil] at c4656 sp c4657 a4658 c4659 c80
  rw [c4656] at sp
  have hrev : ReadsAt Lm.read (σ (.n 15)) rs.reverse := by
    intro k hk
    have hk' : k < n := by simp [hrl] at hk; omega
    have := hchi (n - 1 - k) (by omega)
    rw [show n - 1 - (n - 1 - k) = k by omega] at this
    rw [List.getElem_reverse]
    convert this using 2
    congr 1
    simp [hrl]
  have hpeq := loop80_sound (rd := Lm.read) (peq := σ (.n 4655)) (zeta := σ (.n 5)) (chi := σ (.n 15))
    (n := n) (by unfold ordG; omega) hz hrev hnmu (by simp [hrl]) sp (fun hne => by
      have := c80 (by rw [a4658, c4657, hgn]; exact hne)
      rw [c4659, hgn] at this
      exact this)
  refine ⟨n, ws, rs, cl, cvS, cX, hnmax, hnmu, hgn, hX, hxi, c4622, m4623, m4624, m4625, m4626, hwl, hws,
    hrl, hrun, hrev, hcp, hpeq, ?_, ?_, ?_⟩
  · rw [loadHolds_unique l4649 (by simpa using t0), loadHolds_unique l4650 t1]
  · exact loadHolds_unique l4651 t2
  · exact loadHolds_unique l4652 t3

/-- **The framework claims' values** (G:1604-1612): from the state of `cv` in `(fs0, fs1)`, the
five words at the cursor, absorbed in order to the state at `(3422, 3423)`, stored in
`claim_pool[0 .. 4]` with their blocks' `g^κ` in `claim_cplen_g`. -/
theorem vt_freshM {rd : Reader} {σ : Val} (h : VtHoldsB M.sem rd σ) {cv : Digest}
    (hcv : (σ (.n 0), σ (.n 1)) = digestScalars cv) :
    ReadsAt rd (σ (.n 2)) (freshWords σ) ∧
      (∃ d, obsAllM M cv (freshWords σ) = some d ∧ (σ (.n 3422), σ (.n 3423)) = digestScalars d) ∧
      ReadsAt rd (σ (.n 13)) (freshWords σ) ∧
      ReadsAt rd (σ (.n 14)) [σ (.n 1893), σ (.n 1893), σ (.n 1893), σ (.n 3345), σ (.n 3395)] := by
  have c19 := h.atom 0 (.copy (.n 19) (.n 0)) (by decide +kernel)
  have c20 := h.atom 1 (.copy (.n 20) (.n 1)) (by decide +kernel)
  obtain ⟨r0, f0⟩ := h.fsNext 1664 (.n 19) (.n 20) (.n 2) 0 1937 (by decide +kernel)
  obtain ⟨r1, f1⟩ := h.fsNext 1682 (.n 1950) (.n 1951) (.n 2) 1 1955 (by decide +kernel)
  obtain ⟨r2, f2⟩ := h.fsNext 1700 (.n 1968) (.n 1969) (.n 2) 2 1973 (by decide +kernel)
  obtain ⟨r3, f3⟩ := h.fsNext 3120 (.n 1986) (.n 1987) (.n 2) 3 3359 (by decide +kernel)
  obtain ⟨r4, f4⟩ := h.fsNext 3168 (.n 3372) (.n 3373) (.n 2) 4 3409 (by decide +kernel)
  have p0 := h.atom 1677 (.load (.n 1937) (.n 13) 0) (by decide +kernel)
  have p1 := h.atom 1695 (.load (.n 1955) (.n 13) 1) (by decide +kernel)
  have p2 := h.atom 1713 (.load (.n 1973) (.n 13) 2) (by decide +kernel)
  have p3 := h.atom 3133 (.load (.n 3359) (.n 13) 3) (by decide +kernel)
  have p4 := h.atom 3181 (.load (.n 3409) (.n 13) 4) (by decide +kernel)
  have q0 := h.atom 1678 (.load (.n 1893) (.n 14) 0) (by decide +kernel)
  have q1 := h.atom 1696 (.load (.n 1893) (.n 14) 1) (by decide +kernel)
  have q2 := h.atom 1714 (.load (.n 1893) (.n 14) 2) (by decide +kernel)
  have q3 := h.atom 3134 (.load (.n 3345) (.n 14) 3) (by decide +kernel)
  have q4 := h.atom 3182 (.load (.n 3395) (.n 14) 4) (by decide +kernel)
  simp only [Atom.Holds] at c19 c20 p0 p1 p2 p3 p4 q0 q1 q2 q3 q4
  simp only [Nat.reduceAdd] at f0 f1 f2 f3 f4
  obtain ⟨d0, o0, k0⟩ := fsM_chainAll (obsAllM_nil cv)
    (show (σ (.n 19), σ (.n 20)) = digestScalars cv by rw [c19, c20]; exact hcv) f0
  obtain ⟨d1, o1, k1⟩ := fsM_chainAll o0 k0 f1
  obtain ⟨d2, o2, k2⟩ := fsM_chainAll o1 k1 f2
  obtain ⟨d3, o3, k3⟩ := fsM_chainAll o2 k2 f3
  obtain ⟨d4, o4, k4⟩ := fsM_chainAll o3 k3 f4
  simp only [List.nil_append, List.cons_append] at o4
  refine ⟨fun k hk => ?_, ⟨d4, o4, k4⟩, fun k hk => ?_, fun k hk => ?_⟩
  · simp only [freshWords, List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [r0, r1, r2, r3, r4]
  · simp only [freshWords, List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [p0, p1, p2, p3, p4]
  · simp only [List.length_cons, List.length_nil] at hk
    interval_cases k
    exacts [q0, q1, q2, q3, q4]

/-- **The 104 column evaluations** (G:1752-1758): from the state of `cv` at `(4649, 4650)`, the
words at the cursor `4651`, absorbed in order to the state at `(7569, 7570)`; each stored in
`claim_pool[5 + j]`, with its table's `g^τ` in `claim_cplen_g[5 + j]`; each copied to
`col_evals`. -/
theorem vt_evalsM {rd : Reader} {σ : Val} (h : VtHoldsB M.sem rd σ) {cv : Digest}
    (hcv : (σ (.n 4649), σ (.n 4650)) = digestScalars cv) :
    ReadsAt rd (σ (.n 4651)) (evWords σ) ∧
      (∃ d, obsAllM M cv (evWords σ) = some d ∧ (σ (.n 7569), σ (.n 7570)) = digestScalars d) ∧
      ∀ j < 104, LoadHolds rd (σ (.n 13)) (5 + j) (σ (.n (evVal.getD j 0))) ∧
        LoadHolds rd (σ (.n 14)) (5 + j) (σ (.n (evTau.getD j 0))) ∧
        σ (.n (evVal.getD j 0 + 15)) = σ (.n (evVal.getD j 0)) := by
  have hb : ∀ j < 104, (LoadHolds rd (σ (.n 4651)) j (σ (.n (evVal.getD j 0))) ∧
      ∃ c d, (σ (.n (if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13)),
        σ (.n ((if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13) + 1))) = digestScalars c ∧
        obsCvM M c (σ (.n (evVal.getD j 0))) = some d ∧
        (σ (.n (evVal.getD j 0 + 13)), σ (.n (evVal.getD j 0 + 14))) = digestScalars d)
      ∧ σ (.n (evVal.getD j 0 + 15)) = σ (.n (evVal.getD j 0)) ∧
      LoadHolds rd (σ (.n 13)) (5 + j) (σ (.n (evVal.getD j 0))) ∧
      LoadHolds rd (σ (.n 14)) (5 + j) (σ (.n (evTau.getD j 0))) := by
    intro j hj
    have hs := h.sliceB _ _ (ev_blocks j hj)
    obtain ⟨k, hs⟩ := hs
    rw [evT, holdsListB_append] at hs
    obtain ⟨⟨hl, c, d, hc, hd, hv⟩, hrest⟩ := holdsB_fsNextT _ _ _ _ _ hs
    simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB, and_true] at hrest
    refine ⟨⟨hl, c, d, hc, hd, ?_⟩, hrest⟩
    have h12 := hv 12 (by omega) (by omega)
    have h13 := hv 13 (by omega) (by omega)
    rw [show evVal.getD j 0 + 1 + 12 = evVal.getD j 0 + 13 by omega] at h12
    rw [show evVal.getD j 0 + 1 + 13 = evVal.getD j 0 + 14 by omega] at h13
    rw [h12, h13]
    rfl
  have hchain : ∀ j ≤ 104, ∃ d, obsAllM M cv ((evWords σ).take j) = some d ∧
      (σ (.n (if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13)),
        σ (.n ((if j = 0 then 4649 else evVal.getD (j - 1) 0 + 13) + 1))) = digestScalars d := by
    intro j hj
    induction j with
    | zero => exact ⟨cv, by simp [obsAllM], by simpa using hcv⟩
    | succ j ih =>
      obtain ⟨d, hd, hst⟩ := ih (by omega)
      obtain ⟨⟨-, c, d', hc, hd', hout⟩, -⟩ := hb j (by omega)
      rw [hst] at hc
      obtain rfl := digestScalars_injective hc
      refine ⟨d', ?_, ?_⟩
      · rw [List.take_add_one, List.getElem?_eq_getElem (by simp [evWords]; omega),
          Option.toList_some, obsAllM_snoc, hd, Option.bind_some]
        simpa [evWords] using hd'
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
        exact hout
  refine ⟨fun j hj => ?_, ?_, fun j hj => ⟨(hb j hj).2.2.1, (hb j hj).2.2.2, (hb j hj).2.1⟩⟩
  · have hj' : j < 104 := by simpa [evWords] using hj
    simpa [evWords] using (hb j hj').1.1
  · obtain ⟨d, hd, hst⟩ := hchain 104 le_rfl
    simp only [OfNat.ofNat_ne_zero, ↓reduceIte] at hst
    rw [List.take_of_length_le (by simp [evWords])] at hd
    exact ⟨d, hd, hst⟩

set_option maxHeartbeats 4000000 in
/-- **The public input's claims and the returns** (G:1814-1824): the accumulated terms are the
sumcheck's claim; from the state of `cvR` at `(7569, 7570)`, `rm` is squeezed; both public
words are canonical and their limbs' lines at `rm` are pooled at `109 .. 111`; the function
returns the new state, the cursor 104 words on, `g^n`, the bytecode share and `rm`. -/
theorem vt_piM {rd : Reader} {σ : Val} (h : VtHoldsB M.sem rd σ) {cvR : Digest}
    (hcv : (σ (.n 7569), σ (.n 7570)) = digestScalars cvR) :
    σ (.n 8139) = σ (.n 4652) ∧ ∃ cF, sqCvM M cvR = some cF ∧
      (σ (.n 8145), σ (.n 8146)) = digestScalars cF ∧
      σ (.n 8153) = challengeOf cF ∧ IsCanonical128 (σ (.n 3)) ∧
      IsCanonical128 (σ (.n 4)) ∧
      LoadHolds rd (σ (.n 13)) 109 (ofK ((σ (.n 3)).limb 0) +
        σ (.n 8153) * (ofK ((σ (.n 3)).limb 0) + ofK ((σ (.n 4)).limb 0))) ∧
      LoadHolds rd (σ (.n 13)) 110 (ofK ((σ (.n 3)).limb 1) +
        σ (.n 8153) * (ofK ((σ (.n 3)).limb 1) + ofK ((σ (.n 4)).limb 1))) ∧
      LoadHolds rd (σ (.n 13)) 111 0 ∧
      σ (.n 8171) = σ (.n 8145) ∧ σ (.n 8172) = σ (.n 8146) ∧
      σ (.n 8175) = σ (.n 4651) * gen ^ 104 ∧ σ (.n 8176) = σ (.n 4554) ∧
      σ (.n 8177) = σ (.n 1732) ∧ σ (.n 8178) = σ (.n 8153) := by
  have ae := h.atom 7854 (.assertEq (.n 8139) (.n 4652)) (by decide +kernel)
  obtain ⟨cv, cF, hc, hF, hs, hr⟩ := h.squeeze 7855 (.n 7569) (.n 7570) 8140 (by decide +kernel)
  rw [hcv] at hc
  obtain rfl := digestScalars_injective hc
  obtain ⟨k0, b0⟩ := h.slice _ _ vt_pi_blocks.1 pi_free.1
  obtain ⟨k1, b1⟩ := h.slice _ _ vt_pi_blocks.2 pi_free.2
  rw [holds_canonicalLimbsT] at b0 b1
  obtain ⟨⟨hc0, e8154, -, -, e8157⟩, -⟩ := b0
  obtain ⟨⟨hc1, e8159, -, -, e8162⟩, -⟩ := b1
  have c58 := h.atom 7874 (.copy (.n 8158) (.n 8154)) (by decide +kernel)
  have c63 := h.atom 7880 (.copy (.n 8163) (.n 8159)) (by decide +kernel)
  have a64 := h.atom 7881 (.add (.n 8164) (.n 8158) (.n 8163)) (by decide +kernel)
  have m65 := h.atom 7882 (.mul (.n 8165) (.n 8153) (.n 8164)) (by decide +kernel)
  have a66 := h.atom 7883 (.add (.n 8166) (.n 8158) (.n 8165)) (by decide +kernel)
  have l66 := h.atom 7884 (.load (.n 8166) (.n 13) 109) (by decide +kernel)
  have a67 := h.atom 7885 (.add (.n 8167) (.n 8157) (.n 8162)) (by decide +kernel)
  have m68 := h.atom 7886 (.mul (.n 8168) (.n 8153) (.n 8167)) (by decide +kernel)
  have a69 := h.atom 7887 (.add (.n 8169) (.n 8157) (.n 8168)) (by decide +kernel)
  have l69 := h.atom 7888 (.load (.n 8169) (.n 13) 110) (by decide +kernel)
  have c70 := h.atom 7889 (.const (.n 8170) (word 0 0 0)) (by decide +kernel)
  have l70 := h.atom 7890 (.load (.n 8170) (.n 13) 111) (by decide +kernel)
  have r71 := h.atom 7891 (.copy (.n 8171) (.n 8145)) (by decide +kernel)
  have r72 := h.atom 7892 (.copy (.n 8172) (.n 8146)) (by decide +kernel)
  have c73 := h.atom 7893 (.const (.n 8173) (word 29686813949952 0 0)) (by decide +kernel)
  have m74 := h.atom 7894 (.mul (.n 8174) (.n 4651) (.n 8173)) (by decide +kernel)
  have r75 := h.atom 7895 (.copy (.n 8175) (.n 8174)) (by decide +kernel)
  have r76 := h.atom 7896 (.copy (.n 8176) (.n 4554)) (by decide +kernel)
  have r77 := h.atom 7897 (.copy (.n 8177) (.n 1732)) (by decide +kernel)
  have r78 := h.atom 7898 (.copy (.n 8178) (.n 8153)) (by decide +kernel)
  simp only [Atom.Holds, word_zero] at *
  refine ⟨e_add_eq_zero_iff.mp ae, cF, hF, hs, hr, hc0, hc1, ?_, ?_, by rw [← c70]; exact l70, r71, r72,
    by rw [r75, m74, c73, word_g104], r76, r77, r78⟩
  · rw [a66, m65, a64, c58, c63, e8154, e8159] at l66; exact l66
  · rw [a69, m68, a67, e8157, e8162] at l69; exact l69

end
end LeanVM.Guest.B1.VerifySub
