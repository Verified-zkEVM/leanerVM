/-
  LeanVM.Guest.B1.Comp.VerifySub.Bus

  `verify_sub`'s bus challenges complete over a completeness model: the `alpha`s, `fp_w` and
  `beta` from the model's squeezes.
-/

module

public import LeanVM.Guest.B1.Comp.VerifySub.Front
public import LeanVM.Guest.B1.VerifySub.CBus

/-!
# The bus challenges over a completeness model (G:2137-2153)

`VerifySub/CBus.lean` over a `CompModel`. A run of squeezes is a family of states `st` the model
answers one from the next (`sqCvM CM.hm (st k) = some (st (k + 1))`, from `sqAllM` by
`sqAllM_states`), the deployed `sqCv^[k] cv`:

* `c_squeezes_comp`: `m` squeezes stored at `out`;
* `c_eqwEntryB`: one entry of `fp_w`, under any semantics (no `BLAKE2S` row);
* `c_bus_comp`: the block, from the root's state `st 0` to the four `alpha`s `challengeOf
  (st (c + 1))` and `beta = challengeOf cvB`, `cvB` the model's squeeze of `st 4`.

At `CompModel.deployed` they are `c_squeezes` and `c_bus` (`c_squeezes_of_comp`,
`c_bus_of_comp`).
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {S : BlakeSem} {C : CallRel} {rd : Reader} {D : VsData} {P : VsPtrs}

/-! ## The model's squeezes -/

/-- **`n` answered squeezes are a family of answered states** (`sqAll_eq`). -/
theorem sqAllM_states {M : HashModel} : ∀ (n : ℕ) (cv : Digest) {r : List E × Digest},
    sqAllM M n cv = some r → ∃ st : ℕ → Digest, st 0 = cv ∧
      (∀ k < n, sqCvM M (st k) = some (st (k + 1))) ∧
      r = ((List.range n).map fun k ↦ challengeOf (st (k + 1)), st n)
  | 0, cv, r, h => ⟨fun _ ↦ cv, rfl, fun k hk ↦ absurd hk (by omega), by
      simp only [sqAllM, Option.some.injEq] at h; subst h; rfl⟩
  | n + 1, cv, r, h => by
      simp only [sqAllM, Option.bind_eq_some_iff, Option.map_eq_some_iff] at h
      obtain ⟨cv', h1, r', h2, rfl⟩ := h
      obtain ⟨st, h0, hs, rfl⟩ := sqAllM_states n cv' h2
      refine ⟨fun k ↦ if k = 0 then cv else st (k - 1), by simp, fun k hk ↦ ?_, ?_⟩
      · rcases k with _ | k
        · simp [← h0, h1]
        · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
          exact hs k (by omega)
      · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.range_succ_eq_map,
          List.map_cons, List.map_map, Prod.mk.injEq, List.cons.injEq, h0, true_and, and_true]
        refine List.map_congr_left fun k _ ↦ ?_
        simp

/-! ## Squeezes, stored -/

/-- **`m` squeezes stored at `out` over a completeness model** (`c_squeezes`): from the state
`st 0` at `s0`, the model answering each squeeze from `st k` by `st (k + 1)`, the `k`-th challenge
`challengeOf (st (k + 1))` stored at `po[k]`, the state after them `st m`. -/
theorem c_squeezes_comp {CM : CompModel} {m s0 b0 : ℕ} {out : V} {po : E} {st : ℕ → Digest}
    (hm : 0 < m) (hs : s0 + 1 < b0) (ho : ∃ k < b0, out = .n k)
    (hsq : ∀ k < m, sqCvM CM.hm (st k) = some (st (k + 1)))
    (hst : ∀ k < m, LoadHolds rd po k (challengeOf (st (k + 1))))
    (hnb : ∀ k < m, NumBelow (b0 + 14 * (k + 1)) (Stmt.valsList (sqBlk s0 b0 out k))) (σ : Val)
    (hout : σ out = po) (h0 : (σ (.n s0), σ (.n (s0 + 1))) = digestScalars (st 0)) :
    CompletesB CM.sem C rd b0 (b0 + 14 * m) (bSqueezes m s0 b0 out) σ (fun σ' =>
      σ' out = po ∧ (σ' (.n (b0 + 14 * (m - 1) + 5)), σ' (.n (b0 + 14 * (m - 1) + 6))) =
        digestScalars (st m)) := by
  obtain ⟨ko, hko, rfl⟩ := ho
  rw [bSqueezes_eq]
  have key := CompletesB.flatten (S := CM.sem) (C := C) (rd := rd) (blk := sqBlk s0 b0 (.n ko))
    (st := fun k ↦ b0 + 14 * k) (Inv := fun k σ' ↦ σ' (.n ko) = po ∧
      (σ' (.n (if k = 0 then s0 else b0 + 14 * (k - 1) + 5)),
        σ' (.n ((if k = 0 then s0 else b0 + 14 * (k - 1) + 5) + 1))) = digestScalars (st k))
    m (fun k _ => by omega) hnb (fun k hk σ' ⟨io, is⟩ => ?_) σ ⟨hout, by simpa using h0⟩
  · refine key.post fun σ' _ ⟨io, is⟩ => ⟨io, ?_⟩
    have : m ≠ 0 := by omega
    simpa [this, show b0 + 14 * (m - 1) + 5 + 1 = b0 + 14 * (m - 1) + 6 by omega] using is
  · have hlt : (if k = 0 then s0 else b0 + 14 * (k - 1) + 5) + 1 < b0 + 14 * k := by
      split <;> omega
    have c := completesB_squeezeT_comp (C := C) (rd := rd) (b := b0 + 14 * k)
      ⟨_, by omega, rfl⟩ ⟨_, hlt, rfl⟩ is (hsq k hk) (Post := fun σ'' => σ'' (.n ko) = po ∧
        (σ'' (.n (b0 + 14 * k + 5)), σ'' (.n (b0 + 14 * k + 6))) = digestScalars (st (k + 1)) ∧
        σ'' (.n (b0 + 14 * k + 13)) = challengeOf (st (k + 1)))
      fun σ'' e h5 h13 => ⟨by rw [e.apply (by omega)]; exact io, h5, h13⟩
    rw [show b0 + 14 * (k + 1) = b0 + 14 * k + 14 by omega]
    refine c.append_atom fun σ'' ⟨jo, js, jc⟩ => ⟨?_, jo, ?_⟩
    · show LoadHolds rd (σ'' (.n ko)) k (σ'' (.n (b0 + 14 * k + 13)))
      rw [jo, jc]; exact hst k hk
    · simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel]
      rw [show b0 + 14 * k + 5 + 1 = b0 + 14 * k + 6 by omega]; exact js

theorem sqCvM_iterate_deployed (cv : Digest) (k : ℕ) :
    sqCvM CompModel.deployed.hm (sqCv^[k] cv) = some (sqCv^[k + 1] cv) := by
  rw [Function.iterate_succ_apply']; rfl

/-- The deployed `c_squeezes`, from the model's at `CompModel.deployed`. -/
theorem c_squeezes_of_comp {m s0 b0 : ℕ} {out : V} {po : E} {cv : Digest} (hm : 0 < m)
    (hs : s0 + 1 < b0) (ho : ∃ k < b0, out = .n k)
    (hst : ∀ k < m, LoadHolds rd po k (challengeOf (sqCv^[k + 1] cv)))
    (hnb : ∀ k < m, NumBelow (b0 + 14 * (k + 1)) (Stmt.valsList (sqBlk s0 b0 out k))) (σ : Val)
    (hout : σ out = po) (h0 : (σ (.n s0), σ (.n (s0 + 1))) = digestScalars cv) :
    Completes C rd b0 (b0 + 14 * m) (bSqueezes m s0 b0 out) σ (fun σ' =>
      σ' out = po ∧ (σ' (.n (b0 + 14 * (m - 1) + 5)), σ' (.n (b0 + 14 * (m - 1) + 6))) =
        digestScalars (sqCv^[m] cv)) :=
  (c_squeezes_comp (CM := CompModel.deployed) (st := fun k ↦ sqCv^[k] cv) hm hs ho
    (fun k _ ↦ sqCvM_iterate_deployed cv k) hst hnb σ hout h0).of_deployed

/-! ## `eq_weight` -/

theorem freeInList_append (F : List String) :
    ∀ (xs ys : List Stmt), Stmt.freeInList F (xs ++ ys) = (Stmt.freeInList F xs && Stmt.freeInList F ys)
  | [], _ => by simp [Stmt.freeInList]
  | x :: xs, ys => by
      simp only [List.cons_append, Stmt.freeInList, freeInList_append F xs ys, Bool.and_assoc]

theorem eqwCoord_free (x c v w : ℕ) : Stmt.freeInList [] (eqwCoord x c v w).1 = true := by
  unfold eqwCoord; split <;> split <;> rfl

theorem eqwEntry_free (x v : ℕ) : Stmt.freeInList [] (eqwEntry x v).1 = true := by
  simp only [eqwEntry, freeInList_append, eqwCoord_free, Bool.true_and]
  rfl

/-- **One entry of `fp_w` under any semantics** (`c_eqwEntry`). -/
theorem c_eqwEntryB {a : ℕ → E} (x v : ℕ) (hv : 508 < v)
    (ha : ∀ c < 4, LoadHolds rd P.alpha c (a c))
    (hfw : LoadHolds rd P.fpw x (eqFactor a x 0 * eqFactor a x 1 * eqFactor a x 2 * eqFactor a x 3))
    (σ : Val) (h451 : σ (.n 451) = P.alpha) (h508 : σ (.n 508) = P.fpw) :
    CompletesB S C rd v (eqwEntry x v).2 (eqwEntry x v).1 σ
      (fun σ' => σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw) :=
  CompletesB.of_free (eqwEntry_free x v) (c_eqwEntry x v hv ha hfw σ h451 h508)

/-! ## The block -/

/-- The values the bus challenges leave, the state after them `cvB` (`busOut`). -/
def busOutC (P : VsPtrs) (cvB : Digest) : List (ℕ × E) :=
  [(451, P.alpha), (508, P.fpw), (690, (digestScalars cvB).1), (691, (digestScalars cvB).2),
    (698, challengeOf cvB), (700, P.stream * gen ^ 10)]

theorem busOutC_deployed : busOutC P D.cvB = busOut D P := rfl

/-- **The bus challenges over a completeness model** (G:2137-2153, `c_bus`): from the root's
state `st 0`, the model's squeezes `st 1 … st 4` give the four `alpha`s stored, then `fp_w`,
`cvB` (the model's squeeze of `st 4`) and `beta`, the cursor. -/
theorem c_bus_comp {CM : CompModel} {st : ℕ → Digest} {cvB : Digest}
    (hsq : ∀ k < 4, sqCvM CM.hm (st k) = some (st (k + 1))) (hB : sqCvM CM.hm (st 4) = some cvB)
    (σ : Val) (hσ : Fixes σ ((14, P.stream) :: (rootOutC D (st 0)).drop 2))
    (ha : ∀ c < 4, LoadHolds rd P.alpha c (challengeOf (st (c + 1))))
    (hfw : ∀ x < 16, LoadHolds rd P.fpw x
      (eqFactor (fun c ↦ challengeOf (st (c + 1))) x 0 * eqFactor (fun c ↦ challengeOf (st (c + 1))) x 1 *
        eqFactor (fun c ↦ challengeOf (st (c + 1))) x 2 * eqFactor (fun c ↦ challengeOf (st (c + 1))) x 3)) :
    CompletesB CM.sem C rd 451 701 bBus σ (fun σ' => Fixes σ' (busOutC P cvB)) := by
  have h14 : σ (.n 14) = P.stream := hσ.get (by simp)
  have h447 : σ (.n 447) = (digestScalars (st 0)).1 := hσ.get (by simp [rootOutC])
  have h448 : σ (.n 448) = (digestScalars (st 0)).2 := hσ.get (by simp [rootOutC])
  rw [bBus_eq]
  refine CompletesB.append (m := 699) (P := fun σ' => (σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw ∧
      (σ' (.n 690), σ' (.n 691)) = digestScalars cvB ∧ σ' (.n 698) = challengeOf cvB) ∧
        Fixes σ' [(14, P.stream)]) (by omega) (by omega) (numBelow_of_B (by decide +kernel)) ?_
    fun σ3 _ ⟨⟨j451, j508, j690, j698⟩, j14⟩ => ?_
  · refine CompletesB.keep (l := [(14, P.stream)]) ?_ (by intro p hp; simp at hp; subst hp; exact h14)
      (by simp)
    refine CompletesB.append (m := 685) (P := fun σ' => σ' (.n 451) = P.alpha ∧ σ' (.n 508) = P.fpw ∧
        (σ' (.n 499), σ' (.n 500)) = digestScalars (st 4)) (by omega) (by omega)
      (numBelow_of_B (by decide +kernel)) ?_ fun σ2 _ ⟨j451, j508, j499⟩ => ?_
    · refine CompletesB.append (m := 508) (P := fun σ' => σ' (.n 451) = P.alpha ∧
          (σ' (.n 499), σ' (.n 500)) = digestScalars (st 4)) (by omega) (by omega)
        (numBelow_of_B (by decide +kernel)) ?_ fun σ1 _ ⟨j451, j499⟩ => ?_
      · rw [← List.singleton_append]
        refine CompletesB.append (m := 452) (P := fun σ' => σ' (.n 451) = P.alpha ∧
            (σ' (.n 447), σ' (.n 448)) = digestScalars (st 0)) (by omega) (by omega)
          (numBelow_of_B (by decide +kernel))
          (completesB_hint (k := 451) P.alpha (by vs_ev; rw [h447, h448]; exact ⟨trivial, rfl⟩))
          fun σ' _ ⟨i451, i447⟩ => ?_
        exact c_squeezes_comp (m := 4) (s0 := 447) (b0 := 452) (by omega) (by omega) ⟨451, by omega, rfl⟩
          hsq ha numBelow_sq451 σ' i451 i447
      · rw [← List.singleton_append]
        refine CompletesB.append (m := 509) (P := fun σ' => σ' (.n 451) = P.alpha ∧
            σ' (.n 508) = P.fpw ∧ (σ' (.n 499), σ' (.n 500)) = digestScalars (st 4))
          (by omega) (by omega) (numBelow_of_B (by decide +kernel))
          (completesB_hint (k := 508) P.fpw (by vs_ev; exact ⟨j451, trivial, j499⟩))
          fun σ' _ ⟨i451, i508, i499⟩ => ?_
        have key := CompletesB.flatten (S := CM.sem) (C := C) (rd := rd)
          (blk := fun x ↦ (eqwEntry x (eqwStart x)).1) (st := eqwStart)
          (Inv := fun _ σ'' ↦ σ'' (.n 451) = P.alpha ∧ σ'' (.n 508) = P.fpw) 16
          (fun x hx => (eqwStart_mono x hx).2) numBelow_eqw
          (fun x hx σ'' ⟨k451, k508⟩ => c_eqwEntryB x (eqwStart x) (eqwStart_mono x hx).1 ha
            (hfw x hx) σ'' k451 k508) σ' ⟨i451, i508⟩
        rw [eqwStart_16] at key
        refine (key.keep (l := [(499, (digestScalars (st 4)).1),
          (500, (digestScalars (st 4)).2)]) ?_ (by simp; decide)).post
          fun σ'' _ ⟨⟨k451, k508⟩, kf⟩ => ⟨k451, k508, ?_⟩
        · intro p hp
          simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
          rcases hp with rfl | rfl
          · exact congrArg Prod.fst i499
          · exact congrArg Prod.snd i499
        · rw [kf.get (k := 499) (e := (digestScalars (st 4)).1) (by simp),
            kf.get (k := 500) (e := (digestScalars (st 4)).2) (by simp)]
    · exact completesB_squeezeT_comp (b := 685) ⟨499, by omega, rfl⟩ ⟨500, by omega, rfl⟩ j499 hB
        fun σ' e h5 h13 => ⟨by rw [e.apply (by omega)]; exact j451, by rw [e.apply (by omega)]; exact j508,
          h5, h13⟩
  · refine completesB_upds [(699, word 1024 0 0), (700, P.stream * gen ^ 10)] (by simp)
      (fun next kret hn => ?_) ?_
    · simp only [Stmt.HoldsListB, Stmt.HoldsB, Atom.HoldsB]
      vs_ev
      have w10 : word 1024 0 0 = gen ^ 10 := word_two_pow (a := 10) (by decide)
      rw [j14.get (k := 14) (e := P.stream) (by simp), w10]
      exact ⟨trivial, rfl, hn⟩
    · intro p hp
      simp only [busOutC, List.mem_cons, List.mem_nil_iff, or_false] at hp
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> vs_ev
      · exact j451
      · exact j508
      · exact congrArg Prod.fst j690
      · exact congrArg Prod.snd j690
      · exact j698

/-- The deployed `c_bus`, from the model's at `CompModel.deployed`. -/
theorem c_bus_of_comp (σ : Val) (hσ : Fixes σ ((14, P.stream) :: (rootOut D).drop 2))
    (ha : ∀ c < 4, LoadHolds rd P.alpha c (busA D c))
    (hfw : ∀ x < 16, LoadHolds rd P.fpw x (eqFactor (busA D) x 0 * eqFactor (busA D) x 1 *
      eqFactor (busA D) x 2 * eqFactor (busA D) x 3)) :
    Completes C rd 451 701 bBus σ (fun σ' => Fixes σ' (busOut D P)) := by
  refine (c_bus_comp (CM := CompModel.deployed) (st := fun k ↦ sqCv^[k] D.cv10) (cvB := D.cvB)
    (fun k _ ↦ sqCvM_iterate_deployed D.cv10 k) ?_ σ hσ ha hfw).of_deployed
  simp only [VsData.cvB, sqAll_eq]
  rfl

end
end LeanVM.Guest.B1.VerifySub
