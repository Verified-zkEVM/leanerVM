/-
  LeanVM.Guest.B1.Comp.VerifySub.Blocks

  `verify_sub`'s Fiat-Shamir blocks complete over a completeness model: `fs_next` and `squeeze`
  from the model's answers.
-/

module

public import LeanVM.Guest.B1.Comp.CompletesB
public import LeanVM.Guest.B1.Comp.FsBlocks
public import LeanVM.Guest.B1.Comp.VerifySub.Seed

/-!
# `fs_next` and `squeeze` over a completeness model

`completes_fsNextT` and `completes_squeezeT` (`VerifySub/CBlocks.lean`) over a `CompModel`: from a
state of `cv`, the block's new state is the model's answer `d` (`obsCvM CM.hm cv x = some d`,
`sqCvM CM.hm cv = some d`), its values `fsValsD`, `sqValsD` (`holdsB_fsNextT_comp`,
`holdsB_squeezeT_comp`). At `CompModel.deployed` they are the deployed lemmas
(`completes_fsNextT_of_comp`, `completes_squeezeT_of_comp`).

Also the model's chain over a list of words (`obsAllM`) taken apart at a prefix and a last word
(`obsAllM_append`, `obsAllM_take_succ`), as the announced words absorb one by one.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Protocol LeanVM.Protocol.Blake2sHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Guest.B1.Sig LeanVM.E2E.Complete

@[expose] public section

variable {C : CallRel} {rd : Reader}

/-! ## Values kept below a block -/

/-- A block completing keeps the values below its range (`Completes.keep`). -/
theorem _root_.LeanVM.Guest.B1.Sig.CompletesB.keep {S : BlakeSem} {lo hi : ℕ} {ss : List Stmt}
    {σ : Val} {P : Val → Prop} {l : List (ℕ × E)} (h : CompletesB S C rd lo hi ss σ P)
    (hl : Fixes σ l) (hlo : ∀ p ∈ l, p.1 < lo) :
    CompletesB S C rd lo hi ss σ (fun σ' => P σ' ∧ Fixes σ' l) := by
  obtain ⟨σ', he, hp, hh⟩ := h
  exact ⟨σ', he, ⟨hp, hl.of_ext he hlo⟩, hh⟩

/-- A block's fixed values added to the ones kept (`completes_step`). -/
theorem completesB_step {S : BlakeSem} {lo hi : ℕ} {blk : List Stmt} {σ : Val}
    {Out G : List (ℕ × E)} (h : CompletesB S C rd lo hi blk σ (fun σ' => Fixes σ' Out))
    (hG : Fixes σ G) (hlo : ∀ p ∈ G, p.1 < lo) :
    CompletesB S C rd lo hi blk σ (fun σ' => Fixes σ' (Out ++ G)) :=
  (h.keep hG hlo).post fun _ _ ⟨a, b⟩ => a.append b

/-- The last block, its values kept (`completes_last`). -/
theorem completesB_last {S : BlakeSem} {lo hi : ℕ} {blk : List Stmt} {σ : Val}
    {G : List (ℕ × E)} (h : CompletesB S C rd lo hi blk σ (fun _ => True)) (hG : Fixes σ G)
    (hlo : ∀ p ∈ G, p.1 < lo) : CompletesB S C rd lo hi blk σ (fun σ' => Fixes σ' G) :=
  (h.keep hG hlo).post fun _ _ ⟨_, b⟩ => b

/-! ## `fs_next` -/

/-- The values of an `fs_next` block from its first, the word read, its new state the digest
`d` (`fsNextVals`). -/
def fsNextValsD (x : E) (d : Digest) : ℕ → E
  | 0 => x
  | k + 1 => fsValsD x d 1 k

/-- **`fs_next` completes over a completeness model** (`completes_fsNextT`): from a state of
`cv`, with `x` at the cursor's offset `j` and the model answering its absorb by `d`, the block
reads `x` and its state cells become `d`'s. -/
theorem completesB_fsNextT_comp {CM : CompModel} {s0 s1 cur : V} {j b : ℕ} {σ : Val}
    {cv d : Digest} {x : E} {Post : Val → Prop} (hs0 : ∃ k < b, s0 = .n k)
    (hs1 : ∃ k < b, s1 = .n k) (hcur : ∃ k < b, cur = .n k)
    (hcv : (σ s0, σ s1) = digestScalars cv) (hx : LoadHolds rd (σ cur) j x)
    (hd : obsCvM CM.hm cv x = some d)
    (hp : ∀ σ', Ext b (b + 15) σ σ' → σ' (.n b) = x →
      (σ' (.n (b + 13)), σ' (.n (b + 14))) = digestScalars d → Post σ') :
    CompletesB CM.sem C rd b (b + 15) (fsNextT s0 s1 cur j b) σ Post := by
  have hb : setv σ b 15 (fsNextValsD x d) (.n b) = x := by
    rw [set_n_in (by omega) (by omega)]; simp [fsNextValsD]
  refine completesB_setv (fsNextValsD x d) (fun next kret hn => ?_)
    (hp _ (setv_extB σ b 15 _) hb ?_)
  · refine holdsB_fsNextT_comp s0 s1 cur j b ⟨⟨?_, cv, d, ?_, ?_, fun k h1 h2 => ?_⟩, hn⟩
    · rw [setv_below hcur, hb]; exact hx
    · rw [setv_below hs0, setv_below hs1]; exact hcv
    · rw [hb]; exact hd
    · rw [set_n_in (by omega) (by omega), hb]
      simp only [fsNextValsD, show b + 1 + k - b = k + 1 by omega]
  · rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show b + 13 - b = 12 + 1 by omega, show b + 14 - b = 13 + 1 by omega]
    rfl

/-- The deployed `completes_fsNextT`, from the model's at `CompModel.deployed`. -/
theorem completes_fsNextT_of_comp {s0 s1 cur : V} {j b : ℕ} {σ : Val} {cv : Digest} {x : E}
    {Post : Val → Prop} (hs0 : ∃ k < b, s0 = .n k) (hs1 : ∃ k < b, s1 = .n k)
    (hcur : ∃ k < b, cur = .n k) (hcv : (σ s0, σ s1) = digestScalars cv)
    (hx : LoadHolds rd (σ cur) j x)
    (hp : ∀ σ', Ext b (b + 15) σ σ' → σ' (.n b) = x →
      (σ' (.n (b + 13)), σ' (.n (b + 14))) = digestScalars (obsCv cv x) → Post σ') :
    Completes C rd b (b + 15) (fsNextT s0 s1 cur j b) σ Post :=
  (completesB_fsNextT_comp (CM := CompModel.deployed) hs0 hs1 hcur hcv hx rfl hp).of_deployed

/-! ## `squeeze` -/

/-- **`squeeze` completes over a completeness model** (`completes_squeezeT`): from a state of
`cv`, with the model answering the squeeze by `d`, the new state is `d`'s and the challenge
`challengeOf d`. -/
theorem completesB_squeezeT_comp {CM : CompModel} {s0 s1 : V} {b : ℕ} {σ : Val} {cv d : Digest}
    {Post : Val → Prop} (hs0 : ∃ k < b, s0 = .n k) (hs1 : ∃ k < b, s1 = .n k)
    (hcv : (σ s0, σ s1) = digestScalars cv) (hd : sqCvM CM.hm cv = some d)
    (hp : ∀ σ', Ext b (b + 14) σ σ' →
      (σ' (.n (b + 5)), σ' (.n (b + 6))) = digestScalars d →
      σ' (.n (b + 13)) = challengeOf d → Post σ') :
    CompletesB CM.sem C rd b (b + 14) (squeezeT s0 s1 b) σ Post := by
  refine completesB_setv (sqValsD d) (fun next kret hn => ?_) (hp _ (setv_extB σ b 14 _) ?_ ?_)
  · refine holdsB_squeezeT_comp s0 s1 b ⟨⟨cv, d, ?_, hd, fun k hk => ?_⟩, hn⟩
    · rw [setv_below hs0, setv_below hs1]; exact hcv
    · rw [set_n_in (by omega) (by omega), show b + k - b = k by omega]
  · rw [set_n_in (by omega) (by omega), set_n_in (by omega) (by omega),
      show b + 5 - b = 5 by omega, show b + 6 - b = 6 by omega]
    rfl
  · rw [set_n_in (by omega) (by omega), show b + 13 - b = 13 by omega]
    rfl

/-- The deployed `completes_squeezeT`, from the model's at `CompModel.deployed`. -/
theorem completes_squeezeT_of_comp {s0 s1 : V} {b : ℕ} {σ : Val} {cv : Digest}
    {Post : Val → Prop} (hs0 : ∃ k < b, s0 = .n k) (hs1 : ∃ k < b, s1 = .n k)
    (hcv : (σ s0, σ s1) = digestScalars cv)
    (hp : ∀ σ', Ext b (b + 14) σ σ' →
      (σ' (.n (b + 5)), σ' (.n (b + 6))) = digestScalars (sqCv cv) →
      σ' (.n (b + 13)) = challengeOf (sqCv cv) → Post σ') :
    Completes C rd b (b + 14) (squeezeT s0 s1 b) σ Post :=
  (completesB_squeezeT_comp (CM := CompModel.deployed) hs0 hs1 hcv (sqCvM_hm_deployed cv) hp).of_deployed

/-! ## The model's chain over words -/

theorem obsAllM_append (M : HashModel) : ∀ (cv : Digest) (xs ys : List E),
    obsAllM M cv (xs ++ ys) = (obsAllM M cv xs).bind fun c ↦ obsAllM M c ys
  | cv, [], ys => rfl
  | cv, x :: xs, ys => by
      simp only [List.cons_append, obsAllM, Option.bind_assoc]
      congr 1
      funext c
      exact obsAllM_append M c xs ys

theorem obsAllM_singleton (M : HashModel) (cv : Digest) (x : E) :
    obsAllM M cv [x] = obsCvM M cv x := by
  simp only [obsAllM]
  cases obsCvM M cv x <;> rfl

/-- A prefix of an answered chain is answered. -/
theorem obsAllM_take {M : HashModel} {cv c : Digest} {xs : List E} (h : obsAllM M cv xs = some c)
    (k : ℕ) : ∃ c', obsAllM M cv (xs.take k) = some c' := by
  rw [← List.take_append_drop k xs, obsAllM_append] at h
  cases h' : obsAllM M cv (xs.take k) with
  | none => rw [h'] at h; exact absurd h (by simp)
  | some c' => exact ⟨c', rfl⟩

/-- One more word of an answered chain: the model answers its absorb. -/
theorem obsAllM_take_succ {M : HashModel} {cv c c' : Digest} {xs : List E} {k : ℕ}
    (hk : k < xs.length) (h : obsAllM M cv (xs.take (k + 1)) = some c')
    (h0 : obsAllM M cv (xs.take k) = some c) : obsCvM M c (xs.getD k 0) = some c' := by
  rw [List.take_add_one, List.getElem?_eq_getElem hk, Option.toList_some, obsAllM_append, h0,
    Option.bind_some, obsAllM_singleton] at h
  rw [List.getD_eq_getElem _ _ hk]
  exact h

end
end LeanVM.Guest.B1.VerifySub
