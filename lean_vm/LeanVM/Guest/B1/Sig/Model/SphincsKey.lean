/-
  LeanVM.Guest.B1.Sig.Model.SphincsKey

  `sp_forest_key__L{t}` under a hash model (`SphincsKey` over `M.sem`): the six chains of an opened
  forest key, each step an answered hash, and the child leaf their answered hash.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsCoord
public import LeanVM.Guest.B1.Sig.Model.SphincsScheme

/-!
# The forest keys under a hash model

`FkLeafWith H t pp ka vals leaf`: the six chains of codeword `t` from `vals` end at answered
hashes (`fChainWith`), and `leaf` is the first cell of the answered hash of their ends
(`fkLeaf`). `FkOutWith` is `FkOut` over it, `FkSoundWith`/`FkSoundWWith` are `FkSound`/`FkSoundW`.

* `fkChain_model`, `fkChains_model` (`fkChain_sound`, `fkChains_sound_w`);
* `fkBody_model` (`fkBody_out_w`), `sp_forest_key_model` (`sp_forest_key_sound`, over
  `coreProgram.RelB M.sem`), `fkSoundWith_relB`, `exists_fkSoundWWith` (`exists_fkSoundW`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value

@[expose] public section

variable {M : HashModel} {C : CallRel} {rd : Reader}

/-! ## The chains -/

/-- **A forest chain under a model** (`fkChain_sound`): its tip is the chain walked its deficit from
the hinted value, every step answered. -/
theorem fkChain_model {σ : Val} {i d b : Nat} {next : Prop} {kret : List E → Prop}
    (h : Stmt.HoldsListB M.sem C rd σ (fkChain i d b) next kret) :
    fChainWith M.H (σ (.n 1)) (σ (.n 0)) i (4 - d) (σ (.n b)) d = some (σ (.n (fkTip d b))) ∧ next := by
  rw [fkChain, hintW, holdsB_hint_cons, holdsListB_flatMap_range _ (fun _ => rfl)] at h
  obtain ⟨hb, hn⟩ := h
  refine ⟨?_, hn⟩
  rw [fkTip_after σ d b]
  suffices ∀ m ≤ d, fChainWith M.H (σ (.n 1)) (σ (.n 0)) i (4 - d) (σ (.n b)) m = some (fkAfter σ b m) from
    this d le_rfl
  intro m hm
  induction m with
  | zero => rfl
  | succ m ih =>
      have hj := hb m (by omega)
      simp only [cst, ivs, b2s, addS, List.cons_append, List.nil_append, holdsListB_cons_atom, holdsListB_nil,
        Atom.HoldsB] at hj
      obtain ⟨h0, h1, h2, h3, h4, h5, hc, -⟩ := hj
      rw [h1, h0, h2, h3, h4, h5, word_zero] at hc
      have hprev : σ (if m = 0 then V.n b else V.n (b + 1 + 8 * m - 2)) = fkAfter σ b m := by
        unfold fkAfter; split
        · rfl
        · congr 2; omega
      rw [hprev] at hc
      obtain ⟨-, ho⟩ := compress3_model hc
      rw [fChainWith, ih (by omega), Option.bind_some, ← word_eq_eOfNat, ho, Option.map_some, fkAfter,
        ite_neg' (by omega), show b + 1 + 8 * (m + 1 - 1) + 6 = b + 1 + 8 * m + 6 by omega]

/-- **The chains of a forest key under a model**, from their hinted values (`fkChains_sound_w`). -/
theorem fkChains_model (t : Nat) {σ : Val} :
    ∀ (m i b : Nat) {next : Prop} {kret : List E → Prop},
      Stmt.HoldsListB M.sem C rd σ (fkChains t m i b).1 next kret →
      (∀ r < m, fChainWith M.H (σ (.n 1)) (σ (.n 0)) (i + r) (4 - spCode t (i + r))
        (fkValsFrom t σ m i b (i + r)) (spCode t (i + r)) = some (σ (.n ((fkChains t m i b).2.2.getD r 0)))) ∧ next
  | 0, _, _, _, _, h => ⟨fun _ h => absurd h (by omega), h⟩
  | m + 1, i, b, next, kret, h => by
      simp only [fkChains, holdsListB_append] at h ⊢
      obtain ⟨htip, h⟩ := fkChain_model h
      obtain ⟨hv, hn⟩ := fkChains_model t m (i + 1) _ h
      refine ⟨fun r hr => ?_, hn⟩
      rcases r with _ | r
      · simpa [fkValsFrom] using htip
      · have := hv r (by omega)
        simp only [List.getD_cons_succ]
        rw [← this, show i + 1 + r = i + (r + 1) by omega]
        simp [fkValsFrom]

/-! ## The key -/

/-- **The child leaf of forest key `t`, answered**: the six chains from `vals` end at answered
hashes, and `leaf` is the first cell of the answered hash of their ends (`fkLeaf`). -/
def FkLeafWith (H : List UInt8 → Option Protocol.Digest) (t : Nat) (pp ka : E) (vals : Nat → E) (leaf : E) : Prop :=
  ∃ ends : Nat → E, (∀ k < 6, fChainWith H pp ka k (4 - spCode t k) (vals k) (spCode t k) = some (ends k)) ∧
    ∃ o, hcellWith H (pp :: (ka + eOfNat (tw 16)) :: (List.range 6).map ends) = some o ∧ leaf = o.1

theorem fkLeafWith_deployed {t : Nat} {pp ka : E} {vals : Nat → E} {leaf : E} :
    FkLeafWith HashModel.deployed.H t pp ka vals leaf ↔ leaf = fkLeaf t pp ka vals := by
  constructor
  · rintro ⟨ends, he, o, ho, rfl⟩
    rw [hcellWith_deployed, Option.some.injEq] at ho
    subst ho
    rw [fkLeaf, show (List.range 6).map ends = (List.range 6).map
        (fun k => fChain pp ka k (4 - spCode t k) (vals k) (spCode t k)) from List.map_congr_left fun k hk => by
      have := he k (List.mem_range.mp hk)
      rw [fChainWith_deployed, Option.some.injEq] at this
      exact this.symm]
  · rintro rfl
    exact ⟨fun k => fChain pp ka k (4 - spCode t k) (vals k) (spCode t k), fun k _ => fChainWith_deployed _ _ _ _ _ _,
      _, hcellWith_deployed _, rfl⟩

/-- What a call of `sp_forest_key__L{t}` returns from the chain values `vals`, answered (`FkOut`). -/
def FkOutWith (H : List UInt8 → Option Protocol.Digest) (t : Nat) (args rets : List E) (vals : Nat → E) : Prop :=
  ∃ ka pp, args = [ka, pp] ∧ ∃ leaf, FkLeafWith H t pp ka vals leaf ∧ rets = [leaf, word t 0 0]

/-- **`sp_forest_key__L{t}` under a model**, its frame naming the chain values (`fkBody_out_w`). -/
theorem fkBody_model (t : Nat) {σ : Val} {rets : List E}
    (h : Stmt.HoldsListB M.sem C rd σ (fkBody t) False (fun rs => rs = rets)) :
    FkOutWith M.H t [σ (.n 0), σ (.n 1)] rets (fkVals t σ) := by
  simp only [fkBody, holdsListB_append] at h
  obtain ⟨hv, h⟩ := fkChains_model t 6 0 2 h
  simp only [cst, ivs, b2s, addS, holdsListB_cons_atom, Atom.HoldsB, Stmt.HoldsListB, Stmt.HoldsB, List.map_cons,
    List.map_nil] at h
  obtain ⟨h0, h1, h2, h3, h4, hc1, h7, hc2, h10, h11, hr⟩ := h
  rw [h1, h0, h2, h3, h4] at hc1
  rw [h7] at hc2
  set tip : Nat → E := fun k => σ (.n ((fkChains t 6 0 2).2.2.getD k 0)) with htip
  have hr4 : (blockBytes ![tip 2, tip 3, tip 4, tip 5]).length = 64 := length_blockBytes _
  have hc2' := hc2
  rw [show (128 : Nat) = 64 + (blockBytes ![tip 2, tip 3, tip 4, tip 5]).length by rw [hr4]] at hc2'
  obtain ⟨-, -, -, ho⟩ := compress_two_model (M := M) (b1 := ![tip 2, tip 3, tip 4, tip 5]) (r := blockBytes _)
    (by rw [hr4]; simp) (by rw [hr4]) (by rw [hr4]; omega) hc1 hc2'
  refine ⟨σ (.n 0), σ (.n 1), rfl, σ (.n ((fkChains t 6 0 2).2.1 + 10)), ⟨tip, fun k hk => ?_,
    (σ (.n ((fkChains t 6 0 2).2.1 + 8)), σ (.n ((fkChains t 6 0 2).2.1 + 9))), ?_, ?_⟩, ?_⟩
  · have := hv k hk
    simp only [Nat.zero_add] at this
    exact this
  · rw [hcellWith, ← ho, blockBytes_four, blockBytes_four, ← List.flatMap_append, word_eq_eOfNat]
    simp only [List.range_succ, List.range_zero, List.nil_append, List.map_cons, List.map_nil, List.cons_append]
    rfl
  · exact h10
  · rw [← hr, h11]

theorem find_fkB {t : Nat} (ht : t < 256) : coreProgram.find? (fkNames.getD t "") = some (fkFn t) := find_fk ht

/-- **`sp_forest_key__L{t}` is sound under a model** (`sp_forest_key_sound`). -/
theorem sp_forest_key_model {t : Nat} (ht : t < 256) {args rets : List E}
    (h : coreProgram.RelB M.sem rd (fkNames.getD t "") args rets) : ∃ vals, FkOutWith M.H t args rets vals := by
  obtain ⟨σ, hp, hb⟩ := (relB_iff_sem (find_fk ht) args rets).mp h
  have hb : Stmt.HoldsListB M.sem (coreProgram.RelB M.sem rd) rd σ (fkBody t) False (fun rs => rs = rets) := hb
  have hp : [σ (.n 0), σ (.n 1)] = args := hp
  exact ⟨_, hp ▸ fkBody_model t hb⟩

/-- The forest keys are sound under the call relation `C`, under a model (`FkSound`). -/
def FkSoundWith (M : HashModel) (C : CallRel) : Prop :=
  ∀ t < 256, ∀ args rets, C (fkNames.getD t "") args rets → ∃ vals, FkOutWith M.H t args rets vals

theorem fkSoundWith_relB : FkSoundWith M (coreProgram.RelB M.sem rd) :=
  fun _ ht _ _ h => sp_forest_key_model ht h

/-- The forest keys are sound under `C`, under a model, with the witness `wfk` (`FkSoundW`). -/
def FkSoundWWith (M : HashModel) (C : CallRel) (wfk : List E → List E → Nat → E) : Prop :=
  ∀ t < 256, ∀ args rets, C (fkNames.getD t "") args rets → FkOutWith M.H t args rets (wfk args rets)

/-- One witness serves every key (`exists_fkSoundW`). -/
theorem exists_fkSoundWWith (hfk : FkSoundWith M C) : ∃ wfk, FkSoundWWith M C wfk := by
  have key : ∀ args rets : List E, ∃ vals : Nat → E,
      ∀ t < 256, C (fkNames.getD t "") args rets → FkOutWith M.H t args rets vals := by
    intro args rets
    by_cases hc : ∃ t < 256, C (fkNames.getD t "") args rets
    · obtain ⟨t0, ht0, hc0⟩ := hc
      obtain ⟨vals, ka, pp, ha, leaf, hl, hr⟩ := hfk t0 ht0 _ _ hc0
      refine ⟨vals, fun t ht hct => ?_⟩
      obtain ⟨vals', ka', pp', -, leaf', -, hr'⟩ := hfk t ht _ _ hct
      have htt : t = t0 := by
        rw [hr] at hr'
        simp only [List.cons.injEq, word_eq_eOfNat] at hr'
        exact (eOfNat_inj (by omega) (by omega) hr'.2.1).symm
      subst htt
      exact ⟨ka, pp, ha, leaf, hl, hr⟩
    · exact ⟨fun _ => 0, fun t ht hct => absurd ⟨t, ht, hct⟩ hc⟩
  choose wfk hw using key
  exact ⟨wfk, fun t ht args rets h => hw args rets t ht h⟩

end
end LeanVM.Guest.B1.Sig
