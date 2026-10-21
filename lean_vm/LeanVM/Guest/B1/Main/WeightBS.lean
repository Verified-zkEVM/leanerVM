/-
  LeanVM.Guest.B1.Main.WeightBS

  `WeightB.lean` under any semantics of `BLAKE2S` (`S : BlakeSem`).
-/

module

public import LeanVM.Guest.B1.Main.WeightB
public import LeanVM.Guest.B1.Main.WeightLoopS

/-!
# `WeightB.lean` under any `BLAKE2S` semantics

Each definition and lemma of `WeightB.lean` that mentions the semantics, with `S : BlakeSem` a
parameter and a `S` in its name.
-/

namespace LeanVM.Guest.B1.Main

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.Memory
open LeanVM.Guest.B1 (DisjL Within LowDef CompleteAtB Kid CallsMatch OutsOk OutsIn RegionsOk outRegion
  kidsBound)

@[expose] public section

variable {S : BlakeSem}


variable {fs : String → ℕ} {cert : String → V → ℕ} {Θ : Type} {w : Θ → String → ℕ}

/-- **Every `CompleteAtBS` is `CompleteAtWS` at no weights.** -/
theorem CompleteAtB.toWES {w : Empty → String → ℕ} {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Empty → ℕ} (h : CompleteAtBS S fs cert κ f Lin args Out B) :
    CompleteAtWS S fs cert w κ f Lin args Out B Bw :=
  CompleteAtB.toWS h fun θ => θ.elim

/-- **A `CompleteAtBS` within the words of its valid trees** at the frame sizes `w θ`. -/
theorem CompleteAtB.toWS_total {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} (h : CompleteAtBS S fs cert κ f Lin args Out B)
    (hT : ∀ θ (rd : Reader) (t : Tree) (rets : List E), t.name = f → t.ValidB S coreProgram rd args rets →
      t.BufsOk coreProgram → t.total (w θ) ≤ Bw θ) :
    CompleteAtWS S fs cert w κ f Lin args Out B Bw :=
  CompleteAtB.toWS h fun θ rd t rets hn hv hb => (weight_le_total _ t).trans (hT θ rd t rets hn hv hb)

/-- **A `CompleteAtBS` within the words of its valid trees on the memories holding `Lin`.** -/
theorem CompleteAtB.toWS_memTot {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B : ℕ} {Bw : Θ → ℕ} (h : CompleteAtBS S fs cert κ f Lin args Out B)
    (hT : ∀ θ (rd : Reader), MemL rd Lin → ∀ (t : Tree) (rets : List E), t.name = f →
      t.ValidB S coreProgram rd args rets → t.BufsOk coreProgram → t.total (w θ) ≤ Bw θ) :
    CompleteAtWS S fs cert w κ f Lin args Out B Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn, fun rd hl hm =>
    let ⟨t, a, b, c, d, e, f', g⟩ := hr rd hl hm
    ⟨t, a, b, c, d, e, f', g, fun θ => (weight_le_total _ t).trans
      (hT θ rd (memL_append.mp hm).2 t rets a b c)⟩⟩

theorem CompleteAtWS.bmono {κ : ℕ} {f : String} {Lin : Layout} {args : List E}
    {Out : List E → Layout → Prop} {B B' : ℕ} {Bw : Θ → ℕ} (h : CompleteAtWS S fs cert w κ f Lin args Out B Bw)
    (hB : B ≤ B') : CompleteAtWS S fs cert w κ f Lin args Out B' Bw := fun fp =>
  let ⟨n, Lown, rets, Lout, ho, hW, hd, hn, hr⟩ := h fp
  ⟨n, Lown, rets, Lout, ho, hW, hd, hn.trans hB, hr⟩

theorem kidsWS_of (κ : ℕ) (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) : ∀ ks : List Kid,
    (∀ k ∈ ks, k.taken = true → CompleteAtWS S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k)) →
    KidsWS S fs cert w κ ks (ks.map fun k => if k.taken = true then bd k else fs k.f) (kidsWs bdw ks)
  | [], _ => trivial
  | k :: ks, h => by
      refine ⟨fun ht => ?_, fun ht => ?_, kidsWS_of κ bd bdw ks fun k' hk' => h k' (by simp [hk'])⟩
      · simp only [ht, ↓reduceIte]
        exact (h k (by simp) ht).wmono fun θ => by simp
      · simp [ht]

/-- **`kidsFromInS_append` within weights**, the weights of the first callees one per callee. -/
theorem kidsFromInWS_append {rd : Reader} {σ : Val} {R : ℕ → Prop} :
    ∀ (cs1 cs2 : List Call) (bws1 bws2 : List (Θ → ℕ)) (Dacc : ℕ → Prop) (b n1 n2 : ℕ) (D1 D : ℕ → Prop),
      bws1.length = cs1.length →
      KidsFromInWS S fs cert w rd σ R Dacc cs1 bws1 b n1 D1 →
      (∀ Dacc' : ℕ → Prop, (∀ i, D1 i → Dacc' i) →
        KidsFromInWS S fs cert w rd σ R Dacc' cs2 bws2 (b + n1) n2 D) →
      KidsFromInWS S fs cert w rd σ R Dacc (cs1 ++ cs2) (bws1 ++ bws2) b (n1 + n2) D
  | [], cs2, [], bws2, Dacc, b, n1, n2, D1, D, _, ⟨hn, hD⟩, h2 => by
    subst hn; simpa using h2 Dacc hD
  | [], _, _ :: _, _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: _, _, [], _, _, _, _, _, _, _, hl, _, _ => absurd hl (by simp)
  | _ :: cs1, cs2, _ :: bws1, bws2, Dacc, b, n1, n2, D1, D, hl, ⟨m, n', Rk, Dk, hn, hR, hc, hk⟩, h2 =>
    ⟨m, n' + n2, Rk, Dk, by omega, hR, hc,
      kidsFromInWS_append cs1 cs2 bws1 bws2 _ (b + m) n' n2 D1 D (by simpa using hl) hk fun Dacc' h => by
        rw [show b + m + n' = b + n1 by omega]; exact h2 Dacc' h⟩

/-- **`kidsFromInS_of_kidsB` within weights**: each entered callee within `bdw`. -/
theorem kidsFromInWS_of_kidsBW (κ : ℕ) (bd : Kid → ℕ) (bdw : Kid → Θ → ℕ) (ks : List Kid)
    (hok : ∀ k ∈ ks, k.taken = true → CompleteAtWS S fs cert w κ k.f k.Lin k.args k.Out (bd k) (bdw k))
    (b : ℕ) :
    ∃ (N : ℕ) (L : Layout) (outs : List (List E × Layout)), OutsOk ks outs ∧ Within L b N ∧
      DisjL L ∧ N ≤ kidsBound fs bd ks ∧ OutsIn ks outs L ∧
      ∀ (rd : Reader) (σ : Val) (cs : List Call) (R Dacc : ℕ → Prop), CallsMatch σ cs ks outs →
        LowDef κ rd → MemL rd L → MemL rd (Kid.lins ks) → RegionsOk R Dacc ks outs →
        KidsFromInWS S fs cert w rd σ R Dacc cs (kidsWs bdw ks) b N (fun i => Dacc i ∨ outRegion ks outs i) :=
  kidsFromInWS_of_kidsW κ ks _ _ (kidsWS_of κ bd bdw ks hok) b

end
end LeanVM.Guest.B1.Main
