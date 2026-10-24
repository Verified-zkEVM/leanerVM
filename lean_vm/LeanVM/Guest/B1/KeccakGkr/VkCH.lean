/-
  LeanVM.Guest.B1.KeccakGkr.VkCH

  `verify_keccak`'s honest data: where each part of the stream is, the openings' sponges, the
  claims' records.
-/

module

public import LeanVM.Guest.B1.KeccakGkr.VkCG

/-!
# The honest data, read

For a `VkData` `D` with `D.Ok`:

* `D.xs` split (`xs_reads`): the committed word, layer `s`'s words at `lcur s`, the openings'
  rounds, the word and the slices after them.
* The sponges: after the layers, after each opening, empty (`L_snd`, `O_snd`, …).
* `CL_ok`: claim `s`'s record and buffers (`CL`) hold what `ClaimLay.Ok` asks, wherever the
  layers' buffers are.
-/

namespace LeanVM.Guest.B1.VerifySub

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1
open LeanVM.Guest.Memory
open LeanVM.Protocol LeanVM.Protocol.KeccakHash LeanVM.Protocol.Compile LeanVM.Protocol.Verifier
open LeanVM.Protocol.KeccakGkr

@[expose] public section

theorem readsAt_mid {rd : Reader} {p : E} {A B C : List E} (h : ReadsAt rd p (A ++ B ++ C)) :
    ReadsAt rd (p * gen ^ A.length) B :=
  (Digest.readsAt_append.1 (Digest.readsAt_append.1 h).1).2

theorem flatMap_range_split (f : ℕ → List E) {s n : ℕ} (hs : s < n) :
    (List.range n).flatMap f =
      (List.range s).flatMap f ++ f s ++ (List.range' (s + 1) (n - s - 1)).flatMap f := by
  rw [List.range_eq_range', List.range_eq_range',
    show n = s + (1 + (n - s - 1)) by omega, ← List.range'_append, ← List.range'_append]
  simp [List.flatMap_append]

theorem flatMap_range_length (f : ℕ → List E) {c : ℕ} : ∀ {s : ℕ}, (∀ k < s, (f k).length = c) →
    ((List.range s).flatMap f).length = s * c
  | 0, _ => by simp
  | s + 1, h => by
    rw [List.range_succ, List.flatMap_append, List.length_append, flatMap_range_length f
      (fun k hk ↦ h k (by omega))]
    simp [h s (by omega)]
    ring

theorem flatMap_eq_range {α : Type} [Inhabited α] (l : List α) (f : α → List E) :
    l.flatMap f = (List.range l.length).flatMap fun k ↦ f (l.getD k default) := by
  conv_lhs => rw [show l = (List.range l.length).map (fun k ↦ l.getD k default) from
    List.ext_getElem (by simp) (fun k h1 h2 ↦ by simp [List.getElem?_eq_getElem h1])]
  rw [List.flatMap_map]

namespace VkData

variable {D : VkData}

theorem layer_xs (s : ℕ) : (D.layer s).xs = ltXs (D.T s) := rfl

theorem ltXs_length (h : D.Ok) {s : ℕ} (hs : s < 12) :
    (ltXs (D.T s)).length = 47 + 2 * (D.τ - 3) + 36 := by
  rw [← layer_xs]
  obtain ⟨hpl, hpm, hlm, -, -⟩ := D.layer_facts h hs
  rw [LayerData.xs_length hpl hpm hlm, D.layer_y h (by omega)]

theorem xs_eq (h : D.Ok) : D.xs = [D.committed] ++ (List.range 12).flatMap (fun s ↦ ltXs (D.T s)) ++
    (D.mO.flatMap (fun m ↦ [m.1, m.2]) ++ [D.word] ++ D.mI.flatMap (fun m ↦ [m.1, m.2]) ++
      D.mS.flatMap (fun m ↦ [m.1, m.2]) ++ D.slices) := by
  rw [xs, flatMap_eq_range D.Ts ltXs, ok_Ts h]
  simp only [List.append_assoc]
  rfl

/-- **The stream, split.** -/
theorem xs_reads (h : D.Ok) {rd : Reader} {curE : ℕ} (hr : ReadsAt rd (ptr curE) D.xs) :
    LoadHolds rd (ptr curE) 0 D.committed ∧
      (∀ s < 12, ReadsAt rd (ptr (curE + D.lcur s)) (ltXs (D.T s))) ∧
      ReadsAt rd (ptr (curE + D.lcur 12)) (D.mO.flatMap fun m ↦ [m.1, m.2]) ∧
      LoadHolds rd (ptr (curE + D.lcur 12 + 12)) 0 D.word ∧
      ReadsAt rd (ptr (curE + D.lcur 12 + 13)) (D.mI.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (ptr (curE + D.lcur 12 + 21)) (D.mS.flatMap fun m ↦ [m.1, m.2]) ∧
      ReadsAt rd (ptr (curE + D.lcur 12 + 33)) D.slices := by
  obtain ⟨-, -, -, -, -, -, -, hmO, hmI, hmS, -, -, -⟩ := id h
  have hc : ∀ k < 12, (ltXs (D.T k)).length = 47 + 2 * (D.τ - 3) + 36 :=
    fun k hk ↦ ltXs_length h hk
  rw [xs_eq h] at hr
  refine ⟨?_, fun s hs ↦ ?_, ?_⟩
  · have := (Digest.readsAt_append.1 (Digest.readsAt_append.1 hr).1).1 0 (by simp)
    simpa using this
  · rw [flatMap_range_split _ hs] at hr
    have := readsAt_mid (A := [D.committed] ++ (List.range s).flatMap fun s ↦ ltXs (D.T s))
      (by simpa only [List.append_assoc] using hr)
    rw [ptr_mul_gen, List.length_append, flatMap_range_length _ (fun k hk ↦ hc k (by omega))] at this
    simpa [lcur, Nat.add_assoc, Nat.add_comm] using this
  · have h1 := (Digest.readsAt_append.1 hr).2
    rw [ptr_mul_gen, List.length_append, flatMap_range_length _ hc] at h1
    simp only [List.length_singleton] at h1
    rw [show curE + (1 + 12 * (47 + 2 * (D.τ - 3) + 36)) = curE + D.lcur 12 by simp [lcur]]
      at h1
    simp only [Digest.readsAt_append, flatMap_pairs_length, hmO, hmI, List.length_append,
      List.length_singleton, ptr_mul_gen] at h1
    obtain ⟨⟨⟨⟨r1, r2⟩, r3⟩, r4⟩, r5⟩ := h1
    refine ⟨r1, by simpa using r2 0 (by simp), by simpa using r3, ?_, ?_⟩
    · simpa [Nat.add_assoc] using r4
    · simpa [Nat.add_assoc, hmS] using r5

end VkData

end
end LeanVM.Guest.B1.VerifySub
