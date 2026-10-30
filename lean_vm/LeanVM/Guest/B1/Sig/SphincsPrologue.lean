/-
  LeanVM.Guest.B1.Sig.SphincsPrologue

  The prologue of `verify_sig_lean_sphincs` (`lean_ethereum.py:3632-3677`) is sound: the message
  digest, the index's bits and node indices, the bound's start, the encoding's first two cells and
  the address constants.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsCoords
public import LeanVM.Guest.B1.Sig.SphincsBytes

/-!
# The prologue, sound

`sIdx σ`: the index the frame's bits spell. `SPre σ`: what the prologue establishes
(`sPrologue_sound`); `SBound σ`: the bound's start, `idx` plus the unused bytes' word at bit
`106`, which needs the byte table (`sPrologue_bound`).
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

/-- The index the frame's bits spell. -/
noncomputable def sIdx (σ : Val) : Nat := bitsOf σ 30 26

theorem sIdx_lt (σ : Val) : sIdx σ < 2 ^ 26 := bitsVal_lt _ _

/-- What the prologue establishes. -/
structure SPre (rd : Reader) (σ : Val) : Prop where
  ldP : LoadHolds rd (σ (.n 0)) 1 (σ sPP)
  ld2 : LoadHolds rd (σ (.n 0)) 2 (σ (.n 5))
  ld3 : LoadHolds rd (σ (.n 0)) 3 (σ (.n 6))
  msgAdr : σ (.n 4) = word (tw 12) 0 0
  digest : (σ (.n 17), σ (.n 18)) = hcell [σ sPP, σ (.n 4), σ (.n 5), σ (.n 6), σ (.n 3)]
  pad : PadOK σ sPad
  bits : ∀ l < 26, IsBit (σ (sBit l))
  nodes : ∀ l < 26, σ (sNode l) = eOfNat (sIdx σ >>> l)
  tws : TwsOK σ
  subTws : ∀ a < 8, ∀ l < 2, σ (sSubTws (2 * a + l)) =
    word (a * 2 ^ 40 ^^^ (tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42)) 0 0
  top0 : σ (.n 162) = σ sPP
  top1 : σ (.n 164) = σ (sNode 0) + word (tw 4) 0 0
  bound0 : σ (.n 161) = σ (sNode 0) + σ (.n 158) * word 0 (2 ^ 42) 0

theorem sPrologue_atoms : atomsOnly sPrologue = true := by
  decide

theorem mem_sPrologue_twsWords {k : Nat} (hk : k < 25) :
    cst (165 + k) (sTwsWords.getD k 0) ∈ sPrologue := by
  have hl : sTwsWords.length = 25 := by simp [sTwsWords]
  have : (sTwsWords.getD k 0, k) ∈ sTwsWords.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hk : k < sTwsWords.length)]
  simp only [sPrologue, List.mem_append, List.mem_map]
  exact Or.inl (Or.inr ⟨_, this, rfl⟩)

theorem mem_sPrologue_subTwsWords {k : Nat} (hk : k < 16) :
    cst (190 + k) (sSubTwsWords.getD k 0) ∈ sPrologue := by
  have hl : sSubTwsWords.length = 16 := by simp [sSubTwsWords]
  have : (sSubTwsWords.getD k 0, k) ∈ sSubTwsWords.zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?]
    simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (hl ▸ hk : k < sSubTwsWords.length)]
  simp only [sPrologue, List.mem_append, List.mem_map]
  exact Or.inr ⟨_, this, rfl⟩

theorem sTwsWords_getD {i s : Nat} (hi : i < 6) (hs : s < 4) :
    sTwsWords.getD (4 * i + s) 0 = word (tw 15 + i * 2 ^ 43 + s * stepMul) 0 0 := by
  interval_cases i <;> interval_cases s <;> rfl

theorem sTwsWords_getD24 : sTwsWords.getD 24 0 = word (tw 16) 0 0 := rfl

theorem sSubTwsWords_getD {a l : Nat} (ha : a < 8) (hl : l < 2) :
    sSubTwsWords.getD (2 * a + l) 0 =
      word (a * 2 ^ 40 ^^^ (tw 17 + (l + 1) * 2 ^ 40 + a / 2 ^ (l + 1) * 2 ^ 42)) 0 0 := by
  interval_cases a <;> interval_cases l <;> rfl

theorem sPrologue_sound {rd : Reader} {σ : Val} (h : AtomsHold rd σ sPrologue) : SPre rd σ := by
  have mem : ∀ a : Atom, Stmt.atom a ∈ sPrologue → a.Holds rd σ := h
  have hb : ∀ l < 26, IsBit (σ (sBit l)) := by
    intro l hl
    have := h.atom (a := .mul (.n (30 + l)) (.n (30 + l)) (.n (30 + l))) (by
      simp only [sPrologue, List.mem_append, booleans, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨l, hl, rfl⟩)))))))
    exact this.symm
  have c8 : σ (.n 8) = word 1 0 0 := mem (.const (.n 8) _) (by simp [sPrologue, cst])
  have c9 : σ (.n 9) = word 0 0 0 := mem (.const (.n 9) _) (by simp [sPrologue, cst])
  have c10 : σ (.n 10) = word 0 0 0 := mem (.const (.n 10) _) (by simp [sPrologue, cst])
  have c11 : σ (.n 11) = word (2 ^ 63) 0 0 := mem (.const (.n 11) _) (by simp [sPrologue, cst])
  have hpad : PadOK σ sPad := by
    have p : ∀ k < 5, σ (.n (12 + k)) = word (if k = 0 then 1 else 0) 0 0 := fun k hk =>
      mem (.const (.n (12 + k)) _) (by
        simp only [sPrologue, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl
          (Or.inr ⟨k, hk, rfl⟩)))))))))
    have p0 := p 0 (by norm_num)
    have p1 := p 1 (by norm_num)
    have p2 := p 2 (by norm_num)
    have p3 := p 3 (by norm_num)
    have p4 := p 4 (by norm_num)
    simp only [↓reduceIte, one_ne_zero, OfNat.ofNat_ne_zero, word_zero] at p0 p1 p2 p3 p4
    exact ⟨p0, p1, p2, p3, p4⟩
  have hcp : σ (.n 7) = σ (.n 3) := mem (.copy (.n 7) (.n 3)) (by simp [sPrologue, copyS])
  rw [word_zero] at c9 c10
  have hk := kec80_sound (o := 17) (pp := sPP) (adr := .n 4) (m0 := .n 5) (m1 := .n 6) (r := .n 7)
    (t1 := .n 8) (t2 := .n 9) (t3 := .n 10) (t4 := .n 11) (z1 := .n 13) (z2 := .n 14) (z3 := .n 15)
    (z4 := .n 16) (h.sub fun x hx => by
      simp only [List.mem_singleton] at hx
      subst hx
      simp [sPrologue]) c8 c9 c10 c11 hpad.2.1 hpad.2.2.1 hpad.2.2.2.1 hpad.2.2.2.2
  rw [hcp] at hk
  refine ⟨mem (.load sPP (.n 0) 1) (by simp [sPrologue, loadS]),
    mem (.load (.n 5) (.n 0) 2) (by simp [sPrologue, loadS]),
    mem (.load (.n 6) (.n 0) 3) (by simp [sPrologue, loadS]),
    mem (.const (.n 4) _) (by simp [sPrologue, cst]), hk, hpad, hb, fun l hl => ?_,
    ⟨fun i hi s hs => ?_, ?_⟩, fun a ha l hl => ?_,
    mem (.copy (.n 162) sPP) (by simp [sPrologue, copyS]), ?_, ?_⟩
  · have hs := shifts_sound (σ := σ) (rd := rd) (bitBase := 30) (n := 26) (outBase := 56) (by norm_num)
      (by norm_num) hb (h.sub fun x hx => by
        simp only [sPrologue, List.mem_append]
        exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr hx)))))) (25 - l) (by omega)
    rw [sNode, hs, sIdx]
    congr 2
    omega
  · have := mem _ (mem_sPrologue_twsWords (k := 4 * i + s) (by omega))
    rw [sTwsWords_getD hi hs] at this
    exact this
  · have := mem _ (mem_sPrologue_twsWords (k := 24) (by omega))
    rw [sTwsWords_getD24] at this
    exact this
  · have := mem _ (mem_sPrologue_subTwsWords (k := 2 * a + l) (by omega))
    rw [sSubTwsWords_getD ha hl] at this
    exact this
  · have a1 : σ (.n 164) = σ (sNode 0) + σ (.n 163) :=
      mem (.add (.n 164) (sNode 0) (.n 163)) (by simp [sPrologue, addS])
    have a2 : σ (.n 163) = word (tw 4) 0 0 := mem (.const (.n 163) _) (by simp [sPrologue, cst])
    rw [a1, a2]
  · have a1 : σ (.n 161) = σ (sNode 0) + σ (.n 160) :=
      mem (.add (.n 161) (sNode 0) (.n 160)) (by simp [sPrologue, addS])
    have a2 : σ (.n 160) = σ (.n 158) * σ (.n 159) :=
      mem (.mul (.n 160) (.n 158) (.n 159)) (by simp [sPrologue, mulS])
    have a3 : σ (.n 159) = word 0 (2 ^ 42) 0 := mem (.const (.n 159) _) (by simp [sPrologue, cst])
    rw [a1, a2, a3]

theorem sFromBytes_unused : (sFromBytes (.n 134) [.n 133, .n 132] g63W 135).2.2 = .n 158 := rfl

theorem word_hi_mul {N : Nat} (hN : N < 2 ^ 22) : eOfNat N * word 0 (2 ^ 42) 0 = word 0 (N * 2 ^ 42) 0 := by
  rw [mul_comm, eOfNat, word, word, ofLimbs_mul_ofK, ofBits_zero, zero_mul]
  congr 1
  rw [Nat.mul_comm N]
  exact Value.ofBits_two_pow_mul (by omega)

/-- **The bound's start**: with the byte table, `idx` plus the unused bytes' word below `2^22` at
bit `106`. -/
theorem sPrologue_bound {κ : Nat} (hκ : κ ≤ 32) {L : MemImage κ} {σ : Val}
    (hbb : ByteBits L.read (σ (.n 1))) (h : AtomsHold L.read σ sPrologue) :
    ∃ N < 2 ^ 22, σ (.n 161) = σ (sNode 0) + word 0 (N * 2 ^ 42) 0 := by
  have hb := (sPrologue_sound h).bound0
  have hf : AtomsHold L.read σ (sFromBytes (.n 134) [.n 133, .n 132] g63W 135).1 :=
    h.sub fun x hx => by
      simp only [sPrologue, List.mem_append]
      exact Or.inl (Or.inl (Or.inl (Or.inr hx)))
  obtain ⟨N, hN, hlt⟩ := sFromBytes_sound hκ hbb (K := 64) (by norm_num) (by norm_num) g63W_eq
    (by norm_num) hf
  rw [sFromBytes_unused] at hN
  refine ⟨N, by simpa using hlt, ?_⟩
  rw [hb, hN, word_hi_mul (by simpa using hlt)]

end
end LeanVM.Guest.B1.Sig
