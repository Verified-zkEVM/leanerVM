/-
  LeanVM.Guest.B1.Sig.SphincsMidComplete

  The atoms of `verify_sig_lean_sphincs` between the forest and the codeword complete: the counter
  hinted as its bytes, its word, the 292-byte encoding over the forest key and the powers.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsStepComplete
public import LeanVM.Guest.B1.Sig.SphincsBytesComplete
public import LeanVM.Guest.B1.Sig.SphincsCoordsComplete
public import LeanVM.Guest.B1.Sig.SphincsParts

/-!
# Between the forest and the codeword, complete

* `sCoord_tops_nb`, `sB_ge`, `sT_nb`: the forest key's nodes lie below the counter's base `sB`;
* `csts_seq`: a run of constants is sequential;
* `sMid_complete`: the counter `ctr < 2^32` hinted as its four bytes, its word, the encoding the
  digest of the forest key and the counter, and the powers.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat gen)

@[expose] public section

attribute [local irreducible] fkArms foldArms sSubtree sCoords kMsg

variable {C : CallRel} {rd : Reader}

/-- A coordinate's two level-3 nodes lie below its end. -/
theorem sCoord_tops_nb (c : Nat) {enc : Option V} {bound : V} {b : Nat} (hb : 206 ≤ b)
    (henc : ∀ en, enc = some en → NBv b en) (hbd : NBv b bound) :
    NBv (sCoord c enc bound b).2.1 (sCoord c enc bound b).2.2.2.2.1 ∧
      NBv (sCoord c enc bound b).2.1 (sCoord c enc bound b).2.2.2.2.2 := by
  obtain ⟨s1, -, -, -⟩ := sCoord_shape c hb henc hbd
  set f := (coordS1 c enc bound b).2.1 with hf
  have hfo := foAB_mono (atV := .n (b + 6)) (adr := coordAdr) (height := 4) (node0 := .n (f + 5))
    (markV := .n (b + 1)) (markC := coordMark c) (wC := fun s => cbMul s (26 + 4 * c)) (b := f + 18)
  have hfo3 := foldArms_outs (atV := .n (b + 6)) (adr := coordAdr) (height := 4) (node0 := .n (f + 5))
    (markV := .n (b + 1)) (markC := coordMark c) (wC := fun s => cbMul s (26 + 4 * c)) (f + 18)
  have hLfE : flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 3 ≤ (coordFd c b f).2.1 := by
    have h1 : foAB (.n (b + 6)) coordAdr 4 (.n (f + 5)) (.n (b + 1)) (coordMark c)
        (fun s => cbMul s (26 + 4 * c)) (f + 18) 1 = flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 3 := by
      rw [foAB_one, foldArm_snd, foldLevels_snd]; rfl
    rw [← h1, coordFd_eq, foldArms_end]; exact (hfo 1).2 16 (by omega)
  have hend : (coordFd c b f).2.1 ≤ (sCoord c enc bound b).2.1 := by
    rw [sCoord_fst, ← hf]; split <;> omega
  have ht : (sCoord c enc bound b).2.2.2.2 = ((coordFd c b f).2.2.1, (coordFd c b f).2.2.2.1) := by
    rw [sCoord_eq]
  have hfd : (coordFd c b f).2.2 = (.n (flBase (coordAdr 0) 0 (4 - 1) (f + 18)),
      .n (flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 1), .n (flBase (coordAdr 0) 0 (4 - 1) (f + 18) + 2)) := by
    rw [coordFd_eq, hfo3]
  rw [ht, hfd]
  exact ⟨⟨_, by omega, rfl⟩, ⟨_, by omega, rfl⟩⟩

/-- The counter's base is past the frame's constants. -/
theorem sB_eq : sB = (cSt 8).2.2 := (sCoords_end 8 0).1

theorem sB_ge : 206 ≤ sB := by rw [sB_eq]; exact (cSt_shape 8).1

/-- **The forest key's nodes lie below the counter's base.** -/
theorem sT_nb {k : Nat} (hk : k < 16) : NBv sB (sCs.2.2.2.2.getD k (.n 0)) := by
  have e := sCoords_tops 8 0
  have hp := getD_pairs (fun k => (cCoord (0 + k)).2.2.2.2.1) (fun k => (cCoord (0 + k)).2.2.2.2.2)
    (.n 0) 8 (k / 2) (by omega)
  obtain ⟨b1, b2, b3, -⟩ := cSt_shape (k / 2)
  obtain ⟨t1, t2⟩ := sCoord_tops_nb (k / 2) b1 b2 b3
  have hle : (cSt (k / 2 + 1)).2.2 ≤ sB := by
    have := cSt_mono (k / 2 + 1) (7 - k / 2)
    rw [show k / 2 + 1 + (7 - k / 2) = 8 by omega] at this
    rw [sB_eq]; exact this
  have hend : (sCoord (k / 2) (cSt (k / 2)).1 (cSt (k / 2)).2.1 (cSt (k / 2)).2.2).2.1 = (cSt (k / 2 + 1)).2.2 := rfl
  rw [show sCs = sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2 from rfl, e]
  rcases Nat.mod_two_eq_zero_or_one k with h0 | h1
  · rw [show k = 2 * (k / 2) by omega, hp.1, Nat.zero_add]
    exact (hend ▸ t1).mono' hle
  · rw [show k = 2 * (k / 2) + 1 by omega, hp.2, Nat.zero_add]
    exact (hend ▸ t2).mono' hle

/-- A run of constants is sequential. -/
theorem csts_seq (b : Nat) (w : Nat → E) : ∀ n, SeqOK b ((List.range n).map fun s => cst (b + s) (w s)) (b + n)
  | 0 => rfl
  | n + 1 => by
      rw [List.range_succ, List.map_append]
      exact SeqOK.append (csts_seq b w n) ⟨rfl, rfl⟩

theorem sFb_shape : sFb.2.1 = sB + 37 ∧ NBv (sB + 37) sFb.2.2 ∧ NumBelow (sB + 37) (Stmt.valsList sFb.1) := by
  obtain ⟨r1, r2, r3⟩ := sFromBytes_shape (.n (sB + 3)) [.n (sB + 2), .n (sB + 1), .n sB] g255W (sB + 4)
    ⟨sB + 3, by omega, rfl⟩ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro m (rfl | rfl | rfl) <;> exact ⟨_, by omega, rfl⟩)
  exact ⟨r1, r2, r3⟩

/-- The counter's bytes, low first. -/
def ctrByte (ctr j : Nat) : Nat := ctr / 256 ^ j % 256

theorem sMid_split : sMid = [hintW "sp_counter" (runV sB 4)] ++ (sFb.1 ++ ([copyS (.n sFb.2.1) sFb.2.2] ++
    (sEnc.1 ++ (List.range 10).map (fun s => cst (sEnc.2.1 + s) (word (2 ^ s) 0 0))))) := by
  simp only [sMid, List.append_assoc]

/-- **Between the forest and the codeword, complete**: the counter `ctr < 2^32` hinted as its
bytes, its word at `sFb.2.1`, the encoding's digest the digest of the forest key and the counter, the
chain step's values. -/
theorem sMid_complete (hm : MemOK rd 256) {bb : E} (hbb : ByteBits rd bb) (σ : Val)
    (h1 : σ (.n 1) = bb) (hP : IsCanonical128 (σ sPP)) (hn0 : IsCanonical128 (σ (sNode 0)))
    (h162 : IsCanonical128 (σ (.n 162))) (h164 : IsCanonical128 (σ (.n 164)))
    (htops : ∀ k < 16, IsCanonical128 (sT σ k)) (hpad : PadOK σ sPad) {ctr N : Nat} (hctr : ctr < 2 ^ 32)
    (hd : (digestScalars (keccak256 ((cellsBytes (σ (.n 162) :: σ (.n 164) ::
      (List.range 16).map (sT σ) ++ [eOfNat ctr])).take 292))).1 = lit N) :
    Completes C rd sB (sEnc.2.1 + 10) sMid σ (fun σ' => σ' (.n sFb.2.1) = eOfNat ctr ∧
      σ' (.n sEnc.2.2) = lit N ∧ SGood sEnc.2.1 σ' ∧
      ∀ j < 4, σ' (.n (sB + j)) = ofK (gpow (ctrByte ctr j))) := by
  have hB := sB_ge
  obtain ⟨f1, f2, f3⟩ := sFb_shape
  -- the encoding's cells and bounds
  have hcellsNB : ∀ c ∈ sTops.map KC.cell, KCb (sFb.2.1 + 1) c := by
    intro c hc
    simp only [sTops, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hc
    rcases hc with ((rfl | rfl) | ⟨v, hv, rfl⟩) | rfl
    · exact ⟨162, by omega, rfl⟩
    · exact ⟨164, by omega, rfl⟩
    · obtain ⟨k, hk, e⟩ := List.getElem_of_mem hv
      have hk16 : k < 16 := by rw [sTops_count] at hk; exact hk
      have := sT_nb hk16
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, e] at this
      exact this.mono' (by omega)
    · exact ⟨_, by omega, rfl⟩
  have hE1 : sFb.2.1 + 1 ≤ sEnc.2.1 := kMsg_le (by simp [sPad]; omega) hcellsNB
  have hE2 : sEnc.2.2 + 13 ≤ sEnc.2.1 := kMsg_out _ _ _ _ _
  rw [sMid_split]
  -- the counter's bytes
  set g : Nat → E := fun j => ofK (gpow (ctrByte ctr j)) with hg
  refine Completes.reload ((updRun_ext σ sB 4 g).mono le_rfl (by omega)) ?_
  set σr := updRun σ sB 4 g with hσr
  have rlow : ∀ k < sB, σr (.n k) = σ (.n k) := fun k hk => updRun_below σ sB 4 g ⟨k, hk, rfl⟩
  refine Completes.append (m := sB + 4) (by omega) (by omega)
    (by rw [valsList_hint]; exact fun v hv => runV_mem_nb (by omega) hv) (hintKeep_complete _ _ _ _ _)
    (fun σ2 _ e2 => ?_)
  subst e2
  have hbyte : ∀ j < 4, σr (.n (sB + j)) = ofK (gpow (ctrByte ctr j)) := fun j hj => updRun_at σ sB 4 g hj
  have hfb := sFromBytes_complete (C := C) hm hbb (K := 256) (v0 := ctrByte ctr 3) le_rfl
    (Nat.mod_lt _ (by norm_num)) (.n (sB + 3)) [.n (sB + 2), .n (sB + 1), .n sB]
    [ctrByte ctr 2, ctrByte ctr 1, ctrByte ctr 0] (sB + 4) σr (by omega) ⟨sB + 3, by omega, rfl⟩
    (hbyte 3 (by norm_num))
    (.cons ⟨⟨sB + 2, by omega, rfl⟩, hbyte 2 (by norm_num), Nat.mod_lt _ (by norm_num)⟩
      (.cons ⟨⟨sB + 1, by omega, rfl⟩, hbyte 1 (by norm_num), Nat.mod_lt _ (by norm_num)⟩
        (.cons ⟨⟨sB, by omega, rfl⟩, hbyte 0 (by norm_num), Nat.mod_lt _ (by norm_num)⟩ .nil)))
    (by rw [rlow 1 (by omega)]; exact h1) (by norm_num)
  rw [← g255W_k] at hfb
  have hfold : bFold (ctrByte ctr 3) [ctrByte ctr 2, ctrByte ctr 1, ctrByte ctr 0] = ctr := by
    simp only [bFold, ctrByte]
    omega
  rw [hfold] at hfb
  rw [show sB + 4 + 6 + 9 * [V.n (sB + 2), V.n (sB + 1), V.n sB].length = sB + 37 by simp] at hfb
  have hfb' : Completes C rd (sB + 4) sFb.2.1 sFb.1 σr (fun σ' => σ' sFb.2.2 = eOfNat ctr) := by
    rw [f1]; exact hfb
  refine Completes.append (m := sFb.2.1) (by omega) (by omega) (by rw [f1]; exact f3) hfb'
    (fun σ3 he3 hp3 => ?_)
  -- the counter's word
  have f2' : NBv sFb.2.1 sFb.2.2 := by rw [f1]; exact f2
  refine Completes.append (m := sFb.2.1 + 1) (by omega) (by omega) (nb_copyS f2')
    (copyS_complete σ3 sFb.2.1 f2') (fun σ4 he4 hp4 => ?_)
  replace hp4 : σ4 (.n sFb.2.1) = eOfNat ctr := hp4.trans hp3
  have tr4 : ∀ k < sB, σ4 (.n k) = σ (.n k) := fun k hk => by
    rw [he4.apply (Or.inl (by omega)), he3.apply (Or.inl (by omega)), rlow k hk]
  have hT4 : ∀ k < 16, sT σ4 k = sT σ k := fun k hk => by
    unfold sT
    obtain ⟨j, hj, e⟩ := sT_nb hk
    rw [e, tr4 j hj]
  -- the encoding
  have hck : ∀ c ∈ sTops.map KC.cell, KCb (sFb.2.1 + 1) c ∧ KCc σ4 c := by
    intro c hc
    refine ⟨hcellsNB c hc, ?_⟩
    simp only [sTops, List.map_append, List.map_cons, List.map_nil, List.mem_append, List.mem_cons,
      List.not_mem_nil, or_false, List.mem_map] at hc
    show IsCanonical128 _
    rcases hc with ((rfl | rfl) | ⟨v, hv, rfl⟩) | rfl
    · show IsCanonical128 (σ4 (.n 162)); rw [tr4 162 (by omega)]; exact h162
    · show IsCanonical128 (σ4 (.n 164)); rw [tr4 164 (by omega)]; exact h164
    · obtain ⟨k, hk, e⟩ := List.getElem_of_mem hv
      have hk16 : k < 16 := by rw [sTops_count] at hk; exact hk
      have := hT4 k hk16
      unfold sT at this
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hk, Option.getD_some, e] at this
      show IsCanonical128 (σ4 v)
      rw [this, ← Option.getD_some (a := v) (b := V.n 0), ← e, ← List.getElem?_eq_getElem hk,
        ← List.getD_eq_getElem?_getD]
      exact htops k hk16
    · show IsCanonical128 (σ4 (.n sFb.2.1)); rw [hp4, ← word_eq_eOfNat]; exact canon_word _ 0
  have hpad4 : PadOK σ4 sPad := hpad.congr (b := sB) (by simp only [sPad]; omega) (fun k hk => (tr4 k hk).symm)
  obtain ⟨hk1, hk2, -⟩ := kMsg_complete (C := C) (rd := rd) (tailRun := true) (len := 292) σ4 hpad4
    (by simp only [sPad]; omega) hck (fun _ => tailCells_292 sTops (by simp [sTops, sTops_count]) _)
  refine Completes.append (m := sEnc.2.1) (by omega) (by omega) hk2 hk1.withHolds (fun σ5 he5 hp5 => ?_)
  have hlk : AtomsHold rd σ5 sEnc.1 := atomsHold_of_holdsList (kMsg_atoms ..) hp5.2
  have tr5 : ∀ k < sFb.2.1 + 1, σ5 (.n k) = σ4 (.n k) := fun k hk => he5.apply (Or.inl hk)
  have hpad5 : PadOK σ5 sPad := hpad4.congr (b := sFb.2.1 + 1) (by simp only [sPad]; omega)
    (fun k hk => (tr5 k hk).symm)
  have hx5 : σ5 (.n sFb.2.1) = eOfNat ctr := by rw [tr5 _ (by omega)]; exact hp4
  have henc := sEnc_sound hpad5 hlk hctr hx5
  have hT5 : ∀ k < 16, sT σ5 k = sT σ k := fun k hk => by
    unfold sT
    obtain ⟨j, hj, e⟩ := sT_nb hk
    rw [e, tr5 j (by omega)]
    have := hT4 k hk
    unfold sT at this
    rw [e] at this
    exact this
  have hrange : (List.range 16).map (sT σ5) = (List.range 16).map (sT σ) :=
    List.map_congr_left fun k hk => hT5 k (List.mem_range.mp hk)
  rw [hrange, hx5, tr5 162 (by omega), tr5 164 (by omega), tr4 162 (by omega), tr4 164 (by omega), hd] at henc
  -- the powers
  refine Completes.seq (m := sEnc.2.1 + 10) (csts_seq sEnc.2.1 (fun s => word (2 ^ s) 0 0) 10) le_rfl
    (fun σ6 he6 hh6 => ?_)
  refine ⟨σ6, Ext.refl _ _ _, ⟨?_, ?_, ?_, fun j hj => ?_⟩, fun _ _ hn => hn⟩
  rotate_left 3
  · rw [he6.apply (Or.inl (by omega)), tr5 _ (by omega), he4.apply (Or.inl (by omega)),
      he3.apply (Or.inl (by omega))]
    exact hbyte j hj
  · rw [he6.apply (Or.inl (by omega))]; exact hx5
  · rw [he6.apply (Or.inl (by omega))]; exact henc
  · have tr6 : ∀ k < sB, σ6 (.n k) = σ (.n k) := fun k hk => by
      rw [he6.apply (Or.inl (by omega)), tr5 k (by omega), tr4 k hk]
    refine ⟨by show IsCanonical128 (σ6 (.n 2)); rw [tr6 2 (by omega)]; exact hP,
      by show IsCanonical128 (σ6 (.n 131)); rw [tr6 131 (by omega)]; exact hn0,
      hpad.congr (b := sB) (by simp [sPad]; omega) (fun k hk => (tr6 k hk).symm), fun s hs => ?_⟩
    have e : σ6 (.n (sEnc.2.1 + s)) = word (2 ^ s) 0 0 :=
      hh6.atom (a := .const (.n (sEnc.2.1 + s)) _) (by
        simp only [List.mem_map, List.mem_range]
        exact ⟨s, hs, rfl⟩)
    rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]

end
end LeanVM.Guest.B1.Sig
