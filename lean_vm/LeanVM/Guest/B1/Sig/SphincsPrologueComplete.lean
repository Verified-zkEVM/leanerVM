/-
  LeanVM.Guest.B1.Sig.SphincsPrologueComplete

  The prologue of `verify_sig_lean_sphincs` (`lean_ethereum.py:3632-3677`) completes: `P` and the
  message loaded, the randomizer hinted, the index's bits the digest's second cell's low bits, the
  unused bytes its bits from `106`.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsBytesComplete
public import LeanVM.Guest.B1.Sig.SphincsPrologue
public import LeanVM.Guest.B1.Sig.XmssPieces
public import LeanVM.Guest.B1.Sig.SphincsDigest

/-!
# The prologue, complete

* `eq_eOfNat192_cellNat`: a canonical cell is the `u192` word of its integer;
* `sPrologue_split`: the prologue, block by block;
* `sPrologue_complete`: the prologue completes; `P`, the message's cells and the randomizer are
  where it reads them, the index's bits are the second digest cell's low `26` bits and `n158` the
  word of its bits from `106`.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Protocol.Verifier (eOfNat)

@[expose] public section

variable {C : CallRel} {rd : Reader}

theorem canon_eOfNat192 {n : Nat} (h : n < 2 ^ 128) : IsCanonical128 (eOfNat192 n) := by
  show (E.ofLimbs _ _ _).limb 2 = 0
  rw [Nat.div_eq_of_lt h]
  simp [ofBits_zero]

/-- A canonical cell is the `u192` word of its integer. -/
theorem eq_eOfNat192_cellNat {x : E} (hx : IsCanonical128 x) : x = eOfNat192 (cellNat x) := by
  have hl := cellNat_lt x
  exact cellVal_inj hx (canon_eOfNat192 hl)
    (BitVec.eq_of_toNat_eq (by rw [toNat_cellVal, toNat_cellVal, cellNat_eOfNat192 hl]))

/-- The prologue's constants after the copy of the randomizer. -/
def pSeq7 : List Stmt :=
  [copyS (.n 7) (.n 3), cst 8 (word 1 0 0), cst 9 (word 0 0 0), cst 10 (word 0 0 0),
    cst 11 (word (2 ^ 63) 0 0)] ++ (List.range 5).map (fun k => cst (12 + k) (word (if k = 0 then 1 else 0) 0 0))

/-- The message digest's `KECCAK`. -/
def pKec : Stmt :=
  kecS [sPP, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10, .n 11, .n 13, .n 14, .n 15, .n 16]
    (runV 17 13) false false

/-- The index's bits, hinted and pinned Boolean. -/
def pChecks : List Stmt := .atom (.hint (.bits (.n 18) 0 26 (.stack (runV 30 26)))) :: booleans 30 26

/-- The bound's start, `tops[0]`, `tops[1]` and the address constants. -/
def pTail : List Stmt :=
  [cst 159 (word 0 (2 ^ 42) 0), mulS (.n 160) (.n 158) (.n 159), addS (.n 161) (sNode 0) (.n 160),
    copyS (.n 162) sPP, cst 163 (word (tw 4) 0 0), addS (.n 164) (sNode 0) (.n 163)] ++
  (sTwsWords.zipIdx.map fun (w, k) => cst (165 + k) w) ++
  (sSubTwsWords.zipIdx.map fun (w, k) => cst (190 + k) w)

theorem sPrologue_split : sPrologue = loadS sPP (.n 0) 1 :: hintW "sp_rand" [.n 3] ::
    ([cst 4 (word (tw 12) 0 0)] ++ (loadS (.n 5) (.n 0) 2 :: loadS (.n 6) (.n 0) 3 :: (pSeq7 ++
      ([pKec] ++ (pChecks ++ (shifts 30 26 56 ++ (hintW "sp_unused" [.n 132, .n 133, .n 134] ::
        ((sFromBytes (.n 134) [.n 133, .n 132] g63W 135).1 ++ pTail)))))))) := by
  simp only [sPrologue, pSeq7, pKec, pChecks, pTail, List.append_assoc, List.cons_append,
    List.nil_append]

theorem pSeq7_ok : SeqOK 7 pSeq7 17 := seqB_ok (by decide +kernel)

theorem pCst4_ok : SeqOK 4 [cst 4 (word (tw 12) 0 0)] 5 := seqB_ok (by decide +kernel)

theorem shifts_ok : SeqOK 56 (shifts 30 26 56) 132 := seqB_ok (by decide +kernel)

theorem pTail_ok : SeqOK 159 pTail 206 := seqB_ok (by decide +kernel)

theorem pKec_nb : NumBelow 30 (Stmt.valsList [pKec]) := numBelow_of_all (by decide +kernel)

theorem pChecks_nb : NumBelow 56 (Stmt.valsList pChecks) := numBelow_of_all (by decide +kernel)

theorem pChecks_atoms : atomsOnly pChecks = true := by decide +kernel

theorem sPrologue_nb : NumBelow 206 (Stmt.valsList sPrologue) := numBelow_of_all (by decide +kernel)

/-- The unused bytes of a digest cell's integer: its bits from `106`, low byte first. -/
def unusedBytes (N : Nat) : Nat → Nat
  | 0 => N / 2 ^ 106 % 256
  | 1 => N / 2 ^ 106 / 256 % 256
  | _ => N / 2 ^ 106 / 65536

/-- **The prologue completes.** -/
theorem sPrologue_complete (hm : MemOK rd 256) {bb p Pc m0 m1 rho : E} (hbb : ByteBits rd bb)
    (σ : Val) (h0 : σ (.n 0) = p) (h1 : σ (.n 1) = bb) (hldP : LoadHolds rd p 1 Pc)
    (hld2 : LoadHolds rd p 2 m0) (hld3 : LoadHolds rd p 3 m1) (hPc : IsCanonical128 Pc)
    (hc0 : IsCanonical128 m0) (hc1 : IsCanonical128 m1) (hrho : IsCanonical128 rho) :
    Completes C rd 2 206 sPrologue σ (fun σ' => σ' sPP = Pc ∧ σ' (.n 3) = rho ∧ σ' (.n 5) = m0 ∧
      σ' (.n 6) = m1 ∧
      (∀ l < 26, σ' (.n (30 + l)) = if (cellNat (σ' (.n 18))).testBit l then 1 else 0) ∧
      σ' (.n 158) = eOfNat (cellNat (σ' (.n 18)) / 2 ^ 106) ∧
      ∀ j < 3, σ' (.n (132 + j)) = ofK (gpow (unusedBytes (cellNat (σ' (.n 18))) j))) := by
  rw [sPrologue_split]
  -- `P`
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := Pc) (by rw [h0]; exact hldP) (by norm_num)
    (fun σ1 he1 e1 => ?_)
  -- the randomizer
  have hext : Ext 3 206 σ1 (Function.update σ1 (.n 3) rho) := fun v hv =>
    Function.update_of_ne (hv 3 le_rfl (by norm_num)) _ _
  refine Completes.reload hext ?_
  set σr := Function.update σ1 (.n 3) rho with hσr
  refine Completes.append (xs := [hintW "sp_rand" [.n 3]]) (m := 4) (by norm_num) (by norm_num)
    (by rw [valsList_hint]; exact .cons ⟨3, by norm_num, rfl⟩ (.nil _)) (hintKeep_complete _ _ _ _ _)
    (fun σ2 _ e2 => ?_)
  subst e2
  have r3 : σr (.n 3) = rho := Function.update_self ..
  have rlow : ∀ k < 3, σr (.n k) = σ1 (.n k) := fun k hk => Function.update_of_ne (by simp; omega) _ _
  -- the message's address and cells
  refine Completes.seq (m := 5) pCst4_ok (by norm_num) (fun σ3 he3 hh3 => ?_)
  have e4 : σ3 (.n 4) = word (tw 12) 0 0 := hh3.atom (a := .const (.n 4) _) (by simp [cst])
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := m0)
    (by rw [he3.apply (Or.inl (by norm_num)), rlow 0 (by norm_num), he1.apply (Or.inl (by norm_num)), h0]
        exact hld2) (by norm_num) (fun σ4 he4 e5 => ?_)
  refine Completes.load ⟨0, by norm_num, rfl⟩ (w := m1)
    (by rw [he4.apply (Or.inl (by norm_num)), he3.apply (Or.inl (by norm_num)), rlow 0 (by norm_num),
          he1.apply (Or.inl (by norm_num)), h0]
        exact hld3) (by norm_num) (fun σ5 he5 e6 => ?_)
  refine Completes.seq (m := 17) pSeq7_ok (by norm_num) (fun σ6 he6 hh6 => ?_)
  -- the values below `7`
  have v2 : σ6 (.n 2) = Pc := by
    rw [he6.apply (Or.inl (by norm_num)), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num)),
      he3.apply (Or.inl (by norm_num)), rlow 2 (by norm_num)]
    exact e1
  have v3 : σ6 (.n 3) = rho := by
    rw [he6.apply (Or.inl (by norm_num)), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num)),
      he3.apply (Or.inl (by norm_num))]
    exact r3
  have v4 : σ6 (.n 4) = word (tw 12) 0 0 := by
    rw [he6.apply (Or.inl (by norm_num)), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num))]
    exact e4
  have v5 : σ6 (.n 5) = m0 := by
    rw [he6.apply (Or.inl (by norm_num)), he5.apply (Or.inl (by norm_num))]
    exact e5
  have v6 : σ6 (.n 6) = m1 := by rw [he6.apply (Or.inl (by norm_num))]; exact e6
  have v1 : σ6 (.n 1) = bb := by
    rw [he6.apply (Or.inl (by norm_num)), he5.apply (Or.inl (by norm_num)), he4.apply (Or.inl (by norm_num)),
      he3.apply (Or.inl (by norm_num)), rlow 1 (by norm_num), he1.apply (Or.inl (by norm_num))]
    exact h1
  have vc : ∀ k w, Stmt.atom (.const (.n k) (word w 0 0)) ∈ pSeq7 → IsCanonical128 (σ6 (.n k)) :=
    fun k w h => by rw [show σ6 (.n k) = word w 0 0 from hh6 _ h]; exact canon_word _ _
  have v7 : σ6 (.n 7) = rho := by
    rw [← v3]; exact hh6.atom (a := .copy (.n 7) (.n 3)) (by simp [pSeq7, copyS])
  have vm : ∀ k, 0 < k → k < 5 → IsCanonical128 (σ6 (.n (12 + k))) := fun k h0 h5 =>
    vc (12 + k) 0 (by
      simp only [pSeq7, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inr ⟨k, h5, by simp [cst, show k ≠ 0 by omega]⟩)
  -- the message digest
  have hcan : ∀ cc : Fin 13, IsCanonical128 (cells13 ([sPP, .n 4, .n 5, .n 6, .n 7, .n 8, .n 9, .n 10,
      .n 11, .n 13, .n 14, .n 15, .n 16].map σ6) cc) := by
    intro cc
    fin_cases cc <;> simp only [cells13, List.map_cons, List.map_nil, List.getD_cons_zero,
      List.getD_cons_succ]
    · rw [show sPP = V.n 2 from rfl, v2]; exact hPc
    · rw [v4]; exact canon_word _ _
    · rw [v5]; exact hc0
    · rw [v6]; exact hc1
    · rw [v7]; exact hrho
    · exact vc 8 1 (by simp [pSeq7, cst])
    · exact vc 9 0 (by simp [pSeq7, cst])
    · exact vc 10 0 (by simp [pSeq7, cst])
    · exact vc 11 (2 ^ 63) (by simp [pSeq7, cst])
    · exact vm 1 (by norm_num) (by norm_num)
    · exact vm 2 (by norm_num) (by norm_num)
    · exact vm 3 (by norm_num) (by norm_num)
    · exact vm 4 (by norm_num) (by norm_num)
  refine Completes.append (m := 30) (by norm_num) (by norm_num) pKec_nb
    (kecS_complete σ6 17 rfl (fun v hv => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
      rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        exact ⟨_, by norm_num, rfl⟩) hcan false false) (fun σ7 he7 _ => ?_)
  -- the index's bits
  set N := cellNat (σ7 (.n 18)) with hN
  set f : Nat → E := fun l => if N.testBit l then 1 else 0 with hf
  refine Completes.reload ((updRun_ext σ7 30 26 f).mono le_rfl (by norm_num)) ?_
  set σb := updRun σ7 30 26 f with hσb
  have hchk : AtomsHold rd σb pChecks := by
    intro a ha
    simp only [pChecks, List.mem_cons, booleans, List.mem_map, List.mem_range, Stmt.atom.injEq] at ha
    rcases ha with rfl | ⟨j, hj, e⟩
    · trivial
    · simp only [mulS, Stmt.atom.injEq] at e
      subst e
      show σb (.n (30 + j)) = σb (.n (30 + j)) * σb (.n (30 + j))
      rw [hσb, updRun_at σ7 30 26 f hj, hf]
      dsimp only
      split <;> simp
  refine Completes.append (m := 56) (by norm_num) (by norm_num) pChecks_nb
    (completes_atoms (Post := fun σ' => σ' = σb) pChecks_atoms (Ext.refl _ _ _) rfl hchk)
    (fun σ8 _ e8 => ?_)
  subst e8
  refine Completes.seq (m := 132) shifts_ok (by norm_num) (fun σ9 he9 _ => ?_)
  -- the unused bytes
  set g : Nat → E := fun j => ofK (gpow (unusedBytes N j)) with hg
  refine Completes.reload ((updRun_ext σ9 132 3 g).mono le_rfl (by norm_num)) ?_
  set σu := updRun σ9 132 3 g with hσu
  refine Completes.append (xs := [hintW "sp_unused" [.n 132, .n 133, .n 134]]) (m := 135) (by norm_num)
    (by norm_num) (by
      rw [valsList_hint]
      exact .cons ⟨132, by norm_num, rfl⟩ (.cons ⟨133, by norm_num, rfl⟩ (.cons ⟨134, by norm_num, rfl⟩ (.nil _))))
    (hintKeep_complete _ _ _ _ _) (fun σ10 _ e10 => ?_)
  subst e10
  have hNlt : N < 2 ^ 128 := cellNat_lt _
  have u0 : σu (.n 132) = ofK (gpow (N / 2 ^ 106 % 256)) := updRun_at σ9 132 3 g (j := 0) (by norm_num)
  have u1 : σu (.n 133) = ofK (gpow (N / 2 ^ 106 / 256 % 256)) := updRun_at σ9 132 3 g (j := 1) (by norm_num)
  have u2 : σu (.n 134) = ofK (gpow (N / 2 ^ 106 / 65536)) := updRun_at σ9 132 3 g (j := 2) (by norm_num)
  have ub1 : σu (.n 1) = bb := by
    rw [hσu, updRun_below σ9 132 3 g ⟨1, by norm_num, rfl⟩, he9.apply (Or.inl (by norm_num)), hσb,
      updRun_below σ7 30 26 f ⟨1, by norm_num, rfl⟩, he7.apply (Or.inl (by norm_num))]
    exact v1
  have hfb := sFromBytes_complete (C := C) hm hbb (K := 64) (v0 := N / 2 ^ 106 / 65536) (by norm_num)
    (by omega) (.n 134) [.n 133, .n 132] [N / 2 ^ 106 / 256 % 256, N / 2 ^ 106 % 256] 135 σu
    (by norm_num) ⟨134, by norm_num, rfl⟩ u2
    (.cons ⟨⟨133, by norm_num, rfl⟩, u1, by omega⟩ (.cons ⟨⟨132, by norm_num, rfl⟩, u0, by omega⟩ .nil))
    ub1 (by norm_num)
  rw [← g63W_k] at hfb
  refine Completes.append (m := 159) (by norm_num) (by norm_num)
    (sFromBytes_shape (.n 134) [.n 133, .n 132] g63W 135 ⟨134, by norm_num, rfl⟩ (by
      simp only [List.mem_cons, List.not_mem_nil, or_false]
      rintro m (rfl | rfl) <;> exact ⟨_, by norm_num, rfl⟩)).2.2 hfb (fun σ11 he11 hp11 => ?_)
  rw [sFromBytes_unused] at hp11
  have hfold : bFold (N / 2 ^ 106 / 65536) [N / 2 ^ 106 / 256 % 256, N / 2 ^ 106 % 256] = N / 2 ^ 106 := by
    simp only [bFold]
    omega
  rw [hfold] at hp11
  -- the facts, kept past the tail
  have k18 : σ11 (.n 18) = σ7 (.n 18) := by
    rw [he11.apply (Or.inl (by norm_num)), hσu, updRun_below σ9 132 3 g ⟨18, by norm_num, rfl⟩,
      he9.apply (Or.inl (by norm_num)), hσb, updRun_below σ7 30 26 f ⟨18, by norm_num, rfl⟩]
  have klow : ∀ k < 17, σ11 (.n k) = σ6 (.n k) := fun k hk => by
    rw [he11.apply (Or.inl (by omega)), hσu, updRun_below σ9 132 3 g ⟨k, by omega, rfl⟩,
      he9.apply (Or.inl (by omega)), hσb, updRun_below σ7 30 26 f ⟨k, by omega, rfl⟩,
      he7.apply (Or.inl (by omega))]
  have kbits : ∀ l < 26, σ11 (.n (30 + l)) = f l := fun l hl => by
    rw [he11.apply (Or.inl (by omega)), hσu, updRun_below σ9 132 3 g ⟨30 + l, by omega, rfl⟩,
      he9.apply (Or.inl (by omega)), hσb, updRun_at σ7 30 26 f hl]
  refine ((seq_completes pTail_ok σ11).keep (Q := fun σ' => σ' sPP = Pc ∧ σ' (.n 3) = rho ∧
      σ' (.n 5) = m0 ∧ σ' (.n 6) = m1 ∧
      (∀ l < 26, σ' (.n (30 + l)) = if (cellNat (σ' (.n 18))).testBit l then 1 else 0) ∧
      σ' (.n 158) = eOfNat (cellNat (σ' (.n 18)) / 2 ^ 106) ∧
      ∀ j < 3, σ' (.n (132 + j)) = ofK (gpow (unusedBytes (cellNat (σ' (.n 18))) j)))
    ⟨by rw [show sPP = V.n 2 from rfl, klow 2 (by norm_num)]; exact v2,
      by rw [klow 3 (by norm_num)]; exact v3, by rw [klow 5 (by norm_num)]; exact v5,
      by rw [klow 6 (by norm_num)]; exact v6, fun l hl => by rw [kbits l hl, k18],
      by rw [hp11, k18], fun j hj => by
        rw [he11.apply (Or.inl (by omega)), hσu, updRun_at σ9 132 3 g hj, k18]⟩
    (fun σ' he ⟨q1, q2, q3, q4, q5, q6, q7⟩ => ?_)).mono le_rfl le_rfl (fun _ h => h.2)
  have a : ∀ k < 159, σ' (.n k) = σ11 (.n k) := fun k hk => he.apply (Or.inl hk)
  refine ⟨by rw [show sPP = V.n 2 from rfl, a 2 (by norm_num)]; exact q1, by rw [a 3 (by norm_num)]; exact q2,
    by rw [a 5 (by norm_num)]; exact q3, by rw [a 6 (by norm_num)]; exact q4,
    fun l hl => by rw [a (30 + l) (by omega), a 18 (by norm_num)]; exact q5 l hl,
    by rw [a 158 (by norm_num), a 18 (by norm_num)]; exact q6,
    fun j hj => by rw [a (132 + j) (by omega), a 18 (by norm_num)]; exact q7 j hj⟩

end
end LeanVM.Guest.B1.Sig
