/-
  LeanVM.Guest.B1.Sig.Model.Sphincs

  `verify_sig_lean_sphincs` under a hash model: the signature its frame hints verifies the claim's
  message under its key with the model's answered hash (`Node.sphincsVerifyWith M.H … = some true`).
-/

module

public import LeanVM.Guest.B1.Sig.Sphincs
public import LeanVM.Guest.B1.Sig.Model.SphincsCoord
public import LeanVM.Guest.B1.Sig.Model.SphincsBody

/-!
# `verify_sig_lean_sphincs` under a hash model

`verify_sig_lean_sphincs_model_w` is `verify_sig_lean_sphincs_sound_w` over `M.sem`, the scheme run
in `Option` with the oracle `digestBits <$> M.H`, the forest keys sound with the key's leaf answered
(`FkSoundWWith`); `verify_sig_lean_sphincs_model` hides the signature, and
`verify_sig_lean_sphincs_meaning_model` is `verify_sig_lean_sphincs_meaning` over
`coreProgram.RelB M.sem`, concluding `Meaning_verify_sig_lean_sphincsWith M.H`.
-/

namespace LeanVM.Guest.B1

open LeanVM.Parameters LeanVM.Semantics LeanVM.Protocol LeanVM.Protocol.Blake2sHash
open LeanVM.Protocol.Verifier LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value LeanVM.Guest.B1.Sig

@[expose] public section

/-- **`verify_sig_lean_sphincs(claim)` with the hash `H`** (`Meaning_verify_sig_lean_sphincs`). -/
def Meaning_verify_sig_lean_sphincsWith (H : List UInt8 → Option Protocol.Digest) (rd : Reader)
    (args rets : List E) : Prop :=
  ∃ p, args = [p] ∧ rets = [] ∧ ∃ (pk : Sphincs.PublicKey) (m : Sphincs.Message),
    ClaimAt rd p (claimCells pk.root pk.parameter m) ∧ ∃ σ, Node.sphincsVerifyWith H pk m σ = some true

namespace Sig

variable {M : HashModel} {C : CallRel} {rd : Reader}

/-- A leanSPHINCS step does not read the step addresses, answered. -/
theorem chainFromWith_sp (H : List UInt8 → Option Protocol.Digest) (pp : E) (adr adr' : Nat → E) (idx : E) (i : Nat) :
    ∀ m s v, chainFromWith H false pp adr idx i m s v = chainFromWith H false pp adr' idx i m s v
  | 0, _, _ => rfl
  | m + 1, s, v => by
      simp only [chainFromWith, stepCells]
      congr 1
      funext h
      exact chainFromWith_sp H pp adr adr' idx i m _ _

theorem tipPairWith_sp (H : List UInt8 → Option Protocol.Digest) (pp : E) (adr adr' : Nat → E) (idx : E)
    (i d : Nat) (x : E) : tipPairWith H false pp adr idx i d x = tipPairWith H false pp adr' idx i d x := by
  simp only [tipPairWith]; split <;> simp only [chainFromWith_sp H pp adr adr']

theorem powers_free (b : Nat) : Stmt.freeInList [] (powers b) = true := rfl

/-- **`verify_sig_lean_sphincs` under a model, for the signature it hints**: when the forest keys are
sound under the model with the witness `wfk`, `sphincsSigOf wfk σ` verifies the claim at the pointer
with the model's answered hash. -/
theorem verify_sig_lean_sphincs_model_w {wfk : List E → List E → Nat → E} (hfk : FkSoundWWith M C wfk)
    {σ : Val} {rets : List E} (h : Stmt.HoldsListB M.sem C rd σ sBody False (fun rs => rs = rets)) :
    rets = [] ∧ ∃ (pk : Sphincs.PublicKey) (m : Sphincs.Message),
      ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧
        Node.sphincsVerifyWith M.H pk m (sphincsSigOf wfk σ) = some true := by
  let inst : HasQuery Sphincs.HashSpec Option := ⟨fun x ↦ Node.digestBits <$> M.H x⟩
  have hq : SQW M.H inst := sqw_with M.H
  suffices Hs : rets = [] ∧ ∃ (pk : Sphincs.PublicKey) (m : Sphincs.Message),
      ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧
        @Sphincs.Concrete.verify Option _ inst pk m (sphincsSigOf wfk σ) = some true from Hs
  simp only [sphincsSigOf]
  simp only [sBody, holdsListB_append] at h
  obtain ⟨hl1, hl5, hl6, hpp, hm0, hm1, hdgst, ⟨N, U, hpre⟩, h⟩ := sPrologue_model h
  set index : Sphincs.Index := ⟨N, hpre.ltN⟩
  have hidx : σ (.n 142) = eOfNat index.val := by
    have := hpre.nodes 0 (by omega)
    simpa using this
  have hNe : cellNat (σ (.n 142)) = N := by
    rw [hidx]; exact cellNat_eOfNat (show N < 2 ^ 64 by have := hpre.ltN; omega)
  rw [hNe]
  obtain ⟨⟨marks, hcs, hbound⟩, h⟩ :=
    sCoords_model (inst := inst) hq hfk hpre.md64 index hidx 8 0 (.n 209) 210 (by omega) h
  generalize coordsOpenings wfk σ 8 0 (.n 209) 210 = openings at *
  generalize sCoords 8 0 (.n 209) 210 = cs at *
  obtain ⟨h17, hb18, h⟩ := sLanes_model (t := fun k => ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val)
    (fun k _ => ((marks (k / 2)).word _).isLt) (fun k hk => by
      have := hcs (k / 2) (by omega)
      simp only [Nat.zero_add] at this
      rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
      · simp only [hk2, ↓reduceIte]
        rw [this.2.1, word_eq_eOfNat]
        rfl
      · simp only [hk2, Nat.one_ne_zero, ↓reduceIte]
        rw [this.2.2, word_eq_eOfNat]
        rfl) h
  simp only [Nat.zero_add] at hcs hbound
  simp only [cst, addS, holdsListB_cons_atom, holdsListB_nil, Atom.HoldsB] at h
  obtain ⟨hf, hf1, h⟩ := h
  obtain ⟨⟨ofk, hofk, hfkey⟩, h⟩ := hashValues_model (Or.inl rfl) (by norm_num) h
  obtain ⟨Cn, hCn, hctr, he1, ⟨oe, hoe, he5⟩, h⟩ := sCounter_model h
  rw [(congrArg cellNat hctr).trans (cellNat_eOfNat (by omega))]
  obtain ⟨hpow, h⟩ := (powers_iff _).mp ((holdsListB_free (powers_free _) σ _ _).mp h)
  obtain ⟨⟨dig, hdig, htips, htarget, hd0⟩, h⟩ :=
    cCodeword_model (w := ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩) hpre.md48 hpow (G := 21) (by norm_num) h
  obtain ⟨hc, hc1, h⟩ := h
  obtain ⟨⟨ol, hol, hlf⟩, h⟩ := hashValues_model (Or.inl rfl) (by norm_num) h
  obtain ⟨hroot, h⟩ := merkle_model (β := fun l => N.testBit l) 26 0 _ _
    (fun l' _ hl' => hpre.bits l' (by omega)) h
  generalize mSibs (fun l => l + 1 == 26) (fun l => N.testBit l) σ 26 0 _ = sibs at *
  simp only [Stmt.HoldsListB, Stmt.HoldsB, List.map_nil] at h
  obtain ⟨hload, heq, hret⟩ := h
  generalize cCodeword ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩ _ 21 sTarget _ _ = cw at *
  generalize hashValues (.n 1) _ _ 64 _ = lf at *
  generalize merkle (.n 1) _ _ _ _ 26 0 lf.2 _ = mk at *
  have hN := hpre.ltN
  -- the digest's cells
  have hs : ∀ c < 8, (marks c).super.val < 2 ^ 4 := fun c _ => (marks c).super.isLt
  have ha : ∀ k < 16, ((marks (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val < 2 ^ 3 := fun k _ =>
    ((marks (k / 2)).child _).isLt
  have hV : σ (.n 18) = lit (digestHi N U (fun c => (marks c).super.val)
      (fun k => ((marks (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val)) := by
    rw [← hb18, hbound, hpre.bound, ← lit_digestHi hN hs ha]
    refine congrArg (fun x => eOfNat N + lit (U * 2 ^ 106) + x) (Finset.sum_congr rfl fun c _ => ?_)
    simp only [coordWeight, show 2 * c / 2 = c by omega, show (2 * c + 1) / 2 = c by omega,
      show 2 * c % 2 = 0 by omega, show (2 * c + 1) % 2 = 1 by omega]
    rfl
  have hc18 : cellNat (σ (.n 18)) = digestHi N U (fun c => (marks c).super.val)
      (fun k => ((marks (k / 2)).child ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val) := by
    rw [hV, cellNat_lit, Nat.mod_eq_of_lt (digestHi_lt hN hpre.ltU hs ha)]
  have hw : ∀ k < 16, ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val < 2 ^ 8 := fun k _ =>
    ((marks (k / 2)).word _).isLt
  have hc17 : cellNat (σ (.n 17)) = ∑ k ∈ Finset.range 16,
      ((marks (k / 2)).word ⟨k % 2, Nat.mod_lt _ (by omega)⟩).val * 2 ^ (8 * k) := by
    rw [h17, cellNat_lit, Nat.mod_eq_of_lt (baseW_lt 8 16 hw)]
  -- the message digest, its index and its marks
  set m : Sphincs.Message := BitVec.ofNat 256 (cellNat (σ (.n 5)) + 2 ^ 128 * cellNat (σ (.n 6)))
  have hmsg : Sphincs.bytesLE 32 m = cellBytes (σ (.n 5)) ++ cellBytes (σ (.n 6)) := by
    have := bytesLE_message (m := m) (lo_ofNat _ _) (hi_ofNat _ _)
    rw [bytesLE_eq] at this
    rw [sphincs_bytesLE_eq]
    exact this
  have htw12 : cellBytes (word (tw 12) 0 0) = Sphincs.tweakBytes .message := by
    rw [Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak, word_eq_eOfNat]
    rfl
  set D : Sphincs.MessageDigest :=
    BitVec.ofNat Sphincs.messageDigestBits (cellNat (σ (.n 17)) + 2 ^ 128 * cellNat (σ (.n 18)))
  have hD : ∀ root : Sphincs.Digest, @Sphincs.Concrete.messageDigest Option _ inst (spp (σ (.n 1))) root m
      (sv (σ (.n 12))) = some D :=
    fun root => sMessageDigest_cellsW hq htw12 hmsg hdgst
  have hI : Sphincs.Concrete.digestIndex D = index :=
    Fin.ext (by rw [digestIndex_ofNat (cellNat_lt _), hc18, digestHi_index hN])
  have hmk : ∀ x y : Sphincs.CoordMark, x.super = y.super → x.child = y.child → x.word = y.word → x = y := by
    rintro ⟨⟩ ⟨⟩ h1 h2 h3
    simp only at h1 h2 h3
    rw [h1, h2, h3]
  have hM : Sphincs.Concrete.digestMarks D = fun c => marks c.val := by
    funext c
    have hc8 : c.val < 8 := c.isLt
    refine hmk _ _ (Fin.ext ?_) (funext fun j => Fin.ext ?_) (funext fun j => Fin.ext ?_)
    · rw [digestMarks_super_val, show Sphincs.Concrete.superOffset c = 128 + (26 + 4 * c.val) by
          simp [Sphincs.Concrete.superOffset]; ring,
        digestField_ofNat (cellNat_lt _) (by simp only [Sphincs.topHeight]; omega), hc18]
      exact digestHi_super hN hs hc8
    · have hj : j.val < 2 := j.isLt
      rw [digestMarks_child_val, show Sphincs.Concrete.childOffset c j = 128 + (58 + 3 * (2 * c.val + j.val)) by
          simp [Sphincs.Concrete.childOffset]; ring,
        digestField_ofNat (cellNat_lt _) (by simp only [Sphincs.subHeight]; omega), hc18]
      refine (digestHi_child (k := 2 * c.val + j.val) hN hs ha (by omega)).trans ?_
      simp only [show (2 * c.val + j.val) / 2 = c.val by omega, show (2 * c.val + j.val) % 2 = j.val by omega]
    · have hj : j.val < 2 := j.isLt
      rw [digestMarks_word_val, show Sphincs.Concrete.wordOffset c j = 8 * (2 * c.val + j.val) by
          simp [Sphincs.Concrete.wordOffset],
        digestByte_ofNat (by omega), hc17, baseW_digit 8 16 hw _ (by omega)]
      simp only [show (2 * c.val + j.val) / 2 = c.val by omega, show (2 * c.val + j.val) % 2 = j.val by omega]
  -- the forest key
  have hR : cellBytes (σ (.n (cs.2.1 + 45 + 1))) = Sphincs.tweakBytes (.roots index) := by
    rw [hf1, hf, hidx, show tw 20 = 2 ^ 56 * 20 by simp only [tw]; ring, sp_add_word (by simp [index]; omega),
      Sphincs.tweakBytes, Sphincs.hashDomainFields, sTweak]
    congr 2
    rw [sp_addrNat (by simp [index]; omega) (by omega) (by omega) (by omega)]
    simp [index]
    ring
  have hFK := sForestRecover_cellsW (inst := inst) hq (marks := fun c => marks c.val)
    (opening := fun c => openings c.val)
    (fun k => σ (if k % 2 = 0 then (cs.2.2.2.1.getD (k / 2) (V.n 0, V.n 0)).1
      else (cs.2.2.2.1.getD (k / 2) (V.n 0, V.n 0)).2)) (fun c => by
        have := (hcs c.val c.isLt).1
        simp only [show 2 * c.val % 2 = 0 by omega, show (2 * c.val + 1) % 2 = 1 by omega,
          show 2 * c.val / 2 = c.val by omega, show (2 * c.val + 1) / 2 = c.val by omega, ↓reduceIte,
          Nat.one_ne_zero]
        exact this) hR hofk
  rw [← hfkey] at hFK
  generalize (hashValues (V.n 1) (V.n (cs.2.1 + 45 + 1)) _ 16 (cs.2.1 + 45 + 2)).2 = fkc at *
  -- the one-time leaf
  generalize codeX ⟨.n 1, .n 2, false, fun _ => .n 0, .n 142⟩ _ 21 _ σ = vals at *
  have hsum : ∑ i ∈ Finset.range Sphincs.numChains, dig i = Sphincs.targetSum := by
    rw [sTarget_eq] at htarget
    have := digit_sum_le hdig (3 * 21 + 1)
    exact (gen_pow_inj (by norm_num) (by omega) htarget).symm
  have hleafIdx : (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer).val = N := leafIndexAt_top index
  have hadr : ∀ (i : Sphincs.ChainIndex) (s : Sphincs.ChainStep),
      cellBytes (σ (.n 142) + eOfNat (tw 1 + i.val * hiMul + s.val * stepMul)) =
        Sphincs.tweakBytes (.chain Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) i s) :=
    fun i s => by rw [hidx]; exact sp_chain_addr hN i s _ hleafIdx
  have hrec : ∀ i : Sphincs.ChainIndex, @Sphincs.Concrete.recoverChain Option _ inst (spp (σ (.n 1)))
      Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) i ⟨dig i.val, hdig _⟩ (sv (vals i.val)) =
      some (sv (σ (cw.2.2.getD i.val (V.n 0, V.n 0)).1)) := fun i => by
    obtain ⟨p, hp, hp1, -⟩ := htips i.val i.isLt
    have hp : tipPairWith M.H false (σ (.n 1)) (fun _ => σ (.n 0)) (σ (.n 142)) i.val (dig i.val) (vals i.val) =
      some p := hp
    rw [tipPairWith_sp _ _ _ (fun _ => 0)] at hp
    rw [sRecoverChain_cellsW hq (hadr i) ⟨dig i.val, hdig _⟩ _ hp, hp1]
  have hleafA : cellBytes (σ (.n (cw.2.1 + 1))) =
      Sphincs.tweakBytes (.leaf Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer)) := by
    rw [hc1, hc, hidx, sp_tag_addr hN (by norm_num), ← hleafIdx]
    rw [← sTweak]; rfl
  have htw4 : Sphincs.tweakBytes (.encoding Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer)) =
      cellBytes (σ (.n (cs.2.1 + 45 + 2 + hashValuesSize 16 + 126 + 1))) := by
    rw [he1, hidx, sp_tag_addr hN (by norm_num), ← hleafIdx]
    rw [← sTweak]; rfl
  have hots : @Sphincs.Concrete.otsLeaf Option _ inst (spp (σ (.n 1))) Sphincs.topLayer 0
      (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer) (sv (σ fkc)) (BitVec.ofNat Sphincs.counterBits Cn)
      (fun i => sv (vals i.val)) = some (some (sv (σ lf.2))) := by
    have henc : @Sphincs.Concrete.tweakableHash Option _ inst (spp (σ (.n 1)))
        (.encoding Sphincs.topLayer 0 (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer))
        (Sphincs.bytesLE 16 (sv (σ fkc)) ++ Sphincs.bytesLE 4 (BitVec.ofNat Sphincs.counterBits Cn)) =
        some (sv (σ (.n (cs.2.1 + 45 + 2 + hashValuesSize 16 + 126 + 5)))) := by
      rw [he5]
      refine sHash_bytesW hq ?_ hoe
      show Sphincs.bytesLE 16 (spp (σ (.n 1))) ++ Sphincs.tweakBytes _ ++ _ = _
      rw [bytesLE_spp, htw4, bytesLE_sv, bytesLE_counter hCn]
      simp
    rw [hd0, show 3 * 21 + 1 = Sphincs.numChains from rfl] at henc
    refine sOtsLeaf_someW henc (sDecode_lit hdig hsum) hrec ?_
    rw [hlf]
    exact sLeafHash_cellsW hq (fun i => σ (cw.2.2.getD i (V.n 0, V.n 0)).1) hleafA hol
  -- the tree
  have heq' : σ mk.2.1 = σ (.n mk.2.2) := e_add_eq_zero_iff.mp heq
  have hA : ∀ l < Sphincs.maxLayerHeight, cellBytes (mAddr σ (fun l => .n (142 - 3 * l))
      (fun l => tw 3 + (l + 1) * hiMul) (fun l => l + 1 == 26) l) =
      Sphincs.tweakBytes (.node Sphincs.topLayer 0 (l + 1)
        ((Sphincs.Concrete.leafIndexAt index Sphincs.topLayer).val / 2 ^ (l + 1))) := fun l hl => by
    rw [hleafIdx]
    exact sp_node_addr hN hl (fun h => hpre.nodes (l + 1) (by omega))
  let sib' : Nat → E := fun l => if l < 26 then sibs l else 0
  have hroot' : mFoldWith M.H (σ (.n 1)) (mAddr σ (fun l => .n (142 - 3 * l)) (fun l => tw 3 + (l + 1) * hiMul)
      (fun l => l + 1 == 26)) (fun l => (Sphincs.Concrete.leafIndexAt index Sphincs.topLayer).val.testBit l) sib'
      Sphincs.maxLayerHeight 0 (σ lf.2) = some (σ (.n mk.2.2)) := by
    rw [← heq', ← hroot]
    simp only [hleafIdx]
    exact mFoldWith_congr _ _ _ _ 26 0 (fun l _ hl => by simp [sib', show l < 26 by omega]) _
  have htree := sTreeFold_cellsW (inst := inst) hq hA sib' _ le_rfl _ hroot'
  -- the claim and the signature
  have hrc : IsCanonical128 (σ (.n mk.2.2)) := mFoldWith_canonical (by norm_num) (heq' ▸ hroot)
  refine ⟨hret.symm, ⟨sv (σ (.n mk.2.2)), spp (σ (.n 1))⟩, m, ?_, ?_⟩
  · show ClaimAt rd (σ (.n 0)) (claimCells (xv (σ (.n mk.2.2))) (xpp (σ (.n 1)))
      (BitVec.ofNat 256 (cellNat (σ (.n 5)) + 2 ^ 128 * cellNat (σ (.n 6)))))
    rw [claimCells_of hrc hpp hm0 hm1]
    intro k
    fin_cases k
    · exact hload
    · exact hl1
    · exact hl5
    · exact hl6
  · refine sVerify_of (D := D) (fk := sv (σ fkc)) (leaf := sv (σ lf.2)) (hD _) ?_ ?_ ?_
    · rw [hI, hM]
      exact hFK
    · rw [hI]
      exact hots
    · rw [hI]
      have hsp : Sphincs.Concrete.signaturePath ⟨sv (σ (.n 12)), fun c => openings c.val,
          fun _ => ⟨BitVec.ofNat Sphincs.counterBits Cn, fun i => sv (vals i.val), fun l => sv (sibs l.val)⟩⟩
          Sphincs.topLayer = fun l => sv (sib' l) := funext fun l => by
        simp only [Sphincs.Concrete.signaturePath, Sphincs.layerHeight, Sphincs.maxLayerHeight, sib']
        by_cases hl : l < 26
        · simp only [hl, ↓reduceDIte, ↓reduceIte]
        · simp only [hl, ↓reduceDIte, ↓reduceIte]
          exact sv_zero.symm
      rw [hsp]
      exact htree

/-- **`verify_sig_lean_sphincs` under a model** (`verify_sig_lean_sphincs_sound`). -/
theorem verify_sig_lean_sphincs_model (hfk : FkSoundWith M C) {σ : Val} {rets : List E}
    (h : Stmt.HoldsListB M.sem C rd σ sBody False (fun rs => rs = rets)) :
    rets = [] ∧ ∃ (pk : Sphincs.PublicKey) (m : Sphincs.Message),
      ClaimAt rd (σ (.n 0)) (claimCells pk.root pk.parameter m) ∧
        ∃ sig, Node.sphincsVerifyWith M.H pk m sig = some true := by
  obtain ⟨wfk, hw⟩ := exists_fkSoundWWith hfk
  obtain ⟨h1, pk, m, hc, hv⟩ := verify_sig_lean_sphincs_model_w hw h
  exact ⟨h1, pk, m, hc, _, hv⟩

end Sig

/-- **`verify_sig_lean_sphincs` is sound under a model** (`verify_sig_lean_sphincs_meaning`). -/
theorem verify_sig_lean_sphincs_meaning_model {M : HashModel} {rd : Reader} {args rets : List E}
    (h : coreProgram.RelB M.sem rd "verify_sig_lean_sphincs" args rets) :
    Meaning_verify_sig_lean_sphincsWith M.H rd args rets := by
  obtain ⟨σ, hp, hb⟩ := (relB_iff_sem Sig.find_verify_sig_lean_sphincs args rets).mp h
  obtain ⟨hr, pk, m, hc, sig, hv⟩ := Sig.verify_sig_lean_sphincs_model Sig.fkSoundWith_relB hb
  exact ⟨σ (.n 0), by rw [← hp]; rfl, hr, pk, m, hc, sig, hv⟩

end
end LeanVM.Guest.B1
