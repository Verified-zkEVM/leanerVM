/-
  LeanVM.Guest.B1.Sig.SphincsTail

  The body of `verify_sig_lean_sphincs` after the forest: the counter, the encoding, the one-time
  signature, its leaf and the tree, up to the root's check.
-/

module

public import LeanVM.Guest.B1.Sig.SphincsAddr
public import LeanVM.Guest.B1.Sig.SphincsTables
public import LeanVM.Guest.B1.Sig.XmssLayer

/-!
# After the forest

The parts of `sBody` (`sCs` … `sMk`) and `sBody_split`; the one-time chain step (`sStep_sound`);
`sTail_sound`: the statements after the coordinates hold of `σ`, so the body returns no words, the
codeword and the leaf address are sound, and the root is the claim's first word.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Value.Keccak LeanVM.Protocol.KeccakHash
open LeanVM.Protocol.Verifier (eOfNat gen)

@[expose] public section

/-- The eight coordinates. -/
def sCs : List Stmt × Nat × V × V × List V := sCoords 8 0 (cSt 0).1 (cSt 0).2.1 (cSt 0).2.2

/-- The counter's base. -/
def sB : Nat := sCs.2.1

/-- The counter, `sp_from_bytes` of its four hinted bytes. -/
def sFb : List Stmt × Nat × V := sFromBytes (.n (sB + 3)) [.n (sB + 2), .n (sB + 1), .n sB] g255W (sB + 4)

/-- The encoding's cells: `P`, its address, the sixteen top nodes and the counter. -/
def sTops : List V := [.n 162, .n 164] ++ sCs.2.2.2.2 ++ [.n sFb.2.1]

/-- The encoding's `keccak`, 292 bytes. -/
def sEnc : List Stmt × Nat × Nat := kMsg sPad (sTops.map KC.cell) 292 true none (sFb.2.1 + 1)

/-- The one-time chain steps, powers at `sEnc`'s base. -/
def sW : WotsT := sWots fun s => .n (sEnc.2.1 + s)

/-- The codeword. -/
def sCw : List Stmt × Nat × List V := codewordT sW 21 sTarget (.n sEnc.2.2) (sEnc.2.1 + 10)

/-- The one-time leaf's `keccak`, 1056 bytes. -/
def sLeaf : List Stmt × Nat × Nat :=
  kMsg sPad ((sPP :: V.n (sCw.2.1 + 1) :: sCw.2.2).map KC.cell) 1056 false none (sCw.2.1 + 2)

def sNodeOf (l : Nat) : Option V := if l + 1 = 26 then none else some (sNode (l + 1))

def sAddrOf (l : Nat) : Nat := tw 3 + (l + 1) * hiMul

/-- The tree. -/
def sMk : List Stmt × Nat × V := merkleT sPad sPP sBit sNodeOf sAddrOf 26 0 (.n sLeaf.2.2) sLeaf.2.1

/-- The atoms between the coordinates and the codeword: the counter, the encoding, the powers. -/
def sMid : List Stmt :=
  [hintW "sp_counter" (runV sB 4)] ++ sFb.1 ++ [copyS (.n sFb.2.1) sFb.2.2] ++ sEnc.1 ++
    (List.range 10).map (fun s => cst (sEnc.2.1 + s) (word (2 ^ s) 0 0))

/-- The end: the leaf address, the leaf, the tree, the root's check. -/
def sEnd : List Stmt :=
  [cst sCw.2.1 (word (tw 2) 0 0), addS (.n (sCw.2.1 + 1)) (sNode 0) (.n sCw.2.1)] ++ sLeaf.1 ++ sMk.1 ++
    [loadS (.n sMk.2.1) (.n 0) 0, .atom (.assertEq sMk.2.2 (.n sMk.2.1)), .ret []]

attribute [local irreducible] sCoords kMsg codewordT merkleT

theorem sBody_split : sBody = sPrologue ++ (sCs.1 ++ (sMid ++ (sCw.1 ++ sEnd))) := by
  simp only [sBody, sCs, sB, sFb, sTops, sEnc, sW, sCw, sLeaf, sMk, sMid, sEnd, List.append_assoc, cSt]
  rfl

theorem sMid_atoms : atomsOnly sMid = true := by
  have h1 : atomsOnly sFb.1 = true := by
    simp only [sFb, sFromBytes, sFromBytesRest, atomsOnly_append]
    rfl
  have h2 : atomsOnly sEnc.1 = true := kMsg_atoms ..
  have h3 : ∀ (b : Nat), atomsOnly ((List.range 10).map (fun s => cst (b + s) (word (2 ^ s) 0 0))) = true := by
    intro b
    rfl
  simp only [sMid, atomsOnly_append, h1, h2, h3]
  rfl

variable {C : CallRel} {rd : Reader} {σ : Val} {kret : List E → Prop}

/-- **The one-time chain step**: `keccak` of `P`, the step's address and the value. -/
theorem sStep_sound (hp : PadOK σ sPad) :
    StepSound rd σ sW (fun i s y =>
      (hcell [σ sPP, σ (sNode 0) + word (tw 1 + i * hiMul + s * stepMul) 0 0, y]).1) := by
  intro i s v c o h
  have hc : σ (.n c) = word (tw 1 + i * hiMul + s * stepMul) 0 0 :=
    h.atom (a := .const (.n c) _) (by simp [sW, sWots, cst])
  have ha : σ (.n (c + 1)) = σ (sNode 0) + σ (.n c) :=
    h.atom (a := .add (.n (c + 1)) (sNode 0) (.n c)) (by simp [sW, sWots, addS])
  have hk := k48_sound hp (a := .n (c + 1)) (v := v) (c := c + 2) (o := o)
    (h.sub fun x hx => List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hx))
  have hk1 := congrArg Prod.fst hk
  simp only at hk1
  rw [hk1, ha, hc]

theorem sW_atoms : StepAtoms sW := fun _ _ _ _ _ => rfl

/-- The end before the root's check: the leaf address, the leaf and the tree. -/
def sEndPre : List Stmt :=
  [cst sCw.2.1 (word (tw 2) 0 0), addS (.n (sCw.2.1 + 1)) (sNode 0) (.n sCw.2.1)] ++ sLeaf.1 ++ sMk.1

theorem sEnd_split : sEnd = sEndPre ++
    [loadS (.n sMk.2.1) (.n 0) 0, .atom (.assertEq sMk.2.2 (.n sMk.2.1)), .ret []] := by
  simp only [sEnd, sEndPre, List.append_assoc]

theorem sEndPre_atoms : atomsOnly sEndPre = true := by
  simp only [sEndPre, atomsOnly_append, sLeaf, sMk, kMsg_atoms, merkleT_atoms]
  rfl

/-- **After the coordinates, up to the root's check**: the middle atoms hold, the codeword is sound,
the leaf address is the index's plus `tw(2)`, the leaf's and the tree's atoms hold. -/
theorem sTailPre_sound (hp : PadOK σ sPad) {rest : List Stmt} {next : Prop}
    (h : Stmt.HoldsList C rd σ (sMid ++ (sCw.1 ++ (sEndPre ++ rest))) next kret) :
    Stmt.HoldsList C rd σ rest next kret ∧ AtomsHold rd σ sMid ∧
      (∀ i < 3 * 21 + 1, cwDigit sW 21 (sEnc.2.1 + 10) σ i < 4 ∧
        σ (cwTip sW (sEnc.2.1 + 10) i) =
          chainT (fun i s y => (hcell [σ sPP, σ (sNode 0) + word (tw 1 + i * hiMul + s * stepMul) 0 0,
            y]).1) i (3 - cwDigit sW 21 (sEnc.2.1 + 10) σ i) (cwDigit sW 21 (sEnc.2.1 + 10) σ i)
            (σ (cwStart sW 21 (sEnc.2.1 + 10) σ i))) ∧
      gen ^ (∑ i ∈ Finset.range (3 * 21 + 1), cwDigit sW 21 (sEnc.2.1 + 10) σ i) = sTarget ∧
      σ (.n sEnc.2.2) = lit (∑ i ∈ Finset.range (3 * 21 + 1),
        cwDigit sW 21 (sEnc.2.1 + 10) σ i * 4 ^ i) ∧
      σ (.n (sCw.2.1 + 1)) = σ (sNode 0) + word (tw 2) 0 0 ∧
      AtomsHold rd σ sLeaf.1 ∧ AtomsHold rd σ sMk.1 := by
  have s1 := holdsList_split_atoms sMid_atoms h
  have hm := atomsHold_of_holdsList sMid_atoms s1.1
  have hpow : ∀ s < 10, σ (sW.power s) = gen ^ s := by
    intro s hs
    have e : σ (.n (sEnc.2.1 + s)) = word (2 ^ s) 0 0 :=
      hm.atom (a := .const (.n (sEnc.2.1 + s)) _) (by
        simp only [sMid, List.mem_append, List.mem_map, List.mem_range]
        exact Or.inr ⟨s, hs, rfl⟩)
    show σ (.n (sEnc.2.1 + s)) = _
    rw [e, word_eq_eOfNat, Value.gen_pow_eq_eOfNat (by omega)]
  obtain ⟨s3, hcw, hsum, hd0⟩ := codewordT_sound sW_atoms (sStep_sound hp) hpow (by norm_num) (le_refl _) s1.2
  have s4 := holdsList_split_atoms sEndPre_atoms s3
  have he := atomsHold_of_holdsList sEndPre_atoms s4.1
  have c1 : σ (.n sCw.2.1) = word (tw 2) 0 0 := he.atom (a := .const (.n sCw.2.1) _) (by simp [sEndPre, cst])
  have c2 : σ (.n (sCw.2.1 + 1)) = σ (sNode 0) + σ (.n sCw.2.1) :=
    he.atom (a := .add (.n (sCw.2.1 + 1)) (sNode 0) (.n sCw.2.1)) (by simp [sEndPre, addS])
  exact ⟨s4.2, hm, hcw, hsum, hd0, by rw [c2, c1], he.left.right, he.right⟩

/-- **After the coordinates**: the body returns no words; the middle atoms hold, the codeword is
sound, the leaf address is the index's plus `tw(2)`, the leaf's and the tree's atoms hold and the
root is checked against the claim's first word. -/
theorem sTail_sound (hp : PadOK σ sPad) {rets : List E}
    (h : Stmt.HoldsList C rd σ (sMid ++ (sCw.1 ++ sEnd)) False (fun rs => rs = rets)) :
    rets = [] ∧ AtomsHold rd σ sMid ∧
      (∀ i < 3 * 21 + 1, cwDigit sW 21 (sEnc.2.1 + 10) σ i < 4 ∧
        σ (cwTip sW (sEnc.2.1 + 10) i) =
          chainT (fun i s y => (hcell [σ sPP, σ (sNode 0) + word (tw 1 + i * hiMul + s * stepMul) 0 0,
            y]).1) i (3 - cwDigit sW 21 (sEnc.2.1 + 10) σ i) (cwDigit sW 21 (sEnc.2.1 + 10) σ i)
            (σ (cwStart sW 21 (sEnc.2.1 + 10) σ i))) ∧
      gen ^ (∑ i ∈ Finset.range (3 * 21 + 1), cwDigit sW 21 (sEnc.2.1 + 10) σ i) = sTarget ∧
      σ (.n sEnc.2.2) = lit (∑ i ∈ Finset.range (3 * 21 + 1),
        cwDigit sW 21 (sEnc.2.1 + 10) σ i * 4 ^ i) ∧
      σ (.n (sCw.2.1 + 1)) = σ (sNode 0) + word (tw 2) 0 0 ∧
      AtomsHold rd σ sLeaf.1 ∧ AtomsHold rd σ sMk.1 ∧
      LoadHolds rd (σ (.n 0)) 0 (σ (.n sMk.2.1)) ∧ σ sMk.2.2 + σ (.n sMk.2.1) = 0 := by
  rw [sEnd_split] at h
  obtain ⟨s4, hm, hcw, hsum, hd0, hla, hl, hk⟩ := sTailPre_sound hp h
  have hat : atomsOnly [loadS (.n sMk.2.1) (.n 0) 0, .atom (.assertEq sMk.2.2 (.n sMk.2.1))] = true := rfl
  have s5 := holdsList_split_atoms (xs := [loadS (.n sMk.2.1) (.n 0) 0, .atom (.assertEq sMk.2.2 (.n sMk.2.1))])
    (ys := [.ret []]) hat s4
  have he := atomsHold_of_holdsList hat s5.1
  have hret : rets = [] := by
    have := s5.2
    simp only [Stmt.HoldsList, Stmt.Holds, List.map_nil] at this
    exact this.symm
  exact ⟨hret, hm, hcw, hsum, hd0, hla, hl, hk,
    he.atom (a := .load (.n sMk.2.1) (.n 0) 0) (by simp [loadS]),
    he.atom (a := .assertEq sMk.2.2 (.n sMk.2.1)) (by simp)⟩

end
end LeanVM.Guest.B1.Sig
