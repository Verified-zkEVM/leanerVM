/-
  LeanVM.Guest.B1.Sig.SphincsLoads

  Where `verify_sig_lean_sphincs`'s loads read, for the placed completeness: the valuation its
  completeness builds loads only the claim's four words and the byte table's words
  (`verify_sig_lean_sphincs_complete_loads`).
-/

module

public import LeanVM.Guest.B1.Sig.SphincsComplete
public import LeanVM.Guest.Memory.Regions

/-!
# The loads of `verify_sig_lean_sphincs`

* `loadOkB`, `stmtLoadsB`: a load reads through the argument `n0` at an offset below `4`, or through
  one of the given values at offset `0`; `walk_loadOk`: the path of a block passing the check
  loads only so;
* `core20_loads`: `Data.core20.body` passes it, its other pointers the seven byte reads'
  (`n139`, `n145`, `n154` for the unused bytes, `sB + 8`, `+ 14`, `+ 23`, `+ 32` for the counter);
* `verify_sig_lean_sphincs_complete_loads`: the valuation of `sphincs_complete_val` loads from
  `p·g^k`, `k < 4`, or `bb·g^v`, `v < 256`, along the body's path.
-/

namespace LeanVM.Guest.B1.Sig

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Value
open LeanVM.Guest.Memory
open LeanVM.Protocol.Verifier (eOfNat)
open Sphincs Sphincs.Concrete

@[expose] public section

/-! ## A check of the loads -/

/-- A load reads through `n0` at an offset below `4`, or through one of `ptrs` at offset `0`. -/
def loadOkB (ptrs : List Nat) : Atom → Bool
  | .load _ p off => (p == .n 0 && decide (off < 4)) || (off == 0 && ptrs.any fun q => p == .n q)
  | _ => true

mutual
/-- `loadOkB` of every atom of a statement, through its branches and arms. -/
def stmtLoadsB (ptrs : List Nat) : Stmt → Bool
  | .atom a => loadOkB ptrs a
  | .ite _ z n => listLoadsB ptrs z && listLoadsB ptrs n
  | .match_ _ arms => armsLoadsB ptrs arms
  | .call .. => true
  | .callIf .. => true
  | .dispatch .. => true
  | .ret _ => true

/-- `stmtLoadsB` of a block. -/
def listLoadsB (ptrs : List Nat) : List Stmt → Bool
  | [] => true
  | s :: ss => stmtLoadsB ptrs s && listLoadsB ptrs ss

/-- `stmtLoadsB` of arms. -/
def armsLoadsB (ptrs : List Nat) : List (List Stmt) → Bool
  | [] => true
  | a :: as => listLoadsB ptrs a && armsLoadsB ptrs as
end

/-- An event whose atom passes `loadOkB`. -/
def Ev.loadOk (ptrs : List Nat) : Ev → Prop
  | .atom a => loadOkB ptrs a = true
  | _ => True

variable {σ : Val}

theorem pick_loadOk (ptrs : List Nat) {x : V} {args rets : List V} :
    ∀ (gs : List String) (j : ℕ), (pick σ x args rets j gs).All (Ev.loadOk ptrs)
  | [], _ => trivial
  | g :: gs, j => by
      unfold pick
      split_ifs
      · intro e he
        rw [List.mem_singleton] at he
        subst he
        trivial
      · exact pick_loadOk ptrs gs (j + 1)

mutual
theorem walk1_loadOk (ptrs : List Nat) : ∀ (s : Stmt), stmtLoadsB ptrs s = true →
    (walk1 σ s).All (Ev.loadOk ptrs)
  | .atom _, h => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      exact h
  | .ite c z n, h => by
      simp only [stmtLoadsB, Bool.and_eq_true] at h
      rw [walk1]
      refine Out.all_pre (fun e he => by rw [List.mem_singleton] at he; subst he; trivial) ?_
      split_ifs
      · exact walk_loadOk ptrs z h.1
      · exact walk_loadOk ptrs n h.2
  | .match_ x arms, h => walkArms_loadOk ptrs x arms 0 h
  | .call .., _ => by
      intro e he
      rw [List.mem_singleton] at he
      subst he
      trivial
  | .callIf c f args, _ => by
      rw [walk1]
      intro e he
      simp only [List.mem_cons, List.not_mem_nil, or_false] at he
      rcases he with rfl | rfl
      · trivial
      · split_ifs <;> trivial
  | .dispatch x fs args rets, _ => pick_loadOk ptrs fs 0
  | .ret _, _ => fun _ he => (List.not_mem_nil he).elim

theorem walk_loadOk (ptrs : List Nat) : ∀ (ss : List Stmt), listLoadsB ptrs ss = true →
    (walk σ ss).All (Ev.loadOk ptrs)
  | [], _ => fun _ he => (List.not_mem_nil he).elim
  | s :: ss, h => by
      simp only [listLoadsB, Bool.and_eq_true] at h
      rw [walk]
      exact Out.all_seq (walk_loadOk ptrs ss h.2) (walk1_loadOk ptrs s h.1)

theorem walkArms_loadOk (ptrs : List Nat) (x : V) : ∀ (arms : List (List Stmt)) (j : ℕ),
    armsLoadsB ptrs arms = true → (walkArms σ x j arms).All (Ev.loadOk ptrs)
  | [], _, _ => trivial
  | a :: as, j, h => by
      simp only [armsLoadsB, Bool.and_eq_true] at h
      unfold walkArms
      split_ifs
      · exact walk_loadOk ptrs a h.1
      · exact walkArms_loadOk ptrs x as (j + 1) h.2
end

/-- **The addresses a checked path loads from.** -/
theorem loadAddrs_of_loadOk {ptrs : List Nat} {es : List Ev} (h : ∀ e ∈ es, Ev.loadOk ptrs e) :
    ∀ A ∈ loadAddrs σ es, (∃ k < 4, A = (σ (.n 0)).limb 0 * gpow k) ∨
      ∃ q ∈ ptrs, A = (σ (.n q)).limb 0 := by
  intro A hA
  obtain ⟨e, he, hea⟩ := List.mem_filterMap.mp hA
  have hok := h e he
  rcases e with ⟨_ | _ | _ | _ | ⟨d, p, off⟩ | _ | _ | _ | _ | _ | _ | _⟩ | _ | _ | _ <;>
    simp only [Ev.loadAddr?, reduceCtorEq] at hea
  simp only [Option.some.injEq] at hea
  subst hea
  simp only [Ev.loadOk, loadOkB, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq,
    List.any_eq_true] at hok
  rcases hok with ⟨rfl, hoff⟩ | ⟨rfl, q, hq, rfl⟩
  · exact Or.inl ⟨off, hoff, rfl⟩
  · exact Or.inr ⟨q, hq, by simp [gpow]⟩

/-! ## The body's loads -/

/-- The byte reads' pointers. -/
def sPtrs : List Nat := [139, 145, 154, 412419, 412425, 412434, 412443]

theorem core20_loads : listLoadsB sPtrs Data.core20.body = true := by decide +kernel

theorem sB_val : sB = 412411 := by decide +kernel

/-- A checked block's returning path loads only so. -/
theorem loads_of_walk {ptrs : List Nat} {ss : List Stmt} (h : listLoadsB ptrs ss = true) {es : List Ev}
    {vs : List V} (hw : walk σ ss = .ret es vs) : ∀ e ∈ es, Ev.loadOk ptrs e := by
  have := walk_loadOk (σ := σ) ptrs ss h
  rw [hw] at this
  exact this

/-! ## The pointers' values -/

theorem unusedBytes_lt {N : Nat} (h : N < 2 ^ 128) : ∀ j, unusedBytes N j < 256
  | 0 => Nat.mod_lt _ (by norm_num)
  | 1 => Nat.mod_lt _ (by norm_num)
  | _ + 2 => by simp only [unusedBytes]; omega

theorem limb_mul_ofK {bb : E} (hK : IsInK bb) (v : Nat) :
    (bb * ofK (gpow v)).limb 0 = bb.limb 0 * gpow v := by
  have e : bb * ofK (gpow v) = ofK (bb.limb 0 * gpow v) := by rw [ofK_mul, ← eq_ofK_limb hK]
  rw [e]
  simp

/-- **The byte reads' pointers hold `σ n1 · g^v`**, `v` a byte, the marks the hints'. -/
theorem sPtr_val {rd : Reader} {Pc m0 m1 rho : E} (hsp : SP1 rd σ Pc m0 m1 rho)
    (hmid : AtomsHold rd σ sMid) {ctr : Nat} (hcm : ∀ j < 4, σ (.n (sB + j)) = ofK (gpow (ctrByte ctr j))) :
    ∀ q ∈ sPtrs, ∃ v < 256, σ (.n q) = σ (.n 1) * ofK (gpow v) := by
  have hN := cellNat_lt (σ (.n 18))
  have pro : ∀ (j k : Nat), j < 3 → Stmt.atom (.mul (.n k) (.n 1) (.n (132 + j))) ∈ sPrologue →
      ∃ v < 256, σ (.n k) = σ (.n 1) * ofK (gpow v) := fun j k hj hk =>
    ⟨_, unusedBytes_lt hN j, by rw [hsp.atoms.atom hk, hsp.marks j hj]⟩
  have ctrm : ∀ (j k : Nat), j < 4 → Stmt.atom (.mul (.n k) (.n 1) (.n (sB + j))) ∈ sFb.1 →
      ∃ v < 256, σ (.n k) = σ (.n 1) * ofK (gpow v) := fun j k hj hk =>
    ⟨ctrByte ctr j, Nat.mod_lt _ (by norm_num), by
      rw [hmid.atom (a := .mul (.n k) (.n 1) (.n (sB + j))) (by
        rw [sMid_split]; exact List.mem_append_right _ (List.mem_append_left _ hk)), hcm j hj]⟩
  intro q hq
  simp only [sPtrs, List.mem_cons, List.not_mem_nil, or_false] at hq
  rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact pro 2 139 (by norm_num) (by simp [sPrologue, sFromBytes, sByte, mulS])
  · exact pro 1 145 (by norm_num) (by simp [sPrologue, sFromBytes, sFromBytesRest, sByte, mulS])
  · exact pro 0 154 (by norm_num) (by simp [sPrologue, sFromBytes, sFromBytesRest, sByte, mulS])
  · rw [show (412419 : Nat) = sB + 4 + 4 by rw [sB_val]]
    exact ctrm 3 _ (by norm_num) (by simp [sFb, sFromBytes, sByte, mulS])
  · rw [show (412425 : Nat) = sB + 4 + 6 + 4 by rw [sB_val]]
    exact ctrm 2 _ (by norm_num) (by simp [sFb, sFromBytes, sFromBytesRest, sByte, mulS])
  · rw [show (412434 : Nat) = sB + 4 + 6 + 9 + 4 by rw [sB_val]]
    exact ctrm 1 _ (by norm_num) (by simp [sFb, sFromBytes, sFromBytesRest, sByte, mulS])
  · rw [show (412443 : Nat) = sB + 4 + 6 + 9 + 9 + 4 by rw [sB_val]]
    exact ctrm 0 _ (by norm_num) (by simp [sFb, sFromBytes, sFromBytesRest, sByte, mulS])

/-! ## The statement -/

/-- **Where `verify_sig_lean_sphincs`'s complete valuation loads**: under the hypotheses of
`verify_sig_lean_sphincs_complete_Spec`, a valuation whose arguments are `p` and `bb`, under which
the body holds, and whose path loads only from `p·g^k`, `k < 4` (the claim), or `bb·g^v`,
`v < 256` (the byte table). -/
def verify_sig_lean_sphincs_complete_loads_Spec : Prop :=
  ∀ (C : CallRel) (rd : Reader) (p bb : E) (pk : Sphincs.PublicKey) (m : Sphincs.Message)
    (sig : Sphincs.Signature), MemOK rd 256 → ByteBits rd bb →
    ClaimAt rd p (cellOf128 pk.root) (cellOf128 pk.parameter) (cellOf128 (m.extractLsb' 0 128))
      (cellOf128 (m.extractLsb' 128 128)) →
    Node.sphincsVerify pk m sig = true →
      ∃ σ : Val, σ (.n 0) = p ∧ σ (.n 1) = bb ∧
        Stmt.HoldsList C rd σ Data.core20.body False (fun rs => rs = []) ∧
        ∀ es vs, walk σ Data.core20.body = .ret es vs → ∀ A ∈ loadAddrs σ es,
          (∃ k < 4, A = p.limb 0 * gpow k) ∨ ∃ v < 256, A = bb.limb 0 * gpow v

/-- **`verify_sig_lean_sphincs`'s complete valuation loads only the claim and the byte table.** -/
theorem verify_sig_lean_sphincs_complete_loads : verify_sig_lean_sphincs_complete_loads_Spec := by
  intro C rd p bb pk m sig hm hbb hat hv
  obtain ⟨σf, h0, h1, hb, hF, hh⟩ := sphincs_complete_val C rd p bb pk m sig hm hbb hat hv
  obtain ⟨hsp, -, -, -, -, -, hcm⟩ := hF
  refine ⟨σf, h0, h1, hb, fun es vs hw => ?_⟩
  -- the middle's atoms hold
  have hpre := sPrologue_sound hsp.atoms
  unfold sPre at hh
  have s0 := holdsList_split_atoms sPrologue_atoms hh
  obtain ⟨s2, -⟩ := sCoords_sound (C := C) (rd := rd) (σ := σf) hpre.pad hpre.tws 8 0 s0.2
  have hmid := atomsHold_of_holdsList sMid_atoms (holdsList_split_atoms sMid_atoms s2).1
  -- the path's loads
  generalize hbody : Data.core20.body = ss at hw
  have hall := loads_of_walk (hbody ▸ core20_loads) hw
  intro A hA
  rcases loadAddrs_of_loadOk hall A hA with ⟨k, hk, rfl⟩ | ⟨q, hq, rfl⟩
  · exact Or.inl ⟨k, hk, by rw [h0]⟩
  · obtain ⟨v, hv256, e⟩ := sPtr_val hsp hmid hcm q hq
    exact Or.inr ⟨v, hv256, by rw [e, h1, limb_mul_ofK (hbb 0 (by norm_num)).1]⟩

end
end LeanVM.Guest.B1.Sig
