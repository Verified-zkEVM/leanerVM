/-
  LeanVM.Cost.Samples.AddRaw

  Spike sample 1, a `CPolynomial` operation: CompPoly's `addRaw` over `K` (pad both coefficient
  arrays to the longer one, add entrywise), hand-compiled to the cost machine, with its
  correctness and its price proved. `addRaw` is from CompPoly (github.com/Verified-zkEVM/CompPoly,
  Apache-2.0, "Copyright (c) 2026 CompPoly Contributors"); nothing of it is copied.
-/

module

public import LeanVM.Cost.Loop
public import CompPoly.Univariate.Raw.Proofs
import all CompPoly.Univariate.Raw.Core
public import Statement.Field

namespace LeanVM.Cost.Samples

open LeanVM.Parameters

@[expose] public section

/-- A coefficient of `K` as a word. -/
def wordOf (x : K) : UInt64 := UInt64.ofBitVec x.toBitVec

/-- A polynomial's coefficients as words. -/
def enc (p : CompPoly.CPolynomial.Raw K) : Array UInt64 := Array.map wordOf p

/-- `xor` of words is addition in `K`. -/
theorem wordOf_add (x y : K) : wordOf (x + y) = wordOf x ^^^ wordOf y := by
  simp only [wordOf]
  rfl

theorem wordOf_zero : wordOf 0 = 0 := rfl

/-- `R := A[i]` for the index `i` in register `3`, or `0` past `A`'s end. -/
def readOrZero (A R : ℕ) : Stmt :=
  .seq (.set R (.lit 0)) (.ite (.bin .lt (.var 3) (.len A)) (.set R (.read A (.var 3))) .skip)

/-- The body: `out[i] := p[i] ⊕ q[i]` (`0` past either end), `i := i + 1`. Registers: `0` and `1`
the inputs, `2` the output, `3` the index, `4` the length, `5` and `6` the two coefficients. -/
def addBody : Stmt :=
  .seq (readOrZero 0 5) <| .seq (readOrZero 1 6) <|
  .seq (.write 2 (.var 3) (.bin .xor (.var 5) (.var 6))) (.set 3 (.bin .add (.var 3) (.lit 1)))

/-- **`addRaw`, compiled.** -/
def addRawProg : Stmt :=
  .seq (.set 4 (.len 0)) <|
  .seq (.ite (.bin .lt (.var 4) (.len 1)) (.set 4 (.len 1)) .skip) <|
  .seq (.alloc 2 (.var 4)) <|
  .seq (.set 3 (.lit 0)) <|
  .loop (.bin .lt (.var 3) (.var 4)) addBody

/-- The loop's invariant after `j` iterations: the inputs and their handles unchanged, the output
holding the sum's first `j` words and zeros after. -/
def Inv (p q : CompPoly.CPolynomial.Raw K) (hp hq ho : UInt64) (m j : ℕ) (σ : State) : Prop :=
  σ.regs 0 = hp ∧ σ.regs 1 = hq ∧ σ.regs 2 = ho ∧ (σ.regs 3).toNat = j ∧ (σ.regs 4).toNat = m ∧
    σ.arr hp = some (enc p) ∧ σ.arr hq = some (enc q) ∧
    ∃ out, σ.arr ho = some out ∧ out.size = m ∧
      ∀ i < m, out[i]! = if i < j then wordOf (p.coeff i + q.coeff i) else 0

theorem size_enc (p : CompPoly.CPolynomial.Raw K) : (enc p).size = p.size := Array.size_map ..

theorem enc_getElem? (p : CompPoly.CPolynomial.Raw K) (i : ℕ) :
    (enc p)[i]? = if i < p.size then some (wordOf (p.coeff i)) else none := by
  unfold enc
  split_ifs with h
  · simp [h]
  · simp [h]

theorem coeff_of_ge {p : CompPoly.CPolynomial.Raw K} {i : ℕ} (h : p.size ≤ i) : p.coeff i = 0 := by
  simp [CompPoly.CPolynomial.Raw.coeff, Array.getD, show ¬ i < p.size by omega]

/-- **Reading a coefficient or `0`**: register `R` gets `p`'s coefficient `j`, at price at most
`10`, nothing else changes. -/
theorem readOrZero_exec {A R : ℕ} (hRA : R ≠ A) (hR3 : R ≠ 3) {p : CompPoly.CPolynomial.Raw K}
    {σ : State} {j : ℕ} (hA : σ.arr (σ.regs A) = some (enc p)) (h3 : (σ.regs 3).toNat = j)
    (hp : p.size < 2 ^ 64) (F : ℕ) :
    ∃ σ' c, (readOrZero A R).exec F σ = some (σ', c) ∧ c ≤ 10 ∧
      σ'.regs R = wordOf (p.coeff j) ∧ (∀ r, r ≠ R → σ'.regs r = σ.regs r) ∧ σ'.heap = σ.heap := by
  have hU : UInt64.size = 2 ^ 64 := rfl
  have hA' : (σ.setReg R 0).arr ((σ.setReg R 0).regs A) = some (enc p) := by
    simp [hRA.symm, hA]
  have hc : (Expr.bin .lt (.var 3) (.len A)).eval (σ.setReg R 0) =
      some (if j < p.size then 1 else 0, 3) := by
    rw [eval_bin (eval_var 3) (eval_len hA')]
    simp only [BinOp.eval, BinOp.price, State.setReg_regs, hR3.symm, ite_false, size_enc,
      UInt64.lt_iff_toNat_lt, h3, UInt64.toNat_ofNat_of_lt' (show p.size < UInt64.size by omega)]
  have hs0 := exec_set (F := F) (r := R) (eval_lit (σ := σ) 0)
  by_cases hj : j < p.size
  · have hx : (enc p)[((σ.setReg R 0).regs 3).toNat]? = some (wordOf (p.coeff j)) := by
      simp [hR3.symm, h3, enc_getElem?, hj]
    have hr := exec_set (F := F) (r := R) (eval_read (eval_var 3) hA' hx)
    have hi := exec_ite_true (t := .skip) hc (by simp [hj]) hr
    refine ⟨_, _, exec_seq hs0 hi, by omega, by simp, fun r hr ↦ by simp [hr], rfl⟩
  · have hc0 : (Expr.bin .lt (.var 3) (.len A)).eval (σ.setReg R 0) = some (0, 3) := by
      rw [hc]; simp [hj]
    have hi := exec_ite_false (s := .set R (.read A (.var 3))) (F := F) hc0 exec_skip
    refine ⟨_, _, exec_seq hs0 hi, by omega, ?_, fun r hr ↦ by simp [hr], rfl⟩
    simp [coeff_of_ge (Nat.not_lt.mp hj), wordOf_zero]


/-- **One iteration of the body**: `out[j]` becomes the sum's word, at price at most `30`. -/
theorem addBody_step {p q : CompPoly.CPolynomial.Raw K} {hp hq ho : UInt64} {m j : ℕ}
    (hm : m < 2 ^ 63) (hpm : p.size ≤ m) (hqm : q.size ≤ m) (hjm : j < m)
    (hdp : hp.toNat ≠ ho.toNat) (hdq : hq.toNat ≠ ho.toNat) {σ : State}
    (hI : Inv p q hp hq ho m j σ) (F : ℕ) :
    ∃ σ' d, addBody.exec F σ = some (σ', d) ∧ d ≤ 30 ∧ Inv p q hp hq ho m (j + 1) σ' := by
  obtain ⟨h0, h1, h2, h3, h4, hap, haq, out, hao, hsz, hout⟩ := hI
  obtain ⟨σ1, c1, e1, hc1, r1, o1, k1⟩ := readOrZero_exec (A := 0) (R := 5) (by decide)
    (by decide) (p := p) (σ := σ) (j := j) (by rw [h0]; exact hap) h3 (by omega) F
  have h3' : (σ1.regs 3).toNat = j := by rw [o1 3 (by decide)]; exact h3
  have hq1 : σ1.arr (σ1.regs 1) = some (enc q) := by
    rw [o1 1 (by decide), h1]; simp only [State.arr, k1]; exact haq
  obtain ⟨σ2, c2, e2, hc2, r2, o2, k2⟩ := readOrZero_exec (A := 1) (R := 6) (by decide)
    (by decide) hq1 h3' (by omega) F
  have g : ∀ r, r ≠ 5 → r ≠ 6 → σ2.regs r = σ.regs r := fun r h5 h6 ↦ by
    rw [o2 r h6, o1 r h5]
  have hk : σ2.heap = σ.heap := by rw [k2, k1]
  have ho2 : σ2.arr (σ2.regs 2) = some out := by
    rw [g 2 (by decide) (by decide), h2]; simp only [State.arr, hk]; exact hao
  have h32 : (σ2.regs 3).toNat = j := by rw [g 3 (by decide) (by decide)]; exact h3
  have hw := exec_write (F := F) (r := 2) (eval_var 3) (eval_bin (op := .xor) (eval_var 5)
    (eval_var 6)) ho2 (by rw [h32, hsz]; exact hjm)
  refine ⟨_, _, exec_seq e1 (exec_seq e2 (exec_seq hw
    (exec_set (r := 3) (eval_bin (op := .add) (eval_var 3) (eval_lit 1))))), ?_, ?_⟩
  · simp only [BinOp.price]; omega
  · have hU : UInt64.size = 2 ^ 64 := rfl
    have hset : ∀ h : UInt64, h.toNat ≠ ho.toNat → ∀ a : Array UInt64,
        (σ.heap.set! ho.toNat a)[h.toNat]? = σ.heap[h.toNat]? := fun h hne a ↦ by
      simp [Array.set!, Ne.symm hne]
    have hb : ho.toNat < σ.heap.size := by
      by_contra hc
      simp [State.arr, Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hao
    have e5 : σ2.regs 5 = wordOf (p.coeff j) := by rw [o2 5 (by decide)]; exact r1
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_,
      out.set! (σ2.regs 3).toNat (BinOp.xor.eval (σ2.regs 5) (σ2.regs 6)), ?_, ?_, ?_⟩
    · simp [g 0 (by decide) (by decide), h0]
    · simp [g 1 (by decide) (by decide), h1]
    · simp [g 2 (by decide) (by decide), h2]
    · simp only [State.setReg_regs, ite_true, BinOp.eval]
      rw [UInt64.toNat_add, h32, UInt64.toNat_one]
      exact Nat.mod_eq_of_lt (by omega)
    · simp [g 4 (by decide) (by decide), h4]
    · simp only [State.arr, State.setReg_heap, hk, g 2 (by decide) (by decide), h2]
      rw [hset hp hdp]; exact hap
    · simp only [State.arr, State.setReg_heap, hk, g 2 (by decide) (by decide), h2]
      rw [hset hq hdq]; exact haq
    · simp only [State.arr, State.setReg_heap, hk, g 2 (by decide) (by decide), h2]
      simp [Array.set!, hb]
    · simp [hsz]
    · intro i hi
      rw [h32, BinOp.eval, e5, r2, ← wordOf_add]
      by_cases hij : i = j
      · subst hij; simp [Array.set!, hsz, hi]
      · have := hout i hi
        simp only [Array.set!, getElem!_def, Array.getElem?_setIfInBounds, Ne.symm hij,
          ite_false] at this ⊢
        rw [this]
        split_ifs <;> first | rfl | omega

/-- **`addRaw`, run on the cost machine**: from handles of `p`'s and `q`'s coefficients, the
program leaves in register `2` the handle of `addRaw p q`'s coefficients, at price at most
`35·max |p| |q| + 20`. -/
theorem addRawProg_exec {p q : CompPoly.CPolynomial.Raw K} {σ : State} {hp hq : UInt64}
    (h0 : σ.regs 0 = hp) (h1 : σ.regs 1 = hq) (hap : σ.arr hp = some (enc p))
    (haq : σ.arr hq = some (enc q)) (hm : max p.size q.size < 2 ^ 63)
    (hheap : σ.heap.size < 2 ^ 63) {fuel : ℕ} (hfuel : max p.size q.size < fuel) :
    ∃ σ' d, addRawProg.exec fuel σ = some (σ', d) ∧ d ≤ 35 * max p.size q.size + 20 ∧
      σ'.arr (σ'.regs 2) = some (enc (CompPoly.CPolynomial.Raw.addRaw p q)) := by
  have hU : UInt64.size = 2 ^ 64 := rfl
  set m := max p.size q.size with hmdef
  have hpl : hp.toNat < σ.heap.size := by
    by_contra hc
    simp [State.arr, Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at hap
  have hql : hq.toNat < σ.heap.size := by
    by_contra hc
    simp [State.arr, Array.getElem?_eq_none (Nat.le_of_not_lt hc)] at haq
  have hpz : (p.size.toUInt64).toNat = p.size := UInt64.toNat_ofNat_of_lt' (by omega)
  have hqz : (q.size.toUInt64).toNat = q.size := UInt64.toNat_ofNat_of_lt' (by omega)
  -- `r4 := max |p| |q|`
  have e1 := exec_set (F := fuel) (r := 4) (eval_len (σ := σ) (r := 0) (by rw [h0]; exact hap))
  set σ1 := σ.setReg 4 (enc p).size.toUInt64
  have hq1 : σ1.arr (σ1.regs 1) = some (enc q) := by simp [σ1, h1, haq]
  have hc := eval_bin (op := .lt) (eval_var (σ := σ1) 4) (eval_len hq1)
  obtain ⟨σ2, c2, e2, hc2, h42, hr2⟩ : ∃ σ2 c2,
      (Stmt.ite (.bin .lt (.var 4) (.len 1)) (.set 4 (.len 1)) .skip).exec fuel σ1 =
        some (σ2, c2) ∧ c2 ≤ 6 ∧ (σ2.regs 4).toNat = m ∧ ∀ r, r ≠ 4 → σ2.regs r = σ.regs r ∧
          σ2.heap = σ.heap := by
    by_cases hlt : p.size < q.size
    · refine ⟨_, _, exec_ite_true hc (by simp [σ1, BinOp.eval, size_enc,
        UInt64.lt_iff_toNat_lt, hpz, hqz, hlt]) (exec_set (eval_len hq1)), by simp [BinOp.price],
        ?_, fun r hr ↦ ⟨by simp [σ1, hr], rfl⟩⟩
      simp [size_enc, hqz]; omega
    · have h0' : BinOp.lt.eval (σ1.regs 4) (enc q).size.toUInt64 = 0 := by
        simp [σ1, BinOp.eval, size_enc, UInt64.lt_iff_toNat_lt, hpz, hqz, hlt]
      refine ⟨_, _, exec_ite_false (h0' ▸ hc) exec_skip, by simp [BinOp.price], ?_,
        fun r hr ↦ ⟨by simp [σ1, hr], rfl⟩⟩
      simp [σ1, size_enc, hpz]; omega
  -- the output, zeroed, and `r3 := 0`
  have e3 := exec_alloc (F := fuel) (r := 2) (eval_var (σ := σ2) 4)
  have e4 := exec_set (F := fuel) (r := 3) (eval_lit (σ := { σ2.setReg 2 σ2.heap.size.toUInt64 with
      heap := σ2.heap.push (Array.replicate (σ2.regs 4).toNat 0) }) 0)
  set ho : UInt64 := σ.heap.size.toUInt64 with hho
  have hoz : ho.toNat = σ.heap.size := UInt64.toNat_ofNat_of_lt' (by omega)
  set σ4 := ({ σ2.setReg 2 σ2.heap.size.toUInt64 with
      heap := σ2.heap.push (Array.replicate (σ2.regs 4).toNat 0) } : State).setReg 3 0
  have hk2 : σ2.heap = σ.heap := (hr2 0 (by decide)).2
  have hI0 : Inv p q hp hq ho m 0 σ4 := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, Array.replicate m 0, ?_, ?_, ?_⟩
    · simp [σ4, (hr2 0 (by decide)).1, h0]
    · simp [σ4, (hr2 1 (by decide)).1, h1]
    · simp [σ4, hk2, hho]
    · simp [σ4]
    · simp [σ4, h42]
    · simp only [σ4, State.arr, State.setReg_heap, hk2]
      rw [Array.getElem?_push_lt hpl, ← Array.getElem?_eq_getElem hpl]; exact hap
    · simp only [σ4, State.arr, State.setReg_heap, hk2]
      rw [Array.getElem?_push_lt hql, ← Array.getElem?_eq_getElem hql]; exact haq
    · simp only [σ4, State.arr, hk2, hoz, h42]
      simp
    · simp
    · intro i hi; simp [hi]
  -- the loop
  have hcond : ∀ j σ', Inv p q hp hq ho m j σ' →
      (Expr.bin .lt (.var 3) (.var 4)).eval σ' = some (if j < m then 1 else 0, 3) := by
    intro j σ' hI
    obtain ⟨-, -, -, h3, h4, -⟩ := hI
    rw [eval_bin (eval_var 3) (eval_var 4)]
    simp [BinOp.eval, BinOp.price, UInt64.lt_iff_toNat_lt, h3, h4]
  have hdp : hp.toNat ≠ ho.toNat := by omega
  have hdq : hq.toNat ≠ ho.toNat := by omega
  obtain ⟨σ5, d5, e5, hd5, hI5⟩ := loop_exec (s := addBody) (n := m) (cc := 3) (cb := 30)
    (fun j hj σ' hI ↦ ⟨1, by decide, by rw [hcond j σ' hI]; simp [hj]⟩)
    (fun σ' hI ↦ by rw [hcond m σ' hI]; simp)
    (fun j hj σ' hI F ↦ addBody_step hm (le_max_left _ _) (le_max_right _ _) hj hdp hdq hI F)
    0 (by omega) σ4 hI0 fuel (by omega)
  refine ⟨σ5, _, exec_seq e1 (exec_seq e2 (exec_seq e3 (exec_seq e4 e5))), ?_, ?_⟩
  · simp only [Nat.sub_zero] at hd5
    have : max 1 (σ2.regs 4).toNat ≤ m + 1 := by rw [h42]; omega
    omega
  · obtain ⟨-, -, h2, -, -, -, -, out, hao, hsz, hout⟩ := hI5
    rw [h2, hao]
    congr 1
    apply Array.ext
    · simp [hsz, size_enc, CompPoly.CPolynomial.Raw.add_size, hmdef]
    · intro i hi _
      have him : i < m := hsz ▸ hi
      have := hout i him
      simp only [him, ite_true, getElem!_pos out i hi] at this
      rw [this]
      simp only [enc, Array.getElem_map]
      rw [CompPoly.CPolynomial.Raw.add_coeff]

end

end LeanVM.Cost.Samples
