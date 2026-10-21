/-
  LeanVM.Guest.B2C.CplJustB

  The completeness walk's justifications (`CplJust.lean`) under any semantics of `BLAKE2S`.
-/

module

public import LeanVM.Guest.B2C.CplJust
public import LeanVM.Guest.B2C.CplB
public import LeanVM.Guest.B2C.CplExecB
public import LeanVM.Guest.CheckSoundB

/-!
# What the walk's facts mean under any `BLAKE2S` semantics

`CplJust.lean`'s `LHolds`, `BookOk`, `CWOk` with `S : BlakeSem` a parameter (`LHoldsB`, whose
`BLAKE2S` fact asks `S.check` of its nine cells; `BookOkB`, `CWOkB`), and the lemmas reading
them: `justIB_sound`, `cellKB_sound`, `passLB_sound`, `blakeB_sound`, …, proved as there over
`LogicB.lean`. What does not mention the semantics (`FCHolds`, `FrOk`, `TgOk`, `NxOk`, `CXOk`) is
`CplJust.lean`'s.

* `lHoldsB_deployed`, `bookOkB_deployed`, `cwOkB_deployed`: at `blakeDeployed`, they are
  `CplJust.lean`'s.
-/

namespace LeanVM.Guest.B2C

open LeanVM.Parameters LeanVM.Semantics LeanVM.Guest LeanVM.Guest.Core LeanVM.Guest.Exec
open LeanVM.Guest.Check

@[expose] public section

variable {S : BlakeSem}

section Sem

variable {κ : ℕ} (L : MemImage κ) (fp : ℕ)

variable (S) in
/-- **What a fact on frame cells says.** -/
def LHoldsB : LAtom → Prop
  | .const d x => rdc L fp d = some x
  | .add d a b => ∃ va vb, rdc L fp a = some va ∧ rdc L fp b = some vb ∧ rdc L fp d = some (va + vb)
  | .mul d a b => ∃ va vb, rdc L fp a = some va ∧ rdc L fp b = some vb ∧ rdc L fp d = some (va * vb)
  | .same a b => ∃ v, rdc L fp a = some v ∧ rdc L fp b = some v
  | .load d p off => ∃ pv vd, rdc L fp p = some pv ∧ IsInK pv ∧ rdc L fp d = some vd ∧
      L.read (pv.limb 0 * gpow off) = some vd
  | .ne x i p => ∃ vx vi, rdc L fp x = some vx ∧ rdc L fp i = some vi ∧
      rdc L fp p = some (vx * vi) ∧ vx * vi = 1
  | .range x y t1 t2 k => ∃ vx vy v1 v2, rdc L fp x = some vx ∧ IsInK vx ∧ rdc L fp y = some vy ∧
      IsInK vy ∧ rdc L fp t1 = some v1 ∧ rdc L fp t2 = some v2 ∧
      L.read (vx.limb 0 * gpow 0) = some v1 ∧ L.read (vy.limb 0 * gpow 0) = some v2 ∧
      rdc L fp k = some (vx * vy)
  | .inK a b => ∃ va vb, rdc L fp a = some va ∧ IsInK va ∧ rdc L fp b = some vb ∧ IsInK vb
  | .blake m0 m1 m2 m3 cv0 cv1 o0 o1 md => ∃ w0 w1 w2 w3 c0 c1 d0 d1 v,
      rdc L fp m0 = some w0 ∧ rdc L fp m1 = some w1 ∧ rdc L fp m2 = some w2 ∧
      rdc L fp m3 = some w3 ∧ rdc L fp cv0 = some c0 ∧ rdc L fp cv1 = some c1 ∧
      rdc L fp o0 = some d0 ∧ rdc L fp o1 = some d1 ∧ rdc L fp md = some v ∧
      S.check ![w0, w1, w2, w3] c0 c1 d0 d1 v
  | .addr p run => ∃ c0 rest, run = c0 :: rest ∧ rdc L fp p = some (ofK (gpow (fp + c0)))
  | .none => True

variable (S) in
/-- The facts filed in a book hold, under their keys. -/
def BookOkB (B : BookC) : Prop := ∀ o a, a ∈ lookC B o → LHoldsB S L fp a ∧ o ∈ keysC a

variable (S) in
/-- **The walk's state holds.** -/
structure CWOkB (X : CX) (st : CW) : Prop where
  env : EnvHolds L (gpow fp) st.seg.env
  book : BookOkB S L fp st.book
  fr : FrOk L fp st.fr
  tg : TgOk L fp st.tg
  nx : NxOk L fp X.fs st.nx

end Sem

/-! ## The book -/

section Book

variable {κ : ℕ} {L : MemImage κ} {fp : ℕ}

theorem BookOkB.nil : BookOkB S L fp .nil := fun _ _ h ↦ by simp [lookC, getF_eq] at h

theorem BookOkB.file {B : BookC} (hB : BookOkB S L fp B) {a : LAtom} (ha : LHoldsB S L fp a) :
    BookOkB S L fp (fileC B a) := by
  unfold fileC
  have key : ∀ (ks : List ℕ) (B : BookC), (∀ k ∈ ks, k ∈ keysC a) → BookOkB S L fp B →
      BookOkB S L fp (ks.foldl (addKeyC a) B) := by
    intro ks
    induction ks with
    | nil => exact fun _ _ hB ↦ hB
    | cons k ks ih =>
      intro B hk hB
      refine ih _ (fun k' hk' ↦ hk k' (List.mem_cons_of_mem _ hk')) (fun o b hb ↦ ?_)
      rcases lookC_addKeyC hb with ⟨rfl, rfl⟩ | hb
      · exact ⟨ha, hk o List.mem_cons_self⟩
      · exact hB o b hb
  exact key _ B (fun _ h ↦ h) hB

/-- A cell a fact is filed under holds a word. -/
theorem keysB_read {a : LAtom} (ha : LHoldsB S L fp a) {o : ℕ} (ho : o ∈ keysC a) :
    ∃ v, rdc L fp o = some v := by
  cases a with
  | const d x => simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, ha⟩
  | add d a b =>
    obtain ⟨va, vb, h1, h2, h3⟩ := ha
    simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, h3⟩
  | mul d a b =>
    obtain ⟨va, vb, h1, h2, h3⟩ := ha
    simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, h3⟩
  | same a b =>
    obtain ⟨v, h1, h2⟩ := ha
    simp only [keysC, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    exacts [⟨_, h1⟩, ⟨_, h2⟩]
  | load d p off =>
    obtain ⟨pv, vd, h1, -, h3, -⟩ := ha
    simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, h3⟩
  | ne x i p =>
    obtain ⟨vx, vi, -, -, h3, -⟩ := ha
    simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, h3⟩
  | range x y t1 t2 k =>
    obtain ⟨vx, vy, v1, v2, hx, -, hy, -, h1, h2, -, -, hk⟩ := ha
    simp only [keysC, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    exacts [⟨_, hx⟩, ⟨_, hy⟩]
  | inK a b =>
    obtain ⟨va, vb, h1, -, h2, -⟩ := ha
    simp only [keysC, List.mem_cons, List.not_mem_nil, or_false] at ho
    rcases ho with rfl | rfl
    exacts [⟨_, h1⟩, ⟨_, h2⟩]
  | blake m0 m1 m2 m3 cv0 cv1 o0 o1 md =>
    obtain ⟨w0, w1, w2, w3, c0, c1, d0, d1, v, -, -, -, -, -, -, h, -⟩ := ha
    simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, h⟩
  | addr p run =>
    obtain ⟨c0, rest, -, h⟩ := ha
    simp only [keysC, List.mem_singleton] at ho; subst ho; exact ⟨_, h⟩
  | none => simp [keysC] at ho

end Book

/-! ## Justifications -/

section Just

variable {κ : ℕ} {L : MemImage κ} {fp : ℕ} {X : CX} {st : CW}

theorem cplCstAtB_sound (hX : CXOk L fp X) (hst : BookOkB S L fp st.book) {o k0 k1 k2 : ℕ}
    (h : cplCstAt X st o = some (k0, k1, k2)) : rdc L fp o = some (OInstr.imm k0 k1 k2) := by
  unfold cplCstAt at h
  split at h
  · rename_i a b c hs
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    exact statAt_sound hX hs
  · obtain ⟨a, ha, hf⟩ := List.exists_of_findSome?_eq_some h
    have hh := (hst o a ha).1
    split at hf
    · rename_i d x
      cases hd : Nat.beq d o
      · rw [hd] at hf; cases hf
      · rw [hd] at hf
        obtain rfl := Nat.eq_of_beq_eq_true hd
        simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨h0, h1, h2⟩ := hf
        rw [← eq_imm_of_limbs h0 h1 h2]
        exact hh
    · rename_i x i p
      cases hd : Nat.beq p o
      · rw [hd] at hf; cases hf
      · rw [hd] at hf
        obtain rfl := Nat.eq_of_beq_eq_true hd
        simp only [Bool.cond_true, Option.some.injEq, Prod.mk.injEq] at hf
        obtain ⟨rfl, rfl, rfl⟩ := hf
        obtain ⟨vx, vi, -, -, h3, h4⟩ := hh
        rw [imm_one, h3, h4]
    · cases hf

theorem isZB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {o : ℕ} (h : isZ X st o = true) :
    rdc L fp o = some 0 := by
  unfold isZ at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · split at h
    · rename_i hc
      rw [cplCstAtB_sound hX hst.book hc, imm_zero]
    · cases h
  · exact hst.env o _ (isZero_eq h)

theorem isOB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {o : ℕ} (h : isO X st o = true) :
    rdc L fp o = some 1 := by
  unfold isO at h
  rcases Bool.or_eq_true_iff.mp h with h | h
  · split at h
    · rename_i hc
      rw [cplCstAtB_sound hX hst.book hc, imm_one]
    · cases h
  · obtain ⟨v, hv, h1⟩ := isOne_val h (gpow fp)
    rw [← h1]
    exact hst.env o v hv

theorem knownB_sound (hX : CXOk L fp X) (hst : BookOkB S L fp st.book) {o : ℕ}
    (h : known X st o = true) : ∃ v, rdc L fp o = some v := by
  simp only [known, Bool.or_eq_true, Nat.ble_eq, Option.isSome_iff_exists, Bool.not_eq_true',
    List.isEmpty_eq_false_iff_exists_mem] at h
  rcases h with (h | ⟨p, hp⟩) | ⟨a, ha⟩
  · obtain ⟨v, hv, -⟩ := hX.hdr o h
    exact ⟨v, hv⟩
  · exact ⟨_, statAt_sound hX hp⟩
  · exact keysB_read (hst o a ha).1 (hst o a ha).2

theorem sameCB_sound (hX : CXOk L fp X) (hst : BookOkB S L fp st.book) {a b : ℕ}
    (h : sameC X st a b = true) : ∃ v, rdc L fp a = some v ∧ rdc L fp b = some v := by
  simp only [sameC, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ⟨hab, hk⟩ | h
  · obtain rfl := Nat.eq_of_beq_eq_true hab
    obtain ⟨v, hv⟩ := knownB_sound hX hst hk
    exact ⟨v, hv, hv⟩
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst a x hx).1
    split at hp
    · obtain ⟨v, h1, h2⟩ := hh
      simp only [Bool.or_eq_true, Bool.and_eq_true] at hp
      rcases hp with ⟨hu, hw⟩ | ⟨hu, hw⟩
      · obtain rfl := Nat.eq_of_beq_eq_true hu
        obtain rfl := Nat.eq_of_beq_eq_true hw
        exact ⟨v, h1, h2⟩
      · obtain rfl := Nat.eq_of_beq_eq_true hu
        obtain rfl := Nat.eq_of_beq_eq_true hw
        exact ⟨v, h2, h1⟩
    · cases hp

theorem zeroByB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {a : ℕ}
    (h : zeroBy X st a = true) : rdc L fp a = some 0 := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := (hst.book a x hx).1
  split at hp
  · rename_i u w
    obtain ⟨v, h1, h2⟩ := hh
    simp only [Bool.or_eq_true, Bool.and_eq_true] at hp
    rcases hp with ⟨hu, hz⟩ | ⟨hw, hz⟩
    · obtain rfl := Nat.eq_of_beq_eq_true hu
      rw [h1, ← (isZB_sound hX hst hz).symm.trans h2]
    · obtain rfl := Nat.eq_of_beq_eq_true hw
      rw [h2, ← (isZB_sound hX hst hz).symm.trans h1]
  · cases hp

/-- A product of two cells, in either order. -/
theorem mulB_pair {pc a b x y d : ℕ} (h : (x = a ∧ y = b) ∨ (x = b ∧ y = a)) {vx vy : E}
    (hx : rdc L fp x = some vx) (hy : rdc L fp y = some vy) (hd : rdc L fp d = some (vx * vy)) :
    Guest.HoldsB S L pc (gpow fp) (.mul a b d) := by
  unfold Guest.HoldsB
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨vx, vy, hx, hy, hd⟩
  · exact ⟨vy, vx, hy, hx, by rw [mul_comm vy vx]; exact hd⟩

theorem holdsB_xor_of {pc a b d : ℕ} {va vb vd : E} (ha : rdc L fp a = some va)
    (hb : rdc L fp b = some vb) (hd : rdc L fp d = some vd) (h : vd = va + vb) :
    Guest.HoldsB S L pc (gpow fp) (.xor a b d) := by
  unfold Guest.HoldsB
  exact ⟨va, vb, ha, hb, h ▸ hd⟩

/-- An `XOR` over a permutation of a sum's cells holds, in characteristic two. -/
theorem perm3B_holds {pc a b d p q r : ℕ} (h : perm3 a b d p q r = true) {vx vy : E}
    (hq : rdc L fp q = some vx) (hr : rdc L fp r = some vy) (hp : rdc L fp p = some (vx + vy)) :
    Guest.HoldsB S L pc (gpow fp) (.xor a b d) := by
  simp only [perm3, Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at h
  rcases h with ((((⟨⟨rfl, rfl⟩, rfl⟩ | ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) |
    ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩) | ⟨⟨rfl, rfl⟩, rfl⟩
  · exact holdsB_xor_of hp hq hr (by rw [add_comm, char2])
  · exact holdsB_xor_of hq hp hr (char2 vx vy).symm
  · exact holdsB_xor_of hp hr hq (by rw [add_assoc, CharTwo.add_self_eq_zero, add_zero])
  · exact holdsB_xor_of hr hp hq (by rw [add_comm vx vy, char2])
  · exact holdsB_xor_of hq hr hp rfl
  · exact holdsB_xor_of hr hq hp (add_comm vx vy)

theorem xorB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {pc a b d : ℕ}
    (h : justI X st pc (.xor a b d) = true) : Guest.HoldsB S L pc (gpow fp) (.xor a b d) := by
  have hA : ∀ c, addAt st a b d c = true → Guest.HoldsB S L pc (gpow fp) (.xor a b d) := by
    intro c h
    obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst.book c x hx).1
    split at hp
    · obtain ⟨vx, vy, h1, h2, h3⟩ := hh
      exact perm3B_holds hp h1 h2 h3
    · cases hp
  simp only [justI, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with ((((((h | h) | h) | ⟨hz, hs⟩) | ⟨⟨hab, hz⟩, hk⟩) | ⟨⟨hab, hz⟩, hk⟩) | ⟨⟨hab, hk⟩, hz⟩)
  · exact hA _ h
  · exact hA _ h
  · exact hA _ h
  · obtain ⟨v, h1, h2⟩ := sameCB_sound hX hst.book hs
    exact holdsB_xor_of h1 h2 (isZB_sound hX hst hz) (char2C v).symm
  · obtain rfl := Nat.eq_of_beq_eq_true hab
    obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
    exact holdsB_xor_of hv (isZB_sound hX hst hz) hv (add_zero v).symm
  · obtain rfl := Nat.eq_of_beq_eq_true hab
    obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
    exact holdsB_xor_of (isZB_sound hX hst hz) hv hv (zero_add v).symm
  · obtain rfl := Nat.eq_of_beq_eq_true hab
    obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
    exact holdsB_xor_of (zeroByB_sound hX hst hz) hv hv (zero_add v).symm

theorem mulB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {pc a b d : ℕ}
    (h : justI X st pc (.mul a b d) = true) : Guest.HoldsB S L pc (gpow fp) (.mul a b d) := by
  simp only [justI, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((((h | h) | ⟨ho, hs⟩) | ⟨ho, hs⟩) | h) | ⟨⟨hle, ho⟩, hn⟩)
  rotate_left
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst.book a x hx).1
    split at hp
    · rename_i x' y' t1 t2 k
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hd, hp⟩ := hp
      obtain rfl := Nat.eq_of_beq_eq_true hd
      obtain ⟨vx, vy, v1, v2, h1, -, h2, -, -, -, -, -, h3⟩ := hh
      exact mulB_pair (pairEq_sound hp) h1 h2 h3
    · cases hp
  rotate_right
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst.book d x hx).1
    split at hp
    · rename_i d' x' y'
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hd, hp⟩ := hp
      obtain rfl := Nat.eq_of_beq_eq_true hd
      obtain ⟨vx, vy, h1, h2, h3⟩ := hh
      exact mulB_pair (pairEq_sound hp) h1 h2 h3
    · rename_i x' i' p'
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hd, hp⟩ := hp
      obtain rfl := Nat.eq_of_beq_eq_true hd
      obtain ⟨vx, vi, h1, h2, h3, -⟩ := hh
      exact mulB_pair (pairEq_sound hp) h1 h2 h3
    · rename_i p' run
      simp only [Bool.and_eq_true] at hp
      obtain ⟨hd, hp⟩ := hp
      obtain rfl := Nat.eq_of_beq_eq_true hd
      obtain ⟨c0, rest, rfl, h3⟩ := hh
      unfold addrMul at hp
      split at hp
      · rename_i e1 k0 r rs ha hb hr
        cases he : gpE X k0 with
        | none => rw [he] at hp; cases hp
        | some e2 =>
          rw [he] at hp
          obtain rfl := Nat.eq_of_beq_eq_true hp
          obtain ⟨rfl, -⟩ := List.cons.inj hr
          have h1 := statAt_sound hX ha
          have h2 := cplCstAtB_sound hX hst.book hb
          rw [gpE_sound hX he] at h2
          unfold Guest.HoldsB
          refine ⟨_, _, h1, h2, ?_⟩
          show rdc L fp _ = _
          rw [h3, PC.word, ofK_gpow_mul, Nat.add_assoc]
      · cases hp
    · cases hp
  · obtain ⟨v, h1, h2⟩ := sameCB_sound hX hst.book hs
    unfold Guest.HoldsB
    exact ⟨v, 1, h1, isOB_sound hX hst ho, by rw [mul_one]; exact h2⟩
  · obtain ⟨v, h1, h2⟩ := sameCB_sound hX hst.book hs
    unfold Guest.HoldsB
    exact ⟨1, v, isOB_sound hX hst ho, h1, by rw [one_mul]; exact h2⟩
  · unfold fpgMul at h
    split at h
    · rename_i e e1 k0 hd ha hb
      simp only [Bool.and_eq_true, Nat.ble_eq] at h
      obtain ⟨hle, h⟩ := h
      cases he : gpE X k0 with
      | none => rw [he] at h; cases h
      | some e2 =>
        rw [he] at h
        obtain rfl := Nat.eq_of_beq_eq_true h
        have h1 := statAt_sound hX ha
        have h2 := cplCstAtB_sound hX hst.book hb
        rw [gpE_sound hX he] at h2
        unfold Guest.HoldsB
        refine ⟨_, _, h1, h2, ?_⟩
        refine (statAt_sound hX hd).trans ?_
        rw [PC.word, PC.word, ofK_gpow_mul, show fp + e1 + (e - e1) = fp + e by omega]
    · cases h
  · have hle := Nat.le_of_ble_eq_true hle
    have hb := isOB_sound hX hst ho
    have haddr : gpow (fp + X.fs) * gpow (d - X.fs) = gpow fp * gpow d := by
      rw [← gpow_addC, ← gpow_addC, show fp + X.fs + (d - X.fs) = fp + d by omega]
    unfold nextMul at hn
    split at hn
    · rename_i o cv hf
      have hfc := hst.nx _ (List.mem_of_find?_eq_some hf)
      have ho : o = d - X.fs := by
        have := List.find?_some hf
        exact Nat.eq_of_beq_eq_true this
      subst ho
      obtain ⟨v, hv, hn'⟩ := hfc
      rw [haddr] at hn'
      have ha : rdc L fp a = some v := by
        simp only [Bool.or_eq_true] at hn
        rcases hn with hn | hn
        · rw [Nat.eq_of_beq_eq_true hn]; exact hv
        · obtain ⟨w, h1, h2⟩ := sameCB_sound hX hst.book hn
          rw [h1, ← h2, hv]
      unfold Guest.HoldsB
      exact ⟨v, 1, ha, hb, by rw [mul_one]; exact hn'⟩
    · rename_i o i hf
      have hfc := hst.nx _ (List.mem_of_find?_eq_some hf)
      have ho : o = d - X.fs := by
        have := List.find?_some hf
        exact Nat.eq_of_beq_eq_true this
      subst ho
      obtain ⟨v, hv, hn'⟩ := hfc
      rw [haddr] at hn'
      simp only [Bool.and_eq_true] at hn
      obtain rfl := Nat.eq_of_beq_eq_true hn.1
      unfold Guest.HoldsB
      exact ⟨v, 1, hv, hb, by rw [mul_one]; exact hn'⟩
    · rename_i o hf
      have hfc := hst.nx _ (List.mem_of_find?_eq_some hf)
      have ho : o = d - X.fs := by
        have := List.find?_some hf
        exact Nat.eq_of_beq_eq_true this
      subst ho
      have ha := statAt_sound hX (of_decide_eq_true hn)
      unfold FCHolds at hfc
      rw [haddr] at hfc
      unfold Guest.HoldsB
      refine ⟨_, 1, ha, hb, ?_⟩
      rw [mul_one, PC.word]
      exact hfc
    · cases hn

theorem frameHasB_sound (hst : CWOkB S L fp X st) {o1 o2 : ℕ} {fc : FC}
    (h : frameHas st o1 o2 fc = true) :
    ∃ kfp, rdc L fp o1 = some (ofK (gpow kfp)) ∧ FCHolds L fp kfp o2 fc := by
  unfold frameHas at h
  split at h
  · rename_i o fcs hf
    obtain ⟨kfp, hq, hp⟩ := frame_find hst.fr hf
    obtain ⟨p, hp', hm⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hm
    obtain ⟨h1, rfl⟩ := hm
    obtain rfl := Nat.eq_of_beq_eq_true h1
    exact ⟨kfp, hq, hp p hp'⟩
  · cases h

theorem derefB_holds {pc o1 o2 o3 : ℕ} {mode : DerefMode} {p v3 : E}
    (h1 : rdc L fp o1 = some p) (hK : IsInK p) (h3 : rdc L fp o3 = some v3)
    (h2 : L.read (p.limb 0 * gpow o2) = some (derefSource mode ⟨gpow pc, gpow fp⟩ v3)) :
    Guest.HoldsB S L pc (gpow fp) (.deref o1 o2 o3 mode) := by
  unfold Guest.HoldsB
  exact ⟨p, v3, h1, hK, h3, h2⟩

theorem derefCellB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {pc o1 o2 o3 : ℕ}
    (h : justI X st pc (.deref o1 o2 o3 .cell) = true) :
    Guest.HoldsB S L pc (gpow fp) (.deref o1 o2 o3 .cell) := by
  simp only [justI, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((h | h) | h) | h) | ⟨⟨h0, hs⟩, hk⟩
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst.book o3 x hx).1
    split at hp
    · simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hd, hp'⟩, hoff⟩ := hp
      obtain rfl := Nat.eq_of_beq_eq_true hd
      obtain rfl := Nat.eq_of_beq_eq_true hp'
      obtain rfl := Nat.eq_of_beq_eq_true hoff
      obtain ⟨pv, vd, h1, hK, h3, h2⟩ := hh
      exact derefB_holds h1 hK h3 h2
    · cases hp
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst.book o1 x hx).1
    split at hp
    · simp only [Bool.and_eq_true, Bool.or_eq_true] at hp
      obtain ⟨h0, (⟨hx', ht⟩ | ⟨hy', ht⟩)⟩ := hp
      · obtain rfl := Nat.eq_of_beq_eq_true h0
        obtain rfl := Nat.eq_of_beq_eq_true hx'
        obtain rfl := Nat.eq_of_beq_eq_true ht
        obtain ⟨vx, vy, v1, v2, h1, hK, -, -, h3, -, h2, -, -⟩ := hh
        exact derefB_holds h1 hK h3 h2
      · obtain rfl := Nat.eq_of_beq_eq_true h0
        obtain rfl := Nat.eq_of_beq_eq_true hy'
        obtain rfl := Nat.eq_of_beq_eq_true ht
        obtain ⟨vx, vy, v1, v2, -, -, h1, hK, -, h3, -, h2, -⟩ := hh
        exact derefB_holds h1 hK h3 h2
    · cases hp
  · unfold frameCell at h
    split at h
    · rename_i o fcs hf
      obtain ⟨kfp, hq, hp⟩ := frame_find hst.fr hf
      obtain ⟨⟨o, fc⟩, hp', hm⟩ := List.any_eq_true.mp h
      have hfc := hp _ hp'
      simp only at hfc
      cases fc with
      | val cv =>
        simp only [Bool.and_eq_true, Bool.or_eq_true] at hm
        obtain ⟨h1, hm⟩ := hm
        obtain rfl := Nat.eq_of_beq_eq_true h1
        obtain ⟨v, hv, hc⟩ := hfc
        have h3 : rdc L fp o3 = some v := by
          rcases hm with hm | hm
          · rw [← Nat.eq_of_beq_eq_true hm]; exact hv
          · obtain ⟨w, h1, h2⟩ := sameCB_sound hX hst.book hm
            rw [h2, ← h1, hv]
        exact derefB_holds hq (isInK_ofK _) h3 (by rw [limb_ofK0]; exact hc)
      | self =>
        simp only [Bool.and_eq_true] at hm
        obtain ⟨h1, hm⟩ := hm
        obtain rfl := Nat.eq_of_beq_eq_true h1
        obtain rfl := Nat.eq_of_beq_eq_true hm
        exact derefB_holds hq (isInK_ofK _) hq (by rw [limb_ofK0]; exact hfc)
      | pc r =>
        simp only [Bool.and_eq_true] at hm
        obtain ⟨h1, hm⟩ := hm
        obtain rfl := Nat.eq_of_beq_eq_true h1
        split at hm
        · rename_i k0 hc
          have h3 := cplCstAtB_sound hX hst.book hc
          rw [gpE_sound hX (of_decide_eq_true hm)] at h3
          exact derefB_holds hq (isInK_ofK _) h3 (by rw [limb_ofK0]; exact hfc)
        · cases hm
      | fp => simp at hm
      | hdr i => simp at hm
    · cases h
  · obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true] at hm
    obtain ⟨⟨h1, h2⟩, h3⟩ := hm
    obtain ⟨p, w, hp, hK, hw, -, hr⟩ := hst.tg t ht
    rw [Nat.eq_of_beq_eq_true h1] at hw
    rw [Nat.eq_of_beq_eq_true h2] at hp
    rw [Nat.eq_of_beq_eq_true h3] at hr
    exact derefB_holds hp hK hw hr
  · obtain rfl := Nat.eq_of_beq_eq_true h0
    have h1 := statAt_sound hX (of_decide_eq_true hs)
    obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
    rw [fpg_word] at h1
    exact derefB_holds h1 (isInK_ofK _) hv (by rw [limb_ofK0, gpow_zero', mul_one]; exact hv)

theorem derefFpB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {pc o1 o2 o3 : ℕ}
    (h : justI X st pc (.deref o1 o2 o3 .fp) = true) :
    Guest.HoldsB S L pc (gpow fp) (.deref o1 o2 o3 .fp) := by
  simp only [justI, Bool.or_eq_true, Bool.and_eq_true] at h
  obtain ⟨hk, h | ⟨h0, h⟩⟩ := h
  · obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
    obtain ⟨kfp, hq, hfc⟩ := frameHasB_sound hst h
    exact derefB_holds hq (isInK_ofK _) hv (by rw [limb_ofK0]; exact hfc)
  · obtain rfl := Nat.eq_of_beq_eq_true h0
    obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
    split at h
    · rename_i x hx
      have h1 := statAt_sound hX hx
      have h2 := statAt_sound hX (of_decide_eq_true h)
      rw [fpg_word] at h1 h2
      refine derefB_holds h1 (isInK_ofK _) hv ?_
      rw [limb_ofK0, gpow_zero', mul_one]
      refine h2.trans ?_
      rw [gpow_zero', mul_one]
      rfl
    · cases h

theorem derefPcB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {pc o1 o2 o3 : ℕ}
    (h : justI X st pc (.deref o1 o2 o3 .pc) = true) :
    Guest.HoldsB S L pc (gpow fp) (.deref o1 o2 o3 .pc) := by
  simp only [justI, Bool.and_eq_true] at h
  obtain ⟨hk, h⟩ := h
  obtain ⟨v, hv⟩ := knownB_sound hX hst.book hk
  obtain ⟨kfp, hq, hfc⟩ := frameHasB_sound hst h
  exact derefB_holds hq (isInK_ofK _) hv (by rw [limb_ofK0, derefSource_pc]; exact hfc)

theorem blakeB_sound (hst : CWOkB S L fp X st) {pc m0 m1 m2 m3 cv out md : ℕ}
    (h : justI X st pc (.blake2s m0 m1 m2 m3 cv out md) = true) :
    Guest.HoldsB S L pc (gpow fp) (.blake2s m0 m1 m2 m3 cv out md) := by
  obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
  have hh := (hst.book out x hx).1
  split at hp
  · simp only [Bool.and_eq_true] at hp
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩ := hp
    obtain rfl := Nat.eq_of_beq_eq_true h0
    obtain rfl := Nat.eq_of_beq_eq_true h1
    obtain rfl := Nat.eq_of_beq_eq_true h2
    obtain rfl := Nat.eq_of_beq_eq_true h3
    obtain rfl := Nat.eq_of_beq_eq_true h4
    obtain rfl := Nat.eq_of_beq_eq_true h5
    obtain rfl := Nat.eq_of_beq_eq_true h6
    obtain rfl := Nat.eq_of_beq_eq_true h7
    obtain rfl := Nat.eq_of_beq_eq_true h8
    obtain ⟨w0, w1, w2, w3, c0, c1, d0, d1, v, e0, e1, e2, e3, ec0, ec1, ed0, ed1, ev, hc⟩ := hh
    dsimp only [rdc] at ec1 ed1
    rw [gpow_succ] at ec1 ed1
    unfold Guest.HoldsB
    exact ⟨w0, w1, w2, w3, c0, c1, d0, d1, v, e0, e1, e2, e3, ec0, ec1, ed0, ed1, ev, hc⟩
  · cases hp

/-- **A justified instruction holds.** -/
theorem justIB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {pc : ℕ} {ins : OInstr}
    (h : justI X st pc ins = true) : Guest.HoldsB S L pc (gpow fp) ins := by
  cases ins with
  | set o k0 k1 k2 =>
    unfold Guest.HoldsB
    exact cplCstAtB_sound hX hst.book (of_decide_eq_true h)
  | xor a b d => exact xorB_sound hX hst h
  | mul a b d => exact mulB_sound hX hst h
  | deref o1 o2 o3 mode =>
    cases mode with
    | cell => exact derefCellB_sound hX hst h
    | fp => exact derefFpB_sound hX hst h
    | pc => exact derefPcB_sound hX hst h
  | blake2s m0 m1 m2 m3 cv out md => exact blakeB_sound hst h
  | jump => cases h

/-- **A cell `cellK` accepts holds a word of `K`.** -/
theorem cellKB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) {o : ℕ} (h : cellK X st o = true) :
    ∃ v, rdc L fp o = some v ∧ IsInK v := by
  simp only [cellK, Bool.or_eq_true, Bool.and_eq_true] at h
  rcases h with (((((⟨h1, hm⟩ | h) | h) | h) | h) | h)
  · obtain ⟨v, hv, hK⟩ := hX.hdr o (Nat.le_of_ble_eq_true h1)
    exact ⟨v, hv, hK (by simpa using hm)⟩
  · split at h
    · rename_i k0 k1 k2 hs
      simp only [Bool.and_eq_true] at h
      obtain rfl := Nat.eq_of_beq_eq_true h.1
      obtain rfl := Nat.eq_of_beq_eq_true h.2
      exact ⟨_, statAt_sound hX hs, by rw [PC.word, imm_of_ofBits rfl]; exact isInK_ofK _⟩
    · rename_i e hs
      exact ⟨_, statAt_sound hX hs, by rw [PC.word]; exact isInK_ofK _⟩
    · cases h
  · obtain ⟨x, hx, hp⟩ := List.any_eq_true.mp h
    have hh := (hst.book o x hx).1
    split at hp
    · rename_i d x'
      simp only [Bool.and_eq_true] at hp
      obtain ⟨⟨hd, h1⟩, h2⟩ := hp
      obtain rfl := Nat.eq_of_beq_eq_true hd
      refine ⟨_, hh, ?_⟩
      rw [eq_imm_of_limbs rfl (Nat.eq_of_beq_eq_true h1) (Nat.eq_of_beq_eq_true h2),
        imm_of_ofBits rfl]
      exact isInK_ofK _
    · obtain ⟨vx, vy, v1, v2, hx', hKx, hy', hKy, -⟩ := hh
      simp only [Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · rw [← Nat.eq_of_beq_eq_true hp]; exact ⟨vx, hx', hKx⟩
      · rw [← Nat.eq_of_beq_eq_true hp]; exact ⟨vy, hy', hKy⟩
    · obtain ⟨va, vb, h1, hKa, h2, hKb⟩ := hh
      simp only [Bool.or_eq_true] at hp
      rcases hp with hp | hp
      · rw [← Nat.eq_of_beq_eq_true hp]; exact ⟨va, h1, hKa⟩
      · rw [← Nat.eq_of_beq_eq_true hp]; exact ⟨vb, h2, hKb⟩
    · obtain rfl := Nat.eq_of_beq_eq_true hp
      obtain ⟨c0, rest, -, h1⟩ := hh
      exact ⟨_, h1, isInK_ofK _⟩
    · obtain rfl := Nat.eq_of_beq_eq_true hp
      obtain ⟨vx, vi, -, -, h3, h4⟩ := hh
      exact ⟨_, h3, by rw [h4, ← ofK_one]; exact isInK_ofK _⟩
    · cases hp
  · obtain ⟨q, hq, hm⟩ := List.any_eq_true.mp h
    obtain ⟨kfp, h1, -⟩ := hst.fr q hq
    rw [Nat.eq_of_beq_eq_true hm] at h1
    exact ⟨_, h1, isInK_ofK _⟩
  · obtain ⟨t, ht, hm⟩ := List.any_eq_true.mp h
    obtain ⟨p, w, -, -, hw, hK, -⟩ := hst.tg t ht
    rw [Nat.eq_of_beq_eq_true hm] at hw
    exact ⟨w, hw, hK⟩
  · obtain ⟨v, hv⟩ := Option.isSome_iff_exists.mp h
    refine ⟨_, hst.env o v hv, ?_⟩
    cases v with
    | zero => rw [Sym.val, ← ofK_zero]; exact isInK_ofK _
    | gp e => exact isInK_ofK _
    | fpg e => exact isInK_ofK _

/-! ## Passing items -/

/-- **Passed items hold**, every branch before them falling through: `passL` stops at a branch
or the end, its counts those of the items passed. -/
theorem passLB_sound (hX : CXOk L fp X) (hst : CWOkB S L fp X st) :
    ∀ (its : List Item) (c : Cnt) {its' : List Item} {c' : Cnt}, passL X st its c = .ok (its', c') →
      ∃ pre, pre ++ its' = its ∧ FallB S L (gpow fp) pre ∧
        (∀ op, c'.get op = c.get op + itemOps pre op) ∧
        (its' = [] ∨ ∃ oc od of x rest, its' = .branch oc od of x :: rest)
  | [], c, its', c', h => by
    simp only [passL, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, trivial, fun op ↦ by simp [itemOps], Or.inl rfl⟩
  | .ins (.instr pc ins) :: its, c, its', c', h => by
    simp only [passL] at h
    cases hj : justI X st pc ins
    · rw [hj] at h; cases h
    · rw [hj, Bool.cond_true, Cnt.seq_eq] at h
      obtain ⟨pre, rfl, hf, hc, hb⟩ := passLB_sound hX hst its _ h
      refine ⟨.ins (.instr pc ins) :: pre, rfl, ⟨justIB_sound hX hst hj, hf⟩, fun op ↦ ?_, hb⟩
      rw [hc, Cnt.get_bump, itemOps_cons]
      simp only [itemOp]
      omega
  | .ins (.jump oc od of) :: its, c, its', c', h => by
    simp only [passL] at h
    cases hj : cellK X st oc && cellK X st od && cellK X st of
    · rw [hj] at h; cases h
    · rw [hj, Bool.cond_true, Cnt.seq_eq] at h
      simp only [Bool.and_eq_true] at hj
      obtain ⟨⟨h1, h2⟩, h3⟩ := hj
      obtain ⟨vc, hc1, hK1⟩ := cellKB_sound hX hst h1
      obtain ⟨vd, hd1, hK2⟩ := cellKB_sound hX hst h2
      obtain ⟨vf, hf1, hK3⟩ := cellKB_sound hX hst h3
      obtain ⟨pre, rfl, hf, hc, hb⟩ := passLB_sound hX hst its _ h
      refine ⟨.ins (.jump oc od of) :: pre, rfl, ⟨⟨vc, vd, vf, hc1, hd1, hf1, hK1, hK2, hK3⟩, hf⟩,
        fun op ↦ ?_, hb⟩
      rw [hc, Cnt.get_bumpJ, itemOps_cons]
      simp only [itemOp]
      omega
  | .ins (.copy ..) :: _, _, _, _, h => by simp [passL] at h
  | .ins (.eq ..) :: _, _, _, _, h => by simp [passL] at h
  | .ins (.nz ..) :: _, _, _, _, h => by simp [passL] at h
  | .ins (.ne ..) :: _, _, _, _, h => by simp [passL] at h
  | .ins (.bool ..) :: _, _, _, _, h => by simp [passL] at h
  | .ins (.range ..) :: _, _, _, _, h => by simp [passL] at h
  | .ins (.powPair ..) :: _, _, _, _, h => by simp [passL] at h
  | .fact a :: its, c, its', c', h => by
    simp only [passL] at h
    obtain ⟨pre, rfl, hf, hc, hb⟩ := passLB_sound hX hst its _ h
    refine ⟨.fact a :: pre, rfl, hf, fun op ↦ ?_, hb⟩
    rw [hc, itemOps_cons]
    simp [itemOp]
  | .branch oc od of x :: its, c, its', c', h => by
    simp only [passL, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨[], rfl, trivial, fun op ↦ by simp [itemOps], Or.inr ⟨_, _, _, _, _, rfl⟩⟩

end Just


/-! ## At the deployed semantics -/

section Deployed

variable {κ : ℕ} {L : MemImage κ} {fp : ℕ}

/-- At the deployed semantics, `LHoldsB` is `CplJust.lean`'s `LHolds`. -/
theorem lHoldsB_deployed (a : LAtom) : LHoldsB blakeDeployed L fp a = LHolds L fp a := rfl

/-- At the deployed semantics, `BookOkB` is `CplJust.lean`'s `BookOk`. -/
theorem bookOkB_deployed (B : BookC) : BookOkB blakeDeployed L fp B = BookOk L fp B := rfl

/-- At the deployed semantics, `CWOkB` is `CplJust.lean`'s `CWOk`. -/
theorem cwOkB_deployed (X : CX) (st : CW) : CWOkB blakeDeployed L fp X st = CWOk L fp X st :=
  propext ⟨fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5⟩, fun h ↦ ⟨h.1, h.2, h.3, h.4, h.5⟩⟩

end Deployed

end
end LeanVM.Guest.B2C
